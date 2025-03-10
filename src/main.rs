use std::{
    fs,
    io::{self, Read, Write},
    os::unix::fs::PermissionsExt,
    path,
};

#[derive(Debug)]
struct Arrow {
    column: usize,
    alignment_anchor: usize,
}

#[derive(Debug)]
struct Spacing {
    start: usize,
    end: usize,
    width: usize,
}

#[derive(Debug)]
struct Line {
    /// indentation level
    indent: usize,
    /// content bytes
    content: Vec<u8>,
    arrow: Option<Arrow>,
    double_quotes: Vec<usize>,
    /// inter-token spacing adjustments
    spacing: Vec<Spacing>,
    /// never indent this line
    never_indent: bool,
    /// never truncate this line
    never_truncate: bool,
    /// don't make any changes to this row
    bypass: bool,
}

struct FormatterOptions {
    indent: bool,
    indentation: usize,
    trailing_whitespace: bool,
    double_quoted_strings: bool,
    arrow_alignment: bool,
    spacing: bool,
    strict: bool,
    verbose: bool,
}

const NON_INDENTERS: &[&str] = &[
    "manifest",
    "class_definition",
    "statement",
    "resource_body",
    "attribute_list",
    "argument_list",
    "define_definition",
    "function_definition",
    "if",
    "else",
    "binary",
];

#[derive(argh::FromArgs)]
#[argh(description = "autoformatting for puppet manifests")]
struct Args {
    #[argh(switch, short = 'n', description = "don't auto-indent lines")]
    no_indent: bool,
    #[argh(
        option,
        short = 'N',
        description = "number of spaces for indentation (default 2)",
        default = "2"
    )]
    indentation: usize,
    #[argh(switch, short = 'w', description = "don't remove trailing whitespace")]
    no_trailing_whitespace: bool,
    #[argh(
        switch,
        short = 't',
        description = "don't replace double quotes with single quotes for raw strings"
    )]
    no_double_quoted_strings: bool,
    #[argh(switch, short = 'r', description = "don't fix arrow alignments")]
    no_arrow_alignment: bool,
    #[argh(
        switch,
        short = 's',
        description = "don't adjust spacing between tokens (only for resource declarations atm)"
    )]
    no_spacing: bool,
    #[argh(switch, short = 'S', description = "abort on any parser errors")]
    strict: bool,
    #[argh(switch, short = 'v', description = "show diagnostic messages")]
    verbose: bool,
    #[argh(switch, short = 'i', description = "overwrite input file")]
    in_place: bool,
    #[argh(option, short = 'o', description = "destination filename")]
    output: Option<String>,
    #[argh(
        positional,
        description = "manifest filename, read manifest from stdin if absent"
    )]
    filename: Option<String>,
}

impl From<&Args> for FormatterOptions {
    fn from(value: &Args) -> Self {
        Self {
            indent: !value.no_indent,
            indentation: value.indentation,
            trailing_whitespace: !value.no_trailing_whitespace,
            double_quoted_strings: !value.no_double_quoted_strings,
            arrow_alignment: !value.no_arrow_alignment,
            spacing: !value.no_spacing,
            strict: value.strict,
            verbose: value.verbose,
        }
    }
}

fn main() -> anyhow::Result<()> {
    let args: Args = argh::from_env();
    let mut code = Vec::with_capacity(8192);
    let mut permissions = None;
    if let Some(ref filename) = args.filename {
        let mut f = fs::File::open(filename)?;
        permissions = Some(f.metadata()?.permissions());
        f.read_to_end(&mut code)?;
    } else {
        io::stdin().read_to_end(&mut code)?;
    }
    let dest_path = if args.in_place {
        &args.filename
    } else {
        &args.output
    }
    .as_ref()
    .map(path::Path::new);
    let opts: FormatterOptions = (&args).into();
    let formatted_code = format(&mut code, opts)?;
    if let Some(dest) = dest_path {
        let tmp = {
            let mut builder = tempfile::Builder::new();
            builder.permissions(permissions.unwrap_or(fs::Permissions::from_mode(0o666)));
            if let Some(parent_dir) = dest.parent() {
                builder.tempfile_in(parent_dir)
            } else {
                builder.tempfile()
            }?
        };
        {
            let mut out = io::BufWriter::new(&tmp);
            formatted_code.into_iter().for_each(|line| {
                out.write_all(&line).unwrap();
                out.write_all(b"\n").unwrap();
            });
        }
        tmp.persist(dest)?;
    } else {
        let mut stdout = io::BufWriter::new(io::stdout().lock());
        formatted_code.into_iter().for_each(|line| {
            stdout.write_all(&line).unwrap();
            stdout.write_all(b"\n").unwrap();
        });
    }
    Ok(())
}

fn parse(code: &[u8], lines: &mut [Line], strict: bool, verbose: bool) -> anyhow::Result<()> {
    let mut parser = tree_sitter::Parser::new();
    parser.set_language(&tree_sitter_puppet::language())?;
    let tree = parser.parse(code, None).unwrap();
    let mut cursor = tree.walk();
    let mut last_resource_declaration = 0;
    let mut indented_ranges = rustc_hash::FxHashMap::default();

    // the values of the indented_ranges hashmap aren't used, this is just something
    // that can be helpful when trying to figure out why a line was indented
    fn indentation_value(n: &tree_sitter::Node) -> (&'static str, [usize; 2], [usize; 2]) {
        let start = n.start_position();
        let end = n.end_position();
        (n.kind(), [start.row, start.column], [end.row, end.column])
    }
    let mut lexical_indentation: Option<[usize; 2]> = None;
    loop {
        let node = &cursor.node();
        let node_start_row = node.start_position().row;
        let node_end_row = node.end_position().row;
        let node_kind = node.kind();
        if node_start_row != node_end_row && !NON_INDENTERS.contains(&node_kind) {
            let block_start = node_start_row + 1;
            if node_kind == "}" && node.start_byte() == node.end_byte() {
                if verbose {
                    eprintln!("found parser generated zero-length '}}', indenting next line");
                }
                indented_ranges.insert([block_start, block_start], indentation_value(node));
            }
            let mut block_end = node_end_row;
            let last_line = &code[node.end_byte() - node.end_position().column..node.end_byte()]
                .trim_ascii_start();
            if !last_line.is_empty() && block_end > 0 {
                let first_byte = last_line[0];
                if first_byte == b'}' || first_byte == b']' || first_byte == b')' {
                    block_end -= 1;
                }
            }
            if block_end >= block_start {
                indented_ranges
                    .entry([block_start, block_end])
                    .or_insert_with(|| indentation_value(node));
            }
        }

        if node_kind == "ERROR" {
            let contents = String::from_utf8_lossy(&lines[node_start_row].content);
            if strict {
                return Err(anyhow::anyhow!(
                    "parse error: {}:{}: \n{}",
                    node_start_row + 1,
                    node.start_position().column + 1,
                    contents,
                ));
            }
            if verbose {
                eprintln!(
                    "failed to parse line {}:\n{}\nskipping rest of file",
                    node_start_row + 1,
                    contents
                );
            }
            (node_start_row..lines.len()).for_each(|i| lines[i].bypass = true);
            break;
        }

        if node_kind == "double_quoted_string" {
            let contains_single_quote = code[node.start_byte()..node.end_byte()]
                .iter()
                .any(|b| *b == b'\'');
            let is_raw = node.child(0).map(|n| n.kind()) == Some("\"")
                && node.child(1).map(|n| n.kind()) == Some("\"")
                && node.child(2).is_none();
            if is_raw && !contains_single_quote {
                lines[node_start_row]
                    .double_quotes
                    .push(node.start_position().column);
                lines[node_end_row]
                    .double_quotes
                    .push(node.end_position().column - 1);
            }
        }

        if node_kind == "arrow" && lines[node_start_row].arrow.is_none() {
            let grandparent = node.parent().and_then(|n| n.parent()).map(|n| n.kind());
            // These should be aligned independently
            //
            // file { '/etc/dir':
            //   ensure => directory
            //   ;
            //   '/etc/dir2':
            //   ensure  => file,
            //   content => ''
            // }
            let target = if grandparent == Some("attribute_list") {
                last_resource_declaration
            } else {
                // $hash0 = {
                //   a => 1,
                //   b => 2,
                //   c => {
                //     d => 5
                //   }
                // }

                let mut hash_byte = 0;

                // TODO: why doesn't this walk?
                //
                // let mut walk = node.walk();
                // while walk.goto_parent() {
                //     let n = walk.node();
                //     if n.kind() == "hash" {
                //         hash_byte = n.start_byte();
                //         break;
                //     }
                // }
                let mut n2 = Some(*node);
                while let Some(hash_needle) = n2 {
                    if hash_needle.kind() == "hash" {
                        hash_byte = hash_needle.start_byte();
                        break;
                    }
                    n2 = hash_needle.parent();
                }
                hash_byte
            };
            if target > 0 {
                lines[node_start_row].arrow = Some(Arrow {
                    column: node.start_position().column,
                    alignment_anchor: target,
                });
            } else if verbose && grandparent != Some("selector") {
                eprintln!(
                    "could not find alignment anchor for => at {}:{}",
                    node.start_position().row + 1,
                    node.start_position().column + 1
                );
            }
        }

        // spacing adjustment
        if node_kind == "resource_type" {
            let identifier = node.child(0);
            let curlopen = node.child(1).filter(|n| n.kind() == "{");
            let resource_body = node.child(2).filter(|n| n.kind() == "resource_body");
            let resource_title = resource_body
                .and_then(|n| n.child(0))
                .filter(|n| n.kind() == "resource_title");
            let colon = resource_body
                .and_then(|n| n.child(1))
                .filter(|n| n.kind() == ":");
            for (left, right, spacing) in ([
                (identifier, curlopen, 1),
                (curlopen, resource_body, 1),
                (resource_title, colon, 0),
            ])
            .iter()
            .filter_map(|(n0, n1, s)| {
                if let Some(m0) = n0 {
                    if let Some(m1) = n1 {
                        return Some((m0, m1, s));
                    }
                }
                None
            }) {
                let row = left.end_position().row;
                if row == right.start_position().row {
                    lines[row].spacing.push(Spacing {
                        start: left.end_position().column,
                        end: right.start_position().column,
                        width: *spacing,
                    });
                }
            }
        }

        // preserve leading and trailing whitespace in multiline strings
        if node_kind == "single_quoted_string"
            || node_kind == "double_quoted_string"
            || node_kind == "heredoc"
        {
            (node_start_row + 1..node.end_position().row + 1).for_each(|row| {
                lines[row].never_indent = true;
            });
            (node_start_row..node.end_position().row).for_each(|row| {
                lines[row].never_truncate = true;
            });
        }

        if node_kind == ":" || node_kind == ";" {
            if let Some(resource_name) = node.prev_sibling() {
                if let Some(resource_declaration) = node.parent() {
                    if let Some(mut block) = lexical_indentation {
                        block[1] = block[1].min(node_start_row - 1);
                        indented_ranges.insert(block, indentation_value(&resource_name));
                        lexical_indentation = None;
                    }
                    if node_kind == ":" {
                        // this cannot be found for an arrow when traversing the tree, so
                        // it must be determined lexically
                        if node.parent().map(|n| n.kind()) == Some("resource_body") {
                            last_resource_declaration = node.start_byte();
                        }
                        lexical_indentation = Some([
                            resource_name.start_position().row + 1,
                            resource_declaration.end_position().row,
                        ])
                    } else {
                        // node_kind == ";"
                        last_resource_declaration = 0;
                    }
                }
            }
        }

        let found_child = cursor.goto_first_child();
        if !found_child {
            let found_sibling = cursor.goto_next_sibling();
            if !found_sibling {
                let done = loop {
                    if !cursor.goto_parent() {
                        break true;
                    }
                    if cursor.goto_next_sibling() {
                        break false;
                    }
                };
                if done {
                    break;
                }
            }
        }
    }

    if let Some(block) = lexical_indentation {
        indented_ranges.insert(block, ("unknown", [0, 0], [0, 0]));
    }
    let mut indentations: Vec<_> = indented_ranges.into_keys().collect();
    indentations.sort_unstable();
    lines
        .iter_mut()
        .enumerate()
        .filter(|(_, line)| !(line.bypass || line.never_indent || line.content.is_empty()))
        .for_each(|(row, line)| {
            line.indent = indentations
                .iter()
                .take_while(|range| range[0] <= row)
                .filter(|range| range[1] >= row)
                .count();
        });
    Ok(())
}

fn format(code: &mut [u8], opts: FormatterOptions) -> anyhow::Result<Vec<Vec<u8>>> {
    let mut lines: Vec<_> = code
        .split(|b| *b == b'\n')
        .map(|s| Line {
            indent: 0,
            content: s.to_vec(),
            arrow: None,
            double_quotes: Vec::new(),
            spacing: Vec::new(),
            never_indent: false,
            never_truncate: false,
            bypass: false,
        })
        .collect();

    parse(code, &mut lines, opts.strict, opts.verbose)?;
    // remove last line if empty
    if lines
        .last()
        .map(|l| &l.content)
        .take_if(|c| c.is_empty())
        .is_some()
    {
        lines.pop();
    }

    struct ArrowPosition {
        row: usize,
        column: usize,
    }
    // mapping from start byte of resource declaration to vec of arrow positions
    let mut arrows_by_resource_declarations = rustc_hash::FxHashMap::default();
    lines
        .iter_mut()
        .enumerate()
        .filter(|(_, line)| !line.bypass)
        .for_each(|(row_number, line)| {
            // fix double quoted non-interpolated strings
            if opts.double_quoted_strings {
                line.double_quotes
                    .iter()
                    .for_each(|column| line.content[*column] = b'\'');
            }
            // autospacing
            if opts.spacing && !line.spacing.is_empty() {
                let old_len = line.content.len();
                line.spacing.iter().rev().for_each(|spacing| {
                    if spacing.width < spacing.end - spacing.start {
                        line.content
                            .drain(spacing.start + spacing.width..spacing.end);
                    }
                    if spacing.width > spacing.end - spacing.start {
                        (spacing.end - spacing.start..spacing.width).for_each(|_| {
                            line.content.insert(spacing.start, b' ');
                        });
                    }
                });
                // adjust arrow to new column index
                if let Some(arrow) = &mut line.arrow {
                    if old_len != line.content.len() {
                        let last_spacing = line.spacing.last().unwrap().end;
                        if arrow.column > last_spacing {
                            arrow.column = arrow.column + line.content.len() - old_len
                        }
                    }
                }
            }
            // autoindent lines
            if opts.indent && !line.never_indent {
                let indent = opts.indentation * line.indent;
                let trimmed = line.content.trim_ascii_start();
                if !trimmed.is_empty() && line.content.len() - trimmed.len() != indent {
                    let mut new_line = Vec::with_capacity(trimmed.len() + indent);
                    (0..indent).for_each(|_| new_line.push(b' '));
                    new_line.extend_from_slice(trimmed);
                    // adjust arrow to new column index
                    if let Some(arrow) = &mut line.arrow {
                        arrow.column = arrow.column + new_line.len() - line.content.len();
                    }
                    line.content = new_line;
                }
            };

            // batch arrows by their owning resource declarations
            if let Some(ref arrow) = line.arrow {
                arrows_by_resource_declarations
                    .entry(arrow.alignment_anchor)
                    .or_insert_with(Vec::new)
                    .push(ArrowPosition {
                        row: row_number,
                        column: arrow.column,
                    });
            };

            // remove trailing whitespace
            if opts.trailing_whitespace && !line.never_truncate {
                line.content.truncate(line.content.trim_ascii_end().len());
            }
        });

    // align arrows
    if opts.arrow_alignment {
        arrows_by_resource_declarations
            .into_values()
            // process all arrows beloning to the same resource declaration
            .for_each(|arrow_list| {
                let min_column = if arrow_list.len() == 1 {
                    0
                } else {
                    arrow_list
                        .iter()
                        .map(|arrow| {
                            lines[arrow.row]
                                .content
                                .split_at(arrow.column)
                                .0
                                .trim_ascii_end()
                                .len()
                        })
                        .max()
                        .unwrap_or(0)
                };
                arrow_list.into_iter().for_each(|arrow| {
                    let line = &mut lines[arrow.row];
                    line.content = {
                        let (left, right) = &line.content.split_at(arrow.column);
                        let mut new_line = line.content.clone();
                        new_line.truncate(left.trim_ascii_end().len());
                        if min_column > new_line.len() {
                            (new_line.len()..min_column).for_each(|_| new_line.push(b' '));
                        }
                        new_line.extend_from_slice(b" => ");
                        new_line.extend_from_slice(right[2..].trim_ascii_start());
                        new_line
                    };
                });
            });
    }
    Ok(lines.into_iter().map(|l| l.content).collect())
}

#[cfg(test)]
mod tests {

    use super::*;

    const CODE0: &str = r#"# test class
class test(
  String $var0,  
  String $var1 = "aoeu",
   String $var2 = "$htns",
  String $var3 = "a$htns",
 String $var4 = "
   aoeu",
) {

file { "${dir}/name":
    ensure    => file,
     mode  => '0755',
content => template('template.erb'),
    }
}
"#;

    fn code(src: &str) -> Vec<u8> {
        src.as_bytes().to_vec()
    }

    fn test_format_code(expected: &str, input: &str, opts: FormatterOptions) {
        let expected_lines = expected.split('\n').map(String::from);
        let actual_lines = format(&mut input.as_bytes().to_vec(), opts)
            .unwrap()
            .into_iter()
            .enumerate()
            .map(|(i, v)| {
                let line = String::from_utf8_lossy(&v).to_string();
                eprintln!("{}: {}", i, line);
                line
            });
        expected_lines
            .zip(actual_lines)
            .enumerate()
            .for_each(|(i, (e, a))| assert_eq!(e, a, "line {} mismatch", i));
    }

    fn opts() -> FormatterOptions {
        FormatterOptions {
            indent: false,
            indentation: 2,
            trailing_whitespace: false,
            double_quoted_strings: false,
            arrow_alignment: false,
            spacing: false,
            strict: true,
            verbose: true,
        }
    }

    #[test]
    fn test_arrow_alignment() {
        let mut opts = opts();
        opts.indent = true;
        opts.arrow_alignment = true;
        let lines = format(&mut code(CODE0), opts).unwrap();
        assert_eq!(String::from_utf8_lossy(&lines[11]), "    ensure  => file,");
        assert_eq!(
            String::from_utf8_lossy(&lines[12]),
            "    mode    => '0755',"
        );
        assert_eq!(
            String::from_utf8_lossy(&lines[13]),
            "    content => template('template.erb'),"
        );
    }

    #[test]
    fn test_double_quoted() {
        let mut opts = opts();
        opts.double_quoted_strings = true;
        let lines = format(&mut code(CODE0), opts).unwrap();
        assert_eq!(
            String::from_utf8_lossy(&lines[3]),
            "  String $var1 = 'aoeu',"
        );
        assert_eq!(
            String::from_utf8_lossy(&lines[4]),
            r#"   String $var2 = "$htns","#
        );
        assert_eq!(
            String::from_utf8_lossy(&lines[5]),
            r#"  String $var3 = "a$htns","#
        );
    }

    #[test]
    fn test_trailing_whitespace() {
        let mut opts = opts();
        opts.trailing_whitespace = true;
        let lines = format(&mut code(CODE0), opts).unwrap();
        assert_eq!(String::from_utf8_lossy(&lines[2]), r#"  String $var0,"#);
    }

    #[test]
    fn test_autoindent() {
        let mut opts = opts();
        opts.indent = true;
        let lines = format(&mut code(CODE0), opts).unwrap();
        assert_eq!(
            String::from_utf8_lossy(&lines[3]),
            r#"  String $var1 = "aoeu","#
        );
        assert_eq!(
            String::from_utf8_lossy(&lines[4]),
            r#"  String $var2 = "$htns","#
        );
        assert_eq!(String::from_utf8_lossy(&lines[6]), r#"  String $var4 = ""#);
        assert_eq!(String::from_utf8_lossy(&lines[7]), r#"   aoeu","#);
        assert_eq!(String::from_utf8_lossy(&lines[14]), r#"  }"#);
        assert_eq!(String::from_utf8_lossy(&lines[15]), r#"}"#);
        assert_eq!(
            String::from_utf8_lossy(&lines[10]),
            r#"  file { "${dir}/name":"#
        );
        assert_eq!(
            String::from_utf8_lossy(&lines[11]),
            "    ensure    => file,"
        );
    }

    #[test]
    fn test_relation() {
        let mut opts = opts();
        opts.indent = true;
        let code = r#"
class test_class() {
  file { 'f0':
    ensure => file,
  }
  -> file {'f1':
    ensure => file,
  }
}
"#;
        let lines = format(&mut code.as_bytes().to_vec(), opts).unwrap();
        let mut actual = String::new();
        lines.into_iter().for_each(|l| {
            actual.push_str(&String::from_utf8_lossy(&l));
            actual.push('\n');
        });
        assert_eq!(code, actual);
    }

    #[test]
    fn test_multiline() {
        let mut opts = opts();
        opts.indent = true;
        opts.trailing_whitespace = true;
        let code = r#"
class test_class() {
  file { '  
 f0  
   f1  
 f3  ':
    ensure => file,
  }
  file { " 
 f0
   f1
 f3":
    ensure => file,
  }
}
"#;
        let lines = format(&mut code.as_bytes().to_vec(), opts).unwrap();
        let mut actual = String::new();
        lines.into_iter().for_each(|l| {
            actual.push_str(&String::from_utf8_lossy(&l));
            actual.push('\n');
        });
        assert_eq!(code, actual);
    }

    #[test]
    fn test_heredoc() {
        let mut opts = opts();
        opts.indent = true;
        opts.trailing_whitespace = true;
        opts.arrow_alignment = true;
        opts.double_quoted_strings = true;
        let code = r#"
class test_class() {
  file { '/etc/file':
    ensure   => 'file',
    content2 => @("GITCONFIG"/L)
      [user]
          name = ${displayname}
          email = ${email}
      [color]
          ui = true
      [alias]
          lg = "log --pretty=format:'%C(yellow)%h%C(reset) %s \
      %C(cyan)%cr%C(reset) %C(blue)%an%C(reset) %C(green)%d%C(reset)' --graph"
          wdiff = diff --word-diff=color --ignore-space-at-eol \
      --word-diff-regex='[[:alnum:]]+|[^[:space:][:alnum:]]+'
      [merge]
          defaultToUpstream = true
      [push]
          default = upstream
      | GITCONFIG
    ,
    content  => @(GITCONFIG/L)
          default = upstream
      | GITCONFIG
    ,
  }
}
"#;
        test_format_code(code, code, opts);
    }

    #[test]
    fn test_autospace() {
        let mut opts = opts();
        opts.spacing = true;
        let code = r#"
class test_class() {
  file{'/etc/dir' : ensure => directory }
}"#;
        let lines = format(&mut code.as_bytes().to_vec(), opts).unwrap();
        assert_eq!(
            "  file { '/etc/dir': ensure => directory }",
            String::from_utf8_lossy(&lines[2])
        );
    }

    #[test]
    fn test_class() {
        let mut opts = opts();
        opts.spacing = true;
        opts.indent = true;
        opts.strict = false;
        opts.verbose = true;
        let code = r#"
class test_class() {
  class { 'klass':
    a => {
      b => "c"
    }
  }
}
"#;
        test_format_code(code, code, opts);
    }

    #[test]
    fn test_resource_like_class_definition() {
        let mut opts = opts();
        opts.indent = true;
        opts.arrow_alignment = true;
        opts.strict = false;
        let expected = r#"
class test_class() {
  class { 'klass':
    a => {
      b => "c"
    },
    c => "d"
  }
}"#;

        let mangled_code = expected.replace(" => ", "=>").replace("\n  ", "\n");
        test_format_code(expected, &mangled_code, opts);
    }

    #[test]
    fn test_if_else() {
        let tests = [
            r#"class test_class() {
  if $a {
    info("a")
    info("b")
  }
}
"#,
            r#"class test_class() {
  if $a {
    info("a")
  } else {
    info("b")
  }
}
"#,
        ];
        tests.iter().for_each(|expected| {
            let mut opts = opts();
            opts.indent = true;
            opts.strict = false;
            let mangled_code: String = expected
                .split_inclusive("\n")
                .map(|s| s.trim_start())
                .collect();
            test_format_code(expected, &mangled_code, opts);
        });
    }

    #[test]
    fn extra_indentation() {
        let mut opts = opts();
        opts.indent = true;
        let code = r#"
class test_class() {
  file {
    '/etc/dir':
      ensure => directory,
      mode   => '0755',
    ;
    '/etc/dir2':
      ensure => directory,
      mode   => '0755',
  }
}
"#;
        test_format_code(code, code, opts);
    }

    #[test]
    fn test_hash() {
        let mut opts = opts();
        opts.indent = true;
        let code = r#"
class test_class() {
  $h = {
    a => {
      b => 'c'
    }
  }
}
"#;
        let lines = format(&mut code.as_bytes().to_vec(), opts).unwrap();
        let mut actual = String::new();
        lines.into_iter().for_each(|l| {
            actual.push_str(&String::from_utf8_lossy(&l));
            actual.push('\n')
        });
        assert_eq!(code, actual);
    }

    #[test]
    fn dont_align_selector_arrows() {
        let mut opts = opts();
        opts.arrow_alignment = true;
        let code = r#"
if $maybe {
  $var = $prod ? {
    true => 'option1',
    false => 'option2',
  }
}
"#;
        let lines = format(&mut code.as_bytes().to_vec(), opts).unwrap();
        let mut actual = String::new();
        lines.into_iter().for_each(|l| {
            actual.push_str(&String::from_utf8_lossy(&l));
            actual.push('\n')
        });
        assert_eq!(code, actual);
    }

    #[test]
    fn define_and_function() {
        let tests = [
            // defined_resource_type
            r#"
define org::name(
  String $version=latest,
)
{
  $password = lookup('password, undef, undef, undef)
}
"#,
            // function_declaration
            r#"
function ns::func(
  Hash[String, Hash] $config,
) >> Array[String] {
  ['str']
}
"#,
        ];
        tests.iter().for_each(|test| {
            let mut opts = opts();
            opts.indent = true;
            opts.strict = false;
            test_format_code(test, test, opts);
        });
    }

    #[test]
    fn test_fold_2_indentations() {
        let tests = [r#"
define org::name(
  String $version=latest,
)
{
  ensure_resource('file','/etc/file.txt', {
    content  => file('f/file.txt')
  })
}
"#];
        tests.iter().for_each(|test| {
            let mut opts = opts();
            opts.indent = true;
            opts.strict = false;
            test_format_code(test, test, opts);
        });
    }

    #[test]
    fn test_single_quote_in_double_quoted_string() {
        let do_quote = r#"
define org::name(
  String $version="single-quote this",
) {}
"#;
        let mut opt = opts();
        opt.double_quoted_strings = true;
        test_format_code(&do_quote.replace("\"", "'"), do_quote, opt);

        let dont_quote = r#"
define org::name(
  String $version="don't single-quote this",
) {}
"#;
        let mut opt = opts();
        opt.double_quoted_strings = true;
        test_format_code(dont_quote, dont_quote, opt);

        let also_dont_quote = r#"
define org::name(
  String $version="do not single-quote ${this}",
) {}
"#;
        let mut opt = opts();
        opt.double_quoted_strings = true;
        test_format_code(also_dont_quote, also_dont_quote, opt);
    }

    #[test]
    fn argument_list() {
        let code = r#"
function ns::func() {
  $_choice = pick(
    $facts['f0'][$f1]['opt1'],
    $facts['f0'][$f1]['opt2'],
    $facts['f0'][$f1]['opt3'],
    $facts['f0'][$f1]['opt4'],
    $facts['f0'][$f1]['opt5'],
    '',
  )
}
"#;
        let mut opt = opts();
        opt.indent = true;
        test_format_code(code, code, opt);
    }

    #[test]
    fn and_and_and() {
        let code = r#"
function ns::func() {
  if a
    and b
    and c {
    d
  }
}
"#;
        let mut opt = opts();
        opt.indent = true;
        test_format_code(code, code, opt);
    }
}
