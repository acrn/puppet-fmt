use std::{
    fs,
    io::{self, Read, Write},
    mem,
};

#[derive(Debug)]
struct Arrow {
    column: usize,
    target_resource: usize,
}

#[derive(Debug)]
struct Spacing {
    start: usize,
    end: usize,
    width: usize,
}

#[derive(Debug)]
struct Line {
    row: usize,
    depth: usize,
    indent: usize,
    first_kind: &'static str,
    last_kind: &'static str,
    /// content bytes
    content: Vec<u8>,
    /// raw bytes to append unformatted
    raw: Vec<u8>,
    arrow: Option<Arrow>,
    double_quotes: Vec<usize>,
    /// inter-token spacing adjustments
    spacing: Vec<Spacing>,
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
}

const NON_INDENTERS: &[&str] = &[
    "source_file",
    "class_definition", // always followed by "block"
    "relation",         // ->
    "if_statement",     // followed by "block"
    "else_statement",
];

#[derive(argh::FromArgs)]
#[argh(description = "autoformatting for puppet manifests")]
struct Args {
    #[argh(switch, short = 'a', description = "fix all formatting")]
    all: bool,
    #[argh(switch, short = 'i', description = "auto-indent lines")]
    indent: bool,
    #[argh(
        option,
        short = 'n',
        description = "number of spaces for indentation (default 2)",
        default = "2"
    )]
    indentation: usize,
    #[argh(switch, short = 'w', description = "remove trailing whitespace")]
    trailing_whitespace: bool,
    #[argh(
        switch,
        short = 't',
        description = "replace double quotes with single quotes for raw strings"
    )]
    double_quoted_strings: bool,
    #[argh(
        switch,
        short = 'r',
        description = "fix arrow alignment in resource declarations"
    )]
    arrow_alignment: bool,
    #[argh(
        switch,
        short = 's',
        description = "adjust spacing between tokens (only for resource declarations atm)"
    )]
    spacing: bool,
    #[argh(
        positional,
        description = "manifest filename, read manifest from stdin if absent"
    )]
    filename: Option<String>,
}

impl From<Args> for FormatterOptions {
    fn from(value: Args) -> Self {
        Self {
            indent: value.indent || value.all,
            indentation: value.indentation,
            trailing_whitespace: value.trailing_whitespace || value.all,
            double_quoted_strings: value.double_quoted_strings || value.all,
            arrow_alignment: value.arrow_alignment || value.all,
            spacing: value.spacing || value.all,
        }
    }
}

fn main() -> anyhow::Result<()> {
    let args: Args = argh::from_env();
    let mut code = Vec::with_capacity(8192);
    if let Some(ref filename) = args.filename {
        fs::File::open(filename)?.read_to_end(&mut code)?;
    } else {
        io::stdin().read_to_end(&mut code)?;
    }
    let opts: FormatterOptions = args.into();
    let fixed = format(&mut code, opts)?;
    let mut stdout = io::BufWriter::new(io::stdout().lock());
    fixed.into_iter().for_each(|line| {
        stdout.write_all(&line).unwrap();
        stdout.write_all(b"\n").unwrap();
    });
    Ok(())
}

fn parse(code: &[u8], lines: &mut [Line]) -> anyhow::Result<()> {
    let mut parser = tree_sitter::Parser::new();
    let lang = tree_sitter_puppet::LANGUAGE;
    parser.set_language(&lang.into())?;
    let tree = parser.parse(code, None).unwrap();
    let mut stack: Vec<tree_sitter::Node<'_>> = Vec::new();
    let mut cursor = tree.walk();
    let mut eat_double_quote = false;
    loop {
        let node = &cursor.node();
        let node_row = node.start_position().row;
        if node.kind() == "ERROR" {
            // the parser doesn't support inline classes
            if code[node.byte_range()] == *b"class" {
                cursor.goto_next_sibling();
                eprintln!(
                    "cannot parse class, skipping {}->{}",
                    node_row + 1,
                    cursor.node().end_position().row + 1
                );
                (node_row..cursor.node().end_position().row + 1)
                    .for_each(|row| lines[row].bypass = true);
                if cursor.goto_next_sibling() {
                    continue;
                }
            };
            return Err(anyhow::anyhow!(
                "parse error: {}:{}",
                node_row + 1,
                node.start_position().column + 1,
            ));
        }
        if node.kind() == "\"" {
            if !eat_double_quote {
                let next_node = node.next_sibling();
                let next_next_node = next_node.and_then(|n| n.next_sibling());
                if let Some(corresponding) = next_next_node {
                    if corresponding.kind() == "\""
                        && Some("string_content") == next_node.map(|n| n.kind())
                    {
                        lines[node_row]
                            .double_quotes
                            .push(node.start_position().column);
                        lines[corresponding.start_position().row]
                            .double_quotes
                            .push(corresponding.start_position().column)
                    }
                }
            }
            eat_double_quote = !eat_double_quote;
        }
        if node.kind() == "=>" {
            if let Some(resource_declaration) = node
                .parent()
                .and_then(|n| n.parent())
                .take_if(|n| n.kind() == "resource_declaration")
            {
                lines[node_row].arrow = Some(Arrow {
                    column: node.start_position().column,
                    target_resource: resource_declaration.start_byte(),
                });
            } else {
                eprintln!(
                    "could not find resource declaration for => at {}:{}",
                    node.start_position().row,
                    node.start_position().column
                );
            }
        }
        if node.kind() == "resource_declaration" {
            let identifier = node.child(0);
            let curlopen = node.child(1);
            let name = node.child(2);
            let colon = node.child(3);
            let attribute = node.child(4);
            let neighbors = [identifier, curlopen, name, colon, attribute];
            neighbors
                .iter()
                .zip(neighbors.iter().skip(1))
                .filter_map(|(a, b)| {
                    if let Some(some_a) = a {
                        if let Some(some_b) = b {
                            if some_a.start_position().row == some_b.start_position().row {
                                let space = if some_b.kind() == ":" { 0 } else { 1 };
                                return Some((some_a, some_b, space));
                            }
                        }
                    }
                    None
                })
                .for_each(|(a, b, space)| {
                    let one_space = [a.end_position().column, b.start_position().column];
                    if one_space[1] - one_space[0] != space {
                        lines[a.start_position().row].spacing.push(Spacing {
                            start: a.end_position().column,
                            end: b.start_position().column,
                            width: space,
                        });
                    }
                });
        }
        lines[node_row].last_kind = node.kind();
        if node.kind() == "string_content" {
            (node_row + 1..node.end_position().row + 1).for_each(|row| {
                lines[row].first_kind = node.kind();
                lines[row].last_kind = node.kind();
            });
        }
        if lines[node_row].first_kind.is_empty() {
            lines[node_row].first_kind = node.kind();
            lines[node_row].depth = stack.len();
            // '{' should indent once, but so should also '({' if on the same line
            let mut unique_indenters_by_line = rustc_hash::FxHashMap::default();
            stack
                .iter()
                .filter(|n| !NON_INDENTERS.contains(&n.kind()))
                .for_each(|n| {
                    unique_indenters_by_line.insert(n.start_position().row, n);
                });
            lines[node_row].indent = unique_indenters_by_line.len();
        }
        let found_child = cursor.goto_first_child();
        if found_child {
            stack.push(*node);
        } else {
            let found_sibling = cursor.goto_next_sibling();
            if !found_sibling {
                let done = loop {
                    if cursor.goto_parent() {
                        stack.pop();
                    } else {
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
    Ok(())
}

struct HeredocStart<'a> {
    identifier: &'a [u8],
    left: &'a [u8],
    right: &'a [u8],
}

fn heredoc_start(line: &[u8]) -> Option<HeredocStart> {
    let mut split = line.rsplitn(2, |b| *b == b'@');
    let right = split.next();
    let left = split.next();
    if let Some(left_of_heredoc) = left {
        if let Some(mut heredoc_marker) = right {
            if left_of_heredoc.contains(&b'#') {
                return None;
            }
            heredoc_marker = &line[left_of_heredoc.len()..];
            if heredoc_marker.len() < 4 {
                return None;
            }
            if heredoc_marker[1] != b'(' || heredoc_marker.trim_ascii_end().last() != Some(&b')') {
                return None;
            }
            let mut i0 = 2;
            while heredoc_marker[i0] == b' ' || heredoc_marker[i0] == b'"' {
                i0 += 1;
            }
            let mut i1 = i0;
            while !(heredoc_marker[i1] == b' '
                || heredoc_marker[i1] == b'"'
                || heredoc_marker[i1] == b'/'
                || heredoc_marker[i1] == b')')
            {
                i1 += 1;
            }
            return Some(HeredocStart {
                identifier: &heredoc_marker[i0..i1],
                left: left_of_heredoc,
                right: heredoc_marker,
            });
        }
    }
    None
}

fn heredoc_end(line: &[u8], id: &[u8]) -> bool {
    let trimmed = line.trim_ascii();
    if !trimmed.starts_with(b"|") {
        return false;
    }
    trimmed.ends_with(id)
}

fn format(code: &mut [u8], opts: FormatterOptions) -> anyhow::Result<Vec<Vec<u8>>> {
    let mut in_heredoc = None;
    let mut offset = 0;
    // i list of (offset, bytes) to replace in the code prior to parsing (for heredocs)
    let mut replace = Vec::new();
    // a list of [start, end] offsets to replace with whitespace (for heredocs)
    let mut erase = Vec::new();
    let mut lines: Vec<_> = code
        .split(|b| *b == b'\n')
        .enumerate()
        .map(|(row, s)| {
            let mut line = Line {
                row,
                depth: 0,
                indent: 0,
                first_kind: "",
                last_kind: "",
                content: s.to_vec(),
                raw: Vec::new(),
                arrow: None,
                double_quotes: Vec::new(),
                spacing: Vec::new(),
                bypass: false,
            };
            if let Some(identifier) = in_heredoc {
                if heredoc_end(&line.content, identifier) {
                    in_heredoc = None;
                }
                // move line contents to raw to prevent formatting
                mem::swap(&mut line.content, &mut line.raw);
                // replace heredoc with whitespace prior to parsing
                erase.push([offset, offset + s.len()]);
            } else if let Some(heredoc) = heredoc_start(s) {
                line.content = heredoc.left.to_vec();
                line.raw = heredoc.right.to_vec();
                // replace heredoc with '' and whitespace prior to parsing
                replace.push((offset + line.content.len(), b"''"));
                erase.push([
                    offset + line.content.len() + 2,
                    offset + line.content.len() + line.raw.len(),
                ]);
                in_heredoc = Some(heredoc.identifier)
            }
            offset += s.len() + 1;
            line
        })
        .collect();
    if let Some(heredoc) = in_heredoc {
        return Err(anyhow::anyhow!(
            "unterminated heredoc: {}",
            String::from_utf8_lossy(heredoc)
        ));
    }
    replace.into_iter().for_each(|(offset, b)| {
        b.iter()
            .enumerate()
            .for_each(|(i, b)| code[offset + i] = *b);
    });
    erase.into_iter().for_each(|e| {
        (e[0]..e[1]).for_each(|i| code[i] = b' ');
    });

    parse(code, &mut lines)?;
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
        .filter(|line| !line.bypass)
        .for_each(|line| {
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
            if opts.indent && line.first_kind != "string_content" {
                let mut indent = opts.indentation * line.indent;
                if indent > 0 && line.first_kind == "}"
                    || line.first_kind == ")"
                    || line.first_kind == "]"
                {
                    indent -= opts.indentation;
                }
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
                    .entry(arrow.target_resource)
                    .or_insert_with(Vec::new)
                    .push(ArrowPosition {
                        row: line.row,
                        column: arrow.column,
                    });
            };

            // remove trailing whitespace
            if opts.trailing_whitespace && line.last_kind != "string_content" {
                line.content.truncate(line.content.trim_ascii_end().len());
            }
            line.content.extend_from_slice(&line.raw);
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
 String $var4 = "\
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

    fn opts() -> FormatterOptions {
        FormatterOptions {
            indent: false,
            indentation: 2,
            trailing_whitespace: false,
            double_quoted_strings: false,
            arrow_alignment: false,
            spacing: false,
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
        assert_eq!(String::from_utf8_lossy(&lines[6]), r#"  String $var4 = "\"#);
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
    fn test_heredoc_start() {
        let line = r#"aoeu htns => @("MY_HEREDOC"/L)"#.as_bytes();
        let start = heredoc_start(line);
        assert!(start.is_some());
        let here = start.unwrap();
        assert_eq!(here.identifier, "MY_HEREDOC".as_bytes());
        assert_eq!(here.left, "aoeu htns => ".as_bytes());
        assert_eq!(here.right, r#"@("MY_HEREDOC"/L)"#.as_bytes());
    }

    #[test]
    fn test_heredoc_end() {
        let line = r#"  | MY_HEREDOC"#.as_bytes();
        assert!(heredoc_end(&line, &"MY_HEREDOC".as_bytes()));
        assert!(!heredoc_end(&line, &"NOT_MY_HEREDOC".as_bytes()));
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
    content  => @("GITCONFIG"/L)
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
    content2 => @(GITCONFIG/L)
          default = upstream
      | GITCONFIG
    ,
  }
}
"#;
        let lines = format(&mut code.as_bytes().to_vec(), opts).unwrap();
        let mut actual = String::new();
        lines.into_iter().for_each(|l| {
            actual.push_str(&String::from_utf8_lossy(&l));
            actual.push('\n');
        });
        actual
            .split('\n')
            .into_iter()
            .zip(code.split('\n'))
            .for_each(|(actual, expected)| {
                assert_eq!(expected, actual);
            });
        assert_eq!(code, actual);
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
        let code = r#"
class test_class() {
  class {'klass':
    a => {
      b => "c"
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
    fn test_if_else() {
        let mut opts = opts();
        opts.indent = true;
        let code = r#"
class test_class() {
  if $a {
    info("a")
  } else {
    info("b")
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
}
