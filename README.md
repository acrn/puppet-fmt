# Automatic code formatter for puppet manifests

    Usage: puppet-fmt [<filename>] [-n] [-N <indentation>] [-w] [-t] [-r] [-s] [-i] [-o <output>]

    autoformatting for puppet manifests

    Positional Arguments:
      filename          manifest filename, read manifest from stdin if absent

    Options:
      -n, --no-indent   don't auto-indent lines
      -N, --indentation number of spaces for indentation (default 2)
      -w, --no-trailing-whitespace
                        don't remove trailing whitespace
      -t, --no-double-quoted-strings
                        don't replace double quotes with single quotes for raw
                        strings
      -r, --no-arrow-alignment
                        don't fix arrow alignments
      -s, --no-spacing  don't adjust spacing between tokens (only for resource
                        declarations atm)
      -i, --in-place    overwrite input file
      -o, --output      destination filename
      --help, help      display usage information

## Sample configuration for helix

    [[language]]
    name = "puppet"
    formatter = { command = "puppet-fmt", args = [ "--indentation", "2", ] }

