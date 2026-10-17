"""The module-system header of the Lean sources (Lean's `module` keyword, required by Palomar).

`port(text)` turns a file that starts with plain `import` lines into a module:

    module                          <- added, with a blank line
    public import A                 <- `import` becomes `public import`
    public import B

    @[expose] public section        <- added after the imports, with a blank line, if anything follows

`unport` is its exact inverse; the frozen checks apply it before comparing a file with its frozen version, so they
check that nothing but this header changed.
Run `python3 scripts/module_header.py FILE...` to port files in place (files already ported are left alone).
"""
import re
import sys

MODULE = 'module\n\n'
SECTION = '@[expose] public section\n\n'


def port(text):
    if text.startswith(MODULE):
        return text
    lines = text.split('\n')
    i = 0
    while i < len(lines) and lines[i].startswith('import '):
        i += 1
    imports = ['public ' + line for line in lines[:i]]
    rest = '\n'.join(lines[i:])
    if rest.strip():
        assert rest.startswith('\n'), 'the imports must be followed by a blank line'
        return MODULE + '\n'.join(imports) + '\n\n' + SECTION + rest[1:]
    return MODULE + '\n'.join(imports) + '\n' + rest


def unport(text):
    if not text.startswith(MODULE):
        return text
    text = text[len(MODULE):]
    text = re.sub(r'^public import ', 'import ', text, flags=re.M)
    return text.replace('\n\n' + SECTION, '\n\n', 1)


if __name__ == '__main__':
    for path in sys.argv[1:]:
        old = open(path).read()
        new = port(old)
        assert unport(new) == old, path
        if new != old:
            open(path, 'w').write(new)
            print('ported', path)
