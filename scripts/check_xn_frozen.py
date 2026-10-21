"""Check that the definitions and statements of the X(N) additions are unchanged since their Stage-0 commit.

* NormalizerDelta/DefsXN.lean at FROZEN, without its import line, must occur verbatim in
  NormalizerLean/Defs.lean, which holds the definitions of Parts 1–8.
* NormalizerDelta/StatementsXN.lean, with each proof `:= by apply X' <;> assumption` put back to
  `:= by\\n  sorry` and the line `import NormalizerDelta.ProofsXN` removed, must equal its version at FROZEN.
(The 34 statements of Statements.lean and the 14 of StatementsExtra.lean are checked by
scripts/check_delta_frozen.py and scripts/check_extra_frozen.py.)
Run: python3 scripts/check_xn_frozen.py
"""
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from module_header import unport  # noqa: E402


def current(path):
    """The file without its module-system header, which `module_header.py` adds and removes exactly."""
    return unport(open(path).read())

FROZEN = '1382369'
DEFS = 'NormalizerLean/Defs.lean'


def frozen(path):
    return open(f'frozen/{FROZEN}/{path}.txt').read()


def body(text):
    """`text` without its import lines."""
    lines = text.split('\n')
    while lines and (lines[0].startswith('import ') or not lines[0].strip()):
        lines.pop(0)
    return '\n'.join(lines)


ok = True
if body(frozen('NormalizerDelta/DefsXN.lean')) not in current(DEFS):
    print('DefsXN.lean DIFFERS from', FROZEN, '(not verbatim in ' + DEFS + ')')
    ok = False
cur = current('NormalizerDelta/StatementsXN.lean')
n_proved = len(re.findall(r":= by apply \w+' <;> assumption", cur))
back = re.sub(r":= by apply \w+' <;> assumption", ':= by\n  sorry', cur)
back = back.replace('import NormalizerDelta.ProofsXN\n', '')
if back != frozen('NormalizerDelta/StatementsXN.lean'):
    print('StatementsXN.lean DIFFERS from', FROZEN)
    import difflib
    sys.stdout.writelines(difflib.unified_diff(frozen('NormalizerDelta/StatementsXN.lean').splitlines(True),
                                               back.splitlines(True), 'frozen', 'current'))
    ok = False
print('statements proved: %d, sorry left: %d' % (n_proved, cur.count('sorry')))
print('OK' if ok else 'FAILED')
