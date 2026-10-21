"""Check that the definitions and statements of the general modular curves are unchanged since their Stage-0 commit.

* NormalizerDelta/DefsGeneral.lean at FROZEN, without its import line, must occur verbatim in
  NormalizerLean/Defs.lean, which holds the definitions of Parts 1–8.
* NormalizerDelta/StatementsGeneral.lean, with each proof `:= by apply X' <;> assumption` put back to
  `:= by\\n  sorry` and the line `import NormalizerDelta.ProofsGeneral` removed, must equal its version at FROZEN.
(The earlier statements are checked by scripts/check_delta_frozen.py, check_extra_frozen.py,
check_xn_frozen.py and check_cartan_frozen.py.)
Run: python3 scripts/check_general_frozen.py
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

FROZEN = '28308a2'
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
if body(frozen('NormalizerDelta/DefsGeneral.lean')) not in current(DEFS):
    print('DefsGeneral.lean DIFFERS from', FROZEN, '(not verbatim in ' + DEFS + ')')
    ok = False
cur = current('NormalizerDelta/StatementsGeneral.lean')
n_proved = len(re.findall(r":= by apply \w+' <;> assumption", cur))
back = re.sub(r":= by apply \w+' <;> assumption", ':= by\n  sorry', cur)
back = back.replace('import NormalizerDelta.ProofsGeneral\n', '')
if back != frozen('NormalizerDelta/StatementsGeneral.lean'):
    print('StatementsGeneral.lean DIFFERS from', FROZEN)
    import difflib
    sys.stdout.writelines(difflib.unified_diff(frozen('NormalizerDelta/StatementsGeneral.lean').splitlines(True),
                                               back.splitlines(True), 'frozen', 'current'))
    ok = False
print('statements proved: %d, sorry left: %d' % (n_proved, cur.count('sorry')))
print('OK' if ok else 'FAILED')
