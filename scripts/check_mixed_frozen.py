"""Check that the definitions and statements of Part 8 are unchanged since their Stage-0 commit 54dcc6e.

* The Part 8 section of NormalizerLean/Defs.lean at 54dcc6e (frozen/54dcc6e/NormalizerLean/DefsMixed.lean.txt, from
  the comment "# Part 8" to the end of the file) must occur verbatim in NormalizerLean/Defs.lean.
* NormalizerDelta/StatementsMixed.lean, with each proof `:= by apply X' <;> assumption` put back to `:= by\\n  sorry`
  and the line `import NormalizerDelta.ProofsMixed` removed, must equal its version at 54dcc6e.
Both files are compared without their module-system header (`module_header.unport`).
Run: python3 scripts/check_mixed_frozen.py
"""
import difflib
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from module_header import unport  # noqa: E402

FROZEN = '54dcc6e'


def current(path):
    return unport(open(path).read())


def frozen(path):
    return open(f'frozen/{FROZEN}/{path}.txt').read()


ok = True
if frozen('NormalizerLean/DefsMixed.lean') not in current('NormalizerLean/Defs.lean'):
    print('the Part 8 definitions DIFFER from', FROZEN, '(not verbatim in NormalizerLean/Defs.lean)')
    ok = False
cur = current('NormalizerDelta/StatementsMixed.lean')
n_proved = len(re.findall(r":= by apply \w+' <;> assumption", cur))
back = re.sub(r":= by apply \w+' <;> assumption", ':= by\n  sorry', cur)
back = back.replace('import NormalizerDelta.ProofsMixed\n', '')
if back != frozen('NormalizerDelta/StatementsMixed.lean'):
    print('StatementsMixed.lean DIFFERS from', FROZEN)
    sys.stdout.writelines(difflib.unified_diff(frozen('NormalizerDelta/StatementsMixed.lean').splitlines(True),
                                               back.splitlines(True), 'frozen', 'current'))
    ok = False
print('statements proved: %d, sorry left: %d' % (n_proved, cur.count('sorry')))
print('OK' if ok else 'FAILED')
