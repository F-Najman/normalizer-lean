"""Check that the definitions and statements of Part 7 are unchanged since their Stage-0 commit a3e92bd.

* The Part 7 section of NormalizerLean/Defs.lean at a3e92bd (frozen/a3e92bd/NormalizerLean/DefsStar.lean.txt, from
  the comment "# Part 7" to the end of the file) must occur verbatim in NormalizerLean/Defs.lean.
* NormalizerDelta/StatementsStar.lean, with each proof `:= by apply X' <;> assumption` put back to `:= by\\n  sorry`
  and the line `import NormalizerDelta.ProofsStar` removed, must equal its version at a3e92bd.
Both files are compared without their module-system header (`module_header.unport`).
Run: python3 scripts/check_star_frozen.py
"""
import difflib
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from module_header import unport  # noqa: E402

FROZEN = 'a3e92bd'


def current(path):
    return unport(open(path).read())


def frozen(path):
    return open(f'frozen/{FROZEN}/{path}.txt').read()


ok = True
if frozen('NormalizerLean/DefsStar.lean') not in current('NormalizerLean/Defs.lean'):
    print('the Part 7 definitions DIFFER from', FROZEN, '(not verbatim in NormalizerLean/Defs.lean)')
    ok = False
cur = current('NormalizerDelta/StatementsStar.lean')
n_proved = len(re.findall(r":= by apply \w+' <;> assumption", cur))
back = re.sub(r":= by apply \w+' <;> assumption", ':= by\n  sorry', cur)
back = back.replace('import NormalizerDelta.ProofsStar\n', '')
if back != frozen('NormalizerDelta/StatementsStar.lean'):
    print('StatementsStar.lean DIFFERS from', FROZEN)
    sys.stdout.writelines(difflib.unified_diff(frozen('NormalizerDelta/StatementsStar.lean').splitlines(True),
                                               back.splitlines(True), 'frozen', 'current'))
    ok = False
print('statements proved: %d, sorry left: %d' % (n_proved, cur.count('sorry')))
print('OK' if ok else 'FAILED')
