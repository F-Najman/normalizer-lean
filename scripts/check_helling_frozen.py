"""Check that the definitions and statements of Part 9 are unchanged since their Stage-0 commit 7fc9442.

* Part 9 has no new definitions.  NormalizerDelta/DefsHelling.lean, which only imports NormalizerLean/Defs.lean, must
  equal its version at 7fc9442 (frozen/7fc9442/NormalizerDelta/DefsHelling.lean.txt).  The definitions it uses
  (Gamma0Plus, IsAtkinLehner, SL2ZR, toR, NormG, BG, projSL) belong to Parts 1–3 and are checked by their scripts.
* NormalizerDelta/StatementsHelling.lean, with each proof `:= by apply X' <;> assumption` put back to `:= by\\n  sorry`
  and the line `import NormalizerDelta.ProofsHelling` removed, must equal its version at 7fc9442.
Both files are compared without their module-system header (`module_header.unport`).
Run: python3 scripts/check_helling_frozen.py
"""
import difflib
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from module_header import unport  # noqa: E402

FROZEN = '7fc9442'


def current(path):
    return unport(open(path).read())


def frozen(path):
    return open(f'frozen/{FROZEN}/{path}.txt').read()


ok = True
if current('NormalizerDelta/DefsHelling.lean') != frozen('NormalizerDelta/DefsHelling.lean'):
    print('DefsHelling.lean DIFFERS from', FROZEN)
    ok = False
cur = current('NormalizerDelta/StatementsHelling.lean')
n_proved = len(re.findall(r":= by apply \w+' <;> assumption", cur))
back = re.sub(r":= by apply \w+' <;> assumption", ':= by\n  sorry', cur)
back = back.replace('import NormalizerDelta.ProofsHelling\n', '')
if back != frozen('NormalizerDelta/StatementsHelling.lean'):
    print('StatementsHelling.lean DIFFERS from', FROZEN)
    sys.stdout.writelines(difflib.unified_diff(frozen('NormalizerDelta/StatementsHelling.lean').splitlines(True),
                                               back.splitlines(True), 'frozen', 'current'))
    ok = False
print('statements proved: %d, sorry left: %d' % (n_proved, cur.count('sorry')))
print('OK' if ok else 'FAILED')
