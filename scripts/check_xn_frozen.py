"""Check that the definitions and statements of the X(N) additions are unchanged since their Stage-0 commit.

* NormalizerDelta/DefsXN.lean must equal its version at FROZEN verbatim.
* NormalizerDelta/StatementsXN.lean, with each proof `:= by apply X' <;> assumption` put back to
  `:= by\\n  sorry` and the line `import NormalizerDelta.ProofsXN` removed, must equal its version at FROZEN.
(The 34 statements of Statements.lean and the 14 of StatementsExtra.lean are checked by
scripts/check_delta_frozen.py and scripts/check_extra_frozen.py.)
Run: python3 scripts/check_xn_frozen.py
"""
import re
import subprocess
import sys

FROZEN = '1382369'


def frozen(path):
    return open(f'frozen/{FROZEN}/{path}').read()


ok = True
if open('NormalizerDelta/DefsXN.lean').read() != frozen('NormalizerDelta/DefsXN.lean'):
    print('DefsXN.lean DIFFERS from', FROZEN)
    ok = False
cur = open('NormalizerDelta/StatementsXN.lean').read()
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
