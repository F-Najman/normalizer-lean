"""Check that the definitions and statements of the general modular curves are unchanged since their Stage-0 commit.

* NormalizerDelta/DefsGeneral.lean must equal its version at FROZEN verbatim.
* NormalizerDelta/StatementsGeneral.lean, with each proof `:= by apply X' <;> assumption` put back to
  `:= by\\n  sorry` and the line `import NormalizerDelta.ProofsGeneral` removed, must equal its version at FROZEN.
(The earlier statements are checked by scripts/check_delta_frozen.py, check_extra_frozen.py,
check_xn_frozen.py and check_cartan_frozen.py.)
Run: python3 scripts/check_general_frozen.py
"""
import re
import subprocess
import sys

FROZEN = '28308a2'


def frozen(path):
    return open(f'frozen/{FROZEN}/{path}').read()


ok = True
if open('NormalizerDelta/DefsGeneral.lean').read() != frozen('NormalizerDelta/DefsGeneral.lean'):
    print('DefsGeneral.lean DIFFERS from', FROZEN)
    ok = False
cur = open('NormalizerDelta/StatementsGeneral.lean').read()
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
