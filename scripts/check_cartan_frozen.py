"""Check that the definitions and statements of the Cartan curves are unchanged since their Stage-0 commit.

* NormalizerDelta/DefsCartan.lean must equal its version at FROZEN verbatim.
* NormalizerDelta/StatementsCartan.lean, with each proof `:= by apply X' <;> assumption` put back to
  `:= by\\n  sorry` and the line `import NormalizerDelta.ProofsCartan` removed, must equal its version at FROZEN.
(The earlier statements are checked by scripts/check_delta_frozen.py, check_extra_frozen.py and
check_xn_frozen.py.)
Run: python3 scripts/check_cartan_frozen.py
"""
import re
import subprocess
import sys

FROZEN = '7c6c7de'


def frozen(path):
    return open(f'frozen/{FROZEN}/{path}').read()


ok = True
if open('NormalizerDelta/DefsCartan.lean').read() != frozen('NormalizerDelta/DefsCartan.lean'):
    print('DefsCartan.lean DIFFERS from', FROZEN)
    ok = False
cur = open('NormalizerDelta/StatementsCartan.lean').read()
n_proved = len(re.findall(r":= by apply \w+' <;> assumption", cur))
back = re.sub(r":= by apply \w+' <;> assumption", ':= by\n  sorry', cur)
back = back.replace('import NormalizerDelta.ProofsCartan\n', '')
if back != frozen('NormalizerDelta/StatementsCartan.lean'):
    print('StatementsCartan.lean DIFFERS from', FROZEN)
    import difflib
    sys.stdout.writelines(difflib.unified_diff(frozen('NormalizerDelta/StatementsCartan.lean').splitlines(True),
                                               back.splitlines(True), 'frozen', 'current'))
    ok = False
print('statements proved: %d, sorry left: %d' % (n_proved, cur.count('sorry')))
print('OK' if ok else 'FAILED')
