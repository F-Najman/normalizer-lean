"""Check that the NormalizerDelta definitions and statements are unchanged since the Stage-0 commit.

* NormalizerDelta/Defs.lean must equal its version at FROZEN verbatim.
* NormalizerDelta/Statements.lean, with each proof `:= by apply X' <;> assumption` put back to
  `:= by\\n  sorry` and the line `import NormalizerDelta.Proofs` removed, must equal its version at FROZEN.
Run: python3 scripts/check_delta_frozen.py
"""
import re
import subprocess
import sys

FROZEN = '021bb2f'


def frozen(path):
    return open(f'frozen/{FROZEN}/{path}').read()


ok = True
if open('NormalizerDelta/Defs.lean').read() != frozen('NormalizerDelta/Defs.lean'):
    print('Defs.lean DIFFERS from', FROZEN)
    ok = False
cur = open('NormalizerDelta/Statements.lean').read()
n_proved = len(re.findall(r":= by apply \w+' <;> assumption", cur))
back = re.sub(r":= by apply \w+' <;> assumption", ':= by\n  sorry', cur)
back = back.replace('import NormalizerDelta.Proofs\n', '')
if back != frozen('NormalizerDelta/Statements.lean'):
    print('Statements.lean DIFFERS from', FROZEN)
    import difflib
    sys.stdout.writelines(difflib.unified_diff(frozen('NormalizerDelta/Statements.lean').splitlines(True),
                                               back.splitlines(True), 'frozen', 'current'))
    ok = False
print('statements proved: %d, sorry left: %d' % (n_proved, cur.count('sorry')))
print('OK' if ok else 'FAILED')
