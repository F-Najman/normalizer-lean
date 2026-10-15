"""Check that the NormalizerDelta definitions and statements are unchanged since the Stage-0 commit.

* NormalizerDelta/Defs.lean at FROZEN, without its import line, must occur verbatim in
  NormalizerLean/Defs.lean, which holds the definitions of all six parts.
* NormalizerDelta/Statements.lean, with each proof `:= by apply X' <;> assumption` put back to
  `:= by\\n  sorry` and the line `import NormalizerDelta.Proofs` removed, must equal its version at FROZEN.
Run: python3 scripts/check_delta_frozen.py
"""
import re
import subprocess
import sys

FROZEN = '021bb2f'
DEFS = 'NormalizerLean/Defs.lean'


def frozen(path):
    return open(f'frozen/{FROZEN}/{path}').read()


def body(text):
    """`text` without its import lines."""
    lines = text.split('\n')
    while lines and (lines[0].startswith('import ') or not lines[0].strip()):
        lines.pop(0)
    return '\n'.join(lines)


ok = True
if body(frozen('NormalizerDelta/Defs.lean')) not in open(DEFS).read():
    print('Defs.lean DIFFERS from', FROZEN, '(not verbatim in ' + DEFS + ')')
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
