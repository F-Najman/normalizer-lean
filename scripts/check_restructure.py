"""Check that the restructure changed no definition and no statement.

Compares the frozen Statements.lean (commit 11358c3) with Defs.lean + Statements.lean:
* the definitions region (`open Matrix MatrixGroups` up to `/-! ## T1`) occurs verbatim in Defs.lean;
* the theorems region (`/-! ## T1` up to the final `end`) equals the new one after replacing each
  `:= by apply X' <;> assumption` by `:= sorry`, where X is the theorem being proved.
Run from the repository root: python3 scripts/check_restructure.py
"""
import os, re, subprocess, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from module_header import unport  # the module-system header is added and removed exactly

old = open('frozen/11358c3/NormalizerLean/Statements.lean.txt').read()
defs = unport(open('NormalizerLean/Defs.lean').read())
new = unport(open('NormalizerLean/Statements.lean').read())

def regions(txt):
    L = txt.split('\n')
    i_t1 = next(i for i, l in enumerate(L) if l.startswith('/-! ## T1'))
    i_end = max(i for i, l in enumerate(L) if l.strip() == 'end')
    return L, i_t1, i_end

L, i_t1, i_end = regions(old)
i_open = L.index('open Matrix MatrixGroups')
old_defs = '\n'.join(L[i_open:i_t1])
old_thms = L[i_t1:i_end]

ok = True
if old_defs not in defs:
    print('FAIL: definitions not verbatim in Defs.lean'); ok = False

N, j_t1, j_end = regions(new)
new_thms, cur, n = [], None, 0
for l in N[j_t1:j_end]:
    m = re.match(r'theorem (\w+)', l)
    if m:
        cur = m.group(1)
    suffix = f":= by apply {cur}' <;> assumption"
    if l.endswith(suffix):
        l = l[:-len(suffix)] + ':= sorry'
        n += 1
    new_thms.append(l)
if new_thms != old_thms:
    ok = False
    for a, b in zip(old_thms, new_thms):
        if a != b:
            print('FAIL:\n  old:', a, '\n  new:', b)
            break
if 'sorry' in new:
    print('FAIL: sorry in Statements.lean'); ok = False
print('statements proved by their own X\':', n)
print('OK' if ok and n == 36 else 'FAIL')
sys.exit(0 if ok and n == 36 else 1)
