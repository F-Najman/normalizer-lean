"""Coset-enumeration certificates for |PresentedGroup| = n (T8(c,d); later T5).

Input: the regular permutation representation (right action, coset 0 = identity) from Magma.
Output: rep words (BFS tree from 0) and a list of deductions (v, k, p): reading relator k from
vertex v, every edge except the one at position p is already known, so that edge becomes known.
The Lean checker `CosetCert.check` re-verifies everything; this script only searches.
Run: python3 coset_cert.py  (reads regular_data_output.txt, writes coset_certs.json).
"""
import re, json

def parse(fname):
    txt = open(fname).read()
    out = {}
    for b in re.finditer(r'DATA (\w+) order=(\d+)\nPERM_W \[(.*?)\]\nPERM_S \[(.*?)\]', txt, re.S):
        out[b.group(1)] = (int(b.group(2)), [int(x)-1 for x in b.group(3).split(',')],
                           [int(x)-1 for x in b.group(4).split(',')])
    return out

def W(*letters):  # letters like 'w', 's', 'S' (= s^-1), 'W'
    return [(c.lower(), c.islower()) for c in letters]

RELS = {
    'c5': [W(*'ww'), W(*'ssss'), W(*'wswswsws'), W(*'wSwswSws')],
    'c6': [W(*'ww'), W(*'ssssssss'), W(*'wswsws'), W(*'wSwswSwswSws')],
    'd8': [W(*'ww'), W(*'ssssssss'), W(*'wswswssswsss')],
}

def build(n, pw, ps, rels):
    act = {'w': pw, 's': ps}
    inv = {x: [act[x].index(i) for i in range(n)] for x in act}
    edge = lambda i, x: 2*i + (0 if x == 'w' else 1)
    reps = {0: []}; order = [0]
    for i in order:
        for x in ('w', 's'):
            for (j, letter) in ((act[x][i], (x, True)), (inv[x][i], (x, False))):
                if j not in reps:
                    reps[j] = reps[i] + [letter]; order.append(j)
    assert len(reps) == n
    known = set()
    for i in range(n):
        for x in ('w', 's'):
            j = act[x][i]
            if reps[j] == reps[i] + [(x, True)] or reps[i] == reps[j] + [(x, False)]:
                known.add(edge(i, x))
    def letter_edge(c, a):
        x, b = a
        return edge(c, x) if b else edge(inv[x][c], x)
    def step(c, a):
        x, b = a
        return act[x][c] if b else inv[x][c]
    deds = []
    progress = True
    while progress and len(known) < 2*n:
        progress = False
        for v in range(n):
            for k, r in enumerate(rels):
                c, path = v, []
                for a in r:
                    path.append(letter_edge(c, a)); c = step(c, a)
                assert c == v
                unknown = [p for p, e in enumerate(path) if e not in known]
                if len(unknown) == 1:
                    p = unknown[0]
                    known.add(path[p]); deds.append((v, k, p)); progress = True
    assert len(known) == 2*n, f'stuck: {len(known)} of {2*n}'
    return {'n': n, 'act_w': pw, 'act_s': ps, 'inv_w': inv['w'], 'inv_s': inv['s'],
            'reps': [[[x, b] for (x, b) in reps[i]] for i in range(n)], 'deds': deds}

if __name__ == '__main__':
    data = parse('regular_data_output.txt')
    certs = {}
    for name, (n, pw, ps) in data.items():
        certs[name] = build(n, pw, ps, RELS[name])
        print(name, 'n =', n, 'deductions =', len(certs[name]['deds']),
              'max rep length =', max(len(r) for r in certs[name]['reps']))
    json.dump(certs, open('coset_certs.json', 'w'))
