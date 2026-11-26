#!/usr/bin/env python3
"""For each already vendored module of the closure, compare the vendored file (provenance/
Modified comment lines dropped, ZInQKernel.Contrib.TauCeti[.Backport]. import prefix undone)
with the pin source. usage: vdiff.py TC_ROOT REPO_ROOT ROOT_MOD..."""
import re, sys, os
tc, repo, roots = sys.argv[1], sys.argv[2], sys.argv[3:]
IMP = re.compile(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?(TauCeti\.[\w.]+)')
def imports(m):
    return [mm.group(1) for l in open(os.path.join(tc, *m.split('.')) + '.lean') if (mm := IMP.match(l))]
seen, stack = set(), list(roots)
while stack:
    m = stack.pop()
    if m in seen: continue
    seen.add(m); stack.extend(imports(m))
base = os.path.join(repo, 'ZInQKernel/Contrib/TauCeti')
new = set(l.strip() for l in open(os.path.join(repo, 'scratch/tc-cd-port/modules.txt')))
def norm(text):
    out = []
    for l in text.split('\n'):
        if re.match(r'^-- (Vendored|Modified|Backported|  ?TauCeti\.)', l): continue
        out.append(l.replace('ZInQKernel.Contrib.TauCeti.Backport.', 'TauCeti.').replace('ZInQKernel.Contrib.TauCeti.', 'TauCeti.'))
    return '\n'.join(out).rstrip('\n')
for m in sorted(seen - new):
    rel = m.split('.', 1)[1].replace('.', '/') + '.lean'
    p = os.path.join(base, rel)
    if not os.path.exists(p): p = os.path.join(base, 'Backport', rel)
    a = norm(open(p).read()); b = open(os.path.join(tc, *m.split('.')) + '.lean').read().rstrip('\n')
    if a != b:
        head = [l for l in open(p).read().split('\n')[:12] if l.startswith('--')]
        print('DIFF', os.path.relpath(p, base), '|', ' / '.join(head)[:300])
