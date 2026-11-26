#!/usr/bin/env python3
"""Union of TauCeti import closures; subtract already vendored modules.
usage: closure.py TC_ROOT REPO_ROOT MOD1 [MOD2 ...]"""
import re, sys, os
tc, repo, roots = sys.argv[1], sys.argv[2], sys.argv[3:]
IMP = re.compile(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?(TauCeti\.[\w.]+)')
def path(root, m): return os.path.join(root, *m.split('.')) + '.lean'
def imports(m):
    out = []
    with open(path(tc, m)) as f:
        for line in f:
            mm = IMP.match(line)
            if mm: out.append(mm.group(1))
    return out
seen, stack = set(), list(roots)
while stack:
    m = stack.pop()
    if m in seen: continue
    seen.add(m); stack.extend(imports(m))
base = os.path.join(repo, 'ZInQKernel/Contrib/TauCeti')
def vendored(m):
    rel = m.split('.', 1)[1].replace('.', '/') + '.lean'
    return os.path.exists(os.path.join(base, rel)) or os.path.exists(os.path.join(base, 'Backport', rel))
new = sorted(m for m in seen if not vendored(m))
print(f"closure {len(seen)} vendored {len(seen)-len(new)} new {len(new)}", file=sys.stderr)
for m in new: print(m)
