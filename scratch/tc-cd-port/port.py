#!/usr/bin/env python3
"""Copy Tau Ceti modules into ZInQKernel/Contrib/TauCeti/, add the provenance line after the
copyright header, rewrite TauCeti.X imports (to the Backport/ copy where only that exists).
Never overwrites an existing file.  usage: port.py TC_ROOT REPO_ROOT MODLIST"""
import re, sys, os
tc, repo, modlist = sys.argv[1:4]
base = os.path.join(repo, 'ZInQKernel/Contrib/TauCeti')
mods = [l.strip() for l in open(modlist) if l.strip()]
newset = set(mods)
IMP = re.compile(r'^(\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?)TauCeti\.([\w.]+)(.*)$')
def target(rest):
    m = 'TauCeti.' + rest
    rel = rest.replace('.', '/') + '.lean'
    if m in newset or os.path.exists(os.path.join(base, rel)):
        return 'ZInQKernel.Contrib.TauCeti.' + rest
    if os.path.exists(os.path.join(base, 'Backport', rel)):
        return 'ZInQKernel.Contrib.TauCeti.Backport.' + rest
    raise SystemExit(f'unresolved import {m}')
for m in mods:
    rest = m.split('.', 1)[1]
    src = os.path.join(tc, *m.split('.')) + '.lean'
    dst = os.path.join(base, rest.replace('.', '/') + '.lean')
    if os.path.exists(dst): raise SystemExit(f'exists: {dst}')
    lines = open(src).read().split('\n')
    assert lines[0] == '/-', m
    end = lines.index('-/')
    prov = f'-- Vendored from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 5a01f5fe3621, module {m}), Apache-2.0.'
    out = lines[:end+1] + [prov]
    for l in lines[end+1:]:
        mm = IMP.match(l)
        out.append(mm.group(1) + target(mm.group(2)) + mm.group(3) if mm else l)
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    open(dst, 'w').write('\n'.join(out))
print(len(mods), 'copied')
