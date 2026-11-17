# Closure of the target theorem inside origin/cloud-b3/w13-recovery, mapped to original FLT module names,
# compared with the W16Torsion manifest (modules + reused) on the current tree.
import subprocess, re, json, sys
B = 'origin/cloud-b3/w13-recovery'
root = 'ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isHomogeneous_eval_eq_endDegree_of_abelianSchemePropertyBundle'
files = set(l.strip() for l in open('/tmp/cpp_w13files.txt'))
def path(m): return m.replace('.', '/') + '.lean'
def show(m):
    return subprocess.run(['git','show',f'{B}:{path(m)}'],capture_output=True,text=True).stdout
def orig(m):
    for p in ['ZInQKernel.Contrib.CloudB3W13.Source.','ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.',
              'ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.','ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.',
              'ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.']:
        if m.startswith(p): return m[len(p):]
    return None
seen = {}; stack=[root]
while stack:
    m = stack.pop()
    if m in seen: continue
    if path(m) not in files: seen[m]=None; continue
    txt = show(m); imps = re.findall(r'^import\s+(\S+)', txt, re.M)
    seen[m] = imps
    for i in imps:
        if i.startswith('ZInQKernel'): stack.append(i)
man = json.load(open('ZInQKernel/Contrib/CloudB3W16Torsion/Vendor/AnthropicFLT/SOURCE_MANIFEST.json'))
have = {x['original']: x['local'] for x in man['modules']}
have.update(dict(man['reused_modules']) if isinstance(man['reused_modules'],dict) else {})
deleg = set(man['delegated_giant_modules'])
inW13 = [m for m in seen if seen[m] is not None]
print('closure (ZInQKernel modules on w13 branch):', len(inW13))
missing=[]; nonflt=[]
for m in sorted(inW13):
    o = orig(m)
    if o is None: nonflt.append(m); continue
    if o in have or o in deleg: continue
    missing.append((o,m))
print('non-FLT-mapped:', len(nonflt)); [print('  ',x) for x in nonflt[:80]]
print('missing in W16:', len(missing))
json.dump({'missing':missing,'nonflt':nonflt,'closure':{k:v for k,v in seen.items() if v is not None}}, open('scratch/charpoly-port/tools/closure_w13.json','w'), indent=1)
for o,m in missing: print('  ',o)
