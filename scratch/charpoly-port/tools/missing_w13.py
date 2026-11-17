# Modules of the target's closure (on origin/cloud-b3/w13-recovery) not yet in CloudB3W16Torsion's vendor
# (by original FLT module name); descent stops at modules W16 already has.
import json, re, sys
sys.path.insert(0,'scratch/charpoly-port/tools')
d = json.load(open('scratch/charpoly-port/tools/closure_w13.json'))['closure']
man = json.load(open('ZInQKernel/Contrib/CloudB3W16Torsion/Vendor/AnthropicFLT/SOURCE_MANIFEST.json'))
have = {x['original'] for x in man['modules']} | set(dict(man['reused_modules']).keys()) | set(man['delegated_giant_modules'])
P = ['ZInQKernel.Contrib.CloudB3W13.Source.','ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.',
     'ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.','ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.',
     'ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.','ZInQKernel.Contrib.CloudB3W12FiniteQuotient.Vendor.AnthropicFLT.',
     'ZInQKernel.Contrib.CloudB3W13Shared.FiniteQuotient.Vendor.AnthropicFLT.']
def orig(m):
    for p in P:
        if m.startswith(p): return m[len(p):]
    return None
root = 'ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isHomogeneous_eval_eq_endDegree_of_abelianSchemePropertyBundle'
seen=set(); need=[]; other=set(); stack=[root]
while stack:
    m=stack.pop()
    if m in seen: continue
    seen.add(m); o=orig(m)
    if o is None: other.add(m); continue
    if o in have: continue
    need.append((o,m))
    for i in d.get(m,[]) or []:
        if i.startswith('ZInQKernel'): stack.append(i)
print(len(need)); 
for o,m in sorted(need): print(o, '<-', m.split('.Contrib.')[1].split('.')[0])
print('other', sorted(other))
json.dump(sorted(need), open('scratch/charpoly-port/tools/need.json','w'), indent=1)
