# Convert the 63 needed W13 (wrapped) modules into W16-style unwrapped modules under
# ZInQKernel/Contrib/OneProof/CharPolyPort/Vendor/AnthropicFLT/.
import json, subprocess, re, os
B='origin/cloud-b3/w13-recovery'
NEWP='ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.'
need=json.load(open('scratch/charpoly-port/tools/need.json'))
needo={o for o,m in need}
man=json.load(open('ZInQKernel/Contrib/CloudB3W16Torsion/Vendor/AnthropicFLT/SOURCE_MANIFEST.json'))
have={x['original']:x['local'] for x in man['modules']}; have.update(dict(man['reused_modules']))
P=['ZInQKernel.Contrib.CloudB3W13.Source.','ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.',
   'ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.','ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.',
   'ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.']
def orig(m):
    for p in P:
        if m.startswith(p): return m[len(p):]
SKIP={'Compat.MvPolynomialCoeff','Compat.PresheafOfModulesMonoidal','Compat.TensorProductInduction','PortUtilExt'}
REN={'tensorPow','tensorPow_zero','tensorPow_succ','tensorPowOneIso','tensorPowSection','tensorPowSection_zero',
 'tensorPowSection_succ','pullbackSection','pullbackSection_def','pullback_hom_ext','pullbackTensorObjIso',
 'preservesBinaryProducts_opensMap','preservesTerminal_opensMap','pushforwardRestrictIso',
 'pushforwardRestrictIso_hom_app_app','restrictPushforwardOpensIso','isInvertible_top','isInvertible_unit',
 'isRegularLocalRing_stalk'}
REN2={'monoidalCategory':'fltMonoidalCategory','symmetricCategory':'fltSymmetricCategory'}
def ren_ident(tok):
    parts=tok.split('.')
    out=[]
    for i,p in enumerate(parts):
        if p in REN: p=p+'FLT'
        elif p in REN2 and i>0: p=REN2[p]
        elif p=='geometricallyConnected' and i>0 and parts[i-1]=='GeometricallyIrreducible': p='geometricallyConnectedFLT'
        elif p=='depth' and i>0 and parts[i-1]=='Module': p='depthFLT'
        elif p=='dual' and i>0 and parts[i-1]=='Modules': p='fltDual'
        elif p=='comap_mul' and i>0 and parts[i-1]=='IdealSheafData': p='comap_mulFLT'
        elif p=='IsInvertible' and i>0 and parts[i-1]=='IdealSheafData': p='IsCartierFLT'
        out.append(p)
    return '.'.join(out)
IDENT=re.compile(r"[A-Za-z_][A-Za-z0-9_'!?₀-₉]*(?:\.[A-Za-z_][A-Za-z0-9_'!?₀-₉]*)*")
def convert(o,m):
    t=subprocess.run(['git','show',B+':'+m.replace('.','/')+'.lean'],capture_output=True,text=True).stdout
    lines=t.split('\n')
    first=next(i for i,l in enumerate(lines) if l.startswith('import '))
    body=lines[first:]
    imps=[]; rest=[]; inhdr=True
    for l in body:
        if inhdr and (l.startswith('import ') or not l.strip()):
            if l.startswith('import '):
                i=l.split()[1]
                if i=='Mathlib' or i.startswith('Mathlib.'): imps.append(i); continue
                if i=='ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil': imps.append('ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util'); continue
                oo=orig(i)
                if oo in SKIP: continue
                if oo in have: imps.append(have[oo]); continue
                if oo in needo: imps.append(NEWP+oo); continue
                raise Exception(f'{o}: unmapped import {i}')
            continue
        inhdr=False; rest.append(l)
    out=[]
    for l in rest:
        s=l.strip()
        if s in ('namespace ZInQ.Contrib.CloudW03NeronSurj.FLT','end ZInQ.Contrib.CloudW03NeronSurj.FLT','open ZInQ.Contrib.CloudW03NeronSurj.FLT'): continue
        if s.startswith('r2nos_'): continue
        if s.startswith('set_option backward.isDefEq.respectTransparency.types') : out.append('set_option backward.isDefEq.respectTransparency false'); continue
        if s.startswith('set_option backward.isDefEq.respectTransparency.instanceSearchTypes'): continue
        l=l.replace('_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.','_root_.').replace('ZInQ.Contrib.CloudW03NeronSurj.FLT.','')
        l=re.sub(r'\bw03_(open|exact_reverting|export|reactivate|alias|ns|open_scoped|export_all)\b', r'p2m_\1', l)
        # identifier renames outside string literals / comments is approximated: apply to whole line
        l=IDENT.sub(lambda mm: ren_ident(mm.group(0)), l)
        out.append(l)
    seen=set(); imps=[x for x in imps if not (x in seen or seen.add(x))]
    hdr=f"""/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: {o}. Apache-2.0.
Modification notice (CloudB3 Worker13, 2026-11-15/16): ported to Lean 4.35.0 / Mathlib v4.35.0
(namespace-wrapped port on origin/cloud-b3/w13-recovery).
Modified for the Z-in-Q kernel (charpoly-port, 2026-11-17): the Worker13 port unwrapped into the
CloudB3W16Torsion conventions (original declaration namespaces; imports relocated to the
CloudB3W16Torsion vendor; the FLT-suffixed renames of CloudB3W16Torsion/NOTICE.md applied; port
shim commands removed). Mathematical statements and proofs retained, subject to Lean 4.35 adaptations
listed in scratch/charpoly-port/log.md.
Full original notices/credits: LICENSE, NOTICE.upstream, ATTRIBUTION.upstream.md in this vendor root.
-/"""
    txt=hdr+'\n'+'\n'.join('import '+x for x in imps)+'\n'+'\n'.join(out)
    txt=re.sub(r'\n{3,}', '\n\n', txt)
    p='ZInQKernel/Contrib/OneProof/CharPolyPort/Vendor/AnthropicFLT/'+o.replace('.','/')+'.lean'
    os.makedirs(os.path.dirname(p),exist_ok=True); open(p,'w').write(txt)
for o,m in need:
    if o in SKIP: continue
    convert(o,m)
print('done')
