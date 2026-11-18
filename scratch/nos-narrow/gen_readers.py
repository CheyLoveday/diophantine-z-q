"""Replay the NOS reader copies. Run from the repository root; stdout is NOSNarrow.lean."""
from pathlib import Path
import re

from copylib import context, emit, find_decl, rename

H = 'ZInQKernel/OneProof/H/'
C = 'ZInQKernel/Contrib/OneProof/'
ITEMS = [
    (H + 'TailC.lean', 'point_fixed', 'Transport prime-to-residue-characteristic torsion triviality along the embedding.'),
    (C + 'HomFreeFiniteAlgClosedReroute/Consumers.lean', 'inertiaFixesHomsMon_hf', 'Inertia fixes the conjugacy Hom lattice, by agreement on torsion.'),
    (C + 'HomFreeFiniteAlgClosedReroute/Consumers.lean', 'inertiaFixesHomsMon_of_leaves_hf', 'Hom lattice inertia for the DVR obtained by restriction.'),
    (C + 'HomFreeFiniteAlgClosedReroute/Consumers.lean', 'kernelField_of_model_hf', 'Construct the Hom kernel field and prove unramifiedness outside the given set.'),
    (C + 'D2A6Wrap.lean', 'good_of_QML3U', 'Good reduction from the proper model over ℤ[1/30].'),
    (H + 'D2A6Chain.lean', 'kernelFieldExists_of_pieces_hf_u', 'Construct the kernel field for the chosen fibre.'),
    (H + 'D2A6Chain.lean', 'kernelFieldExists_of_leaves_hf_u', 'Supply the torsion count for the kernel field.'),
    (H + 'D2A6Chain.lean', 'kernelFieldExists_of_leaves_FS5_hf_u', 'Use fibre simplicity to supply the conjugacy maps.'),
    (H + 'D2A6Chain.lean', 'kernelFieldExists_of_split_hf_u', 'Assemble the kernel field from the split conjugacy inputs.'),
    (H + 'D2A6Chain.lean', "kernelFieldExists_of_split_hf_u'", 'Assemble the endomorphism-ring input by transport.'),
    (H + 'D2A6Chain.lean', "kernelFieldExists_of_split_hf_u''", 'Kernel-field reader (L557–560) with only the forward implication.'),
    (C + 'A6IntModel.lean', 'GoodRedTorsionT', 'Good reduction outside the given set gives inertia triviality on prime-power torsion.'),
    (C + 'A6IntModel.lean', 'goodRedTorsionT', 'Transport inertia triviality to torsion on the base-changed variety.'),
    (C + 'A6Z30.lean', 'qmModelG3U_of_z30', 'Good reduction outside the primes ≤ 324 gives unramified Tate modules.'),
    (C + 'A6Z30.lean', 'modelG3G6_of_leavesU_z30', 'G3 and G5–G6 from the proper model and the forward implication.'),
    (C + 'D2A6Wrap.lean', 'modelG3G6_of_leaves3U', 'A6 reader for G11 (L752–753) with only the forward implication.'),
]
BINDER = '(hNOS : PkgI2.NeronOggShafarevich.{0})'
FORWARD = '_root_.NOSNarrow.NOSForward'

def new_name(n):
    return n + ('F' if n == 'GoodRedTorsionT' else '_nos')

def package(f, n):
    hits = find_decl(f, n)
    assert len(hits) == 1, (f, n, hits)
    return '.'.join(op.removeprefix('namespace ') for op, _, _ in context(f, hits[0])
                    if op.startswith('namespace '))

def main():
    header = Path(__file__).with_name('reader-header.txt').read_text()
    print(header)
    axioms = ['NOSNarrow.perfect_of_sep', 'NOSNarrow.nosForward_proof', 'NOSNarrow.nosForward_of_r7a']
    seen_top = {
        'set_option linter.style.longLine false',
        'set_option linter.style.haveILetI false',
    }
    ren = {n: new_name(n) for _, n, _ in ITEMS}
    ren['hNOS'] = 'hF'
    for f, n, desc in ITEMS:
        txt = emit(f, n, ren, seen_top=seen_top)
        start = txt.index('\n' + ('def ' if n == 'GoodRedTorsionT' else 'theorem ') + new_name(n))
        prior = txt[:start]
        prior = re.sub(r'/--[\s\S]*?-/(?=\s*$)', '', prior).rstrip()
        txt = prior + '\n/-- ' + desc + ' -/' + txt[start:]
        orig_signature = re.split(r' :=', txt[txt.index('\ntheorem ') + len('\ntheorem ' + new_name(n)):], maxsplit=1)[0] if n in {
            "kernelFieldExists_of_split_hf_u''", 'modelG3G6_of_leaves3U'} else None
        if n == 'good_of_QML3U':
            txt = txt.replace(rename(BINDER, ren) + ' ', '')
        elif n == 'GoodRedTorsionT':
            txt = txt.replace('PkgI2.NeronOggShafarevich.{0} →', FORWARD + ' →')
        else:
            if n != 'goodRedTorsionT':
                assert rename(BINDER, ren) in txt, n
                txt = txt.replace(rename(BINDER, ren), '(hF : ' + FORWARD + ')')
            swaps = {
                'point_fixed': ("((hF K (w.comap (e : K →+* Qbar)) w' hw' (ObjBridge.toGrp A)).1.mp hgood)",
                                "(hF K (w.comap (e : K →+* Qbar)) w' hw' (ObjBridge.toGrp A) hgood)"),
                'goodRedTorsionT': ('((hF K O w rfl (ObjBridge.toGrp A)).1.mp (hA O p hp hp3 hpO))',
                                    '(hF K O w rfl (ObjBridge.toGrp A) (hA O p hp hp3 hpO))'),
                'kernelFieldExists_of_pieces_hf_u': ('good_of_QML3U_nos hF hRay', 'good_of_QML3U_nos hRay'),
            }
            if n in swaps:
                a, b = swaps[n]
                assert a in txt, n
                txt = txt.replace(a, b)
        assert 'NeronOggShafarevich' not in txt, n
        if orig_signature:
            orig_signature = orig_signature.replace('(hF :', '(hNOS :')
            args = {
                "kernelFieldExists_of_split_hf_u''": 'hHFF {F} hRay hTors hYu h5 hmax hb hG',
                'modelG3G6_of_leaves3U': 'hFS {F} hRay hTors',
            }[n]
            formula = args.format(F='(_root_.NOSNarrow.nosForward_of_r7a hNOS)')
            # Use the original opens and namespace in this signature.
            after = txt.index('\nend', txt.index('\ntheorem '))
            txt = (txt[:after] + '\n\nexample' + orig_signature.rstrip() + ' :=\n  '
                   + new_name(n) + ' ' + formula + '\n' + txt[after:])
        print(txt)
        if n != 'GoodRedTorsionT':
            axioms.append(package(f, n) + '.' + new_name(n))
    for n in axioms:
        print('#print axioms ' + n)

if __name__ == '__main__':
    main()
