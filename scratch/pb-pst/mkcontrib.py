"""Generate ZInQKernel/Contrib/OneProof/PanBergerPst.lean from scratch/pb-pst/BmaxOne.lean and HTFinite.lean."""
import re
a = open('scratch/pb-pst/BmaxOne.lean').read()
b = open('scratch/pb-pst/HTFinite.lean').read()
def body(s):
    lines = s.split('\n')
    return '\n'.join(l for l in lines if not l.startswith('import '))
hdr = '''import ZInQKernel.Contrib.OneProof.PanBergerDict
import ZInQKernel.Contrib.OneProof.AxSenTate

/-!
# pb-pst: Pan's and Berger's leaves of `r11r12`: one `t`, Fontaine's admissibility, Hodge–Tate finiteness

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task pb-pst, 2026-11-17). Report
`docs/research/pb-pst.md`; generated from `scratch/pb-pst/BmaxOne.lean` and `scratch/pb-pst/HTFinite.lean` by
`scratch/pb-pst/mkcontrib.py`.

* **One `t`** (`BmaxOne.bmaxOf_eq`, `BmaxOne.bstOf_eq`): bst-construct's `Bmax`, `Bst` (which invert `log [ε]` for every
  `ε^♯ = 1`, `ε ≠ 1`) are `B_max^+[1/t]` and `B_max^+[1/t][log [p̃]]` for `t = log [ε₀]`, `ε₀` any generator of
  `ℤ_p(1)`: `log [ε] = a t` with `a ∈ ℤ_p` (`logTeich_eq_mul`, from the `p`-adic separatedness of `A_max ⊆ B_dR^+`,
  `amax_sep`).
* **Fontaine's admissibility, basis form** (`BmaxOne.IsAdmissibleT`): `B ⊗_{ℚ_p} V` has a `B`-basis of invariant
  vectors; it implies bst-construct's dimension form (`isAdmissible_of_T`) for every `G_{ℚ_p}`-stable `B ⊆ B_dR`.
* **Restated leaves**: `PanDict.BergerPrintedVT` (Berger 2002 Thm 0.7, one `t`, basis form) with
  `bergerPrintedV_of_T : BergerPrintedVT → BergerPrintedV`; `PanDict.PanPrintedPt` (Pan 2022 Thm 1.0.4 over
  `B_max^+[1/t][log [p̃]]`) with `panPrintedP_of_t : PanPrintedPt → PanPrintedP`.
* **Hodge–Tate finiteness** (`HTFinite.finiteDimensional_htSpaceE`, `HTFinite.htMultE_le`): `(V ⊗_{ℚ_p} ℂ_p(w))^{G_{ℚ_p}}`
  is finite-dimensional over `E`, of dimension `≤ n` (Galois descent with Ax–Sen–Tate, `axSenTate_proof`).
-/
'''
out = hdr + '\n' + body(a).split('-/', 1)[1] + '\n' + body(b).split('-/', 1)[1]
open('ZInQKernel/Contrib/OneProof/PanBergerPst.lean', 'w').write(out)
print(len(out))
