# newform-dict log

## Findings (base 43513d87)
- VERIFIED (read): kernel `IsNewform` has three textual copies, same body:
  `_root_.PkgI4.IsNewform` (ZInQKernel/HDecomp/Conductor/LadicCond.lean:165),
  `ZInQ.Contrib.G9.PkgI4.IsNewform` (ZInQKernel/Contrib/G9/I4Layer.lean:1273),
  `LeafModCurves.IsNewform` (ZInQKernel/OneProof/H/LPrefix.lean:4480).
  Body: `IsNormalizedEigenform f χ ∧ ⇑f ∉ oldSpace N k`, where IsNormalizedEigenform = slash nebentypus χ,
  a_1 = 1, and a_m a_n = Σ_{d | (m,n)} χ(d) d^{k-1} a_{mn/d²} for all m,n ≥ 1 (eigen for all T_n incl. U_p),
  oldSpace = ℂ-span of τ ↦ g(dτ), g ∈ S_k(Γ₁(M)), M | N, M < N, dM | N.
- VERIFIED (read): Tau Ceti `HeckeRing.GL2.Newform N k` (vendored Newforms/Newform.lean:105) = nonzero
  good-Hecke eigenform with nebentypus, in `cuspFormsNew` = Petersson orthogonal complement of
  `cuspFormsOld` (span of level raises V_d from M | N, M ≠ N), a_1 = 1. This is Diamond–Shurman Def. 5.8.1 /
  Atkin–Lehner / Li's newform (Miyake's primitive form).
- VERIFIED (read): T25/Bridge.lean proves only Tau Ceti newform ⇒ IsNewform (newformOfEigenform's proof).

## Compile log
- scratch/newform-dict/Dict.lean: `NewformDict.exists_newform_of_isNewform` (IsNewform f χ ⇒ ∃ g : Newform N k,
  g.toCuspForm = f ∧ g.χ = toUnitHom χ), [NeZero N]. COMPILED, no errors (2026-11-15 22:58).
  Method: Tau Ceti `mem_span_levelRaise_of_forall_heckeTCuspNat_eq_smul` (DS 5.8.3 spanning, eigen-refined);
  generators of compatible character and level N are = f by `eq_qExpansion_coeff_one_smul...` (DS 5.8.2 whole
  χ-space); others are old or in other χ-spaces; old space is diamond-stable so its χ-part is old;
  independence of χ-spaces kills the rest; Tau Ceti old ⊆ kernel oldSpace.
