# isj1-dict results log

Base 60a3fac7 + merges of origin/wip/r16-used (dcf24ac6, R16Used.lean) and origin/wip/ds965-weak (b893b3da).
Build: .lake/build copied from ~/dzq-wt/ds965-weak; `lake build R16Used JacobianExists DSThm965Weak` OK (10152 jobs).

## Part 1: the IsJ1 dictionary (scratch/isj1-dict/Dict.lean) — VERIFIED compiles, standard axioms

- `AfTateAt N χ f J`: the body of `R16Used.AfTateCharPoly` at one `J`; `afTateCharPoly_iff` (Iff.rfl).
- `AfTateAt.of_iso` (glue): body transported along an abelian-variety isomorphism.
- `isJacobian_picZero` (glue, vendored Jacobian-Challenge): Abel–Jacobi map into a tensor-compatible
  representative of `Pic⁰_{X/K}` is a Jacobian in the kernel's sense (`IsJacobian`), any base point.
- `abVarIso_picZero_of_isJacobian`: every kernel Jacobian ≅ Pic⁰ (objection "Pic⁰ is the Albanese": closed in Lean).
- `abVarIso_of_isJacobian`: base-point independence.
- `IsJacobian.of_iso`: transport along curve isomorphisms.
- New Props: `X1PointsConjugate` (Igusa transitivity on x(P), P exact order N ≥ 1),
  `CurveIsoOfFunctionFieldIso` (smooth proper integral curves over ℚ with isomorphic function fields are isomorphic).
- `abVarIso_of_isJ1`: any two `IsJ1 N` (N ≥ 1) are isomorphic, from the two Props.
- `AfTateCharPolyJ1Exists`, `AfTateCharPolyPicZero` (leaf candidates, one model, Pic⁰);
  `afTateCharPoly_of_exists`, `afTateCharPoly_of_picZero`: AfTateCharPoly from them + the two Props;
  `afTateCharPolyPicZero_of_afTate`: converse given a model with a rational point.
- Finding: `X1PointsConjugate` must assume `0 < N` (for N = 0, `addOrderOf P = 0` means infinite order, and
  x(P) ∈ ℚ(j) vs x(P') ∉ ℚ(j) is possible: false without the hypothesis). IsJ1 0 is a degenerate case; the leaf has 0 < N.

## Part 2: weak reading of DS 9.5.4 (scratch/isj1-dict/Weak.lean) — VERIFIED compiles, standard axioms

- `frobAt_pow_of_rootOfUnity`: at `GlueC10.IsFrobAt σ p`, σζ = ζ^p for ζ^m = 1, p ∤ m (ideal-of-ℤ̄ version of
  hodge-split's valuation argument); `cycQ_frobAt`, `eps0_frobAt` (cyclotomic / nebentypus characters at IsFrobAt).
- `exists_iotaL`: for F ⊆ ℂ, emb : F → ℚ̄_ℓ and ιC : ℚ̄ → ℂ there is ιL : ℚ̄ → ℚ̄_ℓ with ιL = emb ∘ ιC on ιC⁻¹(F).
- `frobMat_mul`, `frobMat_one`, `compMat` (= ι_R applied to frobMat), `trace_det_frobOn`, `aeval_compMat`,
  `continuous_compMat_entry` (from TateModuleFree via RhoCont).
- `component_charpoly`: on each ι-component, weak relation (Frobenius satisfies X²−a_pX+χ(p)p over ℚ_ℓ⊗F) +
  oddness (det of complex conjugation = −1 on the component) ⇒ characteristic polynomial X²−ι(a_p)X+ι(χ(p)p)
  at every Frobenius. Chebotarev on the open non-scalar locus (DS965Weak.eq_on_open_of_eq_on_arithFrob, T18),
  determinant = ε₀χ_ℓ there, translate scalar σ by complex conjugation c (non-scalar since det −1, c² = 1).
- Leaf `AfTateWeakOdd` (weak relation + per-component oddness), `r16_of_weakOdd`, `r16CoreY_of_weakOdd`
  (+ mumfordTorsionAlgClosed). Axioms standard.
- `chi_neg_one_of_newform` (χ(−1)=1 for a weight-2 newform), `complexConj_rootOfUnity`, `cycQ_complexConj` (= −1),
  `eps0_complexConj` (= 1 if χ(−1)=1), `odd_of_charpoly`, `weakOdd_of_afTate`: AfTateCharPoly ⇒ AfTateWeakOdd
  (so the weak-odd leaf is never stronger than r16-used's leaf). Axioms standard.
- Finding (argument, not Lean): the scalar case cannot be excluded from the weak relation alone (a G_ℚ-character
  ψ with ψ(Frob_p) a root of P_p and ψ² = εχ_ℓ is not excluded by elementary means); an input about the same A is
  needed. Oddness of each ι-component is the minimal one used here.
