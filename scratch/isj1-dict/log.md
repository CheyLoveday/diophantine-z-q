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

## Contribution and checks (VERIFIED, 11-16)

- `ZInQKernel/Contrib/OneProof/R16IsJ1Dict.lean` = Dict + Weak + Final (`AfTateWeakOddPicZero`, `weakOdd_of_picZero`,
  `r16CoreY_of_dict`, `r16CoreY_of_picZero`, `weakOddPicZero_of_afTate`). Pic⁰ leaves weakened to ∃ representative.
- `lake build +Main +Discharges +R16IsJ1Dict`: success (13670 jobs); rebuild of R16IsJ1Dict after the last edit: success.
- `#discharges`: r16CoreY discharged by r16CoreY_of_picZero / r16CoreY_of_dict / r16CoreY_of_weakOdd; standard axioms;
  "61 open hypotheses, 2400 theorems checked, 11 discharge one".
- autofold dry run (autofold.json): strict 45/10 on 55 -> 47/10 on 57; strictest 43/12 -> 45/12; FoldDryRun.lean
  compiles, sixContactMin_of_open31 standard axioms. Weak spec: 45/10 -> 46/11 (rise; pending-reading flag).

## Part 3: CurveIsoOfFunctionFieldIso PROVED (scratch/isj1-dict/CurveIso.lean) — VERIFIED, standard axioms

- Proof: vendored Scheme.exists_hom_of_valuationRing_stalk (rational maps from integral schemes with valuation stalks
  to proper separated targets extend) + vendored Scheme.valuationRing_stalk (stalks of integral smooth curves are
  valuation rings) give X → X' and X' → X extending the function-field isomorphism; composites are identities by
  Mathlib ext_of_isDominant_of_isSeparated' (Spec K(X) → X dominant, proved). Any two maps Spec K → Spec ℚ agree.
- So the dictionary step 'a curve is determined by its function field' is no longer a leaf.
- Contribution updated: curve leaf proved inside R16IsJ1Dict.lean (`curveIsoOfFunctionFieldIso_proof`); new discharges
  `r16CoreY_of_picZero_igusa` (leaves AfTateCharPolyPicZero, X1PointsConjugate) and `r16CoreY_of_weakPicZero_igusa`.
  lake build +R16IsJ1Dict OK; #discharges: both discharge r16CoreY, standard axioms ("61 open hypotheses, 2410 theorems
  checked, 13 discharge one"). autofold.json (2 leaves) dry run: strict 45/10 on 55 -> 46/10 on 56; strictest 43/12 ->
  44/12; FoldDryRun.lean compiles (sixContactMin_of_open31 standard axioms). Weak spec: 45/10 -> 45/11 (pending reading).
