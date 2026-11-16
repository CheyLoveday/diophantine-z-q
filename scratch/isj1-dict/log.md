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
