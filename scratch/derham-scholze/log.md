# derham-scholze log

Base: wip/derham-scholze at d67ea55f6 (origin/main is an ancestor, VERIFIED `git merge-base --is-ancestor`).

## Findings (reading)

- VERIFIED (read): manuscript lem:de-rham-descent, diophantine_zq.tex L10939-11004; bibitems L11010-11026
  (scholze2013: Cor. 1.8, Thms 9.1, 9.3; scholze-erratum; brinon-conrad 5.2.1, 6.3.3, 6.3.8; milne-av v2.00 Part I Thm 12.1(a)).
- VERIFIED (read): Mathlib v4.35 has `Scheme.EllAdicCohomology X ℓ n` (pro-étale, BMS Def. 6.8.1),
  Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean.
- VERIFIED (read): ZInQKernel/HDecomp/Textbook/T10Etale.lean (t10-etale) gives the ℤ_ℓ-module structure, transport along
  scheme isos (bijective, degree-0 check), `galH` on H¹(A_K̄, ℤ_ℓ), and the leaf `T10_TateDuality`
  (Galois-equivariant H¹ ≅ Hom(T_ℓ A, ℤ_ℓ); cites Milne 1986 Thm 15.1(a)). Functoriality of transport (group law) not proved there.
- VERIFIED (grep OPEN.md): `t10` is not an open field at the base (32 open); it was a textbook leaf in older generations (av-b2 §2.6).
- No network: Scholze arXiv 1205.3463, corrigendum and Milne's notes not re-read here; wording of Cor. 1.8 as quoted by
  h-leaves §3.1 / locators.md (VERIFIED there by other tasks).

## Lean (scratch/derham-scholze/DeRhamScholze.lean; contrib copy ZInQKernel/Contrib/OneProof/DeRhamScholze.lean)

- Statements: `ScholzeDeRhamAlg` (leaf, consequence of Scholze Cor. 1.8 + Thms 9.1/9.3 over Mathlib's EllAdicCohomology),
  reuse `T10Etale.T10_TateDuality` (Milne), glue `DeRhamHodgeTate01` (Hom form).
- VERIFIED (compiled, `lake env lean`, 11-17 ~06:55): whole scratch file, no errors; milneE_comm needs maxHeartbeats 4000000
  (transport between pkg-I4's and the kernel's copies of the abelian variety); ~4 min per compile.
- Pitfalls: `attribute [local instance] algPlus` makes `Module ℚ_[p] (BdR p)` resolve through OreLocalization
  (instance mismatch with `drAct`): do not activate it; `ext` on `Dual (A.V p)` times out (use `LinearMap.ext fun v => _`);
  `rfl` comparing pkg-I4 `galRep` with the kernel's `galT.baseChange` as linear maps times out, the applied form via
  `AbVarBC.vToI4_galRep` is instant; `TensorProduct.inductionOn` has no zero case.
