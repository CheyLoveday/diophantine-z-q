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
