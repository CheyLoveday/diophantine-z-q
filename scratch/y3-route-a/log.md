# y3-route-a log

## 2026-11-17

- Merged origin/wip/y3-audit (8dc5f87d6) into wip/y3-route-a: clean, no conflicts.
- `lake build +ZInQKernel.Contrib.OneProof.Y3RepresentableQ`: OK (14373 jobs) (VERIFIED).
- Manuscript read (VERIFIED, diophantine_zq.tex L443-477): Buzzard Thm 2.1 + Cor 2.3 at V_1(5) over Z[1/30] (L443-446); full five-marking (L447-449); Isom_O(O/3O, A[3]) finite etale, nonempty on geometric fibres (L449-462); X_35 smooth projective (L464-465); G_5 = (O/5O)^x acts freely via torsion-freeness of 1+3M_4(Z_3) (L465-472); quotient X_35/G_5 smooth projective, universal abelian scheme with canonical principal polarization, O-action, three-marking descends; represents the full-three problem; generic fibre Y_3 (L472-477).
- New leaf `Y3RouteA.Y3FullThreeRepZ30` (ZInQKernel/Contrib/OneProof/Y3FullThreeZ30.lean): representability over Z[1/30] = Localization.Away (30:ℤ) of the QMAbSchemeP problem on locally noetherian Z[1/30]-schemes by a proper smooth curve with universal QMAbSchemeP.
- Proved (COMPILED, standard axioms only, VERIFIED by #print axioms):
  - `y3RepresentableQ_of_z30 : Y3FullThreeRepZ30 → Y3Audit.Y3RepresentableQ` (generic fibre; abBC base change copied from scratch/y3-audit/GenFib.lean, where it did not compile: three fixes (id_comp, one_eq via ε ≫ map η, object-typed j));
  - `y3FineModuliAbP_of_z30 : Y3FullThreeRepZ30 → Y3Fix.Y3FineModuliAbP`;
  - `shimuraMainThmIDeligneY3AbU_of_z30`.
- ON THE SPOT (flagged, not built on): polarization-free functor ≅ polarized functor via the canonical principal polarization (relative Lemma P). Not in the tree (Lemma P only over fields / lattices).
