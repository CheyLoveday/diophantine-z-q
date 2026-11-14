# genus-route results log

## Consumers of t34 (VERIFIED by reading ZInQKernel/OneProof/H/TailD.lean:236, :250, LPrefix.lean:12078)
- TailD:236 `LeafModCurves.dim_J1_le t.t34 N hN0 J hJ1` → uses only `∃ g, J.dim = g ∧ g ≤ N²`.
- TailD:250 `javanpeykarJ1 hR18 hBelyi t.t34 ...`; javanpeykarJ1 (LPrefix:12078) uses hT34 only via
  `LeafModCurves.dim_J1_le hT34 N hN J hJ`. So both need exactly DimJ1Le (curve-split's def), nothing more.

## ConstField.lean — COMPILED (lake env lean), axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
- `GenusRoute.constantFieldIsQ_of_curve (X : Over SpecQ) (hC : IsCurve X) [IsIntegral X.left] (F)
  [Field F] [Algebra Qj F] (e : X.left.functionField ≃+* F) : X1Belyi.ConstantFieldIsQ F`.
- Pieces: `exists_global_section` (sheaf gluing over affine opens, irreducible ⇒ overlaps nonempty),
  `exists_global_of_isIntegral` (normal ⇒ Γ(U) integrally closed, Frac = K(X)), `hom_specQ_ext`,
  `not_subsingleton_of_roots` (two roots ⇒ two primes of ℚ̄ ⊗ ℚ[T]/(q)), `algebraic_mem_range`
  (GeometricallyConnected + surjective base change + Artinian ⇒ discrete ⇒ deg minpoly = 1).
- Copied from scratch/curve-split/CurveBij.lean: closure_mem_irreducibleComponents, isDomain_of_dim_one,
  stalk_closed_normal, topDim_le_one, isNormal_of_integral, isIntegrallyClosed_of_normal.

## GenusRoute.lean — COMPILED (16 s), no errors, all 5 #print axioms standard. VERIFIED.
- `GenusRoute.dimJ1Le_of_rh_curve : DimJacobianEqGenus → RiemannHurwitzQj → DimJ1Le`.
- `GenusRoute.genus_le_of_model : RiemannHurwitzQj → ∀ N > 0, IsX1Model N X → ∃ P, 2 g(K_N) + 1 ≤ N²`.
- X0Transitive and GenusX1Field no longer used. Leaf: RiemannHurwitzQj (Stichtenoth 3.4.13 + 3.5.1,
  numbers UNVERIFIED). DimJacobianEqGenus: proved by dimjac-glue (other branch, not checked here).
