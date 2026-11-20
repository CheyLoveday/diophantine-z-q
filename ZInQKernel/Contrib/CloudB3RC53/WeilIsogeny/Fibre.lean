import ZInQKernel.Contrib.CloudB3RC53.WeilIsogeny.Intertwine
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.DivisorPullback

/-!
# The pullback of a point along a separable isogeny is its fibre

For a separable isogeny `φ : W₁ → W₂` over a separably closed field, every place of `F(W₁)` is
unramified over `F(W₂)` and every place of `F(W₂)` splits completely (Tau Ceti's
`ramificationIdx_eq_one`, `isSplitCompletely`). So a place of `F(W₁)` over the place of a point
`Q` is the place of a point `R` with `φ R = Q` (`restrict_eq_pointEquivDegreeOnePlace_iff`), and

    φ^* (Q) = ∑_{φ R = Q} (R)        (`divisorPullback_ofPoint`).

This generalizes Tau Ceti's `divisorPullback_mulByIntIsogeny_ofPoint` from `[n]` to every separable
isogeny; it is the divisor computation in the compatibility of the Weil pairing with isogenies.

Classification: PROVED.
-/

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine TauCeti AlgebraicGeometry

namespace ZInQ.Contrib.CloudB3RC53.WeilIsogeny

variable {F : Type*} [Field F] [DecidableEq F] [IsSepClosed F] {W₁ W₂ : WeierstrassCurve.Affine F}
  [W₁.IsElliptic] [W₂.IsElliptic] (φ : Isogeny W₁ W₂)
  [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField]

/-- **A place over the place of `Q` is the place of a point of the fibre of `φ` over `Q`.**
PROVED. -/
theorem restrict_eq_pointEquivDegreeOnePlace_iff (Q : W₂.Point) (P : Place F W₁.FunctionField) :
    letI := φ.fieldPullback.toRingHom.toAlgebra
    haveI := Isogeny.isScalarTower_of_algebraMap_eq_fieldPullback φ (fun _ ↦ rfl)
    haveI := φ.finiteDimensional_functionField (fun _ ↦ rfl)
    P.restrict F W₂.FunctionField = (W₂.pointEquivDegreeOnePlace Q).1 ↔
      ∃ R, (Isogeny.Hom.ofIsogeny φ).pointMap R = Q ∧ (W₁.pointEquivDegreeOnePlace R).1 = P := by
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  have := Isogeny.isScalarTower_of_algebraMap_eq_fieldPullback φ (fun _ ↦ rfl)
  have := φ.finiteDimensional_functionField (fun _ ↦ rfl)
  have hover (R : W₁.Point) :
      (W₁.pointEquivDegreeOnePlace R).1.restrict F W₂.FunctionField =
        (W₂.pointEquivDegreeOnePlace Q).1 ↔ (Isogeny.Hom.ofIsogeny φ).pointMap R = Q :=
    (Isogeny.Hom.pointMap_ofIsogeny_eq_iff_restrict φ).symm
  refine ⟨fun hP ↦ ?_, fun ⟨R, hR, hRP⟩ ↦ by rw [← hRP]; exact (hover R).mpr hR⟩
  have hdeg : P.degree = 1 := by
    rw [Place.degree_eq_degree_restrict_mul_relativeDegree F W₂.FunctionField P, hP,
      (W₂.pointEquivDegreeOnePlace Q).2, one_mul]
    exact (Isogeny.isSplitCompletely φ (fun _ ↦ rfl) _).relativeDegree_eq_one hP
  obtain ⟨R, hR⟩ : ∃ R, (W₁.pointEquivDegreeOnePlace R).1 = P :=
    ⟨(W₁.pointEquivDegreeOnePlace).symm ⟨P, hdeg⟩, by simp⟩
  exact ⟨R, (hover R).mp (by rw [hR]; exact hP), hR⟩

/-- **`φ^* (Q) = ∑_{φ R = Q} (R)`** for a separable isogeny over a separably closed field.
PROVED. -/
theorem divisorPullback_ofPoint (Q : W₂.Point) :
    letI := φ.fieldPullback.toRingHom.toAlgebra
    φ.divisorPullback (fun _ ↦ rfl) (WeilDivisor.ofPoint (W₂.pointEquivDegreeOnePlace Q).1) =
      ∑ R ∈ (Isogeny.Hom.finite_setOf_pointMap_eq (Isogeny.Hom.ofIsogeny_ne_zero φ) Q).toFinset,
        WeilDivisor.ofPoint (W₁.pointEquivDegreeOnePlace R).1 := by
  classical
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  have := Isogeny.isScalarTower_of_algebraMap_eq_fieldPullback φ (fun _ ↦ rfl)
  have := φ.finiteDimensional_functionField (fun _ ↦ rfl)
  have hfin := Isogeny.Hom.finite_setOf_pointMap_eq (Isogeny.Hom.ofIsogeny_ne_zero φ) Q
  have hsum : ∑ R ∈ hfin.toFinset, WeilDivisor.ofPoint (W₁.pointEquivDegreeOnePlace R).1 =
      WeilDivisor.ofFinset (hfin.toFinset.map ⟨fun R ↦ (W₁.pointEquivDegreeOnePlace R).1,
        Subtype.val_injective.comp (W₁.pointEquivDegreeOnePlace).injective⟩) := by
    rw [WeilDivisor.ofFinset_eq_sum, Finset.sum_map, Function.Embedding.coeFn_mk]
  rw [hsum]
  ext P
  rw [Isogeny.coeff_divisorPullback, Isogeny.ramificationIdx_eq_one _ (fun _ ↦ rfl), Nat.cast_one,
    one_mul, WeilDivisor.coeff_ofFinset]
  split_ifs with hmem
  · obtain ⟨R, hR, hRP⟩ := Finset.mem_map.mp hmem
    rw [(restrict_eq_pointEquivDegreeOnePlace_iff φ Q P).mpr
      ⟨R, (Set.Finite.mem_toFinset hfin).mp hR, hRP⟩, WeilDivisor.coeff_ofPoint_self]
  · refine WeilDivisor.coeff_ofPoint_of_ne fun hP ↦ hmem ?_
    obtain ⟨R, hR, rfl⟩ := (restrict_eq_pointEquivDegreeOnePlace_iff φ Q P).mp hP
    exact Finset.mem_map_of_mem _ ((Set.Finite.mem_toFinset hfin).mpr hR)

end ZInQ.Contrib.CloudB3RC53.WeilIsogeny
