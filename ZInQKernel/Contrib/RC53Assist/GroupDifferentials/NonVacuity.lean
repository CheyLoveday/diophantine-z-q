import ZInQKernel.Contrib.RC53Assist.GroupDifferentials.HigherDimension
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Smooth.Basic

/-!
# Non-vacuity: the multiplicative group over the rationals

The hypotheses of `AbelianCurve.InvariantDifferentialTrivialization` are satisfied by an actual
object: the multiplicative group `𝔾_m = Spec ℚ[T, T⁻¹]` over `Spec ℚ`, with the group structure
coming from the Hopf algebra of Laurent polynomials (Mathlib's
`AlgebraicGeometry.instGrpObjSpecAsOverSpec` and `LaurentPolynomial.instHopfAlgebra`). It is
integral, smooth, quasi-compact over `Spec ℚ` and one-dimensional. Consequently
`invariantDifferentialTrivialization` is applied below to a concrete group curve.

This file introduces no hypothesis and no new proposition; it records that the theorems of
`Trivialization.lean` and `HigherDimension.lean` are not vacuous.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.GroupDifferentials

open AlgebraicGeometry CategoryTheory LaurentPolynomial Polynomial

/-- PROVED. Laurent polynomials over the rationals form a smooth algebra: a localization of
the smooth polynomial algebra away from the variable. Locator: Mathlib's
`Algebra.Smooth.of_isLocalization_Away`, `Algebra.Smooth.comp` and
`LaurentPolynomial.isLocalization`. -/
theorem laurentPolynomial_smooth : Algebra.Smooth ℚ ℚ[T;T⁻¹] := by
  have : Algebra.Smooth ℚ ℚ[X] := ⟨inferInstance, inferInstance⟩
  have : Algebra.Smooth ℚ[X] ℚ[T;T⁻¹] := Algebra.Smooth.of_isLocalization_Away (X : ℚ[X])
  exact Algebra.Smooth.comp ℚ ℚ[X] ℚ[T;T⁻¹]

/-- PROVED. The ring of Laurent polynomials over the rationals is not a field: `T - 1` is a
nonzero element (evaluation at `2` gives `1`) killed by evaluation at `1`.
Locator: Mathlib's `LaurentPolynomial.eval₂`. -/
theorem laurentPolynomial_not_isField : ¬ IsField ℚ[T;T⁻¹] := by
  intro h
  let φ : ℚ[T;T⁻¹] →+* ℚ := LaurentPolynomial.eval₂ (RingHom.id ℚ) 1
  have hne : (T 1 - 1 : ℚ[T;T⁻¹]) ≠ 0 := by
    intro h0
    have h2 := congrArg
      (LaurentPolynomial.eval₂ (RingHom.id ℚ) (Units.mk0 (2 : ℚ) two_ne_zero)) h0
    simp at h2
    norm_num at h2
  obtain ⟨b, hb⟩ := h.mul_inv_cancel hne
  have h2 := congrArg φ hb
  simp [φ] at h2

/-- PROVED. The ring of Laurent polynomials over the rationals has Krull dimension one. It is
at most that of the polynomial ring, of which it is a localization, and it is positive since
the ring is a domain but not a field. Locator: Mathlib's
`Polynomial.ringKrullDim_of_isNoetherianRing`, `PrimeSpectrum.localization_comap_injective`,
`Order.krullDim_le_of_strictMono` and `Ring.KrullDimLE.isField_of_isDomain`. -/
theorem laurentPolynomial_ringKrullDim : ringKrullDim ℚ[T;T⁻¹] = 1 := by
  apply le_antisymm
  · have h1 : ringKrullDim ℚ[X] = 1 := by
      rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]; rfl
    rw [← h1]
    refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap ℚ[X] ℚ[T;T⁻¹]))
      (Monotone.strictMono_of_injective (fun p q h ↦ ?_)
        (PrimeSpectrum.localization_comap_injective _ (Submonoid.powers (X : ℚ[X]))))
    exact Ideal.comap_mono h
  · by_contra h
    have h0 : ringKrullDim ℚ[T;T⁻¹] ≤ 0 := Order.le_of_lt_succ (not_le.mp h)
    rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h0
    exact laurentPolynomial_not_isField Ring.KrullDimLE.isField_of_isDomain

/-- DEFINITION. The multiplicative group `𝔾_m = Spec ℚ[T, T⁻¹]` as an object over `Spec ℚ`;
its group-object structure is Mathlib's `AlgebraicGeometry.instGrpObjSpecAsOverSpec`. -/
abbrev multiplicativeGroupScheme : Over (Spec (.of ℚ)) :=
  (Spec (CommRingCat.of ℚ[T;T⁻¹])).asOver (Spec (CommRingCat.of ℚ))

/-- PROVED. `𝔾_m` is integral: its ring of functions is a domain. Locator: Mathlib's instances
`IsDomain` for Laurent polynomials over a domain and `IsIntegral` for the spectrum of a
domain. -/
instance multiplicativeGroupScheme_isIntegral : IsIntegral multiplicativeGroupScheme.left := by
  change IsIntegral (Spec (CommRingCat.of ℚ[T;T⁻¹]))
  infer_instance

/-- PROVED. `𝔾_m` is smooth over `Spec ℚ`. Locator: `laurentPolynomial_smooth`. -/
instance multiplicativeGroupScheme_smooth : Smooth multiplicativeGroupScheme.hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ[T;T⁻¹])))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr laurentPolynomial_smooth

/-- PROVED. `𝔾_m` is quasi-compact over `Spec ℚ` (a morphism of affine schemes).
Locator: Mathlib's instances for `Spec.map`. -/
instance multiplicativeGroupScheme_quasiCompact : QuasiCompact multiplicativeGroupScheme.hom := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ[T;T⁻¹])))
  infer_instance

/-- PROVED. `𝔾_m` is one-dimensional. Locator: `laurentPolynomial_ringKrullDim` and Mathlib's
`PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`. -/
theorem multiplicativeGroupScheme_dim :
    topologicalKrullDim multiplicativeGroupScheme.left = 1 :=
  (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim ℚ[T;T⁻¹]).trans
    laurentPolynomial_ringKrullDim

/-- PROVED (non-vacuity example). The hypotheses of
`AbelianCurve.InvariantDifferentialTrivialization` are satisfiable: some
group object over `Spec ℚ` is integral, smooth, quasi-compact and one-dimensional. -/
example : ∃ G : Over (Spec (.of ℚ)), ∃ (_ : GrpObj G) (_ : IsIntegral G.left)
    (_ : Smooth G.hom) (_ : QuasiCompact G.hom), topologicalKrullDim G.left = 1 :=
  ⟨multiplicativeGroupScheme, inferInstance, inferInstance, inferInstance, inferInstance,
    multiplicativeGroupScheme_dim⟩

/-- PROVED (non-vacuity example). `invariantDifferentialTrivialization` applied to `𝔾_m`
gives a trivialization of its actual differential sheaf. -/
example : Nonempty (AbelianCurve.differentialSheaf multiplicativeGroupScheme.hom ≅
    SheafOfModules.unit multiplicativeGroupScheme.left.ringCatSheaf) :=
  invariantDifferentialTrivialization multiplicativeGroupScheme multiplicativeGroupScheme_dim

/-- PROVED. `𝔾_m` is smooth of relative dimension one over `Spec ℚ`.
Locator: `AbelianCurve.smooth_relativeDimension_one` and `multiplicativeGroupScheme_dim`. -/
instance multiplicativeGroupScheme_smoothOfRelativeDimension :
    SmoothOfRelativeDimension 1 multiplicativeGroupScheme.hom :=
  AbelianCurve.smooth_relativeDimension_one multiplicativeGroupScheme.hom
    multiplicativeGroupScheme_dim

/-- PROVED (non-vacuity example). The hypotheses of
`nonempty_relativeDifferentials_iso_unit_of_grpObj` and
`nonempty_relativeDifferentials_iso_free_of_grpObj` (with `d = 1`): both apply to `𝔾_m`. -/
example : Nonempty (multiplicativeGroupScheme.hom.relativeDifferentials ≅
      SheafOfModules.unit multiplicativeGroupScheme.left.ringCatSheaf) ∧
    Nonempty (multiplicativeGroupScheme.hom.relativeDifferentials ≅
      SheafOfModules.free (R := multiplicativeGroupScheme.left.ringCatSheaf)
        (ULift.{0} (Fin 1))) := by
  letI : GrpObj (Over.mk multiplicativeGroupScheme.hom) :=
    inferInstanceAs (GrpObj multiplicativeGroupScheme)
  exact ⟨nonempty_relativeDifferentials_iso_unit_of_grpObj multiplicativeGroupScheme.hom,
    nonempty_relativeDifferentials_iso_free_of_grpObj multiplicativeGroupScheme.hom 1⟩

end ZInQ.Contrib.RC53Assist.GroupDifferentials
