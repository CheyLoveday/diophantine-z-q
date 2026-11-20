import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import ZInQKernel.Contrib.CloudB3E1NoCM.Invariance
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Differential

namespace ZInQ.Manuscript.RC.HCMV21

open TauCeti.Isogeny WeierstrassCurve WeierstrassCurve.Affine
open ZInQ.Contrib.CloudB3E1NoCM (vcIsogeny vcX vcY fieldPullback_genericX fieldPullback_genericY)

/-- In characteristic zero, the invariant differential distinguishes elliptic
curve homomorphisms with the same source and target. -/
theorem hom_eq_of_pullback_invariantDifferential {F : Type} [Field F] [CharZero F]
    {U V : WeierstrassCurve.Affine F} [U.IsElliptic] [V.IsElliptic] {f g : Hom U V}
    (h : f.pullbackDifferential (invariantDifferential V) =
      g.pullbackDifferential (invariantDifferential V)) : f = g := by
  by_contra hne
  let φ := Hom.toIsogeny (sub_ne_zero.mpr hne)
  have hf : Hom.ofIsogeny φ = f - g := Hom.ofIsogeny_toIsogeny _
  have : CharZero φ.fieldPullback.fieldRange :=
    charZero_of_injective_algebraMap (algebraMap F φ.fieldPullback.fieldRange).injective
  have hs : Algebra.IsSeparable φ.fieldPullback.fieldRange U.FunctionField := inferInstance
  have hφ := (isSeparable_iff_pullbackDifferential_ne_zero φ).mp hs
  apply hφ
  rw [← Hom.pullbackDifferential_ofIsogeny, hf,
    Hom.pullbackDifferential_sub_invariantDifferential, h, sub_self]

set_option maxHeartbeats 600000 in
/-- The inverse coordinate map of an admissible change of variables pulls back
the invariant differential by the factor `u⁻¹`. -/
theorem vc_pullback_differential {F : Type} [Field F]
    {A B : WeierstrassCurve F} (C : VariableChange F) (h : C • A = B) :
    (vcIsogeny C h).pullbackDifferential (invariantDifferential A.toAffine) =
      (C.u : F)⁻¹ • invariantDifferential B.toAffine := by
  subst B
  let W : WeierstrassCurve.Affine F := (C • A).toAffine
  let φ : TauCeti.Isogeny W A.toAffine := vcIsogeny C (rfl : C • A = C • A)
  let α : F →+* W.FunctionField := algebraMap F W.FunctionField
  let u := α (C.u : F)
  have hu : u ≠ 0 := (map_ne_zero α).2 C.u.ne_zero
  have hden : φ.fieldPullback (invariantDifferentialDenom A.toAffine) =
      u ^ 3 * invariantDifferentialDenom W := by
    simp only [φ, u, α, W, invariantDifferentialDenom_def, map_add, map_mul, map_ofNat,
      AlgHom.commutes, fieldPullback_genericX, fieldPullback_genericY, vcX, vcY,
      variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val, map_inv₀, map_pow]
    have hi : (algebraMap F W.FunctionField (C.u : F)) ≠ 0 := hu
    clear hu
    field_simp [hi]
    ring
  have hdx : KaehlerDifferential.D F W.FunctionField (vcX C) =
      ((C.u : F) ^ 2) • KaehlerDifferential.D F W.FunctionField (genericX W) := by
    rw [vcX, ← Algebra.smul_def, map_add, Derivation.map_smul, Derivation.map_algebraMap, add_zero]
  change φ.pullbackDifferential _ = _ • invariantDifferential W
  rw [invariantDifferential_def, pullbackDifferential_smul, pullbackDifferential_D,
    map_inv₀, hden, show φ.fieldPullback (genericX A.toAffine) = vcX C from
      fieldPullback_genericX C rfl, invariantDifferential_def W]
  rw [hdx, ← IsScalarTower.algebraMap_smul W.FunctionField ((C.u : F) ^ 2),
    ← IsScalarTower.algebraMap_smul W.FunctionField (C.u : F)⁻¹]
  simp only [smul_smul, map_inv₀, map_pow]
  congr 1
  change (u ^ 3 * invariantDifferentialDenom W)⁻¹ * u ^ 2 =
    u⁻¹ * (invariantDifferentialDenom W)⁻¹
  have hpow : (u ^ 3)⁻¹ * u ^ 2 = u⁻¹ := by
    field_simp
  rw [mul_inv_rev, mul_assoc, hpow, mul_comm]

/-- Equality of `j` lifts to a geometric isomorphism respecting the two labels
when their scalar actions on the invariant differentials have the same type.
The isomorphism is an admissible change of variables, whose underlying morphism
is `vcIsogeny` with its explicit Weierstrass coordinate formulas. -/
theorem exists_CM_variableChange_of_j_eq {F : Type} [Field F] [CharZero F] [IsSepClosed F]
    {R : Type*} (τ : R → F) (A B : WeierstrassCurve F) [A.IsElliptic] [B.IsElliptic]
    (ρA : R → Hom A.toAffine A.toAffine) (ρB : R → Hom B.toAffine B.toAffine)
    (hA : ∀ r, (ρA r).pullbackDifferential (invariantDifferential A.toAffine) =
      τ r • invariantDifferential A.toAffine)
    (hB : ∀ r, (ρB r).pullbackDifferential (invariantDifferential B.toAffine) =
      τ r • invariantDifferential B.toAffine) (hj : A.j = B.j) :
    ∃ (C : VariableChange F) (h : C • A = B),
      let f := Hom.ofIsogeny (vcIsogeny C h)
      ∀ r, f.comp (ρB r) = (ρA r).comp f := by
  obtain ⟨C, hC⟩ := A.exists_variableChange_of_j_eq B hj
  refine ⟨C, hC, ?_⟩
  dsimp only
  intro r
  apply hom_eq_of_pullback_invariantDifferential
  let φ := vcIsogeny C hC
  change ((Hom.ofIsogeny φ).comp (ρB r)).pullbackDifferential _ =
    ((ρA r).comp (Hom.ofIsogeny φ)).pullbackDifferential _
  rw [Hom.pullbackDifferential_comp, Hom.pullbackDifferential_comp]
  simp only [LinearMap.comp_apply, hA, map_smul]
  rw [Hom.pullbackDifferential_ofIsogeny, vc_pullback_differential C hC, map_smul, hB,
    smul_comm]

end ZInQ.Manuscript.RC.HCMV21
