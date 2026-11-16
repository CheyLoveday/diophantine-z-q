import ZInQKernel.OneProof.H.LF4T5

/-!
# deg-det, step (3): `|det T_ℓ f|_ℓ = |#ker f|_ℓ` for a surjective `f` with finite kernel

Abstract form: `M` an abelian group with `#M[ℓⁿ] = ℓ^{nr}`, `f : M → M` surjective with finite kernel.
-/

open Polynomial

noncomputable section

namespace DegDet.TateIndex

/-! ## 1. Index of a full sublattice of a free `ℤ_ℓ`-module -/

section Index

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- `|a|_ℓ = #(ℤ_ℓ/(a))⁻¹`. -/
theorem norm_eq_inv_card_quot (a : ℤ_[ℓ]) (ha : a ≠ 0) :
    ‖a‖ = ((Nat.card (ℤ_[ℓ] ⧸ Ideal.span {a}) : ℕ) : ℝ)⁻¹ := by
  have hspan : Ideal.span {a} = Ideal.span {(ℓ : ℤ_[ℓ]) ^ a.valuation} := by
    conv_lhs => rw [PadicInt.unitCoeff_spec ha]
    exact Ideal.span_singleton_mul_left_unit (PadicInt.unitCoeff ha).isUnit _
  have hcard : Nat.card (ℤ_[ℓ] ⧸ Ideal.span {a}) = ℓ ^ a.valuation := by
    rw [hspan, ← PadicInt.ker_toZModPow]
    rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective (PadicInt.toZModPow a.valuation))).toEquiv, Nat.card_zmod]
  rw [hcard, PadicInt.norm_eq_zpow_neg_valuation ha, zpow_neg, zpow_natCast]
  push_cast
  rfl

variable {T : Type*} [AddCommGroup T] [Module ℤ_[ℓ] T] [Module.Free ℤ_[ℓ] T] [Module.Finite ℤ_[ℓ] T]

/-- **`|det F|_ℓ = [T : F(T)]⁻¹`** for an injective `ℤ_ℓ`-linear endomorphism of a free module of finite rank. -/
theorem norm_det_eq_inv_card (F : T →ₗ[ℤ_[ℓ]] T) (hF : Function.Injective F) :
    ‖LinearMap.det F‖ = ((Nat.card (T ⧸ LinearMap.range F) : ℕ) : ℝ)⁻¹ := by
  classical
  set N := LinearMap.range F
  let b := Module.Free.chooseBasis ℤ_[ℓ] T
  let eF : T ≃ₗ[ℤ_[ℓ]] N := LinearEquiv.ofInjective F hF
  have h : Module.finrank ℤ_[ℓ] N = Module.finrank ℤ_[ℓ] T := eF.symm.finrank_eq
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : T ≃ₗ[ℤ_[ℓ]] N := b'.equiv ab (Equiv.refl _)
  let f : T →ₗ[ℤ_[ℓ]] T := N.subtype.comp (e' : T →ₗ[ℤ_[ℓ]] N)
  have hFf : Associated (LinearMap.det F) (LinearMap.det f) := by
    have h1 : F = N.subtype.comp (eF : T →ₗ[ℤ_[ℓ]] N) := by
      ext x; rfl
    rw [h1]
    exact LinearMap.associated_det_comp_equiv _ _ _
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    change ((b'.equiv ab (Equiv.refl _)) (b' i) : T) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdet : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hnorm : ‖LinearMap.det F‖ = ‖LinearMap.det f‖ := by
    obtain ⟨u, hu⟩ := hFf
    rw [← hu, norm_mul, PadicInt.isUnit_iff.mp u.isUnit, mul_one]
  rw [hnorm, hdet, norm_prod]
  rw [Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv, Nat.card_pi]
  push_cast
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact norm_eq_inv_card_quot (a i) (Submodule.smithNormalFormCoeffs_ne_zero b h i)

end Index

end DegDet.TateIndex
