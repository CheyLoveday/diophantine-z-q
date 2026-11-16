import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.Localization.FractionRing

/-! # javanpeykar-dict: fraction fields and base change by an algebraic field extension -/

noncomputable section

namespace JavanpeykarDict

open scoped TensorProduct

variable {K A KA L B M : Type} [Field K] [CommRing A] [IsDomain A] [Algebra K A] [Field KA]
  [Algebra A KA] [IsFractionRing A KA] [Algebra K KA] [IsScalarTower K A KA]
  [Field L] [Algebra K L] [CommRing B] [Algebra K B] [Field M] [Algebra B M] [IsFractionRing B M]
  [Algebra K M] [IsScalarTower K B M]

/-- **The fraction field commutes with an algebraic base change (glue, proved).** If
`β : A ⊗_K L ≅ B` and `KA = Frac A`, `M = Frac B`, then `KA ⊗_K L ≅ M` through `ι` and `s` compatible
with `β`. -/
theorem productMap_bijective_of_fraction (β : A ⊗[K] L →ₐ[K] B) (hβ : Function.Bijective β)
    (ι : KA →ₐ[K] M) (s : L →ₐ[K] M) [Algebra.IsAlgebraic K L]
    (hι : ∀ a : A, ι (algebraMap A KA a) = algebraMap B M (β (a ⊗ₜ 1)))
    (hs : ∀ l : L, s l = algebraMap B M (β (1 ⊗ₜ l))) :
    Function.Bijective (Algebra.TensorProduct.productMap ι s) := by
  set Ψ := Algebra.TensorProduct.productMap ι s
  set incl : A ⊗[K] L →ₐ[K] KA ⊗[K] L :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A KA) (AlgHom.id K L)
  have hcomp : ∀ w, Ψ (incl w) = algebraMap B M (β w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a l =>
      simp only [incl, Ψ, Algebra.TensorProduct.map_tmul, IsScalarTower.coe_toAlgHom',
        AlgHom.id_apply, Algebra.TensorProduct.productMap_apply_tmul, hι, hs, ← map_mul,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => simp [hx, hy]
  have hden : ∀ w : KA ⊗[K] L, ∃ a ∈ nonZeroDivisors A, ∃ w' : A ⊗[K] L,
      (algebraMap A KA a ⊗ₜ (1 : L)) * w = incl w' := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨1, one_mem _, 0, by simp⟩
    | tmul x l =>
      obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (nonZeroDivisors A) x
      refine ⟨b, b.2, a ⊗ₜ l, ?_⟩
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, incl,
        Algebra.TensorProduct.map_tmul, IsScalarTower.coe_toAlgHom', AlgHom.id_apply]
      rw [mul_comm, h]
    | add x y hx hy =>
      obtain ⟨a₁, ha₁, w₁, h₁⟩ := hx
      obtain ⟨a₂, ha₂, w₂, h₂⟩ := hy
      refine ⟨a₁ * a₂, mul_mem ha₁ ha₂, (a₂ ⊗ₜ 1) * w₁ + (a₁ ⊗ₜ 1) * w₂, ?_⟩
      have e1 : (algebraMap A KA (a₁ * a₂) ⊗ₜ (1 : L)) =
          (algebraMap A KA a₂ ⊗ₜ (1 : L)) * (algebraMap A KA a₁ ⊗ₜ (1 : L)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, map_mul, mul_comm]
      have e2 : (algebraMap A KA (a₁ * a₂) ⊗ₜ (1 : L)) =
          (algebraMap A KA a₁ ⊗ₜ (1 : L)) * (algebraMap A KA a₂ ⊗ₜ (1 : L)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, map_mul]
      rw [mul_add, map_add, map_mul, map_mul]
      congr 1
      · rw [e1, mul_assoc, h₁]; rfl
      · rw [e2, mul_assoc, h₂]; rfl
  have hunit : ∀ a ∈ nonZeroDivisors A,
      (algebraMap A KA a)⁻¹ ⊗ₜ (1 : L) * (algebraMap A KA a ⊗ₜ (1 : L)) = 1 := by
    intro a ha
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      inv_mul_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha)]
    rfl
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨a, ha, w', h⟩ := hden w
    have h1 : algebraMap B M (β w') = 0 := by
      rw [← hcomp, ← h, map_mul, hw, mul_zero]
    have h2 : w' = 0 := by
      have := (IsFractionRing.injective B M) (h1.trans (map_zero _).symm)
      exact hβ.1 (this.trans (map_zero β).symm)
    rw [h2, map_zero] at h
    calc w = ((algebraMap A KA a)⁻¹ ⊗ₜ (1 : L) * (algebraMap A KA a ⊗ₜ (1 : L))) * w := by
          rw [hunit a ha, one_mul]
      _ = 0 := by rw [mul_assoc, h, mul_zero]
  haveI : IsDomain (KA ⊗[K] L) := hinj.isDomain Ψ.toRingHom
  have hfield : IsField (KA ⊗[K] L) :=
    Algebra.TensorProduct.isField_of_isAlgebraic K KA L (.inr inferInstance)
  refine ⟨hinj, fun m => ?_⟩
  obtain ⟨b₁, b₂, -, rfl⟩ := IsFractionRing.div_surjective (A := B) m
  obtain ⟨w₁, rfl⟩ := hβ.2 b₁
  obtain ⟨w₂, rfl⟩ := hβ.2 b₂
  by_cases h0 : incl w₂ = 0
  · refine ⟨0, ?_⟩
    rw [map_zero, ← hcomp w₂, h0, map_zero, div_zero]
  obtain ⟨u, hu⟩ := hfield.mul_inv_cancel h0
  refine ⟨incl w₁ * u, ?_⟩
  have hΨu : Ψ (incl w₂) * Ψ u = 1 := by rw [← map_mul, hu, map_one]
  rw [map_mul, hcomp, ← hcomp w₂, eq_div_iff (left_ne_zero_of_mul_eq_one hΨu), mul_assoc,
    mul_comm (Ψ u), hΨu, mul_one]

end JavanpeykarDict
