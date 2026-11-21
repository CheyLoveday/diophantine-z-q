import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedLocalCharacter
import Mathlib.NumberTheory.GaussSum
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! The residual cyclotomic reading of the quadratic character in tex 9810–9811. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine O12 O12Local PrintsArith Symbols
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {p : ℕ} [Fact p.Prime]

/-- If an absolute Galois element acts on a primitive p-th root by
exponent `a`, its sign on `ℚ(√p*)` is the quadratic character of `a`. -/
theorem quadraticChar_of_cyclotomic_action (hp₂ : p ≠ 2) (g : GalQ)
    {ζ : Qbar} (hζ : IsPrimitiveRoot ζ p) (a : (ZMod p)ˣ)
    (hz : g ζ = ζ ^ (a : ZMod p).val) :
    quadraticChar (ZMod p) (a : ZMod p) =
      if bitChar p g = 1 then 1 else -1 := by
  classical
  have hp : p.Prime := Fact.out
  have hchar : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  let ψ := AddChar.zmodChar p hζ.pow_eq_one
  let χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom Qbar)
  let y := gaussSum χ ψ
  have hχ : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (Int.cast_injective (α := Qbar))).mpr (quadraticChar_ne_one hchar)
  have hy : y ^ 2 = (sstar p : Qbar) := by
    rw [show y = gaussSum χ ψ from rfl,
      gaussSum_sq hχ ((quadraticChar_isQuadratic _).comp _)
        (AddChar.zmodChar_primitive_of_primitive_root p hζ)]
    simp only [χ, MulChar.ringHomComp_apply, Int.coe_castRingHom, quadraticChar_neg_one hchar,
      ZMod.card, ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp (hp.odd_of_ne_two hp₂)), sstar, Int.cast_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_one, Int.cast_natCast]
  have hψ (x : ZMod p) : g (ψ x) = (ψ.mulShift a) x := by
    rw [AddChar.mulShift_apply, show ψ x = ζ ^ x.val from rfl, map_pow, hz, ← pow_mul,
      show ψ ((a : ZMod p) * x) = ζ ^ (((a : ZMod p) * x).val) from rfl,
      ZMod.val_mul, pow_eq_pow_mod _ hζ.pow_eq_one]
  have he : g y = gaussSum χ (ψ.mulShift a) := by
    unfold y gaussSum
    simp only [map_sum, map_mul, hψ, χ, MulChar.ringHomComp_apply, Int.coe_castRingHom,
      map_intCast]
  have hsq : χ a ^ 2 = 1 := by
    simp only [χ, MulChar.ringHomComp_apply, ← map_pow, quadraticChar_sq_one a.ne_zero, map_one]
  have ha : g y = χ a * y := by
    have h := gaussSum_mulShift χ ψ a
    rw [← he] at h
    calc
      g y = χ a * (χ a * g y) := by rw [← mul_assoc, ← pow_two, hsq, one_mul]
      _ = χ a * y := by rw [h]
  have hnon : sstar p ≠ 0 := by
    unfold sstar
    exact mul_ne_zero (pow_ne_zero _ (by decide)) (Int.natCast_ne_zero.mpr hp.ne_zero)
  have hy0 : y ≠ 0 := by
    rintro e
    exact (Int.cast_ne_zero.mpr hnon : (sstar p : Qbar) ≠ 0) (hy.symm.trans (by simp [e]))
  have hfix : bitChar p g = 1 ↔ g y = y := by
    rw [bitChar_apply, sqrtChar_eq_one_iff _ hnon]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans (sqrtQbar_sq _).symm) with h | h
    · rw [h]
    · rw [h, map_neg, neg_inj]
  have hfix' : bitChar p g = 1 ↔ quadraticChar (ZMod p) (a : ZMod p) = 1 := by
    rw [hfix, ha]
    constructor
    · intro e
      have e' : χ a = 1 := mul_right_cancel₀ hy0 (e.trans (one_mul _).symm)
      apply Int.cast_injective (α := Qbar)
      simpa only [χ, MulChar.ringHomComp_apply, Int.coe_castRingHom, Int.cast_one] using e'
    · intro e
      change ((quadraticChar (ZMod p) (a : ZMod p) : ℤ) : Qbar) * y = y
      rw [e, Int.cast_one, one_mul]
  rcases quadraticChar_dichotomy (F := ZMod p) a.ne_zero with h | h
  · rw [ite_eq_left (hfix'.mpr h)]
    exact h
  · rw [ite_eq_right (fun e => (by decide : (-1 : ℤ) ≠ 1) (h.symm.trans (hfix'.mp e)))]
    exact h

/-- GLUE (tex 9784–9785). The geometric reciprocity map on the chosen
Weil group reduces on inertia to the action on p-th roots of unity.
The arithmetic Artin map acts on these roots through the inverse unit. -/
def ReciprocityAt.ResidueCyclotomic {Q : LocalPair p} (C : ReciprocityAt Q) : Prop :=
  ∀ w : weilAt Q, ∀ hw : (w : GalQ) ∈ Q.Q.inertia GalQ,
    ∀ ζ : Qbar, IsPrimitiveRoot ζ p →
      (w : GalQ) ζ = ζ ^ ((localUnitResidue (C.toUnits w) (C.inertia_unit w hw) : (ZMod p)ˣ) :
        ZMod p).val

theorem reciprocity_quadratic_of_residue {K : Type*} [Field K] (hp₂ : p ≠ 2)
    {Q : LocalPair p} (C : ReciprocityAt Q) (hC : ReciprocityAt.ResidueCyclotomic C)
    (χ : LocalCharacter p K)
    (hχ : ∀ u hu, (χ u : K) = (quadraticChar (ZMod p) (localUnitResidue u hu) : K)) :
    ∀ w : weilAt Q, (w : GalQ) ∈ Q.Q.inertia GalQ →
      (χ (C.toUnits w) : K) = if bitChar p (w : GalQ) = 1 then 1 else -1 := by
  intro w hw
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Qbar p
  rw [hχ _ (C.inertia_unit w hw), quadraticChar_of_cyclotomic_action hp₂ _
    hζ _ (hC w hw ζ hζ)]
  split <;> simp

end ZInQ.Manuscript.RC.EvenJoin
