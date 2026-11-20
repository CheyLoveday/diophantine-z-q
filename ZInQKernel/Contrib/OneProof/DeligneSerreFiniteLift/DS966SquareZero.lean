import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NoncommRing

/-! Lifting representations of a finite group across one square-zero reduction. -/

set_option autoImplicit false

namespace DS966Lifting

open scoped BigOperators Matrix

/-- Unit lifts exist across a surjective ring homomorphism whose kernel has square zero. -/
theorem exists_unit_lift {B C : Type*} [Ring B] [Ring C] [IsDedekindFiniteMonoid B]
    (f : B →+* C) (hf : Function.Surjective f)
    (hsq : ∀ x y : B, f x = 0 → f y = 0 → x * y = 0) (c : Cˣ) :
    ∃ u : Bˣ, f (u : B) = c := by
  obtain ⟨a, ha⟩ := hf (c : C)
  obtain ⟨b, hb⟩ := hf ((c⁻¹ : Cˣ) : C)
  let d := a * b - 1
  have hd : f d = 0 := by simp [d, ha, hb]
  have hdd := hsq d d hd hd
  have hprod : a * (b * (1 - d)) = 1 := by
    calc
      _ = (1 + d) * (1 - d) := by rw [← mul_assoc]; simp [d]
      _ = 1 - d * d := by noncomm_ring
      _ = 1 := by rw [hdd, sub_zero]
  exact ⟨Units.mkOfMulEqOne a _ hprod, ha⟩

/-- An explicit average of arbitrary unit lifts is multiplicative modulo a square-zero kernel.
No change of group or choice of irreducible constituents is needed. -/
theorem lift_square_zero {A B C H : Type*} [CommRing A] [Ring B] [Ring C]
    [Algebra A B] [Algebra A C] [IsDedekindFiniteMonoid B] [Group H] [Fintype H]
    (f : B →ₐ[A] C) (hf : Function.Surjective f)
    (hsq : ∀ x y : B, f x = 0 → f y = 0 → x * y = 0)
    (q : A) (hq : q * (Fintype.card H : A) = 1) (ρ : H →* Cˣ) :
    ∃ L : H →* Bˣ, ∀ g, f ((L g : Bˣ) : B) = (ρ g : C) := by
  classical
  choose U hU using fun g : H => exists_unit_lift f.toRingHom hf hsq (ρ g)
  let D (g x : H) : B := ↑(U (g * x) * (U x)⁻¹)
  let P (g : H) : B := q • ∑ x : H, D g x
  let E (g x : H) : B := D g x - P g
  have havg (b : B) : q • ∑ _ : H, b = b := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul A,
      smul_smul, hq, one_smul]
  have havg' (b : C) : q • ∑ _ : H, b = b := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul A,
      smul_smul, hq, one_smul]
  have hD (g x : H) : f (D g x) = (ρ g : C) := by
    have hUx (y : H) : Units.map f.toMonoidHom (U y) = ρ y := Units.ext (hU y)
    change ((Units.map f.toMonoidHom (U (g * x) * (U x)⁻¹) : Cˣ) : C) = (ρ g : C)
    rw [map_mul, map_inv, hUx, hUx, map_mul, mul_inv_cancel_right]
  have hP (g : H) : f (P g) = (ρ g : C) := by
    change f (q • ∑ x : H, D g x) = _
    rw [map_smul, map_sum]
    simpa only [hD] using havg' (ρ g : C)
  have hE (g x : H) : f (E g x) = 0 := by simp only [E, map_sub, hD, hP, sub_self]
  have hsum (g : H) : (∑ x : H, E g x) = 0 := by
    simp only [E, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul A]
    change (∑ x : H, D g x) - (Fintype.card H : A) • (q • ∑ x : H, D g x) = 0
    rw [smul_smul, mul_comm _ q, hq, one_smul, sub_self]
  have hsumShift (g h : H) : (∑ x : H, E g (h * x)) = 0 := by
    exact (Fintype.sum_equiv (Equiv.mulLeft h) (fun x => E g (h * x)) (E g)
      (fun _ => rfl)).trans (hsum g)
  have hfactor (g h x : H) : D (g * h) x = D g (h * x) * D h x := by
    change (↑(U ((g * h) * x) * (U x)⁻¹) : B) = ↑(U (g * (h * x)) * (U (h * x))⁻¹) *
      ↑(U (h * x) * (U x)⁻¹)
    rw [← Units.val_mul, mul_assoc g h x]
    simp [mul_assoc]
  have hexpand (g h x : H) : D (g * h) x =
      P g * P h + E g (h * x) * P h + P g * E h x := by
    have hg : D g (h * x) = P g + E g (h * x) := by simp [E]
    have hh : D h x = P h + E h x := by simp [E]
    have hz := hsq _ _ (hE g (h * x)) (hE h x)
    rw [hfactor, hg, hh, add_mul, mul_add, mul_add, hz, add_zero]
    abel
  have hone : P 1 = 1 := by
    simpa [P, D] using havg (1 : B)
  have hmul (g h : H) : P (g * h) = P g * P h := by
    change q • (∑ x : H, D (g * h) x) = _
    have hleft : (∑ x : H, E g (h * x) * P h) = 0 := by
      rw [← Finset.sum_mul, hsumShift, zero_mul]
    have hright : (∑ x : H, P g * E h x) = 0 := by
      rw [← Finset.mul_sum, hsum, mul_zero]
    simp only [hexpand, Finset.sum_add_distrib, hleft, hright, add_zero]
    exact havg (P g * P h)
  let φ : H →* B := { toFun := P, map_one' := hone, map_mul' := hmul }
  exact ⟨φ.toHomUnits, fun g => hP g⟩

/-- Matrix representations lift along a surjective square-zero extension whenever the group
order is invertible upstairs. This can be iterated on the quotients by powers of a maximal ideal. -/
theorem lift_matrix_square_zero {A k n H : Type*} [CommRing A] [CommRing k]
    [Fintype n] [DecidableEq n] [Group H] [Fintype H]
    (red : A →+* k) (hred : Function.Surjective red)
    (hsq : ∀ x y : A, red x = 0 → red y = 0 → x * y = 0)
    (q : A) (hq : q * (Fintype.card H : A) = 1) (ρ : H →* GL n k) :
    ∃ L : H →* GL n A, (Matrix.GeneralLinearGroup.map red).comp L = ρ := by
  let : Algebra A k := red.toAlgebra
  let f : Matrix n n A →ₐ[A] Matrix n n k :=
    { red.mapMatrix with commutes' := fun r =>
        Matrix.map_algebraMap r red (map_zero red) (by rfl) }
  have hf : Function.Surjective f := by
    intro M
    choose B hB using fun i j => hred (M i j)
    exact ⟨Matrix.of B, Matrix.ext hB⟩
  have hm {M : Matrix n n A} (hM : f M = 0) (i j : n) : red (M i j) = 0 :=
    congrArg (fun T : Matrix n n k => T i j) hM
  have hf2 (B D : Matrix n n A) (hB : f B = 0) (hD : f D = 0) : B * D = 0 := by
    ext i j
    exact Finset.sum_eq_zero (fun s _ => hsq _ _ (hm hB i s) (hm hD s j))
  obtain ⟨L, hL⟩ := lift_square_zero f hf hf2 q hq ρ
  refine ⟨L, MonoidHom.ext (fun g => Units.ext ?_)⟩
  exact hL g

end DS966Lifting
