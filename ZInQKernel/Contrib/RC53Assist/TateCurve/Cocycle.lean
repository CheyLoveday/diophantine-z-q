import ZInQKernel.Contrib.RC53Assist.TateCurve.InertiaReadings

/-!
# Character and cocycle identities of the Tate columns

The representation law forces the normalized first character to be
multiplicative and the upper-right coefficient to satisfy the cyclotomic
Kummer cocycle law. No cocycle identity is assumed.

Reference: multiplication of the two upper-triangular Tate matrices.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open Module

section Laws

variable {R G V : Type*} [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- **PROVED**: the two Tate columns have a multiplicative normalized
character and a cyclotomic crossed homomorphism. The quadratic twist is an
arbitrary unit-valued character here. Locator: `Representation.map_mul`. -/
theorem tate_character_cocycle_laws (ρ : Representation R G V) (b : Basis (Fin 2) R V)
    (ε : G →* Rˣ) (χ κ : G → R)
    (h0 : ∀ g, ρ g (b 0) = ((ε g : R) * χ g) • b 0)
    (h1 : ∀ g, ρ g (b 1) = (ε g : R) • (b 1 + κ g • b 0)) :
    χ 1 = 1 ∧ κ 1 = 0 ∧
      (∀ g h, χ (g * h) = χ g * χ h) ∧
      (∀ g h, κ (g * h) = κ g + χ g * κ h) := by
  classical
  have hc1 := congrArg (fun v => b.repr v 0) (h0 1)
  have hk1 := congrArg (fun v => b.repr v 0) (h1 1)
  have hχ1 : χ 1 = 1 := by simpa using hc1.symm
  have hκ1 : κ 1 = 0 := by simpa using hk1.symm
  refine ⟨hχ1, hκ1, ?_, ?_⟩
  · intro g h
    have hr : ρ (g * h) (b 0) = ρ g (ρ h (b 0)) := by
      rw [map_mul, Module.End.mul_apply]
    rw [h0 (g * h), h0 h, map_smul, h0 g, smul_smul] at hr
    have hc := congrArg (fun v => b.repr v 0) hr
    simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
      ite_true, smul_eq_mul, mul_one] at hc
    apply (ε (g * h)).isUnit.mul_left_cancel
    rw [map_mul, Units.val_mul] at hc ⊢
    linear_combination hc
  · intro g h
    have hr : ρ (g * h) (b 1) = ρ g (ρ h (b 1)) := by
      rw [map_mul, Module.End.mul_apply]
    rw [h1 (g * h), h1 h, map_smul, map_add, map_smul, h1 g, h0 g] at hr
    have hc := congrArg (fun v => b.repr v 0) hr
    simp only [map_add, map_smul, Basis.repr_self, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.single_apply, Fin.reduceEq, ite_true, ite_false,
      smul_eq_mul, mul_one, mul_zero, zero_add] at hc
    apply (ε (g * h)).isUnit.mul_left_cancel
    rw [map_mul, Units.val_mul] at hc ⊢
    linear_combination hc

/-- **PROVED DEFINITION**: the normalized first coefficient is a genuine
unit-valued character. Its inverse at `g` is the coefficient at `g⁻¹`.
Locator: `tate_character_cocycle_laws`. -/
def tateCyclotomicCharacter (ρ : Representation R G V) (b : Basis (Fin 2) R V)
    (ε : G →* Rˣ) (χ κ : G → R)
    (h0 : ∀ g, ρ g (b 0) = ((ε g : R) * χ g) • b 0)
    (h1 : ∀ g, ρ g (b 1) = (ε g : R) • (b 1 + κ g • b 0)) : G →* Rˣ := by
  obtain ⟨hχ1, _, hχ, _⟩ := tate_character_cocycle_laws ρ b ε χ κ h0 h1
  refine {
    toFun := fun g => ⟨χ g, χ (g⁻¹), ?_, ?_⟩
    map_one' := Units.ext hχ1
    map_mul' := fun g h => Units.ext (hχ g h) }
  · rw [← hχ, mul_inv_cancel, hχ1]
  · rw [← hχ, inv_mul_cancel, hχ1]

end Laws

end ZInQ.Contrib.RC53Assist.TateCurve
