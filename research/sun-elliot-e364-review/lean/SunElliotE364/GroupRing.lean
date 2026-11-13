import Mathlib

/-! Characterwise units versus universal integral clearing in a finite group
algebra. Coefficients are retained explicitly; `∃ z : ℤ` is not replaced by a
bare nonzero or valuation assertion.
-/

namespace SunElliotE364

open scoped BigOperators
open AddMonoidAlgebra

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The unnormalised uniform group-basis element with constant coefficient. -/
noncomputable def uniform (c : ℚ) : AddMonoidAlgebra ℚ G := ∑ g : G, single g c

/-- The augmentation, written directly in the group basis. -/
noncomputable def augmentation (f : AddMonoidAlgebra ℚ G) : ℚ := ∑ g : G, f.coeff g

/-- Pointwise integrality of every actual group-basis coefficient. -/
def IntegralCoefficients (f : AddMonoidAlgebra ℚ G) : Prop :=
  ∀ g, ∃ z : ℤ, f.coeff g = (z : ℚ)

/-- Evaluation of coefficients against an additive character. -/
noncomputable def evalCharacter (χ : AddChar G ℚ) (f : AddMonoidAlgebra ℚ G) : ℚ :=
  ∑ g : G, χ g * f.coeff g

@[simp] lemma uniform_coeff (c : ℚ) (g : G) : (uniform (G := G) c).coeff g = c := by
  classical simp [uniform]

@[simp] lemma uniform_coeff_apply (c : ℚ) (g : G) :
    ∑ h : G, (single h c : AddMonoidAlgebra ℚ G).coeff g = c := by
  classical simp

lemma single_mul_uniform (g : G) (r c : ℚ) :
    single g r * uniform (G := G) c = r • uniform (G := G) c := by
  classical
  calc
    single g r * uniform (G := G) c = ∑ h : G, single (g + h) (r * c) := by
      simp [uniform, Finset.mul_sum]
    _ = ∑ h : G, single h (r * c) := by
      exact Fintype.sum_equiv (Equiv.addLeft g) _ _ (fun h => rfl)
    _ = r • uniform (G := G) c := by
      simp [uniform, Finset.smul_sum, smul_eq_mul]

lemma mul_uniform (f : AddMonoidAlgebra ℚ G) (c : ℚ) :
    f * uniform (G := G) c = augmentation f • uniform (G := G) c := by
  classical
  induction f using AddMonoidAlgebra.induction_on with
  | of g =>
      change single g (1 : ℚ) * uniform c =
        augmentation (single g (1 : ℚ)) • uniform c
      have haug : augmentation (single g (1 : ℚ)) = 1 := by
        classical simp [augmentation]
      rw [haug]
      simpa using single_mul_uniform g 1 c
  | add f g hf hg =>
      simp only [add_mul, hf, hg]
      simp only [augmentation, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        Finset.sum_add_distrib, add_smul]
  | smul r f hf =>
      rw [smul_mul_assoc, hf]
      have haug : augmentation (r • f) = r • augmentation f := by
        unfold augmentation
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro g hg
        change (r • f).coeff g = r • f.coeff g
        rfl
      rw [haug]
      module

@[simp] lemma augmentation_one :
    augmentation (1 : AddMonoidAlgebra ℚ G) = 1 := by
  classical
  simp [augmentation, AddMonoidAlgebra.one_def]

lemma integralCoefficients_one :
    IntegralCoefficients (1 : AddMonoidAlgebra ℚ G) := by
  classical
  intro g
  by_cases hg : g = 0
  · subst g
    exact ⟨1, by simp [AddMonoidAlgebra.one_def]⟩
  · exact ⟨0, by simp [AddMonoidAlgebra.one_def, hg]⟩

lemma integralCoefficients_augmentation {f : AddMonoidAlgebra ℚ G}
    (hf : IntegralCoefficients f) : ∃ a : ℤ, (a : ℚ) = augmentation f := by
  choose a ha using hf
  refine ⟨∑ g : G, a g, ?_⟩
  simp [augmentation, ← ha]

/-- The elementary binary group `(Z/2)^b`. -/
abbrev BinaryGroup (b : ℕ) := Fin b → ZMod 2

/-- The universal averaged idempotent in the binary family. -/
noncomputable def binaryE (b : ℕ) : AddMonoidAlgebra ℚ (BinaryGroup b) :=
  uniform (Fintype.card (BinaryGroup b) : ℚ)⁻¹

/-- The scalar-unit/universal-unit test element `1 + 2e`. -/
noncomputable def binaryU (b : ℕ) : AddMonoidAlgebra ℚ (BinaryGroup b) :=
  1 + (2 : ℚ) • binaryE b

@[simp] lemma card_binaryGroup (b : ℕ) : Fintype.card (BinaryGroup b) = 2 ^ b := by
  simp [BinaryGroup]

/-- If a universal clearing element is integral both before and after
multiplication by `1 + 2e`, its augmentation is restricted integrally. -/
lemma clearing_integral_remainder {G : Type*} [AddCommGroup G] [Fintype G]
    {f : AddMonoidAlgebra ℚ G} (c : ℚ)
    (hf : IntegralCoefficients f)
    (hfu : IntegralCoefficients (f * (1 + (2 : ℚ) • uniform c))) :
    ∃ a : ℤ, (a : ℚ) = augmentation f ∧
      IntegralCoefficients (G := G) ((2 * (a : ℚ)) • uniform c) := by
  obtain ⟨a, ha⟩ := integralCoefficients_augmentation (G := G) hf
  refine ⟨a, ha, ?_⟩
  have hid : f * (1 + (2 : ℚ) • uniform c) =
      f + (2 * (a : ℚ)) • uniform c := by
    calc
      f * (1 + (2 : ℚ) • uniform c) = f + (2 : ℚ) • (f * uniform c) := by
        rw [mul_add, mul_one, mul_smul_comm]
      _ = f + (2 : ℚ) • (augmentation f • uniform c) := by rw [mul_uniform]
      _ = f + (2 * (a : ℚ)) • uniform c := by rw [← ha]; module
  intro g
  obtain ⟨z1, hz1⟩ := hfu g
  obtain ⟨z2, hz2⟩ := hf g
  refine ⟨z1 - z2, ?_⟩
  rw [hid] at hz1
  simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, uniform_coeff]
  change (2 * (a : ℚ)) * c = ((z1 - z2 : ℤ) : ℚ)
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hz1
  simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, uniform_coeff] at hz1
  change f.coeff g + (2 * (a : ℚ)) * c = (z1 : ℚ) at hz1
  rw [hz2] at hz1
  push_cast at hz1 ⊢
  linear_combination hz1

/-- Every integral clearing of `u_b` forces the displayed power of two into
its augmentation. No scalar or non-scalar special shape is imposed on `f`. -/
theorem binary_clearing_bound {b : ℕ} (hb : 1 ≤ b)
    {f : AddMonoidAlgebra ℚ (BinaryGroup b)}
    (hf : IntegralCoefficients f) (hfu : IntegralCoefficients (f * binaryU b)) :
    ∃ a : ℤ, (a : ℚ) = augmentation f ∧ (2 ^ (b - 1) : ℤ) ∣ a := by
  obtain ⟨a, ha, hrest⟩ := clearing_integral_remainder (G := BinaryGroup b)
    (Fintype.card (BinaryGroup b) : ℚ)⁻¹ hf hfu
  refine ⟨a, ha, ?_⟩
  obtain ⟨z, hz⟩ := hrest 0
  have hbexp : (2 : ℕ) ^ b = 2 ^ (b - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hb]
  have hform : (2 * (a : ℚ)) * (Fintype.card (BinaryGroup b) : ℚ)⁻¹ =
      (a : ℚ) / (2 ^ (b - 1) : ℤ) := by
    rw [card_binaryGroup, hbexp]
    push_cast
    have hp : (2 : ℚ) ^ (b - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, uniform_coeff] at hz
  change (2 * (a : ℚ)) * (Fintype.card (BinaryGroup b) : ℚ)⁻¹ = (z : ℚ) at hz
  rw [hform] at hz
  apply (Rat.den_div_intCast_eq_one_iff a (2 ^ (b - 1) : ℤ) (by positivity)).mp
  rw [hz, Rat.den_intCast]

/-- With the trivial clearing element `f = 1`, this proves that `u_b` itself
is not integral when `b ≥ 2`. -/
theorem binaryU_not_integral {b : ℕ} (hb : 2 ≤ b) :
    ¬IntegralCoefficients (binaryU b) := by
  intro hu
  have hf : IntegralCoefficients (1 : AddMonoidAlgebra ℚ (BinaryGroup b)) :=
    integralCoefficients_one
  have hfu : IntegralCoefficients ((1 : AddMonoidAlgebra ℚ (BinaryGroup b)) * binaryU b) := by
    simpa using hu
  obtain ⟨a, ha, hd⟩ := binary_clearing_bound (by omega) hf hfu
  have haone : a = 1 := by
    have h := ha.trans augmentation_one
    exact_mod_cast h
  subst a
  have hdNat : (2 : ℕ) ^ (b - 1) ∣ 1 := by exact_mod_cast hd
  have honeNat : (2 : ℕ) ^ (b - 1) = 1 := Nat.dvd_one.mp hdNat
  have hone : (2 : ℤ) ^ (b - 1) = 1 := by exact_mod_cast honeNat
  have hpos : 0 < b - 1 := by omega
  have htwo : (2 : ℤ) ^ (b - 1) ≥ 2 := by
    calc
      (2 : ℤ) ^ (b - 1) ≥ (2 : ℤ) ^ 1 := by
        exact pow_le_pow_right₀ (by norm_num) hpos
      _ = 2 := by norm_num
  rw [hone] at htwo
  norm_num at htwo

lemma evalCharacter_add (χ : AddChar G ℚ) (f g : AddMonoidAlgebra ℚ G) :
    evalCharacter χ (f + g) = evalCharacter χ f + evalCharacter χ g := by
  simp [evalCharacter, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add,
    Finset.sum_add_distrib]

lemma evalCharacter_smul (χ : AddChar G ℚ) (r : ℚ) (f : AddMonoidAlgebra ℚ G) :
    evalCharacter χ (r • f) = r * evalCharacter χ f := by
  simp only [evalCharacter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  change χ g * (r • f).coeff g = r * (χ g * f.coeff g)
  change χ g * (r * f.coeff g) = _
  ring

lemma evalCharacter_one (χ : AddChar G ℚ) :
    evalCharacter χ (1 : AddMonoidAlgebra ℚ G) = 1 := by
  classical
  unfold evalCharacter
  rw [Finset.sum_eq_single (0 : G)]
  · simp [AddMonoidAlgebra.one_def]
  · intro g hg hne
    simp [AddMonoidAlgebra.one_def, Finsupp.single_apply, hne]
  · simp

/-- Character evaluation of the averaged idempotent is one at the trivial
character and zero at every other character. -/
theorem evalCharacter_binaryE (b : ℕ) (χ : AddChar (BinaryGroup b) ℚ) :
    evalCharacter χ (binaryE b) = if χ = 0 then 1 else 0 := by
  classical
  have hcard : (Fintype.card (BinaryGroup b) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (BinaryGroup b) ≠ 0)
  simp only [evalCharacter, binaryE, uniform_coeff, ← Finset.sum_mul,
    AddChar.sum_eq_ite]
  split_ifs with hχ
  · exact mul_inv_cancel₀ hcard
  · simp

/-- All sign-character evaluations are `3` or `1`, even though the group-basis
clearing budget is unbounded. -/
theorem evalCharacter_binaryU (b : ℕ) (χ : AddChar (BinaryGroup b) ℚ) :
    evalCharacter χ (binaryU b) = if χ = 0 then 3 else 1 := by
  rw [binaryU, evalCharacter_add, evalCharacter_smul, evalCharacter_one,
    evalCharacter_binaryE]
  split_ifs <;> norm_num


/-- The character values are not merely nonzero: their 2-adic valuations all
vanish. -/
theorem evalCharacter_binaryU_two_adic_unit (b : ℕ) (χ : AddChar (BinaryGroup b) ℚ) :
    padicValRat 2 (evalCharacter χ (binaryU b)) = 0 := by
  rw [evalCharacter_binaryU]
  split_ifs with hχ
  · rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
    norm_num
  · simp

end SunElliotE364
