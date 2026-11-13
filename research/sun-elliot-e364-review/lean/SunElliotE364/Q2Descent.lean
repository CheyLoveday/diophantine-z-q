import SunElliotE364.GroupRing

/-! The full coefficientwise `Z₂` version of the clearing obstruction.
Integrality is the actual padic-norm condition defining `ℤ_[2]`. -/

namespace SunElliotE364

open scoped BigOperators
open AddMonoidAlgebra

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def q2uniform (c : ℚ_[2]) : AddMonoidAlgebra ℚ_[2] G :=
  ∑ g : G, single g c

noncomputable def q2augmentation (f : AddMonoidAlgebra ℚ_[2] G) : ℚ_[2] :=
  ∑ g : G, f.coeff g

/-- Every group-basis coefficient belongs to `ℤ_[2]`, expressed by its
characterizing norm inequality rather than by an assumed representing term. -/
def Q2IntegralCoefficients (f : AddMonoidAlgebra ℚ_[2] G) : Prop :=
  ∀ g, ‖f.coeff g‖ ≤ 1

@[simp] lemma q2uniform_coeff (c : ℚ_[2]) (g : G) :
    (q2uniform (G := G) c).coeff g = c := by
  classical simp [q2uniform]

lemma q2single_mul_uniform (g : G) (r c : ℚ_[2]) :
    single g r * q2uniform (G := G) c = r • q2uniform (G := G) c := by
  classical
  calc
    single g r * q2uniform (G := G) c = ∑ h : G, single (g + h) (r * c) := by
      simp [q2uniform, Finset.mul_sum]
    _ = ∑ h : G, single h (r * c) := by
      exact Fintype.sum_equiv (Equiv.addLeft g) _ _ (fun h => rfl)
    _ = r • q2uniform (G := G) c := by
      simp [q2uniform, Finset.smul_sum, smul_eq_mul]

lemma q2mul_uniform (f : AddMonoidAlgebra ℚ_[2] G) (c : ℚ_[2]) :
    f * q2uniform (G := G) c = q2augmentation f • q2uniform (G := G) c := by
  classical
  induction f using AddMonoidAlgebra.induction_on with
  | of g =>
      change single g (1 : ℚ_[2]) * q2uniform c =
        q2augmentation (single g (1 : ℚ_[2])) • q2uniform c
      have haug : q2augmentation (single g (1 : ℚ_[2])) = 1 := by
        classical simp [q2augmentation]
      rw [haug]
      simpa using q2single_mul_uniform g 1 c
  | add f g hf hg =>
      simp only [add_mul, hf, hg]
      simp only [q2augmentation, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        Finset.sum_add_distrib, add_smul]
  | smul r f hf =>
      rw [smul_mul_assoc, hf]
      have haug : q2augmentation (r • f) = r • q2augmentation f := by
        unfold q2augmentation
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro g hg
        change (r • f).coeff g = r • f.coeff g
        rfl
      rw [haug]
      module

@[simp] lemma q2augmentation_one :
    q2augmentation (1 : AddMonoidAlgebra ℚ_[2] G) = 1 := by
  classical simp [q2augmentation, AddMonoidAlgebra.one_def]

lemma q2integral_one : Q2IntegralCoefficients (1 : AddMonoidAlgebra ℚ_[2] G) := by
  classical
  intro g
  by_cases hg : g = 0
  · subst g
    simp [AddMonoidAlgebra.one_def]
  · have hzero : ((1 : AddMonoidAlgebra ℚ_[2] G).coeff g) = 0 := by
      simp [AddMonoidAlgebra.one_def, hg]
    rw [hzero, norm_zero]
    norm_num

/-- The finite ultrametric sum bound at norm one. -/
lemma q2norm_sum_le_one {ι : Type*} (s : Finset ι) (f : ι → ℚ_[2])
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) : ‖∑ i ∈ s, f i‖ ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      apply le_trans (IsUltrametricDist.norm_add_le_max _ _)
      exact max_le (hf a (Finset.mem_insert_self _ _))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma q2augmentation_integral {f : AddMonoidAlgebra ℚ_[2] G}
    (hf : Q2IntegralCoefficients f) : ‖q2augmentation f‖ ≤ 1 := by
  exact q2norm_sum_le_one Finset.univ _ (fun g hg => hf g)

noncomputable def q2binaryE (b : ℕ) : AddMonoidAlgebra ℚ_[2] (BinaryGroup b) :=
  q2uniform (Fintype.card (BinaryGroup b) : ℚ_[2])⁻¹

noncomputable def q2binaryU (b : ℕ) : AddMonoidAlgebra ℚ_[2] (BinaryGroup b) :=
  1 + (2 : ℚ_[2]) • q2binaryE b

/-- If both `f` and `f*u` have `Z₂` coefficients, the remainder `2 aug(f)e`
has `Z₂` coefficients. -/
lemma q2_clearing_integral_remainder {G : Type*} [AddCommGroup G] [Fintype G]
    {f : AddMonoidAlgebra ℚ_[2] G} (c : ℚ_[2])
    (hf : Q2IntegralCoefficients f)
    (hfu : Q2IntegralCoefficients (f * (1 + (2 : ℚ_[2]) • q2uniform c))) :
    Q2IntegralCoefficients (G := G) ((2 * q2augmentation f) • q2uniform c) := by
  have hid : f * (1 + (2 : ℚ_[2]) • q2uniform c) =
      f + (2 * q2augmentation f) • q2uniform c := by
    calc
      f * (1 + (2 : ℚ_[2]) • q2uniform c) =
          f + (2 : ℚ_[2]) • (f * q2uniform c) := by
        rw [mul_add, mul_one, mul_smul_comm]
      _ = f + (2 : ℚ_[2]) • (q2augmentation f • q2uniform c) := by rw [q2mul_uniform]
      _ = f + (2 * q2augmentation f) • q2uniform c := by module
  intro g
  have hu := hfu g
  have hf0 := hf g
  have hform : (2 * q2augmentation f) * c =
      (f * (1 + (2 : ℚ_[2]) • q2uniform c)).coeff g - f.coeff g := by
    rw [hid, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, q2uniform_coeff,
      smul_eq_mul]
    ring
  simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, q2uniform_coeff,
    smul_eq_mul]
  rw [hform]
  rw [sub_eq_add_neg]
  apply le_trans (IsUltrametricDist.norm_add_le_max _ _)
  simp only [norm_neg]
  exact max_le hu hf0

/-- Universal coefficientwise `Z₂` clearing forces the advertised lower
bound on the augmentation valuation. Zero augmentation is handled separately,
since the valuation convention sends zero to zero rather than to infinity. -/
theorem q2_binary_clearing_bound {b : ℕ}
    {f : AddMonoidAlgebra ℚ_[2] (BinaryGroup b)}
    (hf : Q2IntegralCoefficients f) (hfu : Q2IntegralCoefficients (f * q2binaryU b)) :
    q2augmentation f = 0 ∨ (b : ℤ) - 1 ≤ (q2augmentation f).valuation := by
  by_cases ha : q2augmentation f = 0
  · exact Or.inl ha
  · right
    have hrem := q2_clearing_integral_remainder (G := BinaryGroup b)
      (Fintype.card (BinaryGroup b) : ℚ_[2])⁻¹ hf hfu 0
    simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply,
      q2uniform_coeff, smul_eq_mul] at hrem
    have hcard : (Fintype.card (BinaryGroup b) : ℚ_[2]) = (2 : ℚ_[2]) ^ b := by
      rw [card_binaryGroup]
      norm_num
    have hcard0 : (Fintype.card (BinaryGroup b) : ℚ_[2]) ≠ 0 := by
      rw [hcard]
      exact pow_ne_zero _ (by norm_num)
    have hr0 : (2 * q2augmentation f) * (Fintype.card (BinaryGroup b) : ℚ_[2])⁻¹ ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) ha) (inv_ne_zero hcard0)
    have hval := (Padic.norm_le_one_iff_val_nonneg _).mp hrem
    rw [Padic.valuation_mul (mul_ne_zero (by norm_num) ha) (inv_ne_zero hcard0),
      Padic.valuation_mul (by norm_num) ha, Padic.valuation_inv, hcard,
      Padic.valuation_pow] at hval
    have hpval : (2 : ℚ_[2]).valuation = 1 := by simpa using (Padic.valuation_p (p := 2))
    rw [hpval] at hval
    omega

/-- Consequently `u_b` itself has a nonintegral group-basis coefficient when
`b ≥ 2`, now in the full `Q₂[(Z/2)^b]` model rather than only over `Q`. -/
theorem q2binaryU_not_integral {b : ℕ} (hb : 2 ≤ b) :
    ¬Q2IntegralCoefficients (q2binaryU b) := by
  intro hu
  have hf : Q2IntegralCoefficients (1 : AddMonoidAlgebra ℚ_[2] (BinaryGroup b)) :=
    q2integral_one
  have hfu : Q2IntegralCoefficients ((1 : AddMonoidAlgebra ℚ_[2] (BinaryGroup b)) * q2binaryU b) := by
    simpa using hu
  rcases q2_binary_clearing_bound hf hfu with ha | hval
  · exact one_ne_zero (q2augmentation_one.symm.trans ha)
  · rw [q2augmentation_one, Padic.valuation_one] at hval
    omega

end SunElliotE364
