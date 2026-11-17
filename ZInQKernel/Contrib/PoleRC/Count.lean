import ZInQKernel.Contrib.PoleRC.QClass

/-!
# The dimension-three count from the local images (`diophantine_zq.tex` lines 1061–1074)

The local images of the Kummer map of `E_ℓ` are stated as five textbook GLUE Props (`LocalReal`,
`LocalTwo`, `LocalThree`, `LocalBad`, `LocalGood`), and `dimThreeCount_of_local` proves the
manuscript's `DimThreeCount` from them: the local conditions of a Selmer class become the
equations of `kmat_forces`, which leave exactly the eight classes
`{1, ℓ, β, ℓ/β} × {(1, 1), (3, −ℓ)}`.
-/

namespace ZInQ.Manuscript.PoleRC

open Matrix

variable {ℓ : ℕ}

open Classical in
/-- The indicator, on the prime support of `ℓ`, of the prime factors of `x`. -/
noncomputable def ind (ℓ : ℕ) (x : ℤ) : Supp ℓ → ZMod 2 :=
  fun i => if (i : ℕ) ∈ x.natAbs.primeFactors then 1 else 0

theorem three_not_mem (h12 : ℓ % 12 = 11) : 3 ∉ ℓ.primeFactors := by
  intro h; have := (Nat.mem_primeFactors.mp h).2.1; omega

open Classical in
/-- **`qcls` at a prime of `ℓ` of a squarefree integer supported on `3` and the primes of `ℓ`.**
`(u_i, δλ_i + σ s_i + Σ_{j ≠ i} K_ij u_j)`, the last sum written `(Ku)_i + K_ii u_i`. -/
theorem qcls_formula (h12 : ℓ % 12 = 11) {x : ℤ} (hx : Squarefree x)
    (hsupp : x.natAbs.primeFactors ⊆ insert 3 ℓ.primeFactors) (i : Supp ℓ) :
    haveI := Fact.mk (supp_prime i)
    qcls i x = (ind ℓ x i, (if 3 ∈ x.natAbs.primeFactors then lam ℓ i else 0) +
      (if x < 0 then sgn ℓ i else 0) + ((Kmat ℓ *ᵥ ind ℓ x) i + Kmat ℓ i i * ind ℓ x i)) := by
  have := Fact.mk (supp_prime i)
  have hi3 : (i : ℕ) ≠ 3 := supp_ne_three (by omega) i
  rw [qcls_eq_sum (i : ℕ) hx]
  have h1 : ∑ p ∈ x.natAbs.primeFactors, qcls i p =
      ∑ p ∈ insert 3 ℓ.primeFactors, (if p ∈ x.natAbs.primeFactors then qcls i p else 0) := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsupp]
  rw [h1, Finset.sum_insert (three_not_mem h12), ← Finset.sum_coe_sort ℓ.primeFactors,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have h3 : qcls i ((3 : ℕ) : ℤ) = (0, lam ℓ i) :=
    qcls_prime_ne (i : ℕ) 3 Nat.prime_three (Ne.symm hi3)
  have hself : qcls i ((i : ℕ) : ℤ) = (1, 0) := qcls_self i
  have hne : ∀ j ∈ (Finset.univ : Finset (Supp ℓ)).erase i,
      (if (j : ℕ) ∈ x.natAbs.primeFactors then qcls i ((j : ℕ) : ℤ) else 0) =
        (0, Kmat ℓ i j * ind ℓ x j) := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hji' : (j : ℕ) ≠ i := fun h => hji (Subtype.ext h)
    rw [qcls_prime_ne (i : ℕ) j (supp_prime j) hji']
    simp only [Kmat, ind, if_neg (Ne.symm hji)]
    split_ifs <;> simp <;> rfl
  rw [Finset.sum_congr rfl hne, h3, hself, qcls_neg_one]
  -- the row sum
  have hrow : (Kmat ℓ *ᵥ ind ℓ x) i + Kmat ℓ i i * ind ℓ x i =
      ∑ j ∈ (Finset.univ : Finset (Supp ℓ)).erase i, Kmat ℓ i j * ind ℓ x j := by
    rw [mulVec, dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_comm,
      ← add_assoc, zmod2_add_self, zero_add]
  rw [hrow]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.fst_sum]
    unfold ind
    split_ifs <;> simp
  · split_ifs <;> simp only [Prod.snd_add, Prod.snd_sum, Prod.snd_zero, sgn, add_zero,
      zero_add] <;> ring

/-! ### The local images of the Kummer map of `E_ℓ` (GLUE, textbook local computations) -/

/-- **Local image at the real place**: for `ℓ > 0`, the class `(a, b)` is in the real Kummer image
iff `a > 0` (real points have `x ≥ ℓ`, giving `a, b > 0`, or `−3ℓ ≤ x ≤ 0`, giving `a > 0 > b`).
Proved in Lean below (`localReal`). -/
def LocalReal : Prop :=
  ∀ (ℓ : ℕ) (a b : ℤ), 0 < ℓ → a ≠ 0 → b ≠ 0 → (LocM ℝ ℓ a b ↔ 0 < a)

/-- **Local image at `2`** (GLUE, textbook): for squarefree `ℓ ≡ 3 (mod 4)` and squarefree
`a, b`, the class `(a, b)` is in the Kummer image of `E_ℓ(ℚ₂)` iff `a, b` are odd and
`b ≡ 1 (mod 4)`. The image has `8 = 2 · #E_ℓ(ℚ₂)[2]` elements. Checked numerically
(`scratch/pc-from-rc/local2.py`, `localprops.py`); not proved in Lean. -/
def LocalTwo : Prop :=
  ∀ (ℓ : ℕ) (a b : ℤ), Squarefree ℓ → ℓ % 4 = 3 → Squarefree a → Squarefree b →
    (LocM ℚ_[2] ℓ a b ↔ a % 2 = 1 ∧ b % 4 = 1)

/-- **Local image at `3`** (GLUE, textbook): for squarefree `ℓ ≡ 2 (mod 3)` (split multiplicative
reduction at `3`), the class `(a, b)` is in the Kummer image of `E_ℓ(ℚ₃)` iff `b ≡ 1 (mod 3)`; the
image is spanned by the torsion classes `(ℓ, 1)`, `(3, −ℓ)`. Checked numerically; not proved in
Lean. -/
def LocalThree : Prop :=
  ∀ (ℓ : ℕ) (a b : ℤ), Squarefree ℓ → ℓ % 3 = 2 → Squarefree a → Squarefree b →
    (LocM ℚ_[3] ℓ a b ↔ b % 3 = 1)

/-- **Local image at a prime `q ∣ ℓ`, `q ≠ 2, 3`** (GLUE, textbook): `E_ℓ` is the quadratic twist
by `ℓ` of a curve with good reduction at `q`, so it has reduction type `I₀*` there, and the
Kummer image of `E_ℓ(ℚ_q)` is spanned by the images `(ℓ, 1)`, `(3, −ℓ)` of the two-torsion
points. In square classes at `q` (`qcls`): `(a, b) = e₁ (ℓ, 1) + e₂ (3, −ℓ)`. Checked numerically;
not proved in Lean. -/
def LocalBad : Prop :=
  ∀ (ℓ q : ℕ) [Fact q.Prime] (a b : ℤ), Squarefree ℓ → q ∣ ℓ → q ≠ 2 → q ≠ 3 →
    Squarefree a → Squarefree b →
    (LocM ℚ_[q] ℓ a b ↔ ∃ e₁ e₂ : ZMod 2,
      qcls q a = e₁ • qcls q ℓ + e₂ • qcls q 3 ∧ qcls q b = e₂ • qcls q (-(ℓ : ℤ)))

/-- **Local image at a prime of good reduction** (GLUE, textbook; Silverman X.4): for `p ∤ 6ℓ`, the
Kummer image of `E_ℓ(ℚ_p)` is the unramified classes: `p ∤ a` and `p ∤ b`. Checked numerically;
not proved in Lean. -/
def LocalGood : Prop :=
  ∀ (ℓ p : ℕ) [Fact p.Prime] (a b : ℤ), Squarefree ℓ → ¬ p ∣ 6 * ℓ →
    Squarefree a → Squarefree b → (LocM ℚ_[p] ℓ a b ↔ ¬ (p : ℤ) ∣ a ∧ ¬ (p : ℤ) ∣ b)

theorem isSquare_real_of_nonneg {r : ℝ} (h : 0 ≤ r) : IsSquare r :=
  ⟨Real.sqrt r, (Real.mul_self_sqrt h).symm⟩

/-- **`LocalReal` holds.** -/
theorem localReal : LocalReal := by
  intro ℓ a b hℓ ha hb
  have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  constructor
  · rintro (⟨h1, -⟩ | ⟨x, h1, h2, h3⟩)
    · have : (0 : ℝ) ≤ a := h1.nonneg
      have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
      exact_mod_cast lt_of_le_of_ne this (Ne.symm ha')
    · by_contra hneg
      have ha' : (a : ℝ) < 0 := by
        have : a < 0 := lt_of_le_of_ne (not_lt.mp hneg) ha
        exact_mod_cast this
      have e1 := h1.nonneg
      have hx : x + 3 * ℓ ≤ 0 := by
        by_contra hc
        push Not at hc
        have : (x + 3 * ℓ) / (a : ℝ) < 0 := div_neg_of_pos_of_neg hc ha'
        linarith
      have e2 := h2.nonneg
      have hb' : (b : ℝ) < 0 := by
        rcases lt_or_gt_of_ne (show (b : ℝ) ≠ 0 by exact_mod_cast hb) with h | h
        · exact h
        · have : (x - ℓ) / (b : ℝ) < 0 := div_neg_of_neg_of_pos (by linarith) h
          linarith
      have e3 := h3.nonneg
      have : x / ((a : ℝ) * b) < 0 := div_neg_of_neg_of_pos (by linarith) (mul_pos_of_neg_of_neg ha' hb')
      linarith
  · intro ha0
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha0
    rcases lt_or_gt_of_ne (show (b : ℝ) ≠ 0 by exact_mod_cast hb) with hb' | hb'
    · right
      refine ⟨-ℓ, isSquare_real_of_nonneg ?_, isSquare_real_of_nonneg ?_,
        isSquare_real_of_nonneg ?_⟩
      · exact div_nonneg (by linarith) ha'.le
      · exact div_nonneg_of_nonpos (by linarith) hb'.le
      · exact div_nonneg_of_nonpos (by linarith) (mul_neg_of_pos_of_neg ha' hb').le
    · left
      exact ⟨isSquare_real_of_nonneg ha'.le, isSquare_real_of_nonneg hb'.le⟩

end ZInQ.Manuscript.PoleRC
