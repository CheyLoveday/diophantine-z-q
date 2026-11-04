module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Arithmetic of the smoothing integer

The choice `1 + 2^e * 3 * n * f` is the integer used for both
smoothing parameters in section 2 of the Kato compatibility audit.
-/

public section

namespace ZInQ

/-- The explicit choice for both smoothing integers. -/
@[expose] def smoothingInteger (e n f : ℕ) : ℕ := 1 + 2 ^ e * 3 * n * f

@[simp] theorem smoothing_integer_sub_one (e n f : ℕ) :
    smoothingInteger e n f - 1 = 2 ^ e * 3 * n * f := by
  simp only [smoothingInteger, Nat.add_sub_cancel_left]

theorem smoothing_integer_gt_one (e n f : ℕ) (hn : 0 < n) (hf : 0 < f) :
    1 < smoothingInteger e n f := by
  have hp : 0 < 2 ^ e * 3 * n * f := by positivity
  simp only [smoothingInteger]
  omega

theorem two_pow_dvd_smoothing_integer_sub_one (e n f : ℕ) :
    2 ^ e ∣ smoothingInteger e n f - 1 := by
  rw [smoothing_integer_sub_one]
  exact ⟨3 * n * f, by ring⟩

theorem auxiliary_dvd_smoothing_integer_sub_one (e n f : ℕ) :
    f ∣ smoothingInteger e n f - 1 := by
  rw [smoothing_integer_sub_one]
  exact ⟨2 ^ e * 3 * n, by ring⟩

theorem conductor_dvd_smoothing_integer_sub_one (a e n f : ℕ) (hae : a ≤ e) :
    2 ^ a * n ∣ smoothingInteger e n f - 1 := by
  rw [smoothing_integer_sub_one]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hae
  refine ⟨2 ^ k * 3 * f, ?_⟩
  rw [hk, pow_add]
  ring

private theorem not_two_pow_succ_dvd_mul_of_odd (e m : ℕ) (hm : Odd m) :
    ¬2 ^ (e + 1) ∣ 2 ^ e * m := by
  rintro ⟨k, hk⟩
  have heq : m = 2 * k :=
    mul_left_cancel₀ (by positivity : (2 : ℕ) ^ e ≠ 0)
      (by simpa only [pow_succ, mul_assoc] using hk)
  rcases hm with ⟨j, hj⟩
  omega

/-- The exact power of two dividing `c - 1`, including the case `e = 0`. -/
theorem not_two_pow_succ_dvd_smoothing_integer_sub_one
    (e n f : ℕ) (hn : Odd n) (hf : Odd f) :
    ¬2 ^ (e + 1) ∣ smoothingInteger e n f - 1 := by
  rw [smoothing_integer_sub_one]
  simpa only [mul_assoc] using
    not_two_pow_succ_dvd_mul_of_odd e (3 * n * f)
      (((by decide : Odd (3 : ℕ)).mul hn).mul hf)

theorem odd_smoothing_integer (e n f : ℕ) (he : 1 ≤ e) :
    Odd (smoothingInteger e n f) := by
  cases e with
  | zero => omega
  | succ k =>
      refine ⟨2 ^ k * 3 * n * f, ?_⟩
      simp only [smoothingInteger, pow_succ]
      ring

theorem smoothing_integer_mod_two_pow_succ
    (e n f : ℕ) (he : 1 ≤ e) (hn : Odd n) (hf : Odd f) :
    smoothingInteger e n f % 2 ^ (e + 1) = 1 + 2 ^ e := by
  have hm : Odd (3 * n * f) :=
    ((by decide : Odd (3 : ℕ)).mul hn).mul hf
  obtain ⟨k, hk⟩ := hm
  have hc : smoothingInteger e n f =
      2 ^ (e + 1) * k + (1 + 2 ^ e) := by
    calc
      smoothingInteger e n f = 1 + 2 ^ e * (3 * n * f) := by
        simp only [smoothingInteger]
        ring
      _ = 2 ^ (e + 1) * k + (1 + 2 ^ e) := by
        rw [hk, pow_succ]
        ring
  have hp : 1 < (2 : ℕ) ^ e := by
    cases e with
    | zero => omega
    | succ j =>
        have hj : 0 < (2 : ℕ) ^ j := by positivity
        simp only [pow_succ]
        omega
  have hlt : 1 + 2 ^ e < 2 ^ (e + 1) := by
    rw [pow_succ]
    omega
  rw [hc]
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod,
    Nat.zero_add, Nat.mod_eq_of_lt hlt]

/-- Coprimality needs no parity assumptions on `n` or `f`. -/
theorem smoothing_integer_coprime (a e n f : ℕ) (he : 1 ≤ e) :
    (smoothingInteger e n f).Coprime (6 * (2 ^ a * n) * f) := by
  have hb : (smoothingInteger e n f).Coprime (3 * n * f) := by
    have hc : smoothingInteger e n f = 1 + 2 ^ e * (3 * n * f) := by
      simp only [smoothingInteger]
      ring
    rw [hc]
    exact (Nat.coprime_add_mul_right_left 1 (3 * n * f) (2 ^ e)).2
      (Nat.coprime_one_left _)
  have htwo : (smoothingInteger e n f).Coprime 2 :=
    (odd_smoothing_integer e n f he).coprime_two_right
  have hfac : 6 * (2 ^ a * n) * f = 2 ^ (a + 1) * (3 * n * f) := by
    rw [pow_succ]
    ring
  rw [hfac]
  exact (htwo.pow_right (a + 1)).mul_right hb

/-- Exact two-adic depth of the central smoothing factor with equal parameters. -/
theorem smoothing_square_exact_two_depth
    (e n f : ℕ) (he : 1 ≤ e) (hn : Odd n) (hf : Odd f) :
    2 ^ (2 * e) ∣ (smoothingInteger e n f * (smoothingInteger e n f - 1)) ^ 2 ∧
      ¬2 ^ (2 * e + 1) ∣
        (smoothingInteger e n f * (smoothingInteger e n f - 1)) ^ 2 := by
  let m := smoothingInteger e n f * 3 * n * f
  have hm : Odd m :=
    (((odd_smoothing_integer e n f he).mul (by decide : Odd (3 : ℕ))).mul hn).mul hf
  have hfac :
      (smoothingInteger e n f * (smoothingInteger e n f - 1)) ^ 2 =
        2 ^ (2 * e) * m ^ 2 := by
    calc
      (smoothingInteger e n f * (smoothingInteger e n f - 1)) ^ 2 =
          (2 ^ e * m) ^ 2 := by
        rw [smoothing_integer_sub_one]
        dsimp [m]
        ring
      _ = 2 ^ (2 * e) * m ^ 2 := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm e 2]
  constructor
  · exact ⟨m ^ 2, hfac⟩
  · rw [hfac]
    exact not_two_pow_succ_dvd_mul_of_odd (2 * e) (m ^ 2) hm.pow

/-- The same exact depth stated using natural-number multiplicity. -/
theorem smoothing_square_multiplicity_two
    (e n f : ℕ) (he : 1 ≤ e) (hn : Odd n) (hf : Odd f) :
    multiplicity (2 : ℕ)
      ((smoothingInteger e n f * (smoothingInteger e n f - 1)) ^ 2) = 2 * e := by
  let x := (smoothingInteger e n f * (smoothingInteger e n f - 1)) ^ 2
  have hd : 2 ^ (2 * e) ∣ x ∧ ¬2 ^ (2 * e + 1) ∣ x :=
    smoothing_square_exact_two_depth e n f he hn hf
  have hx : x ≠ 0 := by
    intro h
    apply hd.2
    rw [h]
    exact dvd_zero _
  have hfin : FiniteMultiplicity (2 : ℕ) x :=
    Nat.finiteMultiplicity_iff.mpr ⟨by decide, Nat.pos_of_ne_zero hx⟩
  have hlo : 2 * e ≤ multiplicity (2 : ℕ) x :=
    hfin.pow_dvd_iff_le_multiplicity.mp hd.1
  have hhi : ¬2 * e + 1 ≤ multiplicity (2 : ℕ) x := by
    intro h
    exact hd.2 (hfin.pow_dvd_iff_le_multiplicity.mpr h)
  dsimp only [x] at hlo hhi
  omega

end ZInQ

