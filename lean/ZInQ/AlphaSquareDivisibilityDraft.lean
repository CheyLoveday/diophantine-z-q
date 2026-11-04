module

public import ZInQ.AlphaDivisibility
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Square divisibility for the integer alpha recurrence

Internal arithmetic helpers corresponding to AFP `div_coprime`,
`divisibility_congruence` and `divisibility_alpha2` (Exponentiation.thy,
lines 430-684), stated for the literal integer recurrence `alphaZ`.
The ordinary index divisibility `alphaZ_dvd_iff` is the supplied interface
from `ZInQ.AlphaDivisibility` and is used, not reproved.
These results do not establish the full alpha or power encoding.
-/

public section

namespace ZInQ.AlphaPower

/-- Consecutive values of the integer alpha recurrence are coprime (AFP `div_coprime`,
without the extraneous free `n ≥ 0`). The Bezout witnesses come from the supplied
Cassini identity, which holds for every natural `B`; the bound `2 < B` is not needed. -/
theorem alphaZ_consecutive_coprime (B k : Nat) (hB : 2 < B) :
    IsCoprime (alphaZ B k) (alphaZ B (k + 1)) := by
  clear hB
  refine ⟨alphaZ B k - (B : Int) * alphaZ B (k + 1), alphaZ B (k + 1), ?_⟩
  linear_combination alphaZ_cassini B k

/-- Joint congruences along the multiples of a positive index `j + 1`, writing
`e = alphaZ B (j + 1)` and `f = alphaZ B j`:
`e ∣ alphaZ B ((j + 1) * l + 1) - (-f) ^ l` and
`e ^ 2 ∣ alphaZ B ((j + 1) * (l + 1)) - (l + 1) * e * (-f) ^ l`.
Only the literal recurrence (via `alphaZ_add_succ`) is used, for every natural `B`. -/
private theorem alphaZ_multiple_congr (B j l : Nat) :
    alphaZ B (j + 1) ∣ alphaZ B ((j + 1) * l + 1) - (-alphaZ B j) ^ l ∧
      alphaZ B (j + 1) ^ 2 ∣ alphaZ B ((j + 1) * (l + 1)) -
        ((l : Int) + 1) * alphaZ B (j + 1) * (-alphaZ B j) ^ l := by
  induction l with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [alphaZ_one]
    · simp
  | succ l ih =>
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ih
    have hy : alphaZ B ((j + 1) * (l + 1) + 1) =
        alphaZ B ((j + 1) * l + 1) * alphaZ B (j + 2) -
          alphaZ B ((j + 1) * l) * alphaZ B (j + 1) := by
      have h := alphaZ_add_succ B ((j + 1) * l) (j + 1)
      rw [show (j + 1) * l + (j + 1) + 1 = (j + 1) * (l + 1) + 1 by ring] at h
      exact h
    have hx : alphaZ B ((j + 1) * (l + 1 + 1)) =
        alphaZ B ((j + 1) * (l + 1) + 1) * alphaZ B (j + 1) -
          alphaZ B ((j + 1) * (l + 1)) * alphaZ B j := by
      have h := alphaZ_add_succ B ((j + 1) * (l + 1)) j
      rw [show (j + 1) * (l + 1) + j + 1 = (j + 1) * (l + 1 + 1) by ring] at h
      exact h
    have hg : alphaZ B (j + 2) = (B : Int) * alphaZ B (j + 1) - alphaZ B j :=
      alphaZ_add_two B j
    have hy' : alphaZ B (j + 1) ∣
        alphaZ B ((j + 1) * (l + 1) + 1) - (-alphaZ B j) ^ (l + 1) := by
      refine ⟨alphaZ B (j + 2) * a + (B : Int) * (-alphaZ B j) ^ l -
        alphaZ B ((j + 1) * l), ?_⟩
      rw [pow_succ (-alphaZ B j) l]
      linear_combination hy + alphaZ B (j + 2) * ha + (-alphaZ B j) ^ l * hg
    refine ⟨hy', ?_⟩
    obtain ⟨c, hc⟩ := hy'
    refine ⟨c - alphaZ B j * b, ?_⟩
    rw [pow_succ (-alphaZ B j) l] at hc ⊢
    rw [Nat.cast_add_one]
    linear_combination hx + alphaZ B (j + 1) * hc - alphaZ B j * hb

/-- AFP `divisibility_congruence`: the square-modulus congruence along multiples
`m = k * l` with `0 < m`. The congruence itself holds for every natural `B`. -/
theorem alphaZ_multiple_square_mod (B k l m : Nat)
    (hmkl : m = k * l) (hB : 2 < B) (hm : 0 < m) :
    alphaZ B m % (alphaZ B k) ^ 2 =
      ((-1 : Int) ^ (l - 1) * (l : Int) * alphaZ B k *
        (alphaZ B (k - 1)) ^ (l - 1)) % (alphaZ B k) ^ 2 := by
  clear hB
  have hkl : 0 < k * l := by rw [← hmkl]; exact hm
  have hk : k ≠ 0 := fun h => by simp [h] at hkl
  have hl : l ≠ 0 := fun h => by simp [h] at hkl
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
  subst hmkl
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
  obtain ⟨c, hc⟩ := (alphaZ_multiple_congr B j n).2
  refine Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd ⟨c, ?_⟩)
  rw [neg_pow] at hc
  rw [Nat.cast_add_one]
  linear_combination hc

/-- AFP `divisibility_alpha2`: for `2 < B` and `0 < m`, the square of `alphaZ B k` divides
`alphaZ B m` exactly when `k * alphaZ B k` divides `m` (in `Int`). The case `k = 0` is
included: then both sides are false. -/
theorem alphaZ_sq_dvd_iff (B k m : Nat) (hB : 2 < B) (hm : 0 < m) :
    ((alphaZ B k) ^ 2 ∣ alphaZ B m) ↔ ((k : Int) * alphaZ B k ∣ (m : Int)) := by
  have hB2 : 2 ≤ B := Nat.le_of_lt hB
  have hmpos : (0 : Int) < alphaZ B m :=
    lt_of_lt_of_le (by exact_mod_cast hm) (alphaZ_ge_index B m hB2)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`: `alphaZ B 0 = 0`, and neither `alphaZ B m` nor `m` is zero.
    rw [alphaZ_zero]
    constructor
    · intro h
      have h0 : alphaZ B m = 0 := by simpa using h
      omega
    · intro h
      have h0 : (m : Int) = 0 := by simpa using h
      omega
  · have hk0 : (k : Int) ≠ 0 := by exact_mod_cast hk.ne'
    have hepos : (0 : Int) < alphaZ B k :=
      lt_of_lt_of_le (by exact_mod_cast hk) (alphaZ_ge_index B k hB2)
    have he0 : alphaZ B k ≠ 0 := hepos.ne'
    have hcop : IsCoprime (alphaZ B k) (alphaZ B (k - 1)) := by
      have h := alphaZ_consecutive_coprime B (k - 1) hB
      rw [show k - 1 + 1 = k by omega] at h
      exact h.symm
    constructor
    · intro hP
      -- The supplied ordinary divisibility gives `k ∣ m`.
      obtain ⟨l, hl⟩ : k ∣ m :=
        (alphaZ_dvd_iff B k m hB hk).mp (dvd_trans (dvd_pow_self _ two_ne_zero) hP)
      have hcong := alphaZ_multiple_square_mod B k l m hl hB hm
      have hX : (alphaZ B k) ^ 2 ∣ (-1 : Int) ^ (l - 1) * (l : Int) * alphaZ B k *
          (alphaZ B (k - 1)) ^ (l - 1) := by
        rw [Int.dvd_iff_emod_eq_zero, ← hcong, ← Int.dvd_iff_emod_eq_zero]
        exact hP
      have hX' : alphaZ B k ∣
          (-1 : Int) ^ (l - 1) * ((l : Int) * (alphaZ B (k - 1)) ^ (l - 1)) := by
        obtain ⟨d, hd⟩ := hX
        refine ⟨d, ?_⟩
        apply mul_left_cancel₀ he0
        linear_combination hd
      have hunit : IsCoprime (alphaZ B k) ((-1 : Int) ^ (l - 1)) :=
        (isCoprime_one_right.neg_right).pow_right
      have h1 : alphaZ B k ∣ (l : Int) * (alphaZ B (k - 1)) ^ (l - 1) :=
        hunit.dvd_of_dvd_mul_left hX'
      have h2 : alphaZ B k ∣ (l : Int) :=
        hcop.pow_right.dvd_of_dvd_mul_right h1
      rw [hl, Nat.cast_mul]
      exact mul_dvd_mul_left (k : Int) h2
    · intro hQ
      obtain ⟨l, hl⟩ : k ∣ m :=
        Int.natCast_dvd_natCast.mp (dvd_trans (dvd_mul_right _ _) hQ)
      have hcong := alphaZ_multiple_square_mod B k l m hl hB hm
      have hel : alphaZ B k ∣ (l : Int) := by
        rw [hl, Nat.cast_mul] at hQ
        exact (mul_dvd_mul_iff_left hk0).mp hQ
      rw [Int.dvd_iff_emod_eq_zero, hcong, ← Int.dvd_iff_emod_eq_zero]
      obtain ⟨c, hc⟩ := hel
      exact ⟨(-1 : Int) ^ (l - 1) * c * (alphaZ B (k - 1)) ^ (l - 1), by rw [hc]; ring⟩

end ZInQ.AlphaPower
