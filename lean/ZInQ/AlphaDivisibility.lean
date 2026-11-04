/- Copyright (c) 2026. -/
module

public import ZInQ.AlphaAddition

/-!
# Divisibility of the integer alpha recurrence

The index-divisibility statement of AFP `divisibility_alpha`, using the
addition identity and Cassini identity for the literal integer recurrence.
-/

public section

namespace ZInQ.AlphaPower

/-- Removing one positive index period preserves divisibility. -/
private theorem alphaZ_dvd_add_index_iff (B k n : Nat) (hk : 0 < k) :
    alphaZ B k ∣ alphaZ B (k + n) ↔ alphaZ B k ∣ alphaZ B n := by
  cases k with
  | zero => omega
  | succ j =>
    have ha : alphaZ B (Nat.succ j + n) =
        alphaZ B (j + 1) * alphaZ B (n + 1) - alphaZ B j * alphaZ B n := by
      rw [show Nat.succ j + n = j + n + 1 by omega]
      exact alphaZ_add_succ B j n
    rw [ha]
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨(alphaZ B (j + 1) - (B : Int) * alphaZ B j) * alphaZ B n +
        alphaZ B j * (alphaZ B (n + 1) - q), ?_⟩
      have hc := alphaZ_cassini B j
      linear_combination -(alphaZ B n) * hc - (alphaZ B j) * hq
    · rintro ⟨q, hq⟩
      refine ⟨alphaZ B (n + 1) - alphaZ B j * q, ?_⟩
      rw [hq]
      ring

/-- Alpha divisibility is exactly divisibility of natural indices. -/
theorem alphaZ_dvd_iff (B k m : Nat) (hB : 2 < B) (hk : 0 < k) :
    alphaZ B k ∣ alphaZ B m ↔ k ∣ m := by
  have hB2 : 2 ≤ B := Nat.le_of_lt hB
  have hmono : StrictMono (alphaZ B) :=
    strictMono_nat_of_lt_succ (fun n => alphaZ_succ_strict B n hB2)
  have hforward : ∀ n : Nat, alphaZ B k ∣ alphaZ B n → k ∣ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hdiv
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact dvd_zero k
      · by_cases hnk : n < k
        · have hnInt : (0 : Int) < (n : Int) := by exact_mod_cast hn
          have hpos : 0 < alphaZ B n :=
            lt_of_lt_of_le hnInt (alphaZ_ge_index B n hB2)
          exact (not_le_of_gt (hmono hnk) (Int.le_of_dvd hpos hdiv)).elim
        · have hsmall : n - k < n := by omega
          have hsum : k + (n - k) = n := by omega
          have hred : alphaZ B k ∣ alphaZ B (n - k) := by
            apply (alphaZ_dvd_add_index_iff B k (n - k) hk).mp
            simpa only [hsum] using hdiv
          have hdvd : k ∣ k + (n - k) :=
            dvd_add (dvd_refl k) (ih (n - k) hsmall hred)
          simpa only [hsum] using hdvd
  constructor
  · exact hforward m
  · rintro ⟨q, rfl⟩
    induction q with
    | zero => simpa only [Nat.mul_zero, alphaZ_zero] using (dvd_zero (alphaZ B k))
    | succ q ih =>
      have h : alphaZ B k ∣ alphaZ B (k + k * q) :=
        (alphaZ_dvd_add_index_iff B k (k * q) hk).mpr ih
      simpa only [Nat.mul_succ, Nat.add_comm k (k * q)] using h

end ZInQ.AlphaPower
