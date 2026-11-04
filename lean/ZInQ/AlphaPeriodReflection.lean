module

public import ZInQ.AlphaCompanionPeriod

/-!
# Period and reflection congruences for the alpha recurrence

AFP `Exponentiation.thy` lemmas `361` (general `l`) and `362`, written as divisibility over
`Int`. The modulus is `alphaZ B (m + 1) - alphaZ B (m - 1)`, where `m - 1` is natural
subtraction (so for `m = 0` the modulus is `alphaZ B 1 - alphaZ B 0 = 1`). All indices are
natural numbers; `2 * l * m - j` is natural subtraction, genuine under `j < 2 * l * m`.

* `companion_dvd_alphaZ_add_period`: AFP `361`,
  `alphaZ (j + 2lm) ≡ (-1)^l * alphaZ j`, by induction on `l` from the accepted `l = 1`
  period `companion_dvd_alphaZ_add_two_mul`.
* `companion_dvd_alphaZ_reflection`: AFP `362`,
  `alphaZ (2lm - j) ≡ -((-1)^l * alphaZ j)` for `0 < j < 2lm`, following the source steps:
  with `Y = A(m)^(2l) = A(2lm)` and `Z = A_inv j`, the `(2,1)` entry of `Y * Z` is
  `c * e + d * g` with `c = alphaZ (2lm) ≡ 0`, `d = -alphaZ (2lm - 1) ≡ (-1)^l`,
  `e = -alphaZ (j - 1)` and `g = -alphaZ j` (the reflected sign).

These are internal helpers. They do not establish AFP `3.36`, the full alpha encoding, or the
correctness of any power compiler.
-/

public section

namespace ZInQ.AlphaPower

/-- Reflected `(2,1)` entry, index-shifted (`N = k + i + 1`, `j = i + 1`):
`alphaZ N * (-alphaZ (j - 1)) + (-alphaZ (N - 1)) * (-alphaZ j) = alphaZ (N - j)`.
Proved by induction on `i` from the literal recurrence. -/
private theorem alphaZ_reflect_entry (B k i : Nat) :
    alphaZ B (k + i + 1) * (-alphaZ B i) + (-alphaZ B (k + i)) * (-alphaZ B (i + 1)) =
      alphaZ B k := by
  induction i with
  | zero =>
      show alphaZ B (k + 1) * (-alphaZ B 0) + (-alphaZ B k) * (-alphaZ B 1) = alphaZ B k
      rw [alphaZ_zero, alphaZ_one]
      ring
  | succ i ih =>
      show alphaZ B (k + i + 2) * (-alphaZ B (i + 1)) +
          (-alphaZ B (k + i + 1)) * (-alphaZ B (i + 2)) = alphaZ B k
      rw [alphaZ_add_two B (k + i), alphaZ_add_two B i]
      linear_combination ih

/-- AFP `362`, steps `S4`–`S6`, with natural subtraction: for `0 < j ≤ N`, `alphaZ (N - j)` is
the `(2,1)` entry of `A N * A_inv j`, namely `c * e + d * g` with `c = alphaZ N`,
`e = -alphaZ (j - 1)`, `d = -alphaZ (N - 1)` and `g = -alphaZ j`. -/
private theorem alphaZ_sub_eq_entry (B N j : Nat) (hj : 0 < j) (hjN : j ≤ N) :
    alphaZ B (N - j) =
      alphaZ B N * (-alphaZ B (j - 1)) + (-alphaZ B (N - 1)) * (-alphaZ B j) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, N = k + i + 1 := ⟨N - (i + 1), by omega⟩
  rw [show k + i + 1 - (i + 1) = k by omega, show i + 1 - 1 = i by omega,
    show k + i + 1 - 1 = k + i by omega]
  exact (alphaZ_reflect_entry B k i).symm

/-- AFP `361` as divisibility: `alphaZ (j + 2lm) ≡ (-1)^l * alphaZ j` modulo
`alphaZ (m + 1) - alphaZ (m - 1)`, for all natural `m j l` (including `l = 0` and `m = 0`). -/
theorem companion_dvd_alphaZ_add_period (B m j l : Nat) (hB : 2 < B) :
    (alphaZ B (m + 1) - alphaZ B (m - 1)) ∣
      alphaZ B (j + 2 * l * m) - (-1 : Int) ^ l * alphaZ B j := by
  induction l with
  | zero => simp
  | succ l ih =>
      -- one more application of the accepted `l = 1` period at index `j + 2lm`
      have hstep := companion_dvd_alphaZ_add_two_mul B m (j + 2 * l * m) hB
      have hidx : j + 2 * (l + 1) * m = j + 2 * l * m + 2 * m := by ring
      rw [hidx]
      have hsplit :
          alphaZ B (j + 2 * l * m + 2 * m) - (-1 : Int) ^ (l + 1) * alphaZ B j =
            (alphaZ B (j + 2 * l * m + 2 * m) + alphaZ B (j + 2 * l * m)) -
              (alphaZ B (j + 2 * l * m) - (-1 : Int) ^ l * alphaZ B j) := by
        ring
      rw [hsplit]
      exact dvd_sub hstep ih

/-- AFP `362` as divisibility: for `0 < j < 2lm`,
`alphaZ (2lm - j) ≡ -((-1)^l * alphaZ j)` modulo `alphaZ (m + 1) - alphaZ (m - 1)`. -/
theorem companion_dvd_alphaZ_reflection (B m j l : Nat) (hB : 2 < B)
    (hj : 0 < j) (hjlt : j < 2 * l * m) :
    (alphaZ B (m + 1) - alphaZ B (m - 1)) ∣
      alphaZ B (2 * l * m - j) + (-1 : Int) ^ l * alphaZ B j := by
  -- S3: `c = mat_21 Y = alphaZ (2lm) ≡ 0`, the period at `j = 0`
  have hc : (alphaZ B (m + 1) - alphaZ B (m - 1)) ∣ alphaZ B (2 * l * m) := by
    have h := companion_dvd_alphaZ_add_period B m 0 l hB
    rwa [Nat.zero_add, alphaZ_zero, mul_zero, sub_zero] at h
  -- S0/S2: `d = mat_22 Y = -alphaZ (2lm - 1) ≡ (-1)^l`, the period at `j = 1` plus the
  -- recurrence `alphaZ (2lm + 1) = B * alphaZ (2lm) - alphaZ (2lm - 1)` (uses `0 < 2lm`)
  have hd : (alphaZ B (m + 1) - alphaZ B (m - 1)) ∣
      -alphaZ B (2 * l * m - 1) - (-1 : Int) ^ l := by
    have h := companion_dvd_alphaZ_add_period B m 1 l hB
    have hrec : alphaZ B (1 + 2 * l * m) =
        (B : Int) * alphaZ B (2 * l * m) - alphaZ B (2 * l * m - 1) := by
      obtain ⟨t, ht⟩ : ∃ t, 2 * l * m = t + 1 := ⟨2 * l * m - 1, by omega⟩
      rw [ht, show 1 + (t + 1) = t + 2 by omega, show t + 1 - 1 = t by omega, alphaZ_add_two]
    rw [hrec, alphaZ_one, mul_one] at h
    have hsplit : -alphaZ B (2 * l * m - 1) - (-1 : Int) ^ l =
        ((B : Int) * alphaZ B (2 * l * m) - alphaZ B (2 * l * m - 1) - (-1 : Int) ^ l) -
          (B : Int) * alphaZ B (2 * l * m) := by
      ring
    rw [hsplit]
    exact dvd_sub h (dvd_mul_of_dvd_right hc _)
  -- S4–S6: `alphaZ (2lm - j) = mat_21 (Y * A_inv j) = c * e + d * g`, with `g = -alphaZ j`
  have hX := alphaZ_sub_eq_entry B (2 * l * m) j hj hjlt.le
  rw [hX]
  -- S1 and conclusion: `c * e + d * g + (-1)^l * alphaZ j = c * e + (d - (-1)^l) * g`
  have hsplit :
      alphaZ B (2 * l * m) * (-alphaZ B (j - 1)) +
          (-alphaZ B (2 * l * m - 1)) * (-alphaZ B j) + (-1 : Int) ^ l * alphaZ B j =
        alphaZ B (2 * l * m) * (-alphaZ B (j - 1)) +
          (-alphaZ B (2 * l * m - 1) - (-1 : Int) ^ l) * (-alphaZ B j) := by
    ring
  rw [hsplit]
  exact dvd_add (dvd_mul_of_dvd_left hc _) (dvd_mul_of_dvd_left hd _)

end ZInQ.AlphaPower
