module

public import Mathlib.Data.Nat.Basic

/-!
Literal triangular Cantor pairing and the actual remainder-decreasing decoder
of specialize-precision.js. No theorem about this decoder is assumed here.
-/

public section

namespace ZInQ.CantorDecoder

/-- The exact pairing used by the precision specialization. -/
@[expose] def pair (a b : Nat) : Nat :=
  (a + b) * (a + b + 1) / 2 + b

/-- The actual loop: take a step exactly when the current sum is below the remainder. -/
@[expose] def loop (s r : Nat) : Nat × Nat :=
  if h : s < r then
    loop (s + 1) (r - (s + 1))
  else
    (s - r, r)
termination_by r
decreasing_by
  exact Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le s) h) (Nat.succ_pos s)

/-- Start the source loop with sum zero and the input as its remainder. -/
@[expose] def decode (x : Nat) : Nat × Nat := loop 0 x

/-- The right-nested four-pair encoding of the five input registers. -/
@[expose] def encode5 (a b c d e : Nat) : Nat :=
  pair a (pair b (pair c (pair d e)))

/-- The four actual decoder calls, in source order; the last tail is the fifth output. -/
@[expose] def decode5 (x : Nat) : Nat × Nat × Nat × Nat × Nat :=
  let first := decode x
  let second := decode first.2
  let third := decode second.2
  let fourth := decode third.2
  (first.1, second.1, third.1, fourth.1, fourth.2)



/-!
Proofs of the six Cantor decoder targets from the frozen definitions in
`CantorDecoderDefinitions`. No definition is modified; the proofs work with the
literal pairing `pair`, the well-founded remainder loop `loop` (unfolded through
its own equation lemma), and the source-ordered `decode5`.

No import beyond the frozen definitions module is used, so the target
statements elaborate in exactly the environment of the definitions.
-/

/-! ### Triangular-number helpers, `T(s) = s(s+1)/2` -/

/-- `(n+1)(n+2) = n(n+1) + 2(n+1)`. -/
theorem succ_mul_succ_succ (n : Nat) :
    (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by
  rw [Nat.mul_comm (n + 1) (n + 1 + 1)]
  exact Nat.add_mul n 2 (n + 1)

/-- Consecutive factors have an even product. -/
theorem two_dvd_mul_succ (n : Nat) : 2 ∣ n * (n + 1) := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    rw [succ_mul_succ_succ]
    exact Nat.dvd_add ih (Nat.dvd_mul_right 2 (k + 1))

/-- Halving `n(n+1)` loses nothing. -/
theorem two_mul_tri (n : Nat) : 2 * (n * (n + 1) / 2) = n * (n + 1) :=
  Nat.mul_div_cancel' (two_dvd_mul_succ n)

/-- `T(s+1) = T(s) + (s+1)`. -/
theorem tri_succ (s : Nat) :
    (s + 1) * (s + 1 + 1) / 2 = s * (s + 1) / 2 + (s + 1) := by
  rw [succ_mul_succ_succ]
  omega

/-- `T` is monotone. -/
theorem tri_mono {m n : Nat} (h : m ≤ n) : m * (m + 1) / 2 ≤ n * (n + 1) / 2 := by
  have hmul : m * (m + 1) ≤ n * (n + 1) := Nat.mul_le_mul h (Nat.add_le_add_right h 1)
  omega

/-- The pairing with the division by two eliminated exactly. -/
theorem two_mul_pair (a b : Nat) :
    2 * pair a b = (a + b) * (a + b + 1) + 2 * b := by
  unfold pair
  rw [Nat.mul_add, two_mul_tri]

/-! ### The loop invariant -/

/-- The invariant `pair (loop s r) = T(s) + r`, for every state `(s, r)`,
by strong induction on the remainder `r` (the loop's termination measure). -/
theorem pair_loop (s r : Nat) :
    pair (loop s r).1 (loop s r).2 = s * (s + 1) / 2 + r := by
  induction r using Nat.strong_induction_on generalizing s with
  | _ r ih =>
    rw [loop]
    by_cases h : s < r
    · -- Taken step: `(s, r) ↦ (s + 1, r - (s + 1))`, with `s + 1 ≤ r`.
      rw [dite_eq_left h, ih (r - (s + 1)) (by omega) (s + 1), tri_succ]
      omega
    · -- Terminal output `(s - r, r)` with `r ≤ s`.
      rw [dite_eq_right h]
      have hrs : s - r + r = s := by omega
      simp only [pair, hrs]

theorem pair_decode (x : Nat) :
    pair (decode x).1 (decode x).2 = x := by
  unfold decode
  rw [pair_loop]
  omega

/-! ### Injectivity of the pairing -/

/-- Lower end of the triangular interval: `T(a+b) ≤ pair a b`. -/
theorem tri_le_pair (a b : Nat) : (a + b) * (a + b + 1) / 2 ≤ pair a b := by
  unfold pair
  omega

/-- Upper end of the triangular interval: `pair a b < T(a+b+1)`, as `b ≤ a+b`. -/
theorem pair_lt_tri_succ (a b : Nat) :
    pair a b < (a + b + 1) * (a + b + 1 + 1) / 2 := by
  rw [tri_succ]
  unfold pair
  omega

/-- Equal paired values have equal diagonal index `a + b`: `pair a b` lies in
`[T(a+b), T(a+b+1))`, and these intervals are disjoint. -/
theorem pair_sum_eq {a b c d : Nat} (h : pair a b = pair c d) : a + b = c + d := by
  rcases Nat.lt_trichotomy (a + b) (c + d) with hlt | heq | hgt
  · exfalso
    have h1 := pair_lt_tri_succ a b
    have h2 := tri_mono (show a + b + 1 ≤ c + d from hlt)
    have h3 := tri_le_pair c d
    omega
  · exact heq
  · exfalso
    have h1 := pair_lt_tri_succ c d
    have h2 := tri_mono (show c + d + 1 ≤ a + b from hgt)
    have h3 := tri_le_pair a b
    omega

theorem pair_inj {a b c d : Nat} (h : pair a b = pair c d) : a = c ∧ b = d := by
  have hs := pair_sum_eq h
  have hb : b = d := by
    unfold pair at h
    rw [hs] at h
    omega
  exact ⟨by omega, hb⟩

theorem decode_pair (a b : Nat) :
    decode (pair a b) = (a, b) := by
  obtain ⟨h1, h2⟩ := pair_inj (pair_decode (pair a b))
  exact Prod.ext h1 h2

/-! ### Five-component roundtrips -/

theorem decode5_encode5 (a b c d e : Nat) :
    decode5 (encode5 a b c d e) = (a, b, c, d, e) := by
  simp only [decode5, encode5, decode_pair]

theorem encode5_decode5 (x : Nat) :
    encode5 (decode5 x).1 (decode5 x).2.1 (decode5 x).2.2.1
      (decode5 x).2.2.2.1 (decode5 x).2.2.2.2 = x := by
  simp only [decode5, encode5, pair_decode]

/-! ### The emitted integer pairing equation -/

theorem pairing_equation_iff (a b t : Nat) :
    (2 * (t : Int) - ((a : Int) + (b : Int)) *
      ((a : Int) + (b : Int) + 1) - 2 * (b : Int) = 0) ↔ t = pair a b := by
  have hI : 2 * ((pair a b : Nat) : Int) =
      ((a : Int) + (b : Int)) * ((a : Int) + (b : Int) + 1) + 2 * (b : Int) := by
    exact_mod_cast two_mul_pair a b
  constructor
  · intro heq
    omega
  · intro heq
    omega

end ZInQ.CantorDecoder
