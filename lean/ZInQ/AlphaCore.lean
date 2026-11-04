module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Tactic.Linarith

/-!
# Arithmetic of the alpha sequence

Integer-valued recurrence, Chebyshev correspondence, growth, Cassini identity,
and classification of its ordered quadratic core. The definition and proof
bodies are preserved from the independently checked alpha packet.
These results do not establish the complete alpha or exponentiation encoding.
-/

public section

namespace ZInQ.AlphaPower

@[expose] def alphaZ (B : Nat) : Nat → Int
  | 0 => 0
  | 1 => 1
  | n + 2 => (B : Int) * alphaZ B (n + 1) - alphaZ B n


/-! ### Defining equations (definitional, from the supplied `alphaZ`) -/

theorem alphaZ_zero (B : Nat) : alphaZ B 0 = 0 := rfl

theorem alphaZ_one (B : Nat) : alphaZ B 1 = 1 := rfl

theorem alphaZ_add_two (B n : Nat) :
    alphaZ B (n + 2) = (B : Int) * alphaZ B (n + 1) - alphaZ B n := rfl

/-! ### Chebyshev correspondence (all `B`) -/

/-- `alphaZ B N` is Mathlib's rescaled Chebyshev polynomial `S` (with `S (n+2) = X * S (n+1) - S n`,
`S (-1) = 0`, `S 0 = 1`) at index `N - 1` (an integer index), evaluated at `B`. -/
theorem alphaZ_eq_rescaledChebyshev (B N : Nat) :
    alphaZ B N = (Polynomial.Chebyshev.S Int ((N : Int) - 1)).eval (B : Int) := by
  have key : ∀ n : Nat,
      alphaZ B n = (Polynomial.Chebyshev.S Int ((n : Int) - 1)).eval (B : Int) ∧
      alphaZ B (n + 1) = (Polynomial.Chebyshev.S Int (n : Int)).eval (B : Int) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp [alphaZ_zero]
      · simp [alphaZ_one]
    | succ n ih =>
      obtain ⟨ih0, ih1⟩ := ih
      refine ⟨?_, ?_⟩
      · have e : ((n + 1 : Nat) : Int) - 1 = (n : Int) := by push_cast; ring
        rw [e]
        exact ih1
      · rw [show n + 1 + 1 = n + 2 from rfl, alphaZ_add_two, ih0, ih1]
        have h := Polynomial.Chebyshev.S_add_one Int (n : Int)
        have e : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by push_cast; ring
        rw [e, h]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
  exact (key N).1

/-! ### Cassini / quadratic invariant (all `B`) -/

/-- The quadratic invariant, for every natural `B` (no lower bound on `B`), proved directly
from the integer recurrence. -/
theorem alphaZ_cassini (B N : Nat) :
    alphaZ B N ^ 2 + alphaZ B (N + 1) ^ 2 -
      (B : Int) * alphaZ B N * alphaZ B (N + 1) = 1 := by
  induction N with
  | zero => simp [alphaZ_zero, alphaZ_one]
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 from rfl, alphaZ_add_two]
    linear_combination ih

/-! ### Growth (for `2 ≤ B`) -/

/-- Joint induction (cf. AFP `alpha_strictly_increasing`): nonnegativity and growth by at least
one of consecutive values, for `2 ≤ B` (including `B = 2`). -/
theorem alphaZ_step (B : Nat) (hB : 2 ≤ B) (N : Nat) :
    0 ≤ alphaZ B N ∧ alphaZ B N + 1 ≤ alphaZ B (N + 1) := by
  induction N with
  | zero => simp [alphaZ_zero, alphaZ_one]
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    have hB' : (2 : Int) ≤ (B : Int) := by exact_mod_cast hB
    have ha1 : 0 ≤ alphaZ B (n + 1) := by linarith
    have hm : 0 ≤ ((B : Int) - 2) * alphaZ B (n + 1) :=
      mul_nonneg (by linarith) ha1
    refine ⟨ha1, ?_⟩
    rw [show n + 1 + 1 = n + 2 from rfl, alphaZ_add_two]
    nlinarith

theorem alphaZ_succ_strict (B N : Nat) (hB : 2 ≤ B) :
    alphaZ B N < alphaZ B (N + 1) := by
  have h := (alphaZ_step B hB N).2
  linarith

theorem alphaZ_ge_index (B N : Nat) (hB : 2 ≤ B) :
    (N : Int) ≤ alphaZ B N := by
  induction N with
  | zero => simp [alphaZ_zero]
  | succ n ih =>
    have h := (alphaZ_step B hB n).2
    push_cast
    linarith

/-! ### Ordered quadratic classification -/

/-- Vieta descent on `r` (cf. AFP `alpha_char_eq`): every ordered solution of
`1 + B*s*r = s*s + r*r` with `r < s` is a pair of consecutive values of `alphaZ B`.
No hypothesis on `B` is needed for this direction. -/
theorem alphaZ_descent (B : Nat) :
    ∀ r s : Nat, r < s → 1 + B * s * r = s * s + r * r →
      ∃ n : Nat, (r : Int) = alphaZ B n ∧ (s : Int) = alphaZ B (n + 1) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro s hrs heq
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · -- Base `r = 0`: the equation forces `s * s = 1`, hence `s = 1`.
      subst hr0
      have hss : s * s = 1 := by simpa using heq.symm
      have hs1 : s = 1 := by
        rcases Nat.lt_or_ge s 2 with h | h
        · omega
        · nlinarith
      subst hs1
      exact ⟨0, by simp [alphaZ_zero], by simp [alphaZ_one]⟩
    · have hZ : (1 : Int) + (B : Int) * (s : Int) * (r : Int) =
          (s : Int) * (s : Int) + (r : Int) * (r : Int) := by
        exact_mod_cast heq
      have hrsZ : (r : Int) < (s : Int) := by exact_mod_cast hrs
      have hrposZ : (0 : Int) < (r : Int) := by exact_mod_cast hrpos
      have hr1 : (1 : Int) ≤ (r : Int) := by omega
      have hrr : (1 : Int) ≤ (r : Int) * r := one_le_mul_of_one_le_of_one_le hr1 hr1
      -- Vieta: the other root `B*r - s` times `s` is `r*r - 1`.
      have hprod : ((B : Int) * r - s) * s = (r : Int) * r - 1 := by
        linear_combination hZ
      -- Hence `s ≤ B*r`, so the natural difference below is genuine.
      have hle : s ≤ B * r := by
        have hle' : (s : Int) ≤ (B : Int) * r := by
          by_contra hcon
          have hcon' : (B : Int) * r < s := not_le.mp hcon
          have h1 : ((B : Int) * r - s) * s < 0 :=
            mul_neg_of_neg_of_pos (by linarith) (by linarith)
          linarith
        exact_mod_cast hle'
      obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hle
      have huZ : (B : Int) * r = s + u := by exact_mod_cast hu
      have hu' : (u : Int) = (B : Int) * r - s := by linarith
      have hus : (u : Int) * s = (r : Int) * r - 1 := by
        rw [hu']; exact hprod
      -- The other root is strictly smaller than `r`.
      have hur : u < r := by
        have hurZ : (u : Int) < r := by
          by_contra hcon
          have hcon' : (r : Int) ≤ u := not_lt.mp hcon
          have h1 : (r : Int) * s ≤ (u : Int) * s :=
            mul_le_mul_of_nonneg_right hcon' (by omega)
          have h2 : (r : Int) * r < (r : Int) * s :=
            mul_lt_mul_of_pos_left hrsZ hrposZ
          linarith
        exact_mod_cast hurZ
      -- The smaller pair `(u, r)` satisfies the same ordered equation.
      have heq' : 1 + B * r * u = r * r + u * u := by
        have h : (1 : Int) + (B : Int) * r * u = (r : Int) * r + (u : Int) * u := by
          rw [hu']
          linear_combination hZ
        exact_mod_cast h
      obtain ⟨n, hn0, hn1⟩ := ih u hur r hur heq'
      -- The recurrence recovers `s = B*r - u`.
      refine ⟨n + 1, hn1, ?_⟩
      rw [show n + 1 + 1 = n + 2 from rfl, alphaZ_add_two, ← hn1, ← hn0]
      linarith

theorem ordered_core_iff_consecutive (B r s : Nat) :
    (3 < B ∧ r < s ∧ 1 + B * s * r = s * s + r * r) ↔
    (3 < B ∧ ∃ n : Nat,
      (r : Int) = alphaZ B n ∧ (s : Int) = alphaZ B (n + 1)) := by
  constructor
  · rintro ⟨hB, hrs, heq⟩
    exact ⟨hB, alphaZ_descent B r s hrs heq⟩
  · rintro ⟨hB, n, hr, hs⟩
    refine ⟨hB, ?_, ?_⟩
    · have h := alphaZ_succ_strict B n (by omega)
      rw [← hr, ← hs] at h
      exact_mod_cast h
    · have h := alphaZ_cassini B n
      rw [← hr, ← hs] at h
      have h' : (1 : Int) + (B : Int) * s * r = (s : Int) * s + (r : Int) * r := by
        linear_combination -h
      exact_mod_cast h'

end ZInQ.AlphaPower
