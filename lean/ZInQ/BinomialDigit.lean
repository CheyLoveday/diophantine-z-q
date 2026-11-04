module

public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Digits.Lemmas
import Lean.Elab.Tactic.Omega

/-!
# Literal binomial-digit macro

All inputs and witnesses are natural numbers. Powers denote ordinary
mathematical powers. The separate power-representation layer is outside
this packet.
-/

public section

namespace ZInQ.BinomialDigit

/-- The five-witness arithmetic relation emitted by Builder.binomial. -/
@[expose] def macroHolds (C N K : Nat) : Prop :=
  ∃ base total place u r : Nat,
    base = 2 ^ (N + 1) ∧
    total = (1 + base) ^ N ∧
    place = base ^ K ∧
    C < base ∧
    r < place ∧
    total = place * (base * u + C) + r

end ZInQ.BinomialDigit


end

/-! Exact correctness of the literal natural-number binomial-digit macro. -/

public section

namespace ZInQ.BinomialDigit

open scoped BigOperators

theorem choose_lt_base (N K : Nat) :
    Nat.choose N K < 2 ^ (N + 1) := by
  have hp : 0 < (2 : Nat) ^ N := pow_pos (by decide) _
  have hstep : (2 : Nat) ^ N < 2 ^ (N + 1) := by
    rw [pow_succ]
    omega
  exact (Nat.choose_le_two_pow N K).trans_lt hstep

private theorem of_digits_map_range (b n : Nat) (f : Nat → Nat) :
    Nat.ofDigits b ((List.range n).map f) =
      ∑ i ∈ Finset.range n, f i * b ^ i := by
  induction n with
  | zero =>
      simp only [List.range_zero, List.map_nil, Nat.ofDigits,
        Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
      rw [List.range_succ, List.map_append, Nat.ofDigits_append,
        List.length_map, List.length_range, List.map_singleton,
        Nat.ofDigits_singleton, Finset.sum_range_succ, ih]
      ac_rfl

private theorem binomial_of_digits (N b : Nat) :
    Nat.ofDigits b ((List.range (N + 1)).map (Nat.choose N)) = (1 + b) ^ N := by
  rw [of_digits_map_range, Nat.add_comm 1 b, add_pow]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [one_pow, mul_one, Nat.cast_id]
  exact Nat.mul_comm _ _

private theorem head_drop_choose (N K : Nat) :
    (((List.range (N + 1)).map (Nat.choose N)).drop K).head! = Nat.choose N K := by
  rw [List.head!_eq_head?_getD, List.head?_drop, List.getElem?_map]
  by_cases hK : K < N + 1
  · rw [List.getElem?_range hK]
    rfl
  · have hNK : N < K := by omega
    have hnone : (List.range (N + 1))[K]? = none :=
      List.getElem?_eq_none (by simpa only [List.length_range] using Nat.le_of_not_gt hK)
    rw [hnone]
    simp only [Option.map_none, Option.getD_none, Nat.choose_eq_zero_of_lt hNK]
    rfl

theorem div_pow_mod_eq_choose (N K : Nat) :
    (((1 + 2 ^ (N + 1)) ^ N) / ((2 ^ (N + 1)) ^ K)) % (2 ^ (N + 1)) =
      Nat.choose N K := by
  let B : Nat := 2 ^ (N + 1)
  have hB : 0 < B := pow_pos (by decide) _
  have hL : ∀ x ∈ (List.range (N + 1)).map (Nat.choose N), x < B := by
    intro x hx
    obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hx
    exact choose_lt_base N i
  change ((1 + B) ^ N / B ^ K) % B = Nat.choose N K
  rw [← binomial_of_digits N B,
    Nat.ofDigits_div_pow_eq_ofDigits_drop K hB _ hL,
    Nat.ofDigits_mod_eq_head!, head_drop_choose,
    Nat.mod_eq_of_lt (choose_lt_base N K)]

private theorem digit_witness_iff (B P T C : Nat) (hB : 0 < B) (hP : 0 < P) :
    (∃ u r : Nat, C < B ∧ r < P ∧ T = P * (B * u + C) + r) ↔
      C = (T / P) % B := by
  constructor
  · rintro ⟨u, r, hC, hr, hT⟩
    have hq : T / P = B * u + C := by
      rw [hT, Nat.add_comm (P * (B * u + C)) r,
        Nat.add_mul_div_left r (B * u + C) hP, Nat.div_eq_of_lt hr, Nat.zero_add]
    rw [hq, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hC]
  · intro hC
    refine ⟨(T / P) / B, T % P, ?_, Nat.mod_lt T hP, ?_⟩
    · rw [hC]
      exact Nat.mod_lt _ hB
    · have hq : B * ((T / P) / B) + C = T / P := by
        calc
          B * ((T / P) / B) + C = C + B * ((T / P) / B) := Nat.add_comm _ _
          _ = T / P := by
            rw [hC]
            exact Nat.mod_add_div _ _
      calc
        T = T % P + P * (T / P) := (Nat.mod_add_div T P).symm
        _ = P * (T / P) + T % P := Nat.add_comm _ _
        _ = P * (B * ((T / P) / B) + C) + T % P := by rw [hq]

theorem macro_holds_iff_choose (C N K : Nat) :
    macroHolds C N K ↔ C = Nat.choose N K := by
  have hB : 0 < (2 : Nat) ^ (N + 1) := pow_pos (by decide) _
  have hP : 0 < ((2 : Nat) ^ (N + 1)) ^ K := pow_pos hB _
  constructor
  · rintro ⟨base, total, place, u, r, rfl, rfl, rfl, hC, hr, hT⟩
    have h := (digit_witness_iff _ _ _ C hB hP).mp ⟨u, r, hC, hr, hT⟩
    exact h.trans (div_pow_mod_eq_choose N K)
  · intro h
    have hdigit : C =
        (((1 + 2 ^ (N + 1)) ^ N) / ((2 ^ (N + 1)) ^ K)) % (2 ^ (N + 1)) :=
      h.trans (div_pow_mod_eq_choose N K).symm
    obtain ⟨u, r, hC, hr, hT⟩ := (digit_witness_iff _ _ _ C hB hP).mpr hdigit
    exact ⟨2 ^ (N + 1), (1 + 2 ^ (N + 1)) ^ N, (2 ^ (N + 1)) ^ K,
      u, r, rfl, rfl, rfl, hC, hr, hT⟩

theorem macro_holds_zero_row (C K : Nat) :
    macroHolds C 0 K ↔ C = (if K = 0 then 1 else 0) := by
  rw [macro_holds_iff_choose]
  cases K with
  | zero => rfl
  | succ K => rfl

theorem macro_holds_zero_column (C N : Nat) :
    macroHolds C N 0 ↔ C = 1 := by
  simpa only [Nat.choose_zero_right] using macro_holds_iff_choose C N 0

theorem macro_holds_above_row (C N K : Nat) (_hNK : N < K) :
    macroHolds C N K ↔ C = 0 := by
  simpa only [Nat.choose_eq_zero_of_lt _hNK] using macro_holds_iff_choose C N K

end ZInQ.BinomialDigit

