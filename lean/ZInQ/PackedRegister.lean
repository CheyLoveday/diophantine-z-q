module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

/-!
# Packed register decoding (helper target T2 of the packed-history review)

The compiler's register equation (compiler lines 199-200, proof line 125)

  `R + B*C = initial + B*R + B*A`

is read in base `B` with register digits `ρ t < K`, increment digits `α t ≤ 1`,
decrement digits `γ t ≤ 1` (for `t ≤ q`), an initial value `init < K`, and `K < B`.
Every base-`B` digit on either side is then at most `K < B`, so uniqueness of
base-`B` expansions yields the initial condition, every transition for `t < q`,
and the extra slot `q+1` equation `γ q = ρ q + α q`.

Only ordinary natural-number equalities are used; the proof is a carry-free
comparison of digits, proved here from first principles (no Mathlib digit API).
-/

open scoped BigOperators

public section

namespace ZInQ.PackedHistory

/-- One base-`M` digit comparison: if `a, b < M` and `a + x*M = b + y*M`
then `a = b` and `x = y`. -/
private theorem digit_split {M a b x y : ℕ} (ha : a < M) (hb : b < M)
    (h : a + x * M = b + y * M) : a = b ∧ x = y := by
  have hM : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le a) ha
  have h1 : (a + x * M) % M = a := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  have h2 : (b + y * M) % M = b := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  have h3 : (a + x * M) / M = x := by
    rw [Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt ha, Nat.zero_add]
  have h4 : (b + y * M) / M = y := by
    rw [Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt hb, Nat.zero_add]
  refine ⟨?_, ?_⟩
  · calc a = (a + x * M) % M := h1.symm
      _ = (b + y * M) % M := by rw [h]
      _ = b := h2
  · calc x = (a + x * M) / M := h3.symm
      _ = (b + y * M) / M := by rw [h]
      _ = y := h4

/-- Uniqueness of base-`B` expansions with an arbitrary (unbounded) top part:
if the first `n` digits of `u` and `v` are below `B` and
`∑_{t<n} u t B^t + x B^n = ∑_{t<n} v t B^t + y B^n`, then the first `n` digits
agree and `x = y`. -/
private theorem digits_eq_of_sum_eq {B : ℕ} (u v : ℕ → ℕ) (n : ℕ) :
    ∀ x y : ℕ, (∀ t, t < n → u t < B) → (∀ t, t < n → v t < B) →
      (∑ t ∈ Finset.range n, u t * B ^ t) + x * B ^ n
        = (∑ t ∈ Finset.range n, v t * B ^ t) + y * B ^ n →
      (∀ t, t < n → u t = v t) ∧ x = y := by
  induction n with
  | zero =>
    intro x y _ _ h
    simp only [Finset.sum_range_zero, pow_zero, mul_one, zero_add] at h
    exact ⟨fun t ht => absurd ht (Nat.not_lt_zero t), h⟩
  | succ n ih =>
    intro x y hu hv h
    have e1 : (∑ t ∈ Finset.range (n+1), u t * B ^ t) + x * B ^ (n+1)
        = (∑ t ∈ Finset.range n, u t * B ^ t) + (u n + x * B) * B ^ n := by
      rw [Finset.sum_range_succ]
      ring
    have e2 : (∑ t ∈ Finset.range (n+1), v t * B ^ t) + y * B ^ (n+1)
        = (∑ t ∈ Finset.range n, v t * B ^ t) + (v n + y * B) * B ^ n := by
      rw [Finset.sum_range_succ]
      ring
    have key : (∑ t ∈ Finset.range n, u t * B ^ t) + (u n + x * B) * B ^ n
        = (∑ t ∈ Finset.range n, v t * B ^ t) + (v n + y * B) * B ^ n :=
      e1.symm.trans (h.trans e2)
    obtain ⟨hlow, htop⟩ := ih (u n + x * B) (v n + y * B)
      (fun t ht => hu t (by omega)) (fun t ht => hv t (by omega)) key
    obtain ⟨hn, hxy⟩ := digit_split (hu n (by omega)) (hv n (by omega)) htop
    refine ⟨fun t ht => ?_, hxy⟩
    by_cases htn : t < n
    · exact hlow t htn
    · have htn' : t = n := by omega
      rw [htn']
      exact hn

theorem packed_register_decode {B K q init : ℕ} (hKB : K < B) (ρ α γ : ℕ → ℕ)
    (hρ : ∀ t, t ≤ q → ρ t < K) (hα : ∀ t, t ≤ q → α t ≤ 1)
    (hγ : ∀ t, t ≤ q → γ t ≤ 1) (hinit : init < K)
    (heq : (∑ t ∈ Finset.range (q+1), ρ t * B ^ t) + B * (∑ t ∈ Finset.range (q+1), γ t * B ^ t)
         = init + B * (∑ t ∈ Finset.range (q+1), ρ t * B ^ t)
                + B * (∑ t ∈ Finset.range (q+1), α t * B ^ t)) :
    ρ 0 = init ∧ (∀ t, t < q → ρ (t+1) + γ t = ρ t + α t) ∧ γ q = ρ q + α q := by
  -- Stage 1: slot zero.  Split off the constant digit of the register history.
  have hsplit : (∑ t ∈ Finset.range (q+1), ρ t * B ^ t)
      = ρ 0 + (∑ t ∈ Finset.range q, ρ (t+1) * B ^ t) * B := by
    rw [Finset.sum_range_succ', Finset.sum_mul, pow_zero, mul_one, add_comm]
    congr 1
    exact Finset.sum_congr rfl (fun t _ => by ring)
  have h1 : ρ 0 + ((∑ t ∈ Finset.range q, ρ (t+1) * B ^ t)
        + (∑ t ∈ Finset.range (q+1), γ t * B ^ t)) * B
      = init + ((∑ t ∈ Finset.range (q+1), ρ t * B ^ t)
        + (∑ t ∈ Finset.range (q+1), α t * B ^ t)) * B := by
    calc ρ 0 + ((∑ t ∈ Finset.range q, ρ (t+1) * B ^ t)
          + (∑ t ∈ Finset.range (q+1), γ t * B ^ t)) * B
        = (ρ 0 + (∑ t ∈ Finset.range q, ρ (t+1) * B ^ t) * B)
          + B * (∑ t ∈ Finset.range (q+1), γ t * B ^ t) := by ring
      _ = (∑ t ∈ Finset.range (q+1), ρ t * B ^ t)
          + B * (∑ t ∈ Finset.range (q+1), γ t * B ^ t) := by rw [hsplit]
      _ = init + B * (∑ t ∈ Finset.range (q+1), ρ t * B ^ t)
          + B * (∑ t ∈ Finset.range (q+1), α t * B ^ t) := heq
      _ = init + ((∑ t ∈ Finset.range (q+1), ρ t * B ^ t)
          + (∑ t ∈ Finset.range (q+1), α t * B ^ t)) * B := by ring
  have hρ0 : ρ 0 < B := Nat.lt_trans (hρ 0 (Nat.zero_le q)) hKB
  have hinitB : init < B := Nat.lt_trans hinit hKB
  obtain ⟨h0, h2⟩ := digit_split hρ0 hinitB h1
  -- Stage 2: slots `1, …, q` and the extra slot `q+1`.
  have e1 : (∑ t ∈ Finset.range q, (ρ (t+1) + γ t) * B ^ t) + γ q * B ^ q
      = (∑ t ∈ Finset.range q, ρ (t+1) * B ^ t)
        + (∑ t ∈ Finset.range (q+1), γ t * B ^ t) := by
    have hd : (∑ t ∈ Finset.range q, (ρ (t+1) + γ t) * B ^ t)
        = (∑ t ∈ Finset.range q, ρ (t+1) * B ^ t)
          + (∑ t ∈ Finset.range q, γ t * B ^ t) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun t _ => by ring)
    rw [hd, Finset.sum_range_succ]
    ring
  have e2 : (∑ t ∈ Finset.range q, (ρ t + α t) * B ^ t) + (ρ q + α q) * B ^ q
      = (∑ t ∈ Finset.range (q+1), ρ t * B ^ t)
        + (∑ t ∈ Finset.range (q+1), α t * B ^ t) := by
    have hd : (∑ t ∈ Finset.range q, (ρ t + α t) * B ^ t)
        = (∑ t ∈ Finset.range q, ρ t * B ^ t)
          + (∑ t ∈ Finset.range q, α t * B ^ t) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun t _ => by ring)
    rw [hd, Finset.sum_range_succ, Finset.sum_range_succ]
    ring
  have h3 : (∑ t ∈ Finset.range q, (ρ (t+1) + γ t) * B ^ t) + γ q * B ^ q
      = (∑ t ∈ Finset.range q, (ρ t + α t) * B ^ t) + (ρ q + α q) * B ^ q :=
    e1.trans (h2.trans e2.symm)
  have hu : ∀ t, t < q → ρ (t+1) + γ t < B := by
    intro t ht
    have hr := hρ (t+1) (by omega)
    have hg := hγ t (by omega)
    omega
  have hv : ∀ t, t < q → ρ t + α t < B := by
    intro t ht
    have hr := hρ t (by omega)
    have ha := hα t (by omega)
    omega
  obtain ⟨hstep, hlast⟩ := digits_eq_of_sum_eq (fun t => ρ (t+1) + γ t)
    (fun t => ρ t + α t) q (γ q) (ρ q + α q) hu hv h3
  exact ⟨h0, hstep, hlast⟩

end ZInQ.PackedHistory

end
