module

public import ZInQ.AlphaCore

/-!
# Alpha index and additive-companion assembly interfaces

Internal assembly interfaces L01, L02, L04 and L09 for the alpha-power
characterization (cf. AFP `Exponentiation.thy`, proof of `alpha_equiv_suff`,
Equations 3.57, 3.59, 3.61, and the companion `v` in the necessity direction).

Only the accepted `ZInQ.AlphaCore` API is used (`alphaZ_descent`,
`alphaZ_add_two`). These are internal helpers, not frozen anchors; they do not
establish the complete alpha or exponentiation encoding.
-/

public section

namespace ZInQ.AlphaPower

/-- L01 (cf. Equation 3.57 and `m_pos`): an ordered solution `r < s` of
`s^2 + r^2 = 1 + b*s*r` is `(alphaZ b (m-1), alphaZ b m)` for a positive index `m`.
No hypothesis on `b` is needed. -/
theorem orderedPair_positive_index (b r s : Nat)
    (hrs : r < s) (heq : s^2 + r^2 = 1 + b*s*r) :
    ∃ m : Nat, 0 < m ∧ (r : Int) = alphaZ b (m-1) ∧
      (s : Int) = alphaZ b m := by
  have heq' : 1 + b * s * r = s * s + r * r := by
    rw [← heq]
    ring
  obtain ⟨n, hn0, hn1⟩ := alphaZ_descent b r s hrs heq'
  refine ⟨n + 1, by omega, ?_, hn1⟩
  rw [Nat.add_sub_cancel]
  exact hn0

/-- L02 (cf. Equation 3.59): every natural index `n` is folded around a multiple
`2*l*m` of `2*m`, at distance `j ≤ m`, using literal natural subtraction. -/
theorem exists_folded_index (m n : Nat) (hm : 0 < m) :
    ∃ l j : Nat, j ≤ m ∧
      (n = 2*l*m+j ∨ (n = 2*l*m-j ∧ 0 < j ∧ j < 2*l*m)) := by
  obtain ⟨k, q, hq, hn⟩ : ∃ k q : Nat, q < 2 * m ∧ n = 2 * (k * m) + q := by
    refine ⟨n / (2 * m), n % (2 * m), Nat.mod_lt n (by omega), ?_⟩
    have h := Nat.div_add_mod n (2 * m)
    calc n = 2 * m * (n / (2 * m)) + n % (2 * m) := h.symm
      _ = 2 * (n / (2 * m) * m) + n % (2 * m) := by ring
  rcases Nat.lt_or_ge m q with hmq | hqm
  · -- `m < q`: fold down from `2*(k+1)*m` by `j = 2*m - q`.
    have e : 2 * (k + 1) * m = 2 * (k * m) + 2 * m := by ring
    exact ⟨k + 1, 2 * m - q, by omega, Or.inr ⟨by omega, by omega, by omega⟩⟩
  · -- `q ≤ m`: go up from `2*k*m` by `j = q`.
    have e : 2 * k * m = 2 * (k * m) := by ring
    exact ⟨k, q, hqm, Or.inl (by omega)⟩

/-- L04 (cf. Equation 3.61): the additive witness `v + 2*r = b*s` for the
consecutive pair `(alphaZ b (m-1), alphaZ b m)` is `alphaZ b (m+1) - alphaZ b (m-1)`. -/
theorem companion_of_additive_witness (b r s v m : Nat)
    (hm : 0 < m) (hr : (r : Int) = alphaZ b (m-1))
    (hs : (s : Int) = alphaZ b m) (hv : v+2*r = b*s) :
    (v : Int) = alphaZ b (m+1) - alphaZ b (m-1) := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, m = n + 1 := ⟨m - 1, by omega⟩
  have hv' : (v : Int) + 2 * (r : Int) = (b : Int) * (s : Int) := by
    exact_mod_cast hv
  rw [Nat.add_sub_cancel] at hr ⊢
  rw [show n + 1 + 1 = n + 2 from rfl, alphaZ_add_two, ← hr, ← hs]
  linarith

/-- L09 (cf. the companion `v = b*s - 2*r` and bound 373 in the necessity
direction): for `3 < b` and `r < s`, a natural additive companion exists and
exceeds `2*s`. -/
theorem exists_large_additive_companion (b r s : Nat) (hb : 3 < b) (hrs : r < s) :
    ∃ v : Nat, v+2*r = b*s ∧ 2*s < v := by
  have h4 : 4 * s ≤ b * s := Nat.mul_le_mul (by omega) (Nat.le_refl s)
  exact ⟨b * s - 2 * r, by omega, by omega⟩

end ZInQ.AlphaPower
