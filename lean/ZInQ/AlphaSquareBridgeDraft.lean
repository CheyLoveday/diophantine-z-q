module

public import ZInQ.AlphaSquareDivisibilityDraft

/-!
# Square-divisibility bridge pair (L03, L08)

PROVISIONAL assembly. Both targets consume the supplied theorem
`ZInQ.AlphaPower.alphaZ_sq_dvd_iff` from the pinned, read-only module
`ZInQ.AlphaSquareDivisibilityDraft`. That module is a provisional input
(author-compiled, independent review pending, no root acceptance), so these
results are conditional on its acceptance. The square theorem is used, not
reproved. Natural witness casts are discharged here.
-/

public section

namespace ZInQ.AlphaPower

theorem square_divisibility_to_index (b u s k m : Nat)
    (hb : 2 < b) (hm : 0 < m)
    (hu : (u : Int) = alphaZ b k) (hs : (s : Int) = alphaZ b m)
    (hdiv : u^2 ∣ s) : u ∣ m := by
  have h1 : (u : Int) ^ 2 ∣ (s : Int) := by exact_mod_cast hdiv
  rw [hu, hs] at h1
  have h2 : (k : Int) * alphaZ b k ∣ (m : Int) := (alphaZ_sq_dvd_iff b k m hb hm).mp h1
  rw [← hu] at h2
  have h3 : (u : Int) ∣ (m : Int) := dvd_of_mul_left_dvd h2
  exact_mod_cast h3

theorem square_multiple_pair (b k u : Nat) (hb : 2 < b) (hk : 0 < k)
    (hu : (u : Int) = alphaZ b k) :
    let m := u*k
    ∃ r s : Nat, 0 < m ∧
      (r : Int) = alphaZ b (m-1) ∧ (s : Int) = alphaZ b m ∧
      r < s ∧ s^2+r^2 = 1+b*s*r ∧ u^2 ∣ s := by
  intro m
  have hmdef : m = u * k := rfl
  have hb2 : 2 ≤ b := Nat.le_of_lt hb
  have hupos : 0 < u := by
    have hk' : (0 : Int) < (k : Int) := by exact_mod_cast hk
    have hu' : (0 : Int) < (u : Int) := by
      rw [hu]
      exact lt_of_lt_of_le hk' (alphaZ_ge_index b k hb2)
    exact_mod_cast hu'
  have hm : 0 < m := by
    rw [hmdef]
    exact Nat.mul_pos hupos hk
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel hm
  obtain ⟨r, hr⟩ : ∃ r : Nat, (r : Int) = alphaZ b (m - 1) :=
    ⟨(alphaZ b (m - 1)).toNat, Int.toNat_of_nonneg (alphaZ_step b hb2 (m - 1)).1⟩
  obtain ⟨s, hs⟩ : ∃ s : Nat, (s : Int) = alphaZ b m :=
    ⟨(alphaZ b m).toNat, Int.toNat_of_nonneg (alphaZ_step b hb2 m).1⟩
  refine ⟨r, s, hm, hr, hs, ?_, ?_, ?_⟩
  · have h := alphaZ_succ_strict b (m - 1) hb2
    rw [hm1, ← hr, ← hs] at h
    exact_mod_cast h
  · have h := alphaZ_cassini b (m - 1)
    rw [hm1, ← hr, ← hs] at h
    have h' : (s : Int) ^ 2 + (r : Int) ^ 2 = 1 + (b : Int) * (s : Int) * (r : Int) := by
      linear_combination h
    exact_mod_cast h'
  · have hQ : (k : Int) * alphaZ b k ∣ (m : Int) := by
      refine ⟨1, ?_⟩
      rw [hmdef, ← hu]
      push_cast
      ring
    have hP := (alphaZ_sq_dvd_iff b k m hb hm).mpr hQ
    rw [← hu, ← hs] at hP
    exact_mod_cast hP

end ZInQ.AlphaPower
