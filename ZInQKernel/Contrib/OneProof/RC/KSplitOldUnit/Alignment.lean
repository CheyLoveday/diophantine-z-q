import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Identities

/-! Multiplication by a positive squarefree unit class at the old support. -/

namespace ZInQ.Manuscript.RC.KSplitOldUnit

/-- The numerical filter conditions for `d` in the squareclasses of `D₀`
survive multiplication by a coprime index `n` in the class of one at the
old support (tex 10293–10297). The mod-eight condition is included. -/
theorem mul_old_filter {S₀ : Finset ℕ} {D₀ d n : ℕ}
    (hS₀ : ∀ p ∈ S₀, p.Prime) (hd : 0 < d) (hdSF : Squarefree d)
    (hdS : ∀ p ∈ S₀, ¬ p ∣ d)
    (hdClass : ∀ p ∈ S₀, (p = 2 → (d * D₀) % 8 = 1) ∧
      (p ≠ 2 → IsSquare ((d * D₀ : ℕ) : ZMod p)))
    (hn : 0 < n) (hnSF : Squarefree n) (hnS : ∀ p ∈ S₀, ¬ p ∣ n)
    (hnClass : ∀ p ∈ S₀, (p = 2 → n % 8 = 1) ∧
      (p ≠ 2 → IsSquare (n : ZMod p)))
    (hcop : d.Coprime n) :
    0 < d * n ∧ Squarefree (d * n) ∧ (∀ p ∈ S₀, ¬ p ∣ d * n) ∧
      ∀ p ∈ S₀, (p = 2 → (d * n * D₀) % 8 = 1) ∧
        (p ≠ 2 → IsSquare ((d * n * D₀ : ℕ) : ZMod p)) := by
  refine ⟨Nat.mul_pos hd hn, Nat.squarefree_mul_iff.mpr ⟨hcop, hdSF, hnSF⟩,
    fun p hp hdvd => ((hS₀ p hp).dvd_mul.mp hdvd).elim (hdS p hp) (hnS p hp), ?_⟩
  intro p hp
  rw [mul_right_comm d n D₀]
  refine ⟨fun h2 => ?_, fun h2 => ?_⟩
  · rw [Nat.mul_mod, (hdClass p hp).1 h2, (hnClass p hp).1 h2]
  · rw [Nat.cast_mul]
    exact ((hdClass p hp).2 h2).mul ((hnClass p hp).2 h2)

/-- Adding the primes of `d` to the new support ensures coprimality with each
retained new index (tex 10292–10295). -/
theorem coprime_of_new_support {S : Finset ℕ} {d n : ℕ} (hd : d ≠ 0)
    (hdS : d.primeFactors ⊆ S) (hnS : ∀ p ∈ S, ¬ p ∣ n) : d.Coprime n :=
  Nat.coprime_of_dvd fun p hp hpd hpn => hnS p (hdS (Nat.mem_primeFactors.mpr ⟨hp, hpd, hd⟩)) hpn

end ZInQ.Manuscript.RC.KSplitOldUnit
