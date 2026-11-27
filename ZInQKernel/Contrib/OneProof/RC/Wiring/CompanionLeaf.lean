import ZInQKernel.Contrib.OneProof.RC.Wiring.Data

/-!
# Theorem 5.3, Lane RC0: the final companion, as a leaf

`CompanionLeaf W` (tex 2595–2603, with 2349–2352) and `companionTarget_of` (PROVED), kept in their
own module so that the leaves' providers (lane RC24's address leaf, batch 3's companion) can use them
without importing `RC/Wiring/Leaves.lean`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53

/-- **The final companion, as a leaf** (tex 2595–2603): in Branch 2, `k < 0` squarefree,
`k ≠ −1, −3`, its primes in the fixed support after `k` is fixed (tex 2603, 2609–2612, App G 10282,
10292–10293, 10519–10521), `k ≡ 1 (mod 4)`, a unit square at every prime of `2N`, prime to `h_*`,
and `L_*(k) ≠ 0`. DEPARTURE (order of choices): the data have one support, so the prepared filter,
the stage support and the odd minimum `δ_o` are taken over `D` prime to `k`, with `k` fixed first.
The text fixes `δ_o` before `k` (2703–2704), chooses `k` excluding the old odd support (2596–2597),
and asserts that adding the stationary conditions at `k` does not change `δ_o` (10519–10521). `k`
must also avoid the primes of the witness `D_w`, which `WitnessLeaf` makes admissible. -/
def CompanionLeaf {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ¬ W.OddEmptyUnit → W.kfin < 0 ∧ Squarefree W.kfin ∧ W.kfin ≠ -1 ∧ W.kfin ≠ -3 ∧
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ W.kfin → p ∈ W.S) ∧ W.kfin % 4 = 1 ∧
    (∀ p : ℕ, p.Prime → p ∣ 2 * CST.newformLevel (Ecurve ℓ) → UnitSquareAt p W.kfin) ∧
    IsCoprime W.kfin W.hstar ∧ W.Lstar W.kfin ≠ 0

/-- **`RCSteps.companion`** from the leaf and the normalization of `L_*` (PROVED). -/
theorem companionTarget_of {ℓ : ℕ} {W : WData ℓ} (hL : LstarTarget W.toRCData)
    (h : CompanionLeaf W) : CompanionTarget W.toRCData := fun hU => by
  obtain ⟨hneg, hsf, h1, h3, hS, h4, h2N, hcop, hLk⟩ := h hU
  exact ⟨hneg, hsf, h1, h3, hS, h4, h2N, hcop, (hL _ hneg.ne).mp hLk⟩

end ZInQ.Manuscript.RC.Wiring
