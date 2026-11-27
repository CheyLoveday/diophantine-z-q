import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.SelmerPairing

/-!
# Selmer duality, part 4: ranks of Selmer cones

For the counts of Lemma `ex:limits-residual-bound` (tex L4553–4560, L4593–4597: "the total rank of
the Selmer cone (4.3) ... Cone shifts do not change this sum"): the Selmer complex
`C^n = G^n ⊕ U^n ⊕ L^{n−1}` of `PairedFunctional/SelmerPairing.lean` with finite free terms has
`rank C^n = rank G^n + rank U^n + rank L^{n−1}`, and over any finite set of degrees `s` its total
rank is the sum of the total ranks of `G`, `U` and of `L` shifted by one (`selCx_totalRank`).

**Classification.** GLUE, PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.SelmerDuality

open ZInQ.Contrib.CloudB3RC53.PairedFunctional

universe u

variable {S : Type u} [CommRing S] [StrongRankCondition S] (D : SelData S)
  [∀ n, Module.Free S (D.G.X n)] [∀ n, Module.Finite S (D.G.X n)]
  [∀ n, Module.Free S (D.U.X n)] [∀ n, Module.Finite S (D.U.X n)]
  [∀ n, Module.Free S (D.L.X n)] [∀ n, Module.Finite S (D.L.X n)]

/-- `rank C^n = rank G^n + rank U^n + rank L^{n−1}`. -/
theorem selCx_finrank (n : ℤ) :
    Module.finrank S ((selCx D).X n) =
      Module.finrank S (D.G.X n) + Module.finrank S (D.U.X n) + Module.finrank S (D.L.X (n - 1)) := by
  change Module.finrank S (D.G.X n × D.U.X n × D.L.X (n - 1)) = _
  rw [Module.finrank_prod, Module.finrank_prod, add_assoc]

/-- **The total rank of a Selmer cone** over a finite set of degrees `s`:
`Σ_{n ∈ s} rank C^n = Σ_{n ∈ s} rank G^n + Σ_{n ∈ s} rank U^n + Σ_{n ∈ s} rank L^{n−1}`. -/
theorem selCx_totalRank (s : Finset ℤ) :
    ∑ n ∈ s, Module.finrank S ((selCx D).X n) =
      ∑ n ∈ s, Module.finrank S (D.G.X n) + ∑ n ∈ s, Module.finrank S (D.U.X n) +
        ∑ n ∈ s, Module.finrank S (D.L.X (n - 1)) := by
  simp only [selCx_finrank, Finset.sum_add_distrib]

end ZInQ.Contrib.CloudB3RC53.SelmerDuality
