import ZInQKernel.Contrib.CloudB3RC53.RankCounts.ResidualCounts
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.Rank

/-!
# RankCounts: the global rank bound `hG` of the Selmer-cone model from its identification

Manuscript `diophantine_zq.tex`, tex 4593–4597 ("At each finite coefficient stage, apply Lemma
`ex:limits-inner-limit` separately to these global and local complexes … The mapping cone then has
a finite free model whose total rank is bounded by the sum just computed").

The input `hG` of `residualRankCounts_full` says that the global part `Dsel.G` of the Selmer-cone
model has total rank at most `h⁰ + h¹ + h²` of `RΓ(G_{K,S₀}, W)`. `hG_of_residualModel` proves it
when `Dsel.G` is the residual minimal model of `RΓ(G_{K,S₀}, W)` over `𝔽₂`: degreewise
isomorphic to `Hⁿ(G_{K,S₀}, W)` for `n` in the range `s ⊆ [0, 2]` (over a field a bounded complex
is homotopy equivalent to its cohomology with zero differential, and `H^{>2} = 0` by Milne ADT
I.4.10). The identification itself — a cochain-level model of `RΓ(G_{K,S₀}, W)` with its
restriction maps, i.e. the Selmer complex — is not available in Lean; it is the remaining content
of `hG` (and, place by place with the local conditions of `LocalConditions.condDimAt` and the
archimedean terms of `ArchCounts`, of `hL`). Kinds: PROVED (the identification is a hypothesis).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.RankCounts

open NumberField IsDedekindDomain CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional

variable (K : Type) [Field K] [NumberField K]

omit [NumberField K] in
/-- **`hG` from the residual model** (tex 4593–4597). PROVED. -/
theorem hG_of_residualModel (S₀ : Set (HeightOneSpectrum (𝓞 K))) (Dsel : SelData (ZMod 2))
    (s : Finset ℤ) (hs : s ⊆ Finset.Icc 0 2)
    (eG : ∀ n ∈ s, Dsel.G.X n ≃ₗ[ZMod 2] continuousCohomology n.toNat (Wrep K S₀)) :
    ∑ n ∈ s, Module.finrank (ZMod 2) (Dsel.G.X n) ≤ hW K S₀ 0 + hW K S₀ 1 + hW K S₀ 2 := by
  calc ∑ n ∈ s, Module.finrank (ZMod 2) (Dsel.G.X n)
      = ∑ n ∈ s, hW K S₀ n.toNat := Finset.sum_congr rfl fun n hn => (eG n hn).finrank_eq
    _ ≤ ∑ n ∈ Finset.Icc (0 : ℤ) 2, hW K S₀ n.toNat := Finset.sum_le_sum_of_subset hs
    _ = hW K S₀ 0 + hW K S₀ 1 + hW K S₀ 2 := by
      rw [show Finset.Icc (0 : ℤ) 2 = {0, 1, 2} by decide]
      simp [add_assoc]

/-- A complex with zero differentials. -/
def zeroDiffCx (X : ℤ → ModuleCat.{0} (ZMod 2)) : GCx (ZMod 2) where
  X := X
  d _ _ _ := 0
  d_d _ _ _ _ _ _ := rfl

/-- The zero complex. -/
def zeroCx : GCx (ZMod 2) := zeroDiffCx fun _ => ModuleCat.of (ZMod 2) PUnit

omit [NumberField K] in
/-- **Non-vacuity of `hG_of_residualModel`**: the residual model whose global part is the
cohomology `Hⁿ(G_{K,S₀}, W)` itself (zero differentials) satisfies the identification hypothesis.
PROVED. -/
theorem hG_of_residualModel_nonvacuous (S₀ : Set (HeightOneSpectrum (𝓞 K))) :
    ∃ (Dsel : SelData (ZMod 2)),
      ∀ n ∈ Finset.Icc (0 : ℤ) 2, Nonempty (Dsel.G.X n ≃ₗ[ZMod 2]
        continuousCohomology n.toNat (Wrep K S₀)) :=
  ⟨{ G := zeroDiffCx fun n => (continuousCohomology n.toNat (Wrep K S₀)).toModuleCat
     U := zeroCx
     L := zeroCx
     res := ⟨fun _ _ _ => 0, fun _ _ _ _ _ _ _ _ _ => rfl⟩
     ι := ⟨fun _ _ _ => 0, fun _ _ _ _ _ _ _ _ _ => rfl⟩ },
    fun _ _ => ⟨LinearEquiv.refl _ _⟩⟩

end ZInQ.Contrib.CloudB3RC53.RankCounts
