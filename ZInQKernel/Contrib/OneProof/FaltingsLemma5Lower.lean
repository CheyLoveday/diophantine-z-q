import ZInQKernel.OneProof.H.TailY
import ZInQKernel.Contrib.OneProof.FaltingsLemma5Lower.CotFinal

/-!
# Contributor file: the lower half of Faltings' Lemma 5, `ZInQ.HeightSplit.FaltingsLemma5Lower`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task faltings5-lower, 2026-11-15).

For an isogeny `φ : A → B` over a number field `K` and Néron models `𝒩_A`, `𝒩_B` over `𝓞_K` (the kernel's
`GroupModel`), `h(𝒩_B) ≤ h(𝒩_A) + ½ log deg φ`, from the kernel's definition of `GroupModel.height` (an
infimum over metrizations). Every metrization `M` of `𝒩_A` gives a metrization of `𝒩_B`:
* the Hodge lattice `⋀^g ω_{𝒩_B}` maps into `⋀^g ω_{𝒩_A}` under `f^*` (`f` the Néron extension of `φ`),
  so the finite part of Faltings' formula can only go down (`ZInQ.H5Glue.secIndex_le_of_map`);
* the uniformization is `Φ ≫ f`, with period lattice `Φ⁻¹(ker f(ℂ)) ⊇ Λ_A` of index `#ker f(ℂ) ≤ deg φ`,
  so `covol(Λ_B) = covol(Λ_A)/[Λ_B : Λ_A] ≥ covol(Λ_A)/deg φ` at every complex place
  (`Assembly.lean`, `Lattice.lean`).
The three algebraic inputs are glue statements about `f` (`Reduction.lean`):
* `IsogPtsSurjective` (proved, `Surj.lean`), `IsogKerCard` (proved, `Ker.lean`),
* `IsogCotBijective` (étaleness of `f` at the origin of the generic fibre), proved from Milne's
  quasi-inverse (`CotPts.lean`, `Cot.lean`, `CotTan.lean`, `CotFinal.lean`): a derivation at the origin
  killing `f^*` is a tangent vector `v` of `A` with `v ≫ φ = 1`, hence `v ≫ [d] = 1`, hence `v = 1`
  (`ZInQ.Contrib.AbVarBC.Tangent.eq_one_of_comp_intCast`, characteristic `0`); both cotangent spaces have
  dimension `dim A = dim B` (the kernel's `TangentDim`).

The only hypothesis is the bundle field `HDec.HSyn.OpenAddedLeaves17.milneIsogenyQuasiInverse`
(`AvSplit.MilneIsogenyQuasiInverse`, `ZInQKernel/OneProof/H/TailQ.lean`), a LEAF already on the chain:
Milne, *Abelian varieties* (Cornell–Silverman 1986), Rem. 8.4 (number UNVERIFIED): for an isogeny
`f : A → B` there is `g : B → A` with `g ∘ f = [d]` and `f ∘ g = [d]`, `d ≥ 1`.
-/

namespace GapHeight

/-- **The lower half of Faltings' Lemma 5, given étaleness at the origin** (`IsogCotBijective`). -/
theorem faltingsLemma5Lower_of_cotBijective (h : IsogCotBijective) :
    ZInQ.HeightSplit.FaltingsLemma5Lower :=
  faltingsLemma5Lower_of h isogPtsSurjective isogKerCard

/-- **The lower half of Faltings' Lemma 5** (`ZInQ.HeightSplit.FaltingsLemma5Lower`):
`h(𝒩_B) ≤ h(𝒩_A) + ½ log deg φ` for an isogeny `φ : A → B` over a number field `K` and Néron models
`𝒩_A`, `𝒩_B` over `𝓞_K` (semistability is not used). Hypothesis: the bundle field
`milneIsogenyQuasiInverse` (Milne 1986, Rem. 8.4; LEAF). -/
theorem faltingsLemma5Lower (hM : AvSplit.MilneIsogenyQuasiInverse) :
    ZInQ.HeightSplit.FaltingsLemma5Lower :=
  faltingsLemma5Lower_of_cotBijective (isogCotBijective hM)

end GapHeight
