import ZInQKernel.Contrib.CloudB3E2Norm.H20ThetaMono
import ZInQKernel.Contrib.CloudB3E1RingClass.MovingPi

/-!
# The moving part of the character condition from lane E1's moving character

Manuscript `diophantine_zq.tex`, tex 2847–2855, 3500–3506.

Lane E1's `movingPsi_genuine_pi` ends with the clause that the moving character
`movingCharS i ξ` is trivial on the elements fixing the ring class field `H_r` of the moving
conductor `r` (for every `S' ⊇ C.Sr r` and `S₁ ⊆ S'` containing the primes of `r`).
**`piOfDelta_of_moving`** (PROVED): that clause gives `PiOfDelta f` at every conductor `f` with
`r ∣ f` (`piOfDelta_mono`); with `thetaOfDelta_of_parts` the condition `ThetaOfDelta f` then
reduces to its quadratic part.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.RankCounts
open NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.CST
open TauCeti.ClassFieldTheory

/-- **`PiOfDelta f` from lane E1's factorisation clause** (PROVED): for `r ∣ f` and `S₁`
containing the primes of `r`, the clause of `movingPsi_genuine_pi` (here for any character `π`
of `G_{K,S₀}`) gives `PiOfDelta f`. -/
theorem piOfDelta_of_moving {K : Type} [Field K] [NumberField K]
    {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) (h1 : S₁ ⊆ S) {Δ : Type}
    [CommGroup Δ] (π : GKS K S₀ →* Δ) {r f : ℕ} [NeZero r] [NeZero f] (hrf : r ∣ f)
    (hr1 : ∀ v : HeightOneSpectrum (𝓞 K), ((r : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S₁)
    (hclause : ∀ [NeZero r] {S' S₁ : Set (HeightOneSpectrum (𝓞 K))} (hS' : S₀ ⊆ S')
      (h1 : S₁ ⊆ S'),
      (∀ v : HeightOneSpectrum (𝓞 K), ((r : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S₁) →
      ∀ g : GKS K S', (∀ z : KS K S₁,
          (z : AlgebraicClosure K) ∈ toAlgClosure (ringClassField (conductorOrder K r)) →
          galS K S₁ (inflMap K h1 g) z = z) →
        π (inflMap K hS' g) = 1) :
    PiOfDelta hS h1 π f :=
  piOfDelta_mono hS h1 π hrf fun g hg => hclause hS h1 hr1 g hg

end ZInQ.Contrib.CloudB3E2.NormCochain
