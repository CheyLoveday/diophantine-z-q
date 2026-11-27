import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassMatch

/-!
# The conditions on the character grow with the conductor

Manuscript `diophantine_zq.tex`, tex 2847–2855 (the finite character `θ` of `Δ_f`).

`H20PresClassMatch.ThetaOfDelta f` and its parts `QuadOfDelta f`, `PiOfDelta f` say that `χ_h`,
`π` are trivial on the elements fixing the ring class field `H_f`. For `f ∣ f'`, `H_f ⊆ H_{f'}`
(`RingClassMono`), so an element fixing `H_{f'}` fixes `H_f`, and each condition at `f` gives the
condition at `f'` (`quadOfDelta_mono`, `piOfDelta_mono`, `thetaOfDelta_mono`, PROVED). Thus the
moving part, available at the moving conductor `r`, and the quadratic part, at a conductor
containing the primes of `h`, combine at one conductor divisible by both.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.RankCounts
open NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.CST
open TauCeti.ClassFieldTheory

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [NumberField K] {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h1 : S₁ ⊆ S) (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h)
  (hs0 : s ≠ 0) {Δ : Type} [CommGroup Δ] (π : GKS K S₀ →* Δ)

/-- An element fixing `H_{f'}` fixes `H_f` for `f ∣ f'`. Kind: PROVED. -/
theorem fixes_ringClass_mono {f f' : ℕ} [NeZero f] [NeZero f'] (hff : f ∣ f') (g : GKS K S)
    (hg : ∀ z : KS K S₁,
      (z : AlgebraicClosure K) ∈ toAlgClosure (ringClassField (conductorOrder K f')) →
        galS K S₁ (inflMap K h1 g) z = z) :
    ∀ z : KS K S₁,
      (z : AlgebraicClosure K) ∈ toAlgClosure (ringClassField (conductorOrder K f)) →
        galS K S₁ (inflMap K h1 g) z = z := fun z hz =>
  hg z (IntermediateField.map_mono _ (ringClassField_mono (conductorOrder_le_of_dvd hff)) hz)

/-- `QuadOfDelta` grows with the conductor. Kind: PROVED. -/
theorem quadOfDelta_mono {f f' : ℕ} [NeZero f] [NeZero f'] (hff : f ∣ f')
    (hq : QuadOfDelta hS h1 s hs hs0 f) : QuadOfDelta hS h1 s hs hs0 f' := fun g hg =>
  hq g (fixes_ringClass_mono h1 hff g hg)

/-- `PiOfDelta` grows with the conductor. Kind: PROVED. -/
theorem piOfDelta_mono {f f' : ℕ} [NeZero f] [NeZero f'] (hff : f ∣ f')
    (hp : PiOfDelta hS h1 π f) : PiOfDelta hS h1 π f' := fun g hg =>
  hp g (fixes_ringClass_mono h1 hff g hg)

/-- `ThetaOfDelta` grows with the conductor. Kind: PROVED. -/
theorem thetaOfDelta_mono {f f' : ℕ} [NeZero f] [NeZero f'] (hff : f ∣ f')
    (ht : ThetaOfDelta hS h1 s hs hs0 π f) : ThetaOfDelta hS h1 s hs hs0 π f' := fun g hg =>
  ht g (fixes_ringClass_mono h1 hff g hg)

/-- **`ThetaOfDelta` at a common multiple** (PROVED): the quadratic part at `f₁` and the moving
part at `f₂` give `ThetaOfDelta` at every `f` with `f₁ ∣ f` and `f₂ ∣ f`. -/
theorem thetaOfDelta_of_parts [Finite Δ] {f₁ f₂ f : ℕ} [NeZero f₁] [NeZero f₂] [NeZero f]
    (h₁ : f₁ ∣ f) (h₂ : f₂ ∣ f) (hq : QuadOfDelta hS h1 s hs hs0 f₁)
    (hp : PiOfDelta hS h1 π f₂) : ThetaOfDelta hS h1 s hs hs0 π f :=
  thetaOfDelta_of hS h1 s hs hs0 π f (quadOfDelta_mono hS h1 s hs hs0 h₁ hq)
    (piOfDelta_mono hS h1 π h₂ hp)

end ZInQ.Contrib.CloudB3E2.NormCochain
