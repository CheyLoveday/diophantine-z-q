import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TauCetiComparison
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Instances
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.ConeModel

/-!
# Genuine instantiations, part 4: RankCounts' `hG` from the genuine global complex

Manuscript `diophantine_zq.tex`, tex 4521–4531 (`h⁰, h¹, h²` of `G_{K,S₀}` with coefficients
`W = 𝔽₂²`) and 4593–4597 (the finite free model of the Selmer cone).

`RankCounts.hG_of_residualModel` takes the identification `eG : Dsel.G.X n ≃ Hⁿ(G_{K,S₀}, W)`
(`n ∈ s ⊆ [0, 2]`) of the global part of the cone model as a hypothesis. With the other team's
genuine complexes, the global part of `galoisSelData K S₀ 𝔽₂ W Δ` is
`C^•_cont(G_{K,S₀}, W)`, and its cohomology `genH K S₀ n` is identified with Mathlib's
`continuousCohomology n (Wrep K S₀)` in degrees `n ≤ 2` (`genHEquiv`): degree `0` by
`contH0AddEquiv` and `ContinuousCohomology.zeroIso`, degrees `1`, `2` by `contH1AddEquiv`,
`contH2AddEquiv` and Tau Ceti's comparisons. Hence `hG_of_genuineModel`: `hG` holds for any residual
model whose global part is degreewise isomorphic to the genuine global cohomology (over the field
`𝔽₂` a bounded complex is homotopy equivalent to its cohomology); non-vacuity:
`hG_of_genuineModel_nonvacuous`.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open NumberField IsDedekindDomain CategoryTheory TauCeti.ContCohomology
  ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.RankCounts

variable (K : Type) [Field K] [NumberField K] (S₀ : Set (HeightOneSpectrum (𝓞 K)))

/-- The residual coefficient module `W = 𝔽₂²` with trivial `G_{K,S₀}`-action, for the genuine
complexes. -/
abbrev Wgen : Type := TrivMod (GKS K S₀) (ZMod 2 × ZMod 2)

/-- **`Hⁿ` of the genuine global complex** `C^•_cont(G_{K,S₀}, W)` (the global part of
`galoisSelData K S₀ 𝔽₂ W Δ`). -/
abbrev genH (n : ℕ) : ModuleCat (ZMod 2) := contCohomology (ZMod 2) (GKS K S₀) (Wgen K S₀) n

/-- `G_{K,S₀}` and its frozen synonym. -/
def gksEquiv : GaloisGroupS K S₀ ≃ₜ* GKS K S₀ := ContinuousMulEquiv.refl (GaloisGroupS K S₀)

attribute [local instance] TopRep.distribMulAction

/-- The trivial action is continuous. -/
theorem continuousSMul_Wrep :
    letI := TopRep.distribMulAction (Wrep K S₀)
    ContinuousSMul (GaloisGroupS K S₀) (Wrep K S₀).V :=
  letI := TopRep.distribMulAction (Wrep K S₀)
  ⟨continuous_snd⟩

/-- The identity `W ≃ W` between the two models of the coefficients. -/
def wEquiv : Wgen K S₀ ≃+ (Wrep K S₀).V := AddEquiv.refl (ZMod 2 × ZMod 2)

/-- Degree `1`: the genuine `H¹(G_{K,S₀}, W)` (continuous inhomogeneous cochains) is Mathlib's
`continuousCohomology 1 (Wrep K S₀)`, through the other team's `contH1AddEquiv` and Tau Ceti's
comparison. -/
def genH1Equiv : genH K S₀ 1 ≃+ continuousCohomology 1 (Wrep K S₀) := by
  letI := TopRep.distribMulAction (Wrep K S₀)
  haveI : ContinuousSMul (GaloisGroupS K S₀) (Wrep K S₀).V := continuousSMul_Wrep K S₀
  exact (contH1AddEquiv (ZMod 2) (GKS K S₀) (Wgen K S₀)).trans
    ((AddEquiv.refl _ : H1 (GKS K S₀) (Wgen K S₀) ≃+ H1 (GaloisGroupS K S₀) (Wrep K S₀).V).trans
      (Wrep K S₀).explicitH1AddEquivContinuousCohomologyOfDiscrete)

set_option synthInstance.maxHeartbeats 400000 in
/-- `G_{K,S₀}` is locally compact (compact Hausdorff). -/
theorem locallyCompactSpace_GS : LocallyCompactSpace (GaloisGroupS K S₀) :=
  have : T2Space (GaloisGroupS K S₀) := krullTopology_t2
  inferInstance

/-- Degree `2`: the genuine `H²(G_{K,S₀}, W)` is Mathlib's `continuousCohomology 2 (Wrep K S₀)`. -/
def genH2Equiv : genH K S₀ 2 ≃+ continuousCohomology 2 (Wrep K S₀) := by
  letI := TopRep.distribMulAction (Wrep K S₀)
  haveI : ContinuousSMul (GaloisGroupS K S₀) (Wrep K S₀).V := continuousSMul_Wrep K S₀
  haveI := locallyCompactSpace_GS K S₀
  exact (contH2AddEquiv (ZMod 2) (GKS K S₀) (Wgen K S₀)).trans
    ((AddEquiv.refl _ : H2 (GKS K S₀) (Wgen K S₀) ≃+ H2 (GaloisGroupS K S₀) (Wrep K S₀).V).trans
      (Wrep K S₀).explicitH2AddEquivContinuousCohomologyOfDiscrete)

/-- `W^{G}` in the two models. -/
def h0Bridge : H0 (GKS K S₀) (Wgen K S₀) ≃+ (Wrep K S₀).ρ.invariants where
  toFun x := ⟨x.1, fun _ => rfl⟩
  invFun x := ⟨x.1, fun _ => rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Degree `0`: the genuine `H⁰(G_{K,S₀}, W) = W^G` is Mathlib's `continuousCohomology 0`. -/
def genH0Equiv : genH K S₀ 0 ≃+ continuousCohomology 0 (Wrep K S₀) :=
  ((contH0AddEquiv (ZMod 2) (GKS K S₀) (Wgen K S₀)).trans (h0Bridge K S₀)).trans
    (ContinuousCohomology.zeroIso (Wrep K S₀)).toContinuousLinearEquiv.symm.toLinearEquiv.toAddEquiv

/-- The additive comparisons are `𝔽₂`-linear (every additive map of `𝔽₂`-modules is). -/
def toLin {A B : Type} [AddCommGroup A] [Module (ZMod 2) A] [AddCommGroup B] [Module (ZMod 2) B]
    (e : A ≃+ B) : A ≃ₗ[ZMod 2] B :=
  LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap 2) e.bijective

/-- **The genuine global cohomology is Mathlib's, in degrees `n ≤ 2`** (tex 4521–4531): for
`n ≤ 2`, `Hⁿ(C^•_cont(G_{K,S₀}, W)) ≃ₗ[𝔽₂] continuousCohomology n (Wrep K S₀)`. PROVED. -/
def genHEquiv : ∀ n : ℕ, n ≤ 2 → (genH K S₀ n ≃ₗ[ZMod 2] continuousCohomology n (Wrep K S₀))
  | 0, _ => toLin (genH0Equiv K S₀)
  | 1, _ => toLin (genH1Equiv K S₀)
  | 2, _ => toLin (genH2Equiv K S₀)
  | n + 3, h => absurd h (by omega)

/-- **RankCounts' `hG` from a residual model of the genuine global complex** (tex 4593–4597): if
the global part of the Selmer-cone model is degreewise `𝔽₂`-isomorphic, in a range `s ⊆ [0, 2]`, to
the cohomology `Hⁿ(C^•_cont(G_{K,S₀}, W))` of the global part of the genuine Selmer data
`galoisSelData K S₀ 𝔽₂ W Δ` (the residual minimal model: over a field a bounded complex is homotopy
equivalent to its cohomology), then its total rank is at most `h⁰ + h¹ + h²`. The identification
hypothesis `eG` of `hG_of_residualModel` is PROVED from the genuine data by `genHEquiv`. -/
theorem hG_of_genuineModel (Dsel : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData (ZMod 2))
    (s : Finset ℤ) (hs : s ⊆ Finset.Icc 0 2)
    (eG : ∀ n ∈ s, Dsel.G.X n ≃ₗ[ZMod 2] genH K S₀ n.toNat) :
    ∑ n ∈ s, Module.finrank (ZMod 2) (Dsel.G.X n) ≤ hW K S₀ 0 + hW K S₀ 1 + hW K S₀ 2 :=
  hG_of_residualModel K S₀ Dsel s hs fun n hn =>
    (eG n hn).trans (genHEquiv K S₀ n.toNat (by
      have := Finset.mem_Icc.mp (hs hn)
      omega))

/-- **Non-vacuity of `hG_of_genuineModel`**: the residual model whose global part is the genuine
cohomology itself (zero differentials). PROVED. -/
theorem hG_of_genuineModel_nonvacuous :
    ∃ Dsel : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData (ZMod 2),
      ∀ n ∈ Finset.Icc (0 : ℤ) 2, Nonempty (Dsel.G.X n ≃ₗ[ZMod 2] genH K S₀ n.toNat) :=
  ⟨{ G := zeroDiffCx fun n => genH K S₀ n.toNat
     U := RankCounts.zeroCx
     L := RankCounts.zeroCx
     res := ⟨fun _ _ _ => 0, fun _ _ _ _ _ _ _ _ _ => rfl⟩
     ι := ⟨fun _ _ _ => 0, fun _ _ _ _ _ _ _ _ _ => rfl⟩ },
    fun _ _ => ⟨LinearEquiv.refl _ _⟩⟩

end ZInQ.Contrib.CloudB3RC53.GenuineInst
