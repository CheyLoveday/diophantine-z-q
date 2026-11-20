import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.GlobalCounts

/-!
# Genuine instantiations, part 5: the local terms of `hL` from the genuine local complexes

Manuscript `diophantine_zq.tex`, tex 4544–4573 (the local terms `(h⁰, h¹, h²)(K_w, W)` of the
Selmer cone, for trivial `W`).

The input `hL` of RC6's counts bounds the ranks of the local parts `U`, `L` of the cone model by
the place costs `∑ h^a(U_w) + ∑ h^a(K_w, W)` (`PlaceData`, `placeEntry`). This file supplies the
genuine side of the local terms:

* `trivH0Equiv`, `trivH1Equiv`, `trivH2Equiv`, `finrank_trivH`: for any topological group `G` and
  a discrete `𝔽₂`-module `V` with trivial action, the genuine continuous cohomology
  `contCohomology 𝔽₂ G V` (the other team's continuous cochains) is Mathlib's
  `continuousCohomology n (trivialRepS G V)` in degrees `n ≤ 2` (`contH0/1/2AddEquiv` and Tau Ceti);
* `genLocH`, `finrank_genLocH`: the cohomology of the genuine local complex
  `C^•_cont(G_{K_v}, V)` of `galoisSelData` at `v` (`V` with `G_{K_v}` acting through
  `p_v : G_{K_v} → G_{K,S}`) has the dimensions `localH0`, `localH1`, `localH2` of RC6's place
  entries (`continuousCohomology n (trivialGaloisRep K_v V)`).

The rest of `hL` (summing these over the places above the charged primes with RC6's `placesList`,
and the condition terms `∑ h^a(U_w)` for the genuine conditions) is not done here.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open NumberField IsDedekindDomain CategoryTheory TauCeti.ContCohomology
  ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.RankCounts

attribute [local instance] TopRep.distribMulAction

section Generic

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [TopologicalSpace V] [DiscreteTopology V]
  [IsTopologicalAddGroup V] [ContinuousSMul (ZMod 2) V]

/-- `V` with the trivial `G`-action as a genuine module, and its cohomology. -/
abbrev trivH (n : ℕ) : ModuleCat (ZMod 2) := contCohomology (ZMod 2) G (TrivMod G V) n

/-- The trivial action is continuous. -/
theorem continuousSMul_triv :
    letI := TopRep.distribMulAction (trivialRepS G V)
    ContinuousSMul G (trivialRepS G V).V :=
  letI := TopRep.distribMulAction (trivialRepS G V)
  ⟨continuous_snd⟩

/-- `H⁰` of the trivial module in the two models. -/
def trivH0Equiv : trivH G V 0 ≃+ continuousCohomology 0 (trivialRepS G V) :=
  ((contH0AddEquiv (ZMod 2) G (TrivMod G V)).trans
    ({ toFun := fun x => ⟨x.1, fun _ => rfl⟩
       invFun := fun x => ⟨x.1, fun _ => rfl⟩
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl
       map_add' := fun _ _ => rfl } :
      H0 G (TrivMod G V) ≃+ (trivialRepS G V).ρ.invariants)).trans
    (ContinuousCohomology.zeroIso (trivialRepS G V)).toContinuousLinearEquiv.symm.toLinearEquiv.toAddEquiv

/-- `H¹` of the trivial module in the two models. -/
def trivH1Equiv : trivH G V 1 ≃+ continuousCohomology 1 (trivialRepS G V) := by
  letI := TopRep.distribMulAction (trivialRepS G V)
  haveI : ContinuousSMul G (trivialRepS G V).V := continuousSMul_triv G V
  exact (contH1AddEquiv (ZMod 2) G (TrivMod G V)).trans
    ((AddEquiv.refl _ : H1 G (TrivMod G V) ≃+ H1 G (trivialRepS G V).V).trans
      (trivialRepS G V).explicitH1AddEquivContinuousCohomologyOfDiscrete)

/-- `H²` of the trivial module in the two models (`G` locally compact). -/
def trivH2Equiv [LocallyCompactSpace G] : trivH G V 2 ≃+ continuousCohomology 2 (trivialRepS G V) := by
  letI := TopRep.distribMulAction (trivialRepS G V)
  haveI : ContinuousSMul G (trivialRepS G V).V := continuousSMul_triv G V
  exact (contH2AddEquiv (ZMod 2) G (TrivMod G V)).trans
    ((AddEquiv.refl _ : H2 G (TrivMod G V) ≃+ H2 G (trivialRepS G V).V).trans
      (trivialRepS G V).explicitH2AddEquivContinuousCohomologyOfDiscrete)

/-- **Genuine and Mathlib cohomology of a trivial module agree in degrees `≤ 2`** (dimensions). -/
theorem finrank_trivH [LocallyCompactSpace G] (n : ℕ) (hn : n ≤ 2) :
    Module.finrank (ZMod 2) (trivH G V n) =
      Module.finrank (ZMod 2) (continuousCohomology n (trivialRepS G V)) := by
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl
  · exact (toLin (trivH0Equiv G V)).finrank_eq
  · exact (toLin (trivH1Equiv G V)).finrank_eq
  · exact (toLin (trivH2Equiv G V)).finrank_eq

end Generic

section Local

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [TopologicalSpace V] [DiscreteTopology V]
  [IsTopologicalAddGroup V] [ContinuousSMul (ZMod 2) V]

/-- The module of the genuine local complex at `v ∈ S` for trivial coefficients `V`:
`V` with `G_{K_v}` acting through `p_v : G_{K_v} → G_{K,S}`. -/
abbrev locMod (v : HeightOneSpectrum (𝓞 K)) : Type := ResMod (locMap K S v) (TrivMod (GKS K S) V)

/-- **`Hⁿ` of the genuine local complex** `C^•_cont(G_{K_v}, V)` (a summand of the local part of
`galoisSelData K S 𝔽₂ V Δ`). -/
abbrev genLocH (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) : ModuleCat (ZMod 2) :=
  contCohomology (ZMod 2) (Gloc K v) (locMod K S V v) n

set_option synthInstance.maxHeartbeats 400000 in
/-- `G_{K_v}` is locally compact. -/
theorem locallyCompactSpace_Gloc (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (Gloc K v) :=
  have : T2Space (Gloc K v) := krullTopology_t2
  inferInstance

/-- The genuine local module and the trivial module agree (the action through `p_v` is trivial). -/
def locH1Bridge (v : HeightOneSpectrum (𝓞 K)) :
    H1 (Gloc K v) (locMod K S V v) ≃+ H1 (Gloc K v) (TrivMod (Gloc K v) V) := AddEquiv.refl _

/-- `H²` of the genuine local module is that of the trivial module. -/
def locH2Bridge (v : HeightOneSpectrum (𝓞 K)) :
    H2 (Gloc K v) (locMod K S V v) ≃+ H2 (Gloc K v) (TrivMod (Gloc K v) V) := AddEquiv.refl _

/-- `H⁰` of the genuine local module is that of the trivial module. -/
def locH0Bridge (v : HeightOneSpectrum (𝓞 K)) :
    H0 (Gloc K v) (locMod K S V v) ≃+ H0 (Gloc K v) (TrivMod (Gloc K v) V) where
  toFun x := ⟨x.1, fun _ => rfl⟩
  invFun x := ⟨x.1, fun _ => rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- **The genuine local cohomology has the dimensions of RC6's local entries** (`placeEntry`'s
`localH0`, `localH1`, `localH2`, Mathlib's `continuousCohomology n (trivialGaloisRep K_v V)`), in
degrees `n ≤ 2`. PROVED. -/
theorem finrank_genLocH (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : n ≤ 2) :
    Module.finrank (ZMod 2) (genLocH K S V v n) =
      Module.finrank (ZMod 2) (continuousCohomology n
        (ZInQ.Manuscript.RC.Limits.trivialGaloisRep (v.adicCompletion K) V)) := by
  have := locallyCompactSpace_Gloc K v
  rw [← finrank_trivH (Gloc K v) V n hn]
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl
  · exact (toLin (((contH0AddEquiv (ZMod 2) (Gloc K v) (locMod K S V v)).trans
      (locH0Bridge K S V v)).trans (contH0AddEquiv (ZMod 2) (Gloc K v) (TrivMod (Gloc K v) V)).symm)).finrank_eq
  · exact (toLin (((contH1AddEquiv (ZMod 2) (Gloc K v) (locMod K S V v)).trans
      (locH1Bridge K S V v)).trans (contH1AddEquiv (ZMod 2) (Gloc K v) (TrivMod (Gloc K v) V)).symm)).finrank_eq
  · exact (toLin (((contH2AddEquiv (ZMod 2) (Gloc K v) (locMod K S V v)).trans
      (locH2Bridge K S V v)).trans (contH2AddEquiv (ZMod 2) (Gloc K v) (TrivMod (Gloc K v) V)).symm)).finrank_eq

end Local

end ZInQ.Contrib.CloudB3RC53.GenuineInst
