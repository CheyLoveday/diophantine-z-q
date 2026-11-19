import ZInQKernel.Contrib.CloudB3E2Norm.DualPres
import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassMatch
import ZInQKernel.Contrib.CloudB3E2Norm.H20Paired

/-!
# The paired strict lift for the classes of the actual points

Manuscript `diophantine_zq.tex`, tex 4166–4171 ("The generic paired strict lift satisfies
`j z_S = e_q^c z_{P⊥}`. Conjugation sends `z` to `z⁻¹`, so `e_q^c = e_q`."), tex 3736–3753.

* **`gxClass_step_of_global`** (PROVED): a global identity `g_R = e · g_T + d b_G` of the classes
  of two actual points lifts to the presentation, `[y_R] = e · i([y_T]) + d b` in `C_{T ∪ {p}}¹`
  (the lifts `ux_spec`, `hnorm_changeIncl`).
* **`hlift_actual`** (PROVED): for the transported presentation — the same construction with
  `π⁻¹` (the paired character `θ' = χ_h [π]⁻¹`, `H20Paired`) — and the inverse `Ψ` of the
  orthogonal comparison (`DualPres.OrthComparisonInverse`, the one named input), the classes
  `z_S = ψ_{T ∪ {p}}([y'_R])`, `z_{P⊥} = ψ_T([y'_T])` satisfy lane RC32's `hlift`
  `j z_S = e z_{P⊥} + d b` (`DualPres.hlift_of_transport`) whenever the transported global identity
  holds (for the actual Heegner points: `gx_step_heegner_at` at `π⁻¹`).
* `alphaStage_inv_pi`, **`pointFactor_paired`** (PROVED): `α_{π⁻¹} = α_π⁻¹`, so the transported
  factor `pointFactor a z' z'⁻¹` at `z' = α_{π⁻¹}(Frob_w)` is the original `pointFactor a z z⁻¹`
  (`e_q^c = e_q`); `psiTrivialAt2N_inv`, `thetaOfDelta_inv` (PROVED): the hypotheses of the
  construction for `π` give those for `π⁻¹`.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps ZInQ.Manuscript.RC.Limits
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.Central (pointFactor)
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Contrib.CloudB3RC53.PairedFunctional
open NumberField IsDedekindDomain TensorProduct
open scoped Classical in

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass groupRingTop ptSAction

set_option linter.unusedSectionVars false

section Lift

attribute [local instance] mcoefModuleK

variable {K : Type} [Field K] [NumberField K] {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h01 : S₀ ⊆ S₁) (h1 : S₁ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
  [NeZero i] (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  (hFull : FullTorsion K S₀ W (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)
  [IsOpenKer (alphaShap s hs hs0 π)] [IsOpenKer (alphaStage i s hs hs0 π ψ)]
  (P : Set (HeightOneSpectrum (𝓞 K))) (hψ : Function.Injective ψ) (hΨ : PsiTrivialAt2N i π ψ P)
  (k : Type) [CommRing k] [TopologicalSpace k] [DiscreteTopology k] [StageIsoA k i]
  [DecidableEq (Places K S₀)] {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)
  (hw : ∀ j, (place j).1 ∉ S₀)
  [∀ j, ContinuousSMul (GUr K (place j).1)
    (urRep (MonoidAlgebra ℤ Δ) (shapMod₀ W i s hs hs0 π) (newPlace (place j) (hw j))).V]
  [∀ j, ContinuousSMul (GUr K (place j).1)
    (urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j))).V]
  (EU : ∀ j, SplitInclusion
    (genuineUq K S k (place j)
      (urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j))))
    (genuineLq K S k (MinS hS W i (alphaStage i s hs hs0 π ψ)) (place j)))
  (hE : ∀ j, (EU j).i = genuineιq K S k (MinS hS W i (alphaStage i s hs hs0 π ψ)) (place j)
    (urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
    (urId hS k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
    (urId_compat hS k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (place j) (hw j)))
  {Tp : Finset ι} {p : ι}

  (AT : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tp)
  (AR : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place (insert p Tp))

attribute [local instance] mcoefModuleK

include hψ hE in
/-- **A global identity of the classes lifts to the presentation** (PROVED). -/
theorem gxClass_step_of_global (e : k)
    (bG : (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).X 0)
    (hG : gx hS h01 h1 W i s hs hs0 hFull π ψ P k place AR =
      e • gx hS h01 h1 W i s hs hs0 hFull π ψ P k place AT +
        (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).d 0 1 rfl bG) :
    ∃ b : (suppCxS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
      (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
      (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
      EU (insert p Tp)).X 0,
      gxClass hS h01 h1 W i s hs hs0 hFull π ψ P hψ hΨ k place hw EU hE AR =
        e • (suppInclS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
      (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
      (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
      EU Tp p).f 1 1 rfl
            (gxClass hS h01 h1 W i s hs hs0 hFull π ψ P hψ hΨ k place hw EU hE AT) +
          (suppCxS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
      (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
      (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
      EU (insert p Tp)).d 0 1 rfl b := by
  have hsEU : ∀ j, Function.Surjective ((EU j).i.f 0 0 rfl) := fun j => by
    rw [hE j]
    exact genuineιq_surjective₀ (place j) _ _ _ Function.surjective_id
  obtain ⟨bU, hbU⟩ := exists_presLift₀ K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
    (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
    (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
    EU (insert p Tp) (stageCondK_surjective₀ hS W i s hs hs0 hFull π ψ P hΨ k) hsEU
    ((resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place)
      (MinS hS W i (alphaStage i s hs hs0 π ψ))).f 0 0 rfl bG)
  exact ⟨((bG, bU, 0) : selT (suppDataS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
      (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
      (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
      EU (insert p Tp)) 0),
    hnorm_changeIncl (presCondInclS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
      (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
      (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
      EU Tp p) _ _ _ _ _ bG bU
      (presι_injective K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
        (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
        (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ))
          (newPlace (place j) (hw j))) EU (insert p Tp)
        (stageCondK_injective hS W i s hs hs0 hFull π ψ P hΨ k))
      (ux_spec hS h01 h1 W i s hs hs0 hFull π ψ P hψ hΨ k place hw EU hE AR)
      (ux_spec hS h01 h1 W i s hs hs0 hFull π ψ P hψ hΨ k place hw EU hE AT) hG hbU⟩

include hψ hE in
/-- **The paired strict lift for the classes of the actual points** (PROVED from the named input
`Ψ`, tex 3740–3745, 4166–4171): on the presentation of this construction (for the paired side,
the construction at `π⁻¹`), a global identity `g_R = e · g_T + d b_G` gives
`j(ψ_{T ∪ {p}}[y_R]) = e · ψ_T[y_T] + d b` in the dual complex `C_{T⊥}` — the field `hlift` of
lane RC32's `StepRetention` for `DPp = dsuppDataS T`, `fS = dfS T p`. -/
theorem hlift_actual (hp : p ∉ Tp)
    (Δ' : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K S v.1) (MinS hS W i (alphaStage i s hs hs0 π ψ)))
    (Ψ : DualPres.OrthComparisonInverse K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ)) Δ'
      (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
      (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
      EU) (e : k)
    (bG : (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).X 0)
    (hG : gx hS h01 h1 W i s hs hs0 hFull π ψ P k place AR =
      e • gx hS h01 h1 W i s hs hs0 hFull π ψ P k place AT +
        (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).d 0 1 rfl bG) :
    ∃ b : (selCx (DualPres.dsuppDataS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ)) Δ' place
        (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
        EU Tp)).X 0,
      (ZInQ.Contrib.CloudB3RC53.SelmerDuality.changeMap
          (DualPres.dsuppDataS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ)) Δ' place
            (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ))
              (newPlace (place j) (hw j))) EU Tp)
          (DualPres.dfS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ)) Δ' place
            (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ))
              (newPlace (place j) (hw j))) EU Tp p)).f 1 1 rfl
          (Ψ.ψ (insert p Tp) 1
            (gxClass hS h01 h1 W i s hs hs0 hFull π ψ P hψ hΨ k place hw EU hE AR)) =
        e • Ψ.ψ Tp 1 (gxClass hS h01 h1 W i s hs hs0 hFull π ψ P hψ hΨ k place hw EU hE AT) +
          (selCx (DualPres.dsuppDataS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ)) Δ' place
            (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ))
              (newPlace (place j) (hw j))) EU Tp)).d 0 1 rfl b := by
  obtain ⟨b', hb'⟩ := gxClass_step_of_global hS h01 h1 W i s hs hs0 hFull π ψ P hψ hΨ k place hw
    EU hE AT AR e bG hG
  exact ⟨_, DualPres.hlift_stepRetention Ψ hp _ _ e b' hb'⟩

end Lift

/-! ### The paired character and its factor -/

section Paired

variable {K : Type} [Field K] [NumberField K] {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (i : ℕ) (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  {Δ : Type} [CommGroup Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)

/-- **`α_{π⁻¹} = α_π⁻¹`** (PROVED; `χ_h = ±1`). -/
theorem alphaStage_inv_pi (g : GKS K S₀) :
    alphaStage i s hs hs0 π⁻¹ ψ g = (alphaStage i s hs hs0 π ψ g)⁻¹ := by
  simp only [alphaStage, charMul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, map_inv]
  rw [mul_inv (intUnitsTo (Acoef i) (quadChar s hs hs0 g)) (ψ (π g)),
    ← map_inv (intUnitsTo (Acoef i)), Int.units_inv_eq_self]

/-- **The paired factor is the original one** (PROVED; tex 4171, `e_q^c = e_q`): at
`z' = α_{π⁻¹}(g)`, `pointFactor a z' z'⁻¹ = pointFactor a z z⁻¹` with `z = α_π(g)`. -/
theorem pointFactor_paired (k : Type) [CommRing k] [StageIsoA k i] (a : k) (g : GKS K S₀) :
    pointFactor a ((eK k i).symm (alphaStage i s hs hs0 π⁻¹ ψ g : Acoef i))
        ((eK k i).symm (((alphaStage i s hs hs0 π⁻¹ ψ g)⁻¹ : (Acoef i)ˣ) : Acoef i)) =
      pointFactor a ((eK k i).symm (alphaStage i s hs hs0 π ψ g : Acoef i))
        ((eK k i).symm (((alphaStage i s hs hs0 π ψ g)⁻¹ : (Acoef i)ˣ) : Acoef i)) := by
  rw [alphaStage_inv_pi, inv_inv, pointFactor_swap]

/-- `PsiTrivialAt2N` for `π` gives it for `π⁻¹` (PROVED). -/
theorem psiTrivialAt2N_inv {P : Set (HeightOneSpectrum (𝓞 K))}
    (hΨ : PsiTrivialAt2N i π ψ P) : PsiTrivialAt2N i π⁻¹ ψ P := fun v hv σ => by
  rw [MonoidHom.inv_apply, map_inv, hΨ v hv σ, inv_one]

/-- `ThetaOfDelta` for `π` gives it for `π⁻¹` (PROVED; the two characters have the same kernel).
-/
theorem thetaOfDelta_inv [Finite Δ] (hS : S₀ ⊆ S) (h1 : S₁ ⊆ S) {f : ℕ} [NeZero f]
    (ht : ThetaOfDelta hS h1 s hs hs0 π f) : ThetaOfDelta hS h1 s hs hs0 π⁻¹ f := fun g hg => by
  have := ht g hg
  change alphaShap s hs hs0 π⁻¹ (inflMap K hS g) = 1
  rw [alphaShap_inv_pi]
  change alphaShap s hs hs0 π (inflMap K hS g) = 1 at this
  rw [this, inv_one]

end Paired

end ZInQ.Contrib.CloudB3E2.NormCochain
