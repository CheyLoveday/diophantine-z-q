import ZInQKernel.Contrib.CloudB3E2Norm.CentralSpec

/-!
# The local conditions of the central specialization, and (4.5) on the Selmer cones

Manuscript `diophantine_zq.tex`, tex 3911–3915: "The equality in global cohomology lifts to the
Selmer cone because the local degree-zero maps are onto and the degree-one maps inject."

* **New places** (PROVED): `loc_infl_eq_urFactor` — a cochain of `G_{K,S'}` inflated to
  `G_{K,S}` and restricted to the decomposition group at `w ∉ S'` factors through the unramified
  quotient: it is `c ∘ urFactor ∘ urRes`. So the central cochains (of `G_{K,S_C}`) land in the
  unramified conditions of the presentation at its new places `w ∉ S_C`.
* **Old places**: the level-`i` coordinate of the `2`-adic local Kummer cocycle of `C_K` is the
  level-`i` Kummer cocycle of the same local point (`compTors_tateKummerFunOf`, in the tree). Its
  read-out into the presentation's Kummer condition `kummerAt (localTwist W h v) (2^i)` at `t = 0`
  is the named field `hκU` of `CentralConeComparison` (the local analogue of `hpush`/`hred`); at
  `v ∉ P` the presentation's condition is the full one.
* **`CentralConeComparison`** (definition; GLUE): `CentralStageComparison` with the target's local
  cochains `ZL` and local condition `ZU`, the injective degree-one inclusion `ιZ` (tex 3914), the
  localization `locZ`, the read-outs `specL`/`specU` of the presentation's local terms commuting
  with `resS` and the condition inclusions, and `hκU`.
* `CentralConeComparison.locZ_red_kummer` (PROVED): the localized central Kummer class is the
  read-out of the local twisted Kummer cocycles.
* **`central45_cone`** (PROVED from it, `ux_spec` and `central45_global`): the local-condition
  components satisfy `ιZ(specU(u_R) − m · u_κ) = locZ(dZ(…))` — (4.5) on the Selmer cones, at a
  stage, with `m = a_r − 2χ_h(r)`.

Kinds: definitions, GLUE and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps ZInQ.Manuscript.RC.Limits
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Contrib.CloudB3RC53.PairedFunctional
open NumberField IsDedekindDomain TensorProduct WeierstrassCurve

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass groupRingTop ptSAction

set_option linter.unusedSectionVars false

/-! ### New places: inflated cochains are unramified -/

section NewPlaces

variable {K : Type} [Field K] [NumberField K] {S S' : Set (HeightOneSpectrum (𝓞 K))}

/-- **Inflated cochains are unramified at the new places** (PROVED): for `S' ⊆ S` and
`q ∈ S − S'`, a cochain `c` of `G_{K,S'}` inflated to `G_{K,S}` and restricted along the
decomposition map at `q` is `c ∘ urFactor ∘ urRes`. -/
theorem loc_infl_eq_urFactor (h : S' ⊆ S) (q : NewPlaces K S' S) {M : Type} {n : ℕ}
    (c : (Fin n → GKS K S') → M) :
    (fun σ : Fin n → Gloc K q.1 => c (fun j => inflMap K h (locMap K S q.1 (σ j)))) =
      fun σ => c (fun j => urFactor K q (urRes K q.1 (σ j))) := by
  funext σ
  congr 1
  funext j
  rw [locMap_compat K h q.1 (σ j), urFactor_spec K q (σ j)]

end NewPlaces

/-! ### The cone comparison and (4.5) on the Selmer cones -/

section Cone

open ZInQ.Manuscript.RC.Central (pointFactor)
open ZInQ.Manuscript.RC.CalPoint (IsGlobalDivTower globalKummerCochain)
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (centralCurve)

attribute [local instance] mcoefModuleK

variable {K : Type} [Field K] [NumberField K] [DecidableEq K]
  {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
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
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : GenuineKummerData K E₀ hZ)

/-- **The comparison on the Selmer cones** (tex 3911–3915; GLUE): the global comparison
`CentralStageComparison` together with

* the target's degree-one local cochains `ZL` and local condition `ZU` (`R0`-modules), the
  inclusion `ιZ : ZU → ZL`, injective ("the degree-one maps inject", tex 3914), and the
  localization `locZ : Z1 → ZL`, which on read-out cochains is the read-out `ΦL` of their
  restrictions to the decomposition groups (`hlocΦ`), `ΦL` faithful on torsion-valued local
  cochains (`hΦLinj`);
* the read-out `specL` of the presentation's degree-one local cochains, commuting with the
  localization `resS` (`hspecL`), and the read-outs `specU T` of the presentation's degree-one
  local conditions (support `T`), commuting with the condition inclusions (`hspecU`);
* (C3, old places) `hκU`: the localization of the reduction of a central global Kummer cochain lies
  in the target's local condition — the read-out of `C_K`'s Kummer conditions (level `i`:
  `compTors_tateKummerFunOf`) inside the presentation's `kummerAt (localTwist W h v) (2^i)` at
  `t = 0`; at the new places this is `loc_infl_eq_urFactor`.

Kind: definition (GLUE). -/
structure CentralConeComparison extends
    CentralStageComparison hS h01 h1 W i s hs hs0 π ψ k G where
  /-- the target's degree-one local cochains -/
  ZL : Type
  [acgZL : AddCommGroup ZL]
  [modZL : Module R0 ZL]
  /-- the target's degree-one local condition -/
  ZU : Type
  [acgZU : AddCommGroup ZU]
  [modZU : Module R0 ZU]
  /-- its inclusion -/
  ιZ : ZU →ₗ[R0] ZL
  /-- the degree-one maps inject -/
  hιZ : Function.Injective ιZ
  /-- the localization of the target -/
  locZ : Z1 →ₗ[R0] ZL
  /-- the read-out of local torsion cochains at the places of the presentation -/
  ΦL : (∀ v : Places K S₀ ⊕ (ι × Bool), (Fin 1 → presGv K S₀ S place v) → PtS K S₁ W) →+ ZL
  /-- the localization of a read-out global cochain is the read-out of its restrictions -/
  hlocΦ : ∀ f, locZ (Φ f) = ΦL (fun v σ => f (fun j => presLoc K S₀ S place v (σ j)))
  /-- faithfulness: `ΦL` is injective on `2^i`-torsion-valued local cochains -/
  hΦLinj : ∀ F : ∀ v : Places K S₀ ⊕ (ι × Bool), (Fin 1 → presGv K S₀ S place v) → PtS K S₁ W,
    (∀ v σ, (2 ^ i : ℕ) • F v σ = 0) → ΦL F = 0 → F = 0
  /-- the read-out of the presentation's local cochains -/
  specL : (localSumCx k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place)
    (MinS hS W i (alphaStage i s hs hs0 π ψ))).X 1 →+ ZL
  /-- it commutes with the localization -/
  hspecL : ∀ x, specL ((resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place)
    (MinS hS W i (alphaStage i s hs hs0 π ψ))).f 1 1 rfl x) = locZ (specG x)
  /-- the read-out of the presentation's local conditions -/
  specU : ∀ Tp : Finset ι, (piCx (presCondS K S₀ S k (MinS hS W i (alphaStage i s hs hs0 π ψ))
    (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
    (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
    EU Tp).U).X 1 →+ ZU
  /-- it commutes with the condition inclusions -/
  hspecU : ∀ Tp u, ιZ (specU Tp u) = specL ((piMap (presCondS K S₀ S k
    (MinS hS W i (alphaStage i s hs hs0 π ψ)) (stageCondsK hS W i s hs hs0 hFull π ψ P hΨ k) place
    (fun j => urRep k (Mcoef K S₀ W i (alphaStage i s hs hs0 π ψ)) (newPlace (place j) (hw j)))
    EU Tp).i).f 1 1 rfl u)
  /-- (C3) the central Kummer conditions read into the target's condition -/
  hκU : ∀ {Pc : (centralCurve G).toAffine.Point}
    {Rt : ℕ → ((centralCurve G).baseChange (KS K G.S)).toAffine.Point}
    (hR : IsGlobalDivTower (centralCurve G) Pc Rt),
    ∃ u : ZU, ιZ u = locZ (red (globalKummerCochain hR))

attribute [instance] CentralConeComparison.acgZL CentralConeComparison.modZL
  CentralConeComparison.acgZU CentralConeComparison.modZU

variable {hS h01 h1 W i s hs hs0 hFull π ψ P hψ hΨ k place hw EU hE G}

/-- **The localized central Kummer class is the read-out of the local twisted Kummer cocycles**
(PROVED from `hred`, `hlocΦ`): the class `hκU` asks to lie in the target's local condition. -/
theorem CentralConeComparison.locZ_red_kummer
    (C : CentralConeComparison hS h01 h1 W i s hs hs0 hFull π ψ P hΨ k place hw EU G)
    {Pc : (centralCurve G).toAffine.Point}
    {Rt : ℕ → ((centralCurve G).baseChange (KS K G.S)).toAffine.Point}
    (hR : IsGlobalDivTower (centralCurve G) Pc Rt) :
    C.locZ (C.red (globalKummerCochain hR)) = C.ΦL (fun v σ =>
      ((quadChar s hs hs0 (inflMap K hS (presLoc K S₀ S place v (σ 0))) : ℤˣ) : ℤ) •
        (inflMap K h1 (presLoc K S₀ S place v (σ 0)) • C.twistPt (Rt i)) - C.twistPt (Rt i)) := by
  rw [C.hred hR, C.hlocΦ]

/-- **(4.5) on the Selmer cones, at a stage** (PROVED from the cone comparison; tex 3911–3915):
with the hypotheses of `central45_global`, and `u_κ` the read-out of the central Kummer condition
(`hκU`), the local-condition component `u_R = ux A_R` of the class of `A_R` satisfies
`ιZ(specU(u_R) − m · u_κ) = locZ(dZ(specG0 b_G))`, `m = sp a − 2χ_h(σ)`. -/
theorem central45_cone
    (C : CentralConeComparison hS h01 h1 W i s hs hs0 hFull π ψ P hΨ k place hw EU G)
    {Tp Tq : Finset ι}
    (AT : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tp)
    (AR : ActualPoint hS h01 h1 W i s hs hs0 hFull π P place Tq)
    (a : k) (σ : GKS K S₀)
    (bG : (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).X 0)
    (hG : gx hS h01 h1 W i s hs hs0 hFull π ψ P k place AR =
      pointFactor a ((eK k i).symm (alphaStage i s hs hs0 π ψ σ : Acoef i))
          ((eK k i).symm (((alphaStage i s hs hs0 π ψ σ)⁻¹ : (Acoef i)ˣ) : Acoef i)) •
        gx hS h01 h1 W i s hs hs0 hFull π ψ P k place AT +
      (globalCx k (GKS K S) (MinS hS W i (alphaStage i s hs hs0 π ψ))).d 0 1 rfl bG)
    {Pc : (centralCurve G).toAffine.Point}
    {Rt : ℕ → ((centralCurve G).baseChange (KS K G.S)).toAffine.Point}
    (hR : IsGlobalDivTower (centralCurve G) Pc Rt)
    (htower : C.twistPt (Rt i) = augAmb h1 W AT.wsumQ)
    (uκ : C.ZU) (huκ : C.ιZ uκ = C.locZ (C.red (globalKummerCochain hR))) :
    C.ιZ (C.specU Tq (ux hS h01 h1 W i s hs hs0 hFull π ψ P hψ hΨ k place hw EU hE AR) -
        (C.sp a - 2 * (((quadChar s hs hs0 σ : ℤˣ) : ℤ) : C.R0)) • uκ) =
      C.locZ (C.dZ (C.specG0 bG)) := by
  have h45 := central45_global hFull C.toCentralStageComparison AT AR a σ bG hG hR htower
  rw [map_sub, C.hspecU, ux_spec, C.hspecL, h45, map_smul, huκ, map_add, map_smul,
    add_sub_cancel_left]

end Cone

end ZInQ.Contrib.CloudB3E2.NormCochain
