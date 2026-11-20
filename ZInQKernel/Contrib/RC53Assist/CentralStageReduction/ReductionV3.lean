import ZInQKernel.Contrib.CloudB3E2Norm.CentralTwistDict

/-! Finite-level reduction of central Tate cochains on the original support presentation. -/

noncomputable section

set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.CentralStageReduction

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.LambdaCoef ZInQ.Manuscript.RC.CalPoint
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.CloudB3E2.NormCochain

attribute [local instance] levTop ptSAction

variable {K : Type} [Field K] [NumberField K] [DecidableEq K]

omit [DecidableEq K] in
/-- Coercing the composite support inclusion retains the original algebraic-closure value. -/
theorem supportInclusion_values
    {S₀ S₁ S₂ : Set (HeightOneSpectrum (𝓞 K))}
    (h01 : S₀ ⊆ S₁) (h12 : S₁ ⊆ S₂) (x : KS K S₀) :
    ((ksIncl h12 (ksIncl h01 x) : KS K S₂) : AlgebraicClosure K) = x := by
  simp only [coe_ksIncl]

omit [DecidableEq K] in
/-- The typed inclusion composition follows from its original underlying values. -/
theorem supportInclusion_comp
    {S₀ S₁ S₂ : Set (HeightOneSpectrum (𝓞 K))}
    (h01 : S₀ ⊆ S₁) (h12 : S₁ ⊆ S₂) (x : KS K S₀) :
    ksIncl h12 (ksIncl h01 x) = ksIncl (h01.trans h12) x := by
  apply Subtype.ext
  rw [supportInclusion_values, coe_ksIncl]

/-- The support point inclusions compose as the underlying field inclusions do. -/
theorem supportPointMap_comp
    {S₀ S₁ S₂ : Set (HeightOneSpectrum (𝓞 K))}
    (h01 : S₀ ⊆ S₁) (h12 : S₁ ⊆ S₂) (W : WeierstrassCurve K)
    (P : PtS K S₀ W) :
    ptMap h12 W (ptMap h01 W P) = ptMap (h01.trans h12) W P := by
  rcases P with _ | ⟨x, y, hxy⟩
  · rw [← Affine.Point.zero_def]
    simp only [map_zero]
  · obtain ⟨h1, e1⟩ := ptMap_some h01 W hxy
    obtain ⟨h2, e2⟩ := ptMap_some h12 W h1
    obtain ⟨h02, e02⟩ := ptMap_some (h01.trans h12) W hxy
    rw [e1, e2, e02]
    simp only [Affine.Point.some.injEq]
    exact ⟨supportInclusion_comp h01 h12 x, supportInclusion_comp h01 h12 y⟩

/-- Forward support transport on the actual finite torsion subgroups. -/
def torsionSupportMap {S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
    (h01 : S₀ ⊆ S₁) (W : WeierstrassCurve K) (i : ℕ) :
    Lev K S₀ W i →+ Lev K S₁ W i where
  toFun P := ⟨ptMap h01 W P.1, (mem_lev_iff _).2 (by
    rw [← map_nsmul, two_pow_nsmul_lev P, map_zero])⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ _ _)

/-- Curve equality transports only the target finite torsion module. -/
def supportTorsionCast {S : Set (HeightOneSpectrum (𝓞 K))}
    {W W' : WeierstrassCurve K} (e : W = W') (i : ℕ) :
    Lev K S W i ≃+ Lev K S W' i :=
  AddEquiv.cast (M := fun B : WeierstrassCurve K => Lev K S B i) e

variable {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {G : GenuineKummerData K E₀ hZ}
  {h01 : S₀ ⊆ S₁} {W : WeierstrassCurve K} {h : K}
  {s : KS K S₀} {hs : s ^ 2 = algebraMap K (KS K S₀) h}

/-- Projection, the same normalized untwisting, and forward support transport. -/
def stageCoefficient (D : CentralTwistDict G h01 W s hs) (i : ℕ) :
    TateS K G.S (centralCurve G) →+ TorsT S₀ W i :=
  (torsionSupportMap D.hGS W i).comp
    ((supportTorsionCast D.hW i).toAddMonoidHom.comp
      ((globalTwistTorsEquiv G.W G.s G.hs G.hs0 i).toAddMonoidHom.comp (projLev i)))

/-- The coefficient map and the canonical point untwisting are literally compatible. -/
theorem torsInclS_stageCoefficient (D : CentralTwistDict G h01 W s hs) (i : ℕ)
    (P : TateS K G.S (centralCurve G)) :
    torsInclS h01 W i (stageCoefficient D i P) = D.twistPt (P.pt i) := by
  obtain ⟨hGS, hW, hh, hsG⟩ := D
  subst hW
  change ptMap h01 G.W (ptMap hGS G.W
      (globalTwistPointEquiv G.W G.s G.hs G.hs0 (P.pt i))) =
    ptMap (hGS.trans h01) G.W
      (globalTwistPointEquiv G.W G.s G.hs G.hs0 (P.pt i))
  exact supportPointMap_comp hGS h01 G.W _

/-- The projected coefficient map is continuous for the discrete finite target. -/
theorem stageCoefficient_continuous (D : CentralTwistDict G h01 W s hs) (i : ℕ) :
    @Continuous _ _ _ (⊥ : TopologicalSpace (TorsT S₀ W i)) (stageCoefficient D i) := by
  let _ : TopologicalSpace (TorsT S₀ W i) := ⊥
  exact (continuous_of_discreteTopology
    (f := fun P : Lev K G.S (centralCurve G) i =>
      torsionSupportMap D.hGS W i
        (supportTorsionCast D.hW i (globalTwistTorsEquiv G.W G.s G.hs G.hs0 i P)))).comp
          (continuous_projLev i)

/-- Reduction of genuine continuous cochains along the original support restriction. -/
def stageReduction (D : CentralTwistDict G h01 W s hs) (h1 : S₁ ⊆ S) (i : ℕ) :
    contCochain ℤ_[2] (GKS K G.S) (TateS K G.S (centralCurve G)) 1 →+
      Z1C W i (S := S) (S₀ := S₀) where
  toFun c g := stageCoefficient D i
    (cfun c (fun j => inflMap K ((D.hGS.trans h01).trans h1) (g j)))
  map_zero' := by
    funext g
    exact map_zero _
  map_add' c c' := by
    funext g
    exact map_add _ _ _

/-- The plain-cochain readout retains continuity; no cochain is replaced by a model. -/
theorem stageReduction_continuous (D : CentralTwistDict G h01 W s hs) (h1 : S₁ ⊆ S)
    (i : ℕ) (c : contCochain ℤ_[2] (GKS K G.S) (TateS K G.S (centralCurve G)) 1) :
    @Continuous _ _ _ (⊥ : TopologicalSpace (TorsT S₀ W i)) (stageReduction D h1 i c) := by
  exact (stageCoefficient_continuous D i).comp (c.2.comp
    (continuous_pi fun j =>
      (inflMap K ((D.hGS.trans h01).trans h1)).continuous_toFun.comp (continuous_apply j)))

/-- The exact level-wise Kummer formula supplies the original reduction field. -/
theorem stageReduction_kummer (D : CentralTwistDict G h01 W s hs) (hs0 : s ≠ 0)
    (hS : S₀ ⊆ S) (h1 : S₁ ⊆ S) (i : ℕ)
    {P : (centralCurve G).toAffine.Point}
    {Rt : ℕ → ((centralCurve G).baseChange (KS K G.S)).toAffine.Point}
    (hR : IsGlobalDivTower (centralCurve G) P Rt)
    (f : (Fin 1 → GKS K S) → TorsT S₀ W i)
    (hf : ∀ g, torsInclS h01 W i (f g) =
      ((quadChar s hs hs0 (inflMap K hS (g 0)) : ℤˣ) : ℤ) •
        (inflMap K h1 (g 0) • D.twistPt (Rt i)) - D.twistPt (Rt i)) :
    stageReduction D h1 i (globalKummerCochain hR) = f := by
  funext g
  have hι : Function.Injective (torsInclS h01 W i) :=
    (ptMap_injective h01 W).comp Subtype.val_injective
  apply hι
  change torsInclS h01 W i (stageCoefficient D i
      (globalKummerFun hR (inflMap K ((D.hGS.trans h01).trans h1) (g 0)))) =
    torsInclS h01 W i (f g)
  rw [torsInclS_stageCoefficient, globalKummerFun_pt, map_sub,
    D.twistPt_galois hs0 hS h1]
  exact (hf g).symm

section OriginalConsumer

open ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Manuscript.RC.KummerMaps

attribute [local instance] mcoefModuleK

variable [W.IsElliptic] (i : ℕ) [NeZero i]
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)

/-- The concrete comparison receives the constructed reduction, not an assumed Kummer identity. -/
def comparisonOfDictionary (D : CentralTwistDict G h01 W s hs) (hs0 : s ≠ 0)
    (hS : S₀ ⊆ S) (h1 : S₁ ⊆ S)
    [IsOpenKer (alphaShap s hs hs0 π)] [IsOpenKer (alphaStage i s hs hs0 π ψ)]
    (k : Type) [CommRing k] [TopologicalSpace k] [DiscreteTopology k] [StageIsoA k i]
    (hψ1 : ∀ d : Δ, evalT0 i (ψ d : Acoef i) = 1) :
    CentralStageComparison₂ hS h01 h1 W i s hs hs0 π ψ k G :=
  centralStageComparison₂_of_C2 hS h01 h1 W i s hs hs0 π k G hψ1
    D.twistPt D.twistPt_injective (stageReduction D h1 i)
      (stageReduction_kummer D hs0 hS h1 i)

end OriginalConsumer

end ZInQ.Contrib.RC53Assist.CentralStageReduction
