import ZInQKernel.Contrib.RC53Assist.RetainedAssembly.SupportChange.Assembly
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.StageArith

/-!
# Realization of retained matrices on the actual stage complexes

The finite free stage model, its normalized inclusion and projection, and the
coordinate identities for localization and global trace are retained together.
One application of the stage-diagram limit construction produces the retained
complex, pairing and inverse homotopies. The same witnesses give all three
realization identities on one ultrafilter-large set of positive stages.

The arithmetic support-change assumptions are unchanged. No realization or
comparison of the actual stage cochains with the retained matrices is assumed.
This is not a realization theorem for an arbitrary previously chosen retained
complex: the retained complex and its realization are produced together.

Sources: `diophantine_zq.tex`, lines 4385–4451 and 4976–5135.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange

open CategoryTheory Matrix IsLocalRing NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex ComplexStages)
open ZInQ.Contrib.RC53Assist.InnerLimitArith (ResidualCohomologyFinite)
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.Limits (Lambda StageA stageMap stageIdeal GRetract GradedModel
  residualCohomologyAt exists_gradedModel)
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open scoped Classical

section StageCoordinates

variable {A : Type} [CommRing A] {X : GCx A} (P : StagePairingInput X)
  {rank : ℤ → ℕ} (S : StageMatrixDiagram A rank)

/-- Kind: definition. A stage diagram realized by a normalized finite free
model of the actual complex, with exact coordinate identities on all model
cochains, not merely their cohomology classes; tex 4391–4442. -/
structure StageDiagramRealization where
  /-- Kind: definition. The finite free model complex; tex 4391–4437. -/
  model : GCx A
  /-- Kind: PROVED. Normalized inclusion, projection and contraction from the
  actual complex to this model; tex 4423–4437. -/
  retract : GRetract X model
  /-- Kind: definition. Coordinates in the diagram's ranks; tex 4438–4442. -/
  coordinate : ∀ n : ℤ, model.X n ≃ₗ[A] (Fin (rank n) → A)
  /-- Kind: PROVED. The actual model differential is the diagram matrix;
  tex 4431, 4438–4442. -/
  differential : ∀ a b (hab : a + 1 = b) (x : model.X a),
    coordinate b (model.d a b hab x) = S.dC a b hab *ᵥ coordinate a x
  /-- Kind: PROVED. The actual localization composed with the same model
  inclusion is the diagram's localization; tex 4438–4442. -/
  localization : ∀ n (x : model.X n),
    lCoordR A n (P.res.f n n rfl (retract.i.f n n rfl x)) = S.res n *ᵥ coordinate n x
  /-- Kind: PROVED. The global trace on the same included model cochains is
  the diagram's bilinear form; tex 4385–4388, 4438–4442. -/
  globalTrace : ∀ a b (hab : a + b = 3) (x : model.X a) (y : model.X b),
    P.glob a b hab (retract.i.f a a rfl x) (retract.i.f b b rfl y) =
      coordinate a x ⬝ᵥ (S.glob a b hab *ᵥ coordinate b y)

/-- Kind: PROVED. Preserve the normalized model and all coordinate identities
when the diagram ranks are fixed on the large set; tex 4443–4447. -/
def StageDiagramRealization.cast {rank' : ℤ → ℕ} (h : rank = rank')
    (R : StageDiagramRealization P S) : StageDiagramRealization P (S.cast h) := by
  subst h
  exact R

/-- Kind: PROVED. The stage model and the actual complex are homotopy
equivalent, with homotopy maps given by the retained normalized retract;
tex 4423–4437. -/
def StageDiagramRealization.homotopyEquiv (R : StageDiagramRealization P S) :
    HomotopyEquiv R.model.toCC X.toCC := R.retract.homotopyEquiv

/-- Kind: PROVED. The finite-model construction and stage pairing transport
produce the stage realization while retaining their actual inclusion;
tex 4391–4442. -/
theorem exists_stageDiagramRealization (R : GradedModel X)
    (hdual : QuasiIso (GHom.toCC (stageDualityMap P))) (lo hi : ℤ)
    (hr : ∀ n, n < lo ∨ hi < n → R.rank n = 0) :
    ∃ S : StageMatrixDiagram A R.rank,
      S.loc = P.loc ∧ Nonempty (StageDiagramRealization P S) := by
  obtain ⟨S, hd, hres, hglob, hloc⟩ := exists_stageMatrixDiagram R P hdual lo hi hr
  refine ⟨S, hloc, ⟨⟨R.modelCx, R.retract,
    fun n => LinearEquiv.refl A (Fin (R.rank n) → A), ?_, ?_, ?_⟩⟩⟩
  · intro a b hab x
    rw [hd]
    rfl
  · intro n x
    rw [hres]
    exact (modelRes_mulVec R P n x).symm
  · intro a b hab x y
    rw [hglob]
    exact (modelGlob_form R P a b hab x y).symm

end StageCoordinates

section RetainedCoordinates

variable {U : Ultrafilter ℕ} (C : ComplexStages (R := Lambda) stageIdeal U)
  (D : RetainedLimitPairingStages U C) (i : ℕ) {X : GCx (StageA i)}
  (P : StagePairingInput X)

/-- Kind: definition. The retained stage matrices realized on a finite free
model of the actual stage complex. The normalized retract fixes the inclusion
used in both localization and global trace identities; tex 4391–4451. -/
structure RetainedStageRealization where
  /-- Kind: definition. The finite free model of the actual stage complex;
  tex 4391–4437. -/
  model : GCx (StageA i)
  /-- Kind: PROVED. Actual normalized inclusion, projection and contraction;
  tex 4423–4437. -/
  retract : GRetract X model
  /-- Kind: definition. Coordinates of the retained rank at this stage;
  tex 4443–4447. -/
  coordinate : ∀ n : ℤ, model.X n ≃ₗ[StageA i] (Fin (C.rank n) → StageA i)
  /-- Kind: PROVED. The model differential is the stage image of `C.d`;
  tex 4431, 4443–4447. -/
  differential : ∀ a b (hab : a + 1 = b) (x : model.X a),
    coordinate b (model.d a b hab x) =
      (C.d i a b hab).map (stageMap i) *ᵥ coordinate a x
  /-- Kind: PROVED. Localization of the actual included model cochains is
  the stage image of the retained localization matrix; tex 4438–4447. -/
  localization : ∀ n (x : model.X n),
    lCoordR (StageA i) n (P.res.f n n rfl (retract.i.f n n rfl x)) =
      (D.res n i).map (stageMap i) *ᵥ coordinate n x
  /-- Kind: PROVED. The actual global trace on the included model cochains
  is the stage image of the retained global bilinear form;
  tex 4385–4388, 4438–4447. -/
  globalTrace : ∀ a b (hab : a + b = 3) (x : model.X a) (y : model.X b),
    P.glob a b hab (retract.i.f a a rfl x) (retract.i.f b b rfl y) =
      coordinate a x ⬝ᵥ ((D.glob a b hab i).map (stageMap i) *ᵥ coordinate b y)

/-- Kind: PROVED. A retained stage realization supplies an actual homotopy
equivalence to the stage cochains; tex 4423–4437. -/
def RetainedStageRealization.homotopyEquiv (R : RetainedStageRealization C D i P) :
    HomotopyEquiv R.model.toCC X.toCC := R.retract.homotopyEquiv

/-- Kind: PROVED. Thread the same stage realization through the three matrix
lift identities of the retained stage-diagram construction;
tex 4438–4451. -/
def StageDiagramRealization.toRetained {rank : ℤ → ℕ}
    (S : StageMatrixDiagram (StageA i) rank) (R : StageDiagramRealization P S)
    (h : rank = C.rank)
    (hd : ∀ a b hab, (C.d i a b hab).map (stageMap i) = (S.cast h).dC a b hab)
    (hr : ∀ n, (D.res n i).map (stageMap i) = (S.cast h).res n)
    (hg : ∀ a b hab, (D.glob a b hab i).map (stageMap i) = (S.cast h).glob a b hab) :
    RetainedStageRealization C D i P := by
  let T := StageDiagramRealization.cast P S h R
  refine ⟨T.model, T.retract, T.coordinate, ?_, ?_, ?_⟩
  · intro a b hab x
    rw [hd]
    exact T.differential a b hab x
  · intro n x
    rw [hr]
    exact T.localization n x
  · intro a b hab x y
    rw [hg]
    exact T.globalTrace a b hab x y

end RetainedCoordinates

section RealizedProducer

/-- Kind: PROVED. One arithmetic stage retains the finite model and all three
coordinate identities instead of discarding them at the stage-diagram
interface. The zeroth coefficient ring requires no realization assumption;
tex 4391–4451. -/
theorem exists_stageDiagram_of_inputs_realized (i : ℕ) (G : GCx (StageA i))
    (hflat : ∀ n, Module.Flat (StageA i) (G.X n)) (P : StagePairingInput G)
    (hdual : QuasiIso (GHom.toCC (stageDualityMap P)))
    (hres : ∀ [NeZero i], ResidualCohomologyFinite G) (lo hi : ℤ)
    (hbdd : ∀ [NeZero i] (n : ℤ), n < lo ∨ hi < n →
      Module.finrank (ResidueField (StageA i)) (residualCohomologyAt G n) = 0)
    (B : ℕ) (hB : ∀ [NeZero i] (n : ℤ),
      Module.finrank (ResidueField (StageA i)) (residualCohomologyAt G n) ≤ B) :
    ∃ rk : ℤ → ℕ,
      (∀ n, n < lo ∨ hi < n → rk n = 0) ∧ (∀ n, rk n ≤ B) ∧
      (∀ [NeZero i] (n : ℤ),
        rk n = Module.finrank (ResidueField (StageA i)) (residualCohomologyAt G n)) ∧
      ∃ S : StageMatrixDiagram (StageA i) rk,
        (i ≠ 0 → S.loc = P.loc) ∧
        (∀ [NeZero i], Nonempty (StageDiagramRealization P S)) := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    have : Subsingleton (StageA 0) := stageA_zero_subsingleton
    refine ⟨fun _ => 0, fun _ _ => rfl, fun _ => Nat.zero_le _, ?_,
      StageMatrixDiagram.ofSubsingleton _ _, fun h => absurd rfl h, ?_⟩
    · intro _ _
      exact absurd rfl (NeZero.ne 0)
    · intro _
      exact absurd rfl (NeZero.ne 0)
  · have : NeZero i := ⟨by omega⟩
    have : ∀ n, Module.Flat (StageA i) (G.X n) := hflat
    obtain ⟨R, hR⟩ := exists_gradedModel (stageA_isNilpotent_maximalIdeal i) G
      (finite_residualCohomologyAt_of hres)
    have hr : ∀ n, n < lo ∨ hi < n → R.rank n = 0 :=
      fun n hn => (hR n).trans (hbdd n hn)
    obtain ⟨S, hloc, hreal⟩ := exists_stageDiagramRealization P R hdual lo hi hr
    exact ⟨R.rank, hr, fun n => (hR n).trans_le (hB n), fun n => hR n,
      S, fun _ => hloc, hreal⟩

/-- Kind: PROVED. The arithmetic-input retained producer, strengthened by
realization of its differential, localization and global trace matrices on
models of the actual stage complexes. The retained diagram and the actual
models are made from the same stage witnesses. The identities hold on one
ultrafilter-large set, as required when ranks are fixed;
tex 4385–4451. -/
theorem exists_retained_of_stageInputs_realized (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (G : ∀ i, GCx (StageA i))
    (hflat : ∀ i n, Module.Flat (StageA i) ((G i).X n))
    (Uc : ∀ i, GCx (StageA i))
    (res : ∀ i, GHom (G i) (splitLocalComplex (StageA i)))
    (ι : ∀ i, GHom (Uc i) (splitLocalComplex (StageA i)))
    (Q : ∀ i, SelPairData (splitSelData (G i) (res i) (Uc i) (ι i))
      (splitSelData (G i) (res i) (Uc i) (ι i)))
    (tr : ∀ i, (coneCx (Q i).resE).X 3 →ₗ[StageA i] StageA i)
    (htr : ∀ i z, tr i ((coneCx (Q i).resE).d 2 3 rfl z) = 0)
    (hdual : ∀ i, QuasiIso (GHom.toCC (globalDualityMap (Q i) (tr i) (htr i))))
    (hres : ∀ i [NeZero i], ResidualCohomologyFinite (G i)) (lo hi : ℤ)
    (hbdd : ∀ i [NeZero i] (n : ℤ), n < lo ∨ hi < n →
      Module.finrank (ResidueField (StageA i)) (residualCohomologyAt (G i) n) = 0)
    (B : ℕ) (hB : ∀ i [NeZero i] (n : ℤ),
      Module.finrank (ResidueField (StageA i)) (residualCohomologyAt (G i) n) ≤ B) :
    ∃ (r₀ : ℤ → ℕ) (C : ComplexStages (R := Lambda) stageIdeal U)
      (D : RetainedLimitPairingStages U C) (_ : RetainedGlobalDualityStages D),
      C.rank = r₀ ∧ C.low = lo ∧ C.high = hi ∧ (∀ n, r₀ n ≤ B) ∧
      (∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i] (n : ℤ),
        r₀ n = Module.finrank (ResidueField (StageA i)) (residualCohomologyAt (G i) n)) ∧
      (∀ i, i ≠ 0 → ∀ a b,
        (D.loc a b i).map (stageMap i) = stageLocMat (Q i) (tr i) a b) ∧
      (∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i], Nonempty
        (RetainedStageRealization C D i (stagePairingInputOfSel (Q i) (tr i) (htr i)))) := by
  choose rk hrk0 hrkB hrkfin hS using fun i => exists_stageDiagram_of_inputs_realized i
    (G i) (hflat i) (stagePairingInputOfSel (Q i) (tr i) (htr i))
    (quasiIso_stageDualityMap_of_global (Q i) (tr i) (htr i) (hdual i))
    (hres i) lo hi (hbdd i) B (hB i)
  choose S hSloc hSreal using hS
  obtain ⟨r₀, C, D, E, hC, hlow, hhigh, hr₀B, hev, hloc, hreal⟩ :=
    exists_retained_of_stageDiagrams U hU rk S lo hi B hrk0 hrkB
  refine ⟨r₀, C, D, E, hC, hlow, hhigh, hr₀B, ?_, ?_, ?_⟩
  · filter_upwards [hev] with i hri
    intro _ n
    rw [← hri]
    exact hrkfin i n
  · intro i hi0 a b
    rw [hloc i a b, hSloc i hi0]
    rfl
  · filter_upwards [hreal] with i hi
    intro _
    obtain ⟨h, hd, hr, hg, _, _, _⟩ := hi
    obtain ⟨R⟩ := hSreal i
    exact ⟨StageDiagramRealization.toRetained C D i
      (stagePairingInputOfSel (Q i) (tr i) (htr i)) (S i) R h hd hr hg⟩

end RealizedProducer

section RealizedArithmeticAssembly

variable {K : Type} [Field K] [NumberField K]
  {S₀ : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K} [W.IsElliptic]
  {α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ} [∀ i, IsOpenKer (α i)]
  [HasFullTwoTorsion K S₀ W]
  {F : ActualStageFamily S₀ W α} {O : OldDualityData F}
  {R : StandardOldReference S₀ W α} {width : ℕ}
  {a : ArithmeticInputs F O R width} {U : Ultrafilter ℕ}
  {hU : (U : Filter ℕ) ≤ Filter.cofinite} {Cn : ActualConj K S₀}
  {hW : W.map (Cn.κ : K →+* K) = W}

/-- Kind: definition. Realization of an assembled retained diagram on the
actual old-condition arithmetic complexes, using exactly its chosen stage
localization and global trace data. All three identities use the same
normalized model inclusion at a stage; tex 4385–4451. -/
def AssembledLimit.Realized (L : AssembledLimit a U hU Cn hW) : Prop :=
  ∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i], Nonempty
    (RetainedStageRealization L.C L.D i
      (stagePairingInputOfSel (L.stages i).pairing (L.stages i).trace (L.stages i).trace_kills))

/-- Kind: PROVED. Assemble the retained arithmetic diagram and its stage
realizations together from the same finite-model witnesses. All fields of the
previous assembly are retained, including conditional certificates on this
same complex and localization. No realization hypothesis is added;
tex 4385–4451, 4976–5135. -/
theorem assemble_inner_limit_realized (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (a : ArithmeticInputs F O R width)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (Cn : ActualConj K S₀) (hW : W.map (Cn.κ : K →+* K) = W) :
    ∃ L : AssembledLimit a U hU Cn hW,
      L.stages = producedStages a p hK hS₀ h2 ∧ L.Realized := by
  let s := producedStages a p hK hS₀ h2
  obtain ⟨B, hbdd, hB⟩ := a.residualSupport.producerBounds p hK hS₀ h2
  obtain ⟨r₀, C, D, E, hrank, hlow, hhigh, hrankB, hev, hloc, hreal⟩ :=
    exists_retained_of_stageInputs_realized U hU (fun i => F.globalCx i)
      (F.flat hS₀ a.oldFlat) (retainedConditions a)
      (fun i => stageRes F i (s i).projection)
      (fun i => ghomComp (retainedInclusions a i) (s i).projection)
      (fun i => (s i).pairing) (fun i => (s i).trace)
      (fun i => (s i).trace_kills) (fun i => (s i).duality)
      (a.residualSupport.residual_finite p hS₀ h2) 0 3 hbdd B hB
  have hbound : ∀ n, C.rank n ≤ B := by
    intro n
    rw [hrank]
    exact hrankB n
  have hranks : ∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i] (n : ℤ),
      C.rank n = Module.finrank (ResidueField (StageA i))
        (residualCohomologyAt (F.globalCx i) n) := by
    filter_upwards [hev] with i hi
    intro _ n
    rw [hrank]
    exact hi n
  have hcertificate : FibreCertificates hU Cn hW D := by
    intro P _ ε₀ ε₂ ε σ hε₂ hε hσ hl
    exact fibreInnerLimitPairingCertificate_of_retained hU E P Cn W hW
      ε₀ ε₂ ε σ hε₂ hε hσ hl
  let L : AssembledLimit a U hU Cn hW :=
    ⟨B, s, C, D, E, hlow, hhigh, hbound, hranks, hloc, hcertificate⟩
  exact ⟨L, rfl, hreal⟩

/-- Kind: PROVED. The support-change arithmetic assembler, strengthened with
actual stage-complex realizations of the retained differential, localization
and global trace pairing. The six-coordinate support comparison is produced
from the same original local-dimension input as before. The retained complex,
pairing, certificates and all realization identities share the same witnesses.
No realization or additional arithmetic assumption is supplied;
tex 3483–3498, 4385–4451, 4976–5135. -/
theorem assemble_from_support_change_realized (p : ArithmeticPrints K)
    (h788 : NekovarProp788ii K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (P : ActualSupportPresentation F R) (oldFlat : F.NontrivialOldFlat)
    (stage : ∀ i [NeZero i], StageArithmeticInput F O i)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (Cn : ActualConj K S₀) (hW : W.map (Cn.κ : K →+* K) = W) :
    ∃ T : ResidualSupportControl F R 6,
      ∃ L : AssembledLimit (⟨oldFlat, T, stage⟩ : ArithmeticInputs F O R 6) U hU Cn hW,
        L.stages = producedStages (⟨oldFlat, T, stage⟩ : ArithmeticInputs F O R 6)
          p hK hS₀ h2 ∧ L.Realized := by
  let T := residualSupport_six_of_stage_dimensions F R p h788 hK hS₀ h2 P
    (fun i _ => (stage i).localDimensions)
  obtain ⟨L, hstage, hreal⟩ :=
    assemble_inner_limit_realized p hK hS₀ h2 ⟨oldFlat, T, stage⟩ U hU Cn hW
  exact ⟨T, L, hstage, hreal⟩

end RealizedArithmeticAssembly

end ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange
