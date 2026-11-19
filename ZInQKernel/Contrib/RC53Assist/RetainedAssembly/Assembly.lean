import ZInQKernel.Contrib.OneProof.RC.FibreDuality.StageArith
import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitStageActual
import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.StageFlat
import ZInQKernel.Contrib.RC53Assist.ResidualFiniteness.StageResidual
import ZInQKernel.Contrib.RC53Assist.ResidualBounds.StageBounds
import ZInQKernel.Contrib.RC53Assist.LocalDegreeTwo.NormalizedPairing
import ZInQKernel.Contrib.RC53Assist.OldOrthogonality.VerifiedOrthogonality
import ZInQKernel.Contrib.RC53Assist.Detection.Producer

/-!
# Assembly of the retained inner limit on arithmetic cochains

The global complex at stage `i` is the actual continuous cochain complex on
`S₀ ∪ {qᵢ}`, with the old local conditions absorbed. Its one remaining local
complex uses the coefficient module formed on that same enlarged support.
The local restriction is the actual restriction of continuous cochains.

The fixed-support finiteness and rank suppliers are used without changing
support in their statements. The comparison needed for varying derivative
supports is named explicitly. Original pairings are compared on cochains,
including their scalar cones and both duality maps. No split pairing, split
trace, split duality, model, retained diagram, or detecting determinant is
assumed.

Sources: `diophantine_zq.tex`, lines 4391–4451 and 4976–5135.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.RetainedAssembly

open CategoryTheory NumberField IsDedekindDomain IsLocalRing Module
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.Duality (MilneLocalTateDualityKummerCharZero
  LocalTruncIsotropy)
open ZInQ.Contrib.CloudB3RC53.RankCounts (MilneADT_I_4_10_totallyComplex)
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.RC53Assist.ResidualFiniteness
open ZInQ.Contrib.RC53Assist.ResidualBounds
open ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace
open ZInQ.Contrib.RC53Assist.OldOrthogonality.Truncations
open ZInQ.Contrib.RC53Assist.OldOrthogonality.SupportCoefficients
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.Limits (Lambda StageA stageMap stageIdeal residualCohomologyAt)
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex ComplexStages)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open scoped Classical WeierstrassCurve

section ZeroStage

/-- Kind: PROVED. Modules over the zero ring are flat; tex 4391–4406. -/
theorem flat_over_zeroRing (A M : Type) [CommRing A] [Subsingleton A]
    [AddCommGroup M] [Module A M] : Module.Flat A M := by
  have : Subsingleton M := Module.subsingleton A M
  have : Module.Free A M :=
    Module.Free.of_basis (Module.Basis.empty _ : Module.Basis Empty A M)
  infer_instance

/-- Kind: PROVED. Every cochain map over the zero ring is a quasi-isomorphism;
tex 4391–4406. -/
theorem quasiIso_over_zeroRing {A : Type} [CommRing A] [Subsingleton A]
    {C C' : GCx A} (f : GHom C C') : QuasiIso (GHom.toCC f) := by
  have : IsIso (GHom.toCC f) := isIso_toCC_of_bijective f (fun n => by
    have : Subsingleton (C.X n) := Module.subsingleton A (C.X n)
    have : Subsingleton (C'.X n) := Module.subsingleton A (C'.X n)
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩)
  infer_instance

/-- Kind: definition. The zero-target pairing used only at coefficient stage
zero; tex 4391–4406. -/
def zeroTargetPair {A : Type} [CommRing A] (D : SelData A) : SelPairData D D where
  E := ZInQ.Manuscript.RC.SelmerComplex.zeroCx A
  EL := ZInQ.Manuscript.RC.SelmerComplex.zeroCx A
  resE := zeroGHom _ _
  cupG := ⟨fun _ _ _ _ => 0, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  cupL := ⟨fun _ _ _ _ => 0, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  compat _ _ _ _ _ _ _ _ _ _ _ _ _ := rfl
  hU _ _ _ _ := 0
  isotropy _ _ _ _ _ _ _ _ _ _ _ _ := rfl

/-- Kind: PROVED. The zero and full conditions are complementary under full
local duality, for every actual truncated isotropy primitive;
tex 2813–2814, 5055–5071. -/
theorem zero_full_complement {A : Type} [CommRing A] {C C' T : GCx A}
    (P : GPair C C' T) (tr : T.X 2 →ₗ[A] A)
    (htr : ∀ z, tr (T.d 1 2 rfl z) = 0)
    (J : LocalTruncIsotropy (zeroGHom (ZInQ.Manuscript.RC.SelmerComplex.zeroCx A) C)
      (idGHom C') P)
    (hLD : QuasiIso (GHom.toCC (adjHom P 2 tr htr))) :
    QuasiIso (GHom.toCC (orthLocalMap
      (zeroGHom (ZInQ.Manuscript.RC.SelmerComplex.zeroCx A) C) (idGHom C') P J tr htr)) := by
  let f := orthLocalMap
    (zeroGHom (ZInQ.Manuscript.RC.SelmerComplex.zeroCx A) C) (idGHom C') P J tr htr
  have hacyc := coneCx_acyclic_of_quasiIso (adjHom P 2 tr htr) hLD
  apply quasiIso_of_coneCx_acyclic f
  intro i j l hij hjl c hc
  obtain ⟨⟨u, x⟩, φ⟩ := c
  have hu : u = 0 := Subsingleton.elim (α := PUnit) _ _
  have hx0 := congrArg (fun z : coneT f l => z.1.2) hc
  change -(0 : C.X (l - 1)) - C.d (j - 1) (l - 1) (by omega) x = 0 at hx0
  rw [neg_zero, zero_sub, neg_eq_zero] at hx0
  have hxc : C.d (j - 1) (l - 1) (by omega) (-x) = 0 := by
    rw [map_neg, hx0, neg_zero]
  have hz : ∀ y : C'.X (3 - (l - 1)),
      tr (P.P (j - 1) (3 - (l - 1)) 2 (by omega) (-x) y) =
        (-(sgn (j - 1 - 1))) • asDual φ
          (C'.d (3 - (l - 1)) (3 - (j - 1)) (by omega) y) := by
    intro y
    have he := congrArg (fun z : coneT f l => asDual z.2 y) hc
    change asDual (f.f j (l - 1) (by omega) (u, x)) y -
      asDual ((dualCx C' 3).d (j - 1) (l - 1) (by omega) φ) y = 0 at he
    rw [orthLocalMap_apply] at he
    change tr (P.P (j - 1) (3 - (l - 1)) 2 (by omega) x y +
      J.h j (3 - (l - 1)) 2 (by omega) u y) -
      asDual ((dualCx C' 3).d (j - 1) (l - 1) (by omega) φ) y = 0 at he
    rw [hu, LinearMap.map_zero₂, add_zero] at he
    erw [dualCx_d_apply] at he
    have heq := sub_eq_zero.mp he
    rw [LinearMap.map_neg₂, map_neg, heq, sgn_pred (j - 1), neg_smul, neg_neg]
    simp only [neg_neg]
  obtain ⟨e, z, he, hz'⟩ := coneAdj_solve P tr htr hacyc
    (i - 1) (j - 1) (l - 1) (by omega) (by omega)
    (3 - (l - 1)) (3 - (j - 1)) (3 - (i - 1))
    (by omega) (by omega) (by omega) (-x) (asDual φ) hxc hz
  refine ⟨((0, e), -z), Prod.ext (Prod.ext ?_ ?_) (dualCx_ext fun y => ?_)⟩
  · exact Subsingleton.elim (α := PUnit) _ _
  · change -(0 : C.X (j - 1)) - C.d (i - 1) (j - 1) (by omega) e = x
    rw [neg_zero, zero_sub, he, neg_neg]
  · change asDual (f.f i (j - 1) (by omega) (0, e)) y -
      asDual ((dualCx C' 3).d (i - 1) (j - 1) (by omega) (-z)) y = asDual φ y
    rw [orthLocalMap_apply]
    change tr (P.P (i - 1) (3 - (j - 1)) 2 (by omega) e y +
      J.h i (3 - (j - 1)) 2 (by omega) 0 y) -
      asDual ((dualCx C' 3).d (i - 1) (j - 1) (by omega) (-z)) y = asDual φ y
    rw [LinearMap.map_zero₂, add_zero]
    erw [dualCx_d_apply]
    simpa only [sgn_pred, neg_neg, asDual, LinearMap.neg_apply, smul_neg, neg_smul]
      using hz' y

end ZeroStage

section OriginalComparison

variable {A : Type} [CommRing A]
  {Da Db Na Nb : SelData A} (Q : SelPairData Da Db) (N : SelPairData Na Nb)

/-- Kind: definition. Pull back an original scalar-cone trace along an actual
cochain map; tex 4385–4388, 4438–4442. -/
def pullScalarTrace (s : GHom (coneCx Q.resE) (coneCx N.resE))
    (tr : (coneCx N.resE).X 3 →ₗ[A] A) : (coneCx Q.resE).X 3 →ₗ[A] A :=
  tr.comp (s.f 3 3 rfl)

/-- Kind: PROVED. A scalar-cone cochain comparison preserves the boundary
identity for the trace; tex 4385–4388, 4438–4442. -/
theorem pullScalarTrace_kills (s : GHom (coneCx Q.resE) (coneCx N.resE))
    (tr : (coneCx N.resE).X 3 →ₗ[A] A)
    (htr : ∀ z, tr ((coneCx N.resE).d 2 3 rfl z) = 0) :
    ∀ z, pullScalarTrace Q N s tr ((coneCx Q.resE).d 2 3 rfl z) = 0 := by
  intro z
  change tr (s.f 3 3 rfl ((coneCx Q.resE).d 2 3 rfl z)) = 0
  rw [s.comm 2 3 2 3 rfl rfl rfl rfl]
  exact htr _

/-- Kind: GLUE. Exact original-diagram comparison, before replacing the retained
local complex. All comparison maps are cochain maps with bijective components;
both trace-duality squares commute for every original boundary-killing trace.
There is no duality or trace-existence conclusion in this input.
Tex 4385–4388, 4438–4442, 5035–5071. -/
structure OriginalDiagramComparison where
  /-- Kind: GLUE. Scalar-cone comparison; tex 4438–4442. -/
  scalar : GHom (coneCx Q.resE) (coneCx N.resE)
  /-- Kind: GLUE. Original global cochain comparison; tex 4438–4442. -/
  global : GHom Da.G Na.G
  /-- Kind: GLUE. Original compact cochain comparison; tex 4438–4442. -/
  compact : GHom (compactCx Db) (compactCx Nb)
  /-- Kind: GLUE. Original local-condition-cone comparison; tex 4438–4442. -/
  localCone : GHom (locCx Da) (locCx Na)
  /-- Kind: GLUE. Original dual-condition comparison; tex 4438–4442. -/
  condition : GHom Db.U Nb.U
  /-- Kind: GLUE. Global components are bijective; tex 4438–4442. -/
  global_bijective : ∀ n, Function.Bijective (global.f n n rfl)
  /-- Kind: GLUE. Compact components are bijective; tex 4438–4442. -/
  compact_bijective : ∀ n, Function.Bijective (compact.f n n rfl)
  /-- Kind: GLUE. Local-cone components are bijective; tex 4438–4442. -/
  localCone_bijective : ∀ n, Function.Bijective (localCone.f n n rfl)
  /-- Kind: GLUE. Dual-condition components are bijective; tex 4438–4442. -/
  condition_bijective : ∀ n, Function.Bijective (condition.f n n rfl)
  /-- Kind: GLUE. The global trace-duality square commutes; tex 4438–4442. -/
  global_square : ∀ (tr : (coneCx N.resE).X 3 →ₗ[A] A)
    (htr : ∀ z, tr ((coneCx N.resE).d 2 3 rfl z) = 0),
    GHom.toCC (globalDualityMap Q (pullScalarTrace Q N scalar tr)
      (pullScalarTrace_kills Q N scalar tr htr)) =
    GHom.toCC (ghomComp (ghomComp global (globalDualityMap N tr htr))
      (dualHom compact 3))
  /-- Kind: GLUE. The local trace-duality square commutes; tex 4438–4442. -/
  local_square : ∀ (tr : (coneCx N.resE).X 3 →ₗ[A] A)
    (htr : ∀ z, tr ((coneCx N.resE).d 2 3 rfl z) = 0),
    GHom.toCC (localDualityMap Q (pullScalarTrace Q N scalar tr)
      (pullScalarTrace_kills Q N scalar tr htr)) =
    GHom.toCC (ghomComp (ghomComp localCone (localDualityMap N tr htr))
      (dualHom condition 3))

/-- Kind: PROVED. Original global and local duality transport through the
specified cochain squares, not through dimension equalities;
tex 4385–4388, 4438–4442, 5040–5071. -/
theorem OriginalDiagramComparison.duality [Module.Injective A A]
    (T : OriginalDiagramComparison Q N) (tr : (coneCx N.resE).X 3 →ₗ[A] A)
    (htr : ∀ z, tr ((coneCx N.resE).d 2 3 rfl z) = 0)
    (hG : QuasiIso (GHom.toCC (globalDualityMap N tr htr)))
    (hL : QuasiIso (GHom.toCC (localDualityMap N tr htr))) :
    QuasiIso (GHom.toCC (globalDualityMap Q (pullScalarTrace Q N T.scalar tr)
      (pullScalarTrace_kills Q N T.scalar tr htr))) ∧
    QuasiIso (GHom.toCC (localDualityMap Q (pullScalarTrace Q N T.scalar tr)
      (pullScalarTrace_kills Q N T.scalar tr htr))) := by
  have : IsIso (GHom.toCC T.global) :=
    isIso_toCC_of_bijective T.global T.global_bijective
  have : IsIso (GHom.toCC T.compact) :=
    isIso_toCC_of_bijective T.compact T.compact_bijective
  have : IsIso (GHom.toCC T.localCone) :=
    isIso_toCC_of_bijective T.localCone T.localCone_bijective
  have : IsIso (GHom.toCC T.condition) :=
    isIso_toCC_of_bijective T.condition T.condition_bijective
  have : QuasiIso (GHom.toCC (dualHom T.compact 3)) :=
    dualHom_quasiIso T.compact 3 (inferInstance)
  have : QuasiIso (GHom.toCC (dualHom T.condition 3)) :=
    dualHom_quasiIso T.condition 3 (inferInstance)
  have : QuasiIso (GHom.toCC (globalDualityMap N tr htr)) := hG
  have : QuasiIso (GHom.toCC (localDualityMap N tr htr)) := hL
  constructor
  · rw [T.global_square tr htr, ← GHom.toCC_comp, ← GHom.toCC_comp]
    infer_instance
  · rw [T.local_square tr htr, ← GHom.toCC_comp, ← GHom.toCC_comp]
    infer_instance

end OriginalComparison

section ArithmeticStages

variable {K : Type} [Field K] [NumberField K]
  (S₀ : Set (HeightOneSpectrum (𝓞 K))) (W : WeierstrassCurve K) [W.IsElliptic]
  (α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ) [∀ i, IsOpenKer (α i)]

/-- Kind: definition. The arithmetic family has one new derivative place at
each coefficient precision. Old conditions are actual subcomplex maps at the
fixed old places. Tex 4401–4406, 4809–4830, 5055–5059. -/
structure ActualStageFamily where
  /-- Kind: definition. The derivative place; tex 4809–4830. -/
  q : ℕ → HeightOneSpectrum (𝓞 K)
  /-- Kind: GLUE. It is new relative to the old support; tex 4809–4830. -/
  new : ∀ i, q i ∉ S₀
  /-- Kind: GLUE. It has odd residue characteristic; tex 4809–4830. -/
  odd : ∀ i, (2 : 𝓞 K) ∉ (q i).asIdeal
  /-- Kind: definition. The old condition in the enlarged coefficient model;
  tex 4385–4388, 5055–5059. -/
  old : ∀ (i : ℕ) (v : Places K S₀),
    CondAt K (insert (q i) S₀) (Acoef i)
      (Mcoef K (insert (q i) S₀) W i
        (characterAfterSupport (S := insert (q i) S₀) (S₀ := S₀)
          (fun _ h => Or.inr h) i (α i)))
      ⟨v.1, Or.inr v.2⟩

variable {S₀ W α}

/-- Kind: definition. The actual enlarged support; tex 4809–4830. -/
abbrev ActualStageFamily.support (F : ActualStageFamily S₀ W α) (i : ℕ) :=
  insert (F.q i) S₀

omit [W.IsElliptic] in
/-- Kind: PROVED. The old support is contained in the enlarged support;
tex 4809–4830. -/
theorem ActualStageFamily.inclusion (F : ActualStageFamily S₀ W α) (i : ℕ) :
    S₀ ⊆ F.support i := fun _ h => Or.inr h

/-- Kind: definition. The unchanged arithmetic character on the enlarged
support; tex 2781–2796, 4809–4830. -/
abbrev ActualStageFamily.character (F : ActualStageFamily S₀ W α) (i : ℕ) :=
  characterAfterSupport (F.inclusion i) i (α i)

/-- Kind: definition. The coefficient module is formed on the enlarged
support, before restriction to any local group; tex 4385–4388, 4809–4830. -/
abbrev ActualStageFamily.coefficient (F : ActualStageFamily S₀ W α) (i : ℕ) :=
  Mcoef K (F.support i) W i (F.character i)

/-- Kind: definition. The old local conditions, indexed only by old places;
tex 4385–4388, 5055–5059. -/
def ActualStageFamily.conditions (F : ActualStageFamily S₀ W α) (i : ℕ) :
    LocalConditions (Acoef i) (GKS K (F.support i))
      (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K (F.support i) v.1) (F.coefficient i) where
  U v := (F.old i v).U
  i v := (F.old i v).i

/-- Kind: definition. The actual stage Selmer datum absorbs only the old
places. The derivative place is not included a second time;
tex 4385–4388, 4401–4406, 5055–5065. -/
def ActualStageFamily.datum (F : ActualStageFamily S₀ W α) (i : ℕ) : SelData (Acoef i) :=
  selData (Acoef i) (GKS K (F.support i)) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K (F.support i) v.1) (F.coefficient i) (F.conditions i)

/-- Kind: definition. The global input to the retained producer is the actual
old-condition Selmer complex; tex 4385–4388, 4391–4406. -/
abbrev ActualStageFamily.globalCx (F : ActualStageFamily S₀ W α) (i : ℕ) :=
  selCx (F.datum i)

/-- Kind: definition. The local complex has the exact native restricted
coefficient type of the normalized pairing supplier; tex 4859–4868. -/
abbrev ActualStageFamily.localCx (F : ActualStageFamily S₀ W α) (i : ℕ) :=
  actualStageLocalCx W i (F.character i) (F.q i)

/-- Kind: definition. Actual restriction of global continuous cochains to the
derivative place; tex 4859–4868. -/
def ActualStageFamily.restriction (F : ActualStageFamily S₀ W α) (i : ℕ) :
    GHom (F.datum i).G (F.localCx i) :=
  natHom (resCochains (k := Acoef i) (M := F.coefficient i)
    (locMap K (F.support i) (F.q i)))

/-- Kind: PROVED. The enlarged support retains the full coefficient torsion;
tex 2725–2727, 4809–4830. -/
theorem ActualStageFamily.fullTorsion (F : ActualStageFamily S₀ W α)
    [HasFullTwoTorsion K S₀ W] (i : ℕ) :
    FullTorsion K (F.support i) W (2 ^ i) := by
  have : NeZero (2 ^ i) := ⟨pow_ne_zero i two_ne_zero⟩
  exact fullTorsion_afterSupport (F.inclusion i) W (2 ^ i)
    (HasFullTwoTorsion.full i)

/-- Kind: PROVED. Native derivative-local residual cohomology is finite from
the existing local finiteness supplier. This is not an additional input to the
normalized pairing producer; tex 4392–4394, 4859–4868. -/
theorem ActualStageFamily.local_residual_finite (F : ActualStageFamily S₀ W α)
    (hloc : MilneLocalFiniteness) (i : ℕ) [NeZero i] (n : ℤ) :
    Module.Finite (ResidueField (Acoef i)) (residualCohomologyAt (F.localCx i) n) :=
  finite_residualCohomologyAt_of
    (localCx_residualCohomologyFinite K (F.support i) (F.coefficient i) hloc
      ⟨F.q i, Or.inl rfl⟩) n

end ArithmeticStages

section PrintedArithmetic

variable (K : Type) [Field K] [NumberField K]

/-- Kind: PRINT. The independent finiteness, dimension, local-duality, global-duality,
and normalized-trace statements used by the arithmetic assembly;
tex 4391–4451, 5035–5071. -/
structure ArithmeticPrints where
  /-- Kind: PRINT. Local finiteness; tex 4392–4394, 4547. -/
  localFinite : MilneLocalFiniteness
  /-- Kind: PRINT. Global finiteness; tex 4392–4394, 4526. -/
  globalFinite : MilneGlobalFiniteness
  /-- Kind: PRINT. Global dimension two; tex 4392–4394, 4526. -/
  globalDimension : MilneADT_I_4_10_totallyComplex
  /-- Kind: PRINT. Local dimension two; tex 4392–4394, 4547. -/
  localDimension : MilneLocalDimensionTwo
  /-- Kind: PRINT. The arithmetic local Kummer pairing; tex 3413–3468, 5055–5059. -/
  localKummer : MilneLocalTateDualityKummerCharZero
  /-- Kind: PRINT. Full local duality; tex 3454–3456, 5067–5071. -/
  localDuality : NekovarProp524 K
  /-- Kind: PRINT. Finite global duality; tex 4391–4451, 5067–5071. -/
  globalDuality : NekovarProp543T K
  /-- Kind: PRINT. Unramified old-condition duality; tex 3483–3498, 5055–5059. -/
  unramifiedDuality : NekovarProp756 K
  /-- Kind: PRINT. Normalized local and global traces; tex 4385–4388, 3465–3467. -/
  traces : NekovarFiniteTraces K

end PrintedArithmetic

/-- Kind: definition. The canonical discrete finite-coefficient topology used
by the unramified arithmetic conditions; tex 4391–4414. -/
local instance stageTopology (i : ℕ) : TopologicalSpace (Acoef i) := acoefTop i

/-- Kind: PROVED. The canonical finite-coefficient topology is discrete;
tex 4391–4414. -/
local instance stageDiscrete (i : ℕ) : DiscreteTopology (Acoef i) := acoefTop_discrete i

section NativeOriginal

variable {K : Type} [Field K] [NumberField K]
  {S₀ : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K} [W.IsElliptic]
  {α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ} [∀ i, IsOpenKer (α i)]
  (F : ActualStageFamily S₀ W α) [HasFullTwoTorsion K S₀ W]

/-- Kind: definition. The original arithmetic old-condition and derivative
truncation data. These are coefficient and condition data, not duality
conclusions; tex 2743–2760, 5055–5071. -/
structure OldDualityData where
  /-- Kind: definition. The old quadratic generator; tex 2743–2760. -/
  root : KS K S₀
  /-- Kind: definition. The old quadratic parameter; tex 2743–2760. -/
  parameter : K
  /-- Kind: GLUE. The actual quadratic relation; tex 2743–2760. -/
  square : root ^ 2 = algebraMap K (KS K S₀) parameter
  /-- Kind: GLUE. The quadratic generator is nonzero; tex 2743–2760. -/
  nonzero : root ≠ 0
  /-- Kind: definition. The primitive Kummer places; tex 2743–2760, 5055–5059. -/
  kummerPlaces : Set (HeightOneSpectrum (𝓞 K))
  /-- Kind: ELLIOT. The old arithmetic character dictionary; tex 2729, 3500–3506. -/
  locallyQuadratic : ∀ i [NeZero i], ∀ v ∈ kummerPlaces,
    IsLocallyQuadAt i (α i) (quadChar root square nonzero) v
  /-- Kind: GLUE. Original global roots of unity; tex 2725–2727, 4385–4388. -/
  roots : ∀ i [NeZero i], HasRootsOfUnity K S₀ (2 ^ i)
  /-- Kind: definition. Previously specified derivative truncations;
  tex 5055–5059. -/
  derivatives : ∀ i, Finset (Places K (F.support i))
  /-- Kind: GLUE. Previous derivative places are old; tex 5055–5059. -/
  derivative_old : ∀ i v, v ∈ derivatives i → v.1 ∈ S₀
  /-- Kind: definition. The actual first old derivative condition;
  tex 5055–5059. -/
  derivativeA : ∀ i [NeZero i] (v : Places K (F.support i)), v ∈ derivatives i →
    CondAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (α i)) v
  /-- Kind: definition. The actual second old derivative condition;
  tex 5055–5059. -/
  derivativeB : ∀ i [NeZero i] (v : Places K (F.support i)), v ∈ derivatives i →
    CondAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (charInv (α i))) v
  /-- Kind: definition. Actual original first old conditions, including the
  primitive full/zero choices at conjugate places; tex 5055–5059. -/
  originalOldA : ∀ i [NeZero i] (v : Places K (F.support i)),
    CondAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (α i)) v
  /-- Kind: definition. Actual original second old conditions, including the
  conjugate primitive choices; tex 5055–5059. -/
  originalOldB : ∀ i [NeZero i] (v : Places K (F.support i)),
    CondAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (charInv (α i))) v

variable {F} (O : OldDualityData F) (i : ℕ) [NeZero i]

/-- Kind: definition. Original first conditions, with the new place fully
relaxed before the relative compact comparison; tex 4385–4388, 5055–5071. -/
def OldDualityData.oldA (v : Places K (F.support i)) :
    CondAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (α i)) v :=
  if v.1 = F.q i then fullAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (α i)) v
  else O.originalOldA i v

/-- Kind: definition. Original second conditions, with the new place strictly
zero in the auxiliary all-place comparison; tex 4385–4388, 5055–5071. -/
def OldDualityData.oldB (v : Places K (F.support i)) :
    CondAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (charInv (α i))) v :=
  if v.1 = F.q i then zeroAt K (F.support i) (Acoef i)
    (MinS (F.inclusion i) W i (charInv (α i))) v
  else O.originalOldB i v

/-- Kind: definition. Retain the actual old first derivative condition instead
of replacing it by a strict truncation; tex 5055–5059. -/
def OldDualityData.atA (v : Places K (F.support i)) :
    CondAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (α i)) v :=
  if hv : v ∈ O.derivatives i then O.derivativeA i v hv else O.oldA i v

/-- Kind: definition. Retain the actual old second derivative condition instead
of replacing it by a relaxed truncation; tex 5055–5059. -/
def OldDualityData.atB (v : Places K (F.support i)) :
    CondAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (charInv (α i))) v :=
  if hv : v ∈ O.derivatives i then O.derivativeB i v hv else O.oldB i v

/-- Kind: definition. Original first arithmetic conditions, including the
actual old derivative conditions; tex 5055–5071. -/
def OldDualityData.conditionsA :
    GaloisLocalConditions K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (α i)) :=
  ofCondAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (α i)) (O.atA i)

/-- Kind: definition. Original second arithmetic conditions, including the
actual old derivative conditions; tex 5055–5071. -/
def OldDualityData.conditionsB :
    GaloisLocalConditions K (F.support i) (Acoef i)
      (MinS (F.inclusion i) W i (charInv (α i))) :=
  ofCondAt K (F.support i) (Acoef i)
    (MinS (F.inclusion i) W i (charInv (α i))) (O.atB i)

/-- Kind: definition. The original inflated Weil pairing, before any actual
cochain comparison to the enlarged-support coefficient model;
tex 4385–4388, 5035–5071. -/
abbrev OldDualityData.coefficientPair := actLBeta (F.inclusion i) W i (α i) (O.roots i)

/-- Kind: definition. Actual original isotropy data, not a split-stage pairing;
tex 4385–4388, 5055–5071. -/
abbrev OldDualityData.Isotropy :=
  GaloisTruncIsotropyData K (F.support i) (Acoef i) (O.coefficientPair i)
    (actLBeta_smul (F.inclusion i) W i (α i) (O.roots i))
    (O.conditionsA i) (O.conditionsB i)

/-- Kind: definition. The actual original paired Galois-cochain diagram;
tex 4385–4388, 5035–5071. -/
abbrev OldDualityData.pair (I : O.Isotropy i) :=
  galoisPairDataT K (F.support i) (Acoef i) (O.coefficientPair i)
    (actLBeta_smul (F.inclusion i) W i (α i) (O.roots i))
    (O.conditionsA i) (O.conditionsB i) I

/-- Kind: PROVED. The full local-duality print applies to the original
inflated coefficient systems at each derivative place; tex 5055–5071. -/
theorem OldDualityData.full_local_duality (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (L : FiniteLocalTraces (F.support i) (Acoef i)
      (InflMod (F.inclusion i) (Tate1 (Acoef i) (O.roots i))))
    (v : Places K (F.support i)) :
    QuasiIso (GHom.toCC (adjHom (orthGaloisPair K (O.coefficientPair i)
      (actLBeta_smul (F.inclusion i) W i (α i) (O.roots i)) v)
      2 (L.trv v) (L.htrv₁ v))) := by
  have : Finite (MinS (F.inclusion i) W i (α i)) :=
    inferInstanceAs (Finite (Mcoef K S₀ W i (α i)))
  have : Finite (MinS (F.inclusion i) W i (charInv (α i))) :=
    inferInstanceAs (Finite (Mcoef K S₀ W i (charInv (α i))))
  exact p.localDuality (F.support i) 2 (Acoef i)
    (nekovarFiniteSetting_acoef K hK (F.support i) (hS₀.insert (F.q i))
      (fun v hv => F.inclusion i (h2 v hv)) i)
    (MinS (F.inclusion i) W i (α i)) (MinS (F.inclusion i) W i (charInv (α i)))
    (InflMod (F.inclusion i) (Tate1 (Acoef i) (O.roots i))) (O.coefficientPair i)
    (actLBeta_smul (F.inclusion i) W i (α i) (O.roots i))
    (weilPairingM_bijective W (O.roots i) (Acoef i) (α i) (HasFullTwoTorsion.full i))
    (weilPairingM_flip_bijective W (O.roots i) (Acoef i) (α i)
      (HasFullTwoTorsion.full i))
    (cycloInfl_isCyclotomicTwist_tate1 (F.inclusion i) i (O.roots i))
    v (L.trv v) (L.htrv₁ v) (L.iso v)

/-- Kind: definition. Canonical first old conditions of the established
Kummer/full/unramified complement supplier; tex 5055–5059. -/
abbrev OldDualityData.canonicalOldA (v : Places K (F.support i)) :=
  actLCondA (F.inclusion i) W i O.root O.square O.nonzero
    (HasFullTwoTorsion.full i) O.kummerPlaces (α i) (O.locallyQuadratic i) v

/-- Kind: definition. Canonical second old conditions of the established
complement supplier; tex 5055–5059. -/
abbrev OldDualityData.canonicalOldB (v : Places K (F.support i)) :=
  actLCondB (F.inclusion i) W i O.root O.square O.nonzero
    (HasFullTwoTorsion.full i) O.kummerPlaces (α i) (O.locallyQuadratic i) v

/-- Kind: definition. Old pairs whose complement theorem is already supplied:
canonical arithmetic conditions, either full/zero orientation, or the actual
strict/relaxed truncation pair. Tex 2813–2814, 5055–5071. -/
def OldDualityData.KnownOldPair (v : Places K (F.support i)) : Prop :=
  (O.oldA i v = O.canonicalOldA i v ∧ O.oldB i v = O.canonicalOldB i v) ∨
  (O.oldA i v = fullAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (α i)) v ∧
    O.oldB i v = zeroAt K (F.support i) (Acoef i)
      (MinS (F.inclusion i) W i (charInv (α i))) v) ∨
  (O.oldA i v = zeroAt K (F.support i) (Acoef i) (MinS (F.inclusion i) W i (α i)) v ∧
    O.oldB i v = fullAt K (F.support i) (Acoef i)
      (MinS (F.inclusion i) W i (charInv (α i))) v) ∨
  (O.oldA i v = derivativeStrictAt v ∧ O.oldB i v = derivativeRelaxedAt v)

/-- Kind: GLUE. Only actual old pairs not matching any supplied complement
shape require an additional original cochain-complement input. This avoids
changing primitive full/zero choices or actual old planes to other conditions.
Tex 5055–5071. -/
def OldDualityData.OtherOldComplements : Prop :=
  ∀ (L : FiniteLocalTraces (F.support i) (Acoef i)
      (InflMod (F.inclusion i) (Tate1 (Acoef i) (O.roots i))))
    (v : Places K (F.support i)), ¬ O.KnownOldPair i v →
    ∀ (J : LocalTruncIsotropy (O.oldA i v).i (O.oldB i v).i
      (orthGaloisPair K (O.coefficientPair i)
        (actLBeta_smul (F.inclusion i) W i (α i) (O.roots i)) v)),
      QuasiIso (GHom.toCC (orthLocalMap (O.oldA i v).i (O.oldB i v).i
        (orthGaloisPair K (O.coefficientPair i)
          (actLBeta_smul (F.inclusion i) W i (α i) (O.roots i)) v)
        J (L.trv v) (L.htrv₁ v)))

/-- Kind: PROVED. All established old complement cases, including both
primitive full/zero orientations, are supplied. Only genuinely unmatched
original old conditions consume the named remaining input; tex 5055–5071. -/
theorem OldDualityData.old_complement (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (hOther : O.OtherOldComplements i)
    (L : FiniteLocalTraces (F.support i) (Acoef i)
      (InflMod (F.inclusion i) (Tate1 (Acoef i) (O.roots i))))
    (v : Places K (F.support i))
    (J : LocalTruncIsotropy (O.oldA i v).i (O.oldB i v).i
      (orthGaloisPair K (O.coefficientPair i)
        (actLBeta_smul (F.inclusion i) W i (α i) (O.roots i)) v)) :
    QuasiIso (GHom.toCC (orthLocalMap (O.oldA i v).i (O.oldB i v).i
      (orthGaloisPair K (O.coefficientPair i)
        (actLBeta_smul (F.inclusion i) W i (α i) (O.roots i)) v)
      J (L.trv v) (L.htrv₁ v))) := by
  by_cases hstd : O.oldA i v = O.canonicalOldA i v ∧ O.oldB i v = O.canonicalOldB i v
  · exact actLPerf_congr _ _ hstd.1 hstd.2 (L.trv v) (L.htrv₁ v)
      (fun J' => actLPerf (F.inclusion i) W i O.root O.square O.nonzero
        (HasFullTwoTorsion.full i) O.kummerPlaces (α i) (O.roots i)
        (O.locallyQuadratic i) L.trv L.htrv₁ p.localKummer p.localDuality
        p.unramifiedDuality hK (hS₀.insert (F.q i)) hS₀ h2 L.iso v J') J
  · by_cases hFZ : O.oldA i v = fullAt K (F.support i) (Acoef i)
        (MinS (F.inclusion i) W i (α i)) v ∧
        O.oldB i v = zeroAt K (F.support i) (Acoef i)
          (MinS (F.inclusion i) W i (charInv (α i))) v
    · exact actLPerf_congr _ _ hFZ.1 hFZ.2 (L.trv v) (L.htrv₁ v)
        (actLPerf_full_zero _ _ v (L.trv v) (L.htrv₁ v)) J
    · by_cases hZF : O.oldA i v = zeroAt K (F.support i) (Acoef i)
          (MinS (F.inclusion i) W i (α i)) v ∧
          O.oldB i v = fullAt K (F.support i) (Acoef i)
            (MinS (F.inclusion i) W i (charInv (α i))) v
      · exact actLPerf_congr _ _ hZF.1 hZF.2 (L.trv v) (L.htrv₁ v)
          (fun J' => zero_full_complement
            (orthGaloisPair K (O.coefficientPair i)
              (actLBeta_smul (F.inclusion i) W i (α i) (O.roots i)) v)
            (L.trv v) (L.htrv₁ v) J' (O.full_local_duality i p hK hS₀ h2 L v)) J
      · by_cases hSR : O.oldA i v = derivativeStrictAt v ∧
            O.oldB i v = derivativeRelaxedAt v
        · have : Module.Injective (Acoef i) (Acoef i) := acoef_selfInjective i
          exact actLPerf_congr _ _ hSR.1 hSR.2 (L.trv v) (L.htrv₁ v)
            (fun J' => derivativeAt_local_complement (O.coefficientPair i)
              (actLBeta_smul (F.inclusion i) W i (α i) (O.roots i)) v
              (L.trv v) (L.htrv₁ v) J' (O.full_local_duality i p hK hS₀ h2 L v)) J
        · exact hOther L v (fun h => h.elim hstd
            (fun h => h.elim hFZ (fun h => h.elim hZF hSR))) J

/-- Kind: GLUE. Complement comparison for an actual old derivative condition
which is not the supplied strict/relaxed truncation pair. In particular, old
finite/singular conditions are not silently changed to that different pair.
Tex 5055–5059, 5067–5071. -/
def OldDualityData.OtherDerivativeComplements : Prop :=
  ∀ (L : FiniteLocalTraces (F.support i) (Acoef i)
      (InflMod (F.inclusion i) (Tate1 (Acoef i) (O.roots i))))
    (v : Places K (F.support i)) (hv : v ∈ O.derivatives i),
    (O.derivativeA i v hv ≠ derivativeStrictAt v ∨
      O.derivativeB i v hv ≠ derivativeRelaxedAt v) →
    ∀ (J : ZInQ.Contrib.CloudB3RC53.Duality.LocalTruncIsotropy
      (O.derivativeA i v hv).i (O.derivativeB i v hv).i
      (orthGaloisPair K (O.coefficientPair i)
        (actLBeta_smul (F.inclusion i) W i (α i) (O.roots i)) v)),
      QuasiIso (GHom.toCC (orthLocalMap
        (O.derivativeA i v hv).i (O.derivativeB i v hv).i
        (orthGaloisPair K (O.coefficientPair i)
          (actLBeta_smul (F.inclusion i) W i (α i) (O.roots i)) v)
        J (L.trv v) (L.htrv₁ v)))

/-- Kind: PROVED. Use the verified truncation complement whenever its exact
condition types match. Only other old derivative conditions consume the named
remaining comparison; tex 5055–5071. -/
theorem OldDualityData.derivative_complement (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (hOther : O.OtherDerivativeComplements i)
    (L : FiniteLocalTraces (F.support i) (Acoef i)
      (InflMod (F.inclusion i) (Tate1 (Acoef i) (O.roots i))))
    (v : Places K (F.support i)) (hv : v ∈ O.derivatives i)
    (J : ZInQ.Contrib.CloudB3RC53.Duality.LocalTruncIsotropy
      (O.derivativeA i v hv).i (O.derivativeB i v hv).i
      (orthGaloisPair K (O.coefficientPair i)
        (actLBeta_smul (F.inclusion i) W i (α i) (O.roots i)) v)) :
    QuasiIso (GHom.toCC (orthLocalMap
      (O.derivativeA i v hv).i (O.derivativeB i v hv).i
      (orthGaloisPair K (O.coefficientPair i)
        (actLBeta_smul (F.inclusion i) W i (α i) (O.roots i)) v)
      J (L.trv v) (L.htrv₁ v))) := by
  by_cases hA : O.derivativeA i v hv = derivativeStrictAt v
  · by_cases hB : O.derivativeB i v hv = derivativeRelaxedAt v
    · have : Module.Injective (Acoef i) (Acoef i) := acoef_selfInjective i
      exact actLPerf_congr _ _ hA hB (L.trv v) (L.htrv₁ v)
        (fun J' => derivativeAt_local_complement (O.coefficientPair i)
          (actLBeta_smul (F.inclusion i) W i (α i) (O.roots i)) v
          (L.trv v) (L.htrv₁ v) J' (O.full_local_duality i p hK hS₀ h2 L v)) J
    · exact hOther L v hv (Or.inr hB) J
  · exact hOther L v hv (Or.inl hA) J

/-- Kind: PROVED. Assemble old-condition orthogonality place by place, retaining
actual old derivative conditions and using the verified strict/relaxed theorem
only where it matches; tex 5055–5071. -/
theorem OldDualityData.local_complements [Fintype (Places K (F.support i))]
    (p : ArithmeticPrints K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (hOld : O.OtherOldComplements i)
    (hOther : O.OtherDerivativeComplements i) (I : O.Isotropy i)
    (L : FiniteLocalTraces (F.support i) (Acoef i)
      (InflMod (F.inclusion i) (Tate1 (Acoef i) (O.roots i))))
    (tr : (coneCx (O.pair i I).resE).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((coneCx (O.pair i I).resE).d 2 3 rfl z) = 0)
    (hN : L.Normalizes tr) :
    QuasiIso (GHom.toCC (localDualityMap (O.pair i I) tr htr)) := by
  apply orthogonalComplementsT_of_places K (O.coefficientPair i)
    (actLBeta_smul (F.inclusion i) W i (α i) (O.roots i))
    (O.conditionsA i) (O.conditionsB i) I L.trv L.htrv₁ tr htr hN
  intro v
  by_cases hv : v ∈ O.derivatives i
  · exact actLPerf_congr _ _ (by simp only [OldDualityData.atA, dite_eq_left hv])
      (by simp only [OldDualityData.atB, dite_eq_left hv]) (L.trv v) (L.htrv₁ v)
      (O.derivative_complement i p hK hS₀ h2 hOther L v hv) (I.toLocal v)
  · exact actLPerf_congr _ _ (by simp only [OldDualityData.atA, dite_eq_right hv])
      (by simp only [OldDualityData.atB, dite_eq_right hv]) (L.trv v) (L.htrv₁ v)
      (O.old_complement i p hK hS₀ h2 hOld L v) (I.toLocal v)

/-- Kind: PROVED. The finite global-duality print applies to the actual
original coefficient systems on the enlarged support; tex 4385–4451. -/
theorem OldDualityData.global_duality (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (I : O.Isotropy i)
    (tr : (coneCx (O.pair i I).resE).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((coneCx (O.pair i I).resE).d 2 3 rfl z) = 0)
    (h3 : InducesIsoH3 tr) :
    QuasiIso (GHom.toCC (globalDualityMap (O.pair i I) tr htr)) := by
  have : Finite (MinS (F.inclusion i) W i (α i)) :=
    inferInstanceAs (Finite (Mcoef K S₀ W i (α i)))
  have : Finite (MinS (F.inclusion i) W i (charInv (α i))) :=
    inferInstanceAs (Finite (Mcoef K S₀ W i (charInv (α i))))
  exact p.globalDuality (F.support i) 2 (Acoef i)
    (nekovarFiniteSetting_acoef K hK (F.support i) (hS₀.insert (F.q i))
      (fun v hv => F.inclusion i (h2 v hv)) i)
    (MinS (F.inclusion i) W i (α i)) (MinS (F.inclusion i) W i (charInv (α i)))
    (InflMod (F.inclusion i) (Tate1 (Acoef i) (O.roots i))) (O.coefficientPair i)
    (actLBeta_smul (F.inclusion i) W i (α i) (O.roots i))
    (weilPairingM_bijective W (O.roots i) (Acoef i) (α i) (HasFullTwoTorsion.full i))
    (weilPairingM_flip_bijective W (O.roots i) (Acoef i) (α i)
      (HasFullTwoTorsion.full i))
    (cycloInfl_isCyclotomicTwist_tate1 (F.inclusion i) i (O.roots i))
    (O.conditionsA i) (O.conditionsB i) I tr htr h3

/-- Kind: PROVED. The original trace and both original duality obligations
come from the printed arithmetic results and the established old-condition
and derivative-truncation complement computations. Tex 4385–4451, 5055–5071. -/
theorem OldDualityData.exists_original_trace_duality (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (hOld : O.OtherOldComplements i)
    (hOther : O.OtherDerivativeComplements i) (I : O.Isotropy i) :
    ∃ (tr : (coneCx (O.pair i I).resE).X 3 →ₗ[Acoef i] Acoef i)
      (htr : ∀ z, tr ((coneCx (O.pair i I).resE).d 2 3 rfl z) = 0),
      QuasiIso (GHom.toCC (globalDualityMap (O.pair i I) tr htr)) ∧
      QuasiIso (GHom.toCC (localDualityMap (O.pair i I) tr htr)) := by
  let S := F.support i
  have hS : S.Finite := hS₀.insert (F.q i)
  let : Fintype (Places K S) := hS.fintype
  have h2S : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S :=
    fun v hv => F.inclusion i (h2 v hv)
  have hset := nekovarFiniteSetting_acoef K hK S hS h2S i
  have hT := cycloInfl_isCyclotomicTwist_tate1 (F.inclusion i) i (O.roots i)
  have : Finite (MinS (F.inclusion i) W i (α i)) :=
    inferInstanceAs (Finite (Mcoef K S₀ W i (α i)))
  have : Finite (MinS (F.inclusion i) W i (charInv (α i))) :=
    inferInstanceAs (Finite (Mcoef K S₀ W i (charInv (α i))))
  obtain ⟨L, hL⟩ := p.traces S 2 (Acoef i) hset
    (InflMod (F.inclusion i) (Tate1 (Acoef i) (O.roots i))) hT
  obtain ⟨tr, htr, h3, hN⟩ := hL (MinS (F.inclusion i) W i (α i))
    (MinS (F.inclusion i) W i (charInv (α i))) (O.coefficientPair i)
    (actLBeta_smul (F.inclusion i) W i (α i) (O.roots i))
    (O.conditionsA i) (O.conditionsB i) I
  exact ⟨tr, htr, O.global_duality i p hK hS₀ h2 I tr htr h3,
    O.local_complements i p hK hS₀ h2 hOld hOther I L tr htr hN⟩

end NativeOriginal

section ReferenceFamily

variable {K : Type} [Field K] [NumberField K]
  (S₀ : Set (HeightOneSpectrum (𝓞 K))) (W : WeierstrassCurve K) [W.IsElliptic]
  (α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ) [∀ i, IsOpenKer (α i)]

/-- Kind: definition. Fixed-support standard old conditions used by the existing
residual finiteness and bounded-rank suppliers; tex 4401–4406. -/
structure StandardOldReference where
  /-- Kind: definition. The fixed local elliptic curves; tex 3413–3468. -/
  curve : ∀ v : Places K S₀, WeierstrassCurve (v.1.adicCompletion K)
  /-- Kind: GLUE. The local curves are elliptic; tex 3413–3468. -/
  elliptic : ∀ v, (curve v).IsElliptic
  /-- Kind: definition. The torsion levels; tex 3413–3468. -/
  level : ℕ → ℕ
  /-- Kind: GLUE. The torsion levels are nonzero; tex 3413–3468. -/
  level_nonzero : ∀ i, NeZero (level i)
  /-- Kind: definition. Zero, full, and Kummer labels; tex 4401–4406. -/
  label : ℕ → Places K S₀ → ℕ
  /-- Kind: definition. The actual local coefficient maps; tex 3413–3468. -/
  iota : ∀ i (v : Places K S₀), letI := elliptic v
    TorsAlg (v.1.adicCompletion K) (curve v) (level i) →+
      ResMod (locMap K S₀ v.1) (MinS (fun _ h => h) W i (α i))
  /-- Kind: GLUE. Equivariance of the actual local coefficient maps; tex 3413–3468. -/
  equivariant : ∀ i (v : Places K S₀), letI := elliptic v
    ∀ (g : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (curve v) (level i)),
      iota i v (g • t) = g • iota i v t

variable {S₀ W α}

/-- Kind: PROVED. Ellipticity is carried by the fixed arithmetic curve data;
tex 3413–3468. -/
local instance referenceElliptic (R : StandardOldReference S₀ W α) (v : Places K S₀) :
    (R.curve v).IsElliptic := R.elliptic v

/-- Kind: PROVED. Nonzero torsion levels are carried by the arithmetic data;
tex 3413–3468. -/
local instance referenceLevel (R : StandardOldReference S₀ W α) (i : ℕ) :
    NeZero (R.level i) := R.level_nonzero i

/-- Kind: definition. The exact standard old Selmer datum of the fixed-support
supplier; tex 4401–4406. -/
def StandardOldReference.datum (R : StandardOldReference S₀ W α) (i : ℕ) :
    SelData (Acoef i) :=
  actualSelData (fun _ h => h) W i (α i) (fun v _ =>
    standardOldAt K S₀ (Acoef i) (MinS (fun _ h => h) W i (α i))
      v (R.label i v) (R.curve v) (R.level i) (R.iota i v) (R.equivariant i v))

/-- Kind: definition. The fixed-support reference stage complex; tex 4401–4406. -/
abbrev StandardOldReference.globalCx (R : StandardOldReference S₀ W α) (i : ℕ) :=
  selCx (R.datum i)

/-- Kind: PROVED. All reference local conditions have finite residual
cohomology, with no condition-finiteness input left; tex 4392–4394. -/
theorem StandardOldReference.residual_finite (R : StandardOldReference S₀ W α)
    (p : ArithmeticPrints K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (i : ℕ) [NeZero i] : ResidualCohomologyFinite (R.globalCx i) := by
  have : Finite (MinS (fun _ h => h) W i (α i)) :=
    inferInstanceAs (Finite (Mcoef K S₀ W i (α i)))
  apply actualStageSelmer_residualCohomologyFinite (fun _ h => h) W i (α i)
    p.localFinite p.globalFinite hS₀ h2
  intro v _
  unfold standardOldAt
  split_ifs
  · exact residualCohomologyFinite_zeroCx
  · exact localCx_residualCohomologyFinite K S₀ (MinS (fun _ h => h) W i (α i))
      p.localFinite v
  · have : Finite (ResMod (locMap K S₀ v.1) (MinS (fun _ h => h) W i (α i))) :=
      inferInstanceAs (Finite (Mcoef K S₀ W i (α i)))
    exact residualCohomologyFinite_cocycleCondition _ _
      (p.localFinite K v.1 (Acoef i)
        (ResMod (locMap K S₀ v.1) (MinS (fun _ h => h) W i (α i))) inferInstance 1)

/-- Kind: PROVED. The existing standard-old supplier gives the range `[0,3]`
and one rank bound at the fixed support; tex 4401–4406. -/
theorem StandardOldReference.producerBounds (R : StandardOldReference S₀ W α)
    [HasFullTwoTorsion K S₀ W] (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) :
    ∃ B : ℕ,
      (∀ i [NeZero i] (n : ℤ), n < 0 ∨ 3 < n →
        Module.finrank (ResidueField (Acoef i))
          (residualCohomologyAt (R.globalCx i) n) = 0) ∧
      (∀ i [NeZero i] (n : ℤ), Module.finrank (ResidueField (Acoef i))
        (residualCohomologyAt (R.globalCx i) n) ≤ B) :=
  standardOld_producerBounds (fun _ h => h) W α
    (fun i => HasFullTwoTorsion.full i) p.globalDimension p.localDimension
    p.localFinite p.globalFinite hK hS₀ h2 R.curve R.label R.level R.iota R.equivariant

end ReferenceFamily

section ResidualControl

/-- Kind: definition. A fixed number of extra residual coordinates, only in
the Selmer range; tex 4401–4406. -/
def extraRank (width : ℕ) (n : ℤ) : ℕ := if 0 ≤ n ∧ n ≤ 3 then width else 0

/-- Kind: PROVED. The extra residual coordinates vanish outside `[0,3]`;
tex 4401–4406. -/
theorem extraRank_outside (width : ℕ) (n : ℤ) (hn : n < 0 ∨ 3 < n) :
    extraRank width n = 0 := ite_eq_right (by omega)

/-- Kind: PROVED. The extra coordinate count is uniformly bounded by its
specified width; tex 4401–4406. -/
theorem extraRank_le (width : ℕ) (n : ℤ) : extraRank width n ≤ width := by
  unfold extraRank
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

variable {K : Type} [Field K] [NumberField K]
  {S₀ : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K} [W.IsElliptic]
  {α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ} [∀ i, IsOpenKer (α i)]

/-- Kind: ELLIOT. The remaining residual-support comparison for one fixed
active support. The actual enlarged-support residual groups inject into the
fixed reference groups plus a bounded finite coordinate space. This is not a
rank bound uniform over all supports, nor an assumption about finite models.
Tex 4401–4406. -/
structure ResidualSupportControl (F : ActualStageFamily S₀ W α)
    (R : StandardOldReference S₀ W α) (width : ℕ) where
  /-- Kind: ELLIOT. The actual residual-support comparison; tex 4401–4406. -/
  map : ∀ i [NeZero i] (n : ℤ), residualCohomologyAt (F.globalCx i) n →ₗ[ResidueField (Acoef i)]
    residualCohomologyAt (R.globalCx i) n × (Fin (extraRank width n) → ResidueField (Acoef i))
  /-- Kind: ELLIOT. The residual comparison is injective; tex 4401–4406. -/
  injective : ∀ i [NeZero i] (n : ℤ), Function.Injective (map i n)

/-- Kind: PROVED. The support comparison and existing fixed-support finiteness
supplier prove finite residual cohomology for the actual stage complex;
tex 4392–4394, 4401–4406. -/
theorem ResidualSupportControl.residual_finite
    {F : ActualStageFamily S₀ W α} {R : StandardOldReference S₀ W α} {width : ℕ}
    (T : ResidualSupportControl F R width) (p : ArithmeticPrints K)
    (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (i : ℕ) [NeZero i] : ResidualCohomologyFinite (F.globalCx i) := by
  intro n
  have : Module.Finite (ResidueField (Acoef i))
      (residualCohomologyAt (R.globalCx i) n) :=
    finite_residualCohomologyAt_of (R.residual_finite p hS₀ h2 i) n
  have : Module.Finite (ResidueField (Acoef i))
      (residualCohomologyAt (F.globalCx i) n) :=
    Module.Finite.of_injective (T.map i n) (T.injective i n)
  exact (Module.Finite.equiv_iff (residualHomologyEquiv (F.globalCx i) n)).2 this

/-- Kind: PROVED. The support comparison and the existing fixed-support
rank supplier give the actual producer's range and uniform bound;
tex 4401–4406. -/
theorem ResidualSupportControl.producerBounds
    {F : ActualStageFamily S₀ W α} {R : StandardOldReference S₀ W α} {width : ℕ}
    (T : ResidualSupportControl F R width) [HasFullTwoTorsion K S₀ W]
    (p : ArithmeticPrints K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) :
    ∃ B : ℕ,
      (∀ i [NeZero i] (n : ℤ), n < 0 ∨ 3 < n →
        Module.finrank (ResidueField (Acoef i))
          (residualCohomologyAt (F.globalCx i) n) = 0) ∧
      (∀ i [NeZero i] (n : ℤ), Module.finrank (ResidueField (Acoef i))
        (residualCohomologyAt (F.globalCx i) n) ≤ B) := by
  obtain ⟨B, hbdd, hB⟩ := R.producerBounds p hK hS₀ h2
  have hle : ∀ i [NeZero i] (n : ℤ),
      Module.finrank (ResidueField (Acoef i)) (residualCohomologyAt (F.globalCx i) n) ≤
        Module.finrank (ResidueField (Acoef i)) (residualCohomologyAt (R.globalCx i) n) +
          extraRank width n := by
    intro i _ n
    have : Module.Finite (ResidueField (Acoef i))
        (residualCohomologyAt (R.globalCx i) n) :=
      finite_residualCohomologyAt_of (R.residual_finite p hS₀ h2 i) n
    have hr := LinearMap.finrank_le_finrank_of_injective (T.injective i n)
    simpa using hr
  refine ⟨B + width, ?_, ?_⟩
  · intro i _ n hn
    have hr := hle i n
    rw [hbdd i n hn, extraRank_outside width n hn, add_zero] at hr
    exact Nat.eq_zero_of_le_zero hr
  · intro i _ n
    exact (hle i n).trans (Nat.add_le_add (hB i n) (extraRank_le width n))

end ResidualControl

section RemainingArithmetic

variable {K : Type} [Field K] [NumberField K]
  {S₀ : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K} [W.IsElliptic]
  {α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ} [∀ i, IsOpenKer (α i)]

/-- Kind: GLUE. Only old conditions other than the already supplied full and
zero conditions require a term-flatness input; tex 4391–4414. -/
def ActualStageFamily.NontrivialOldFlat (F : ActualStageFamily S₀ W α) : Prop :=
  ∀ i [NeZero i] (v : Places K S₀),
    F.old i v ≠ fullAt K (F.support i) (Acoef i) (F.coefficient i) ⟨v.1, Or.inr v.2⟩ →
    F.old i v ≠ zeroAt K (F.support i) (Acoef i) (F.coefficient i) ⟨v.1, Or.inr v.2⟩ →
    ∀ n : ℤ, Module.Flat (Acoef i) ((F.old i v).U.X n)

/-- Kind: PROVED. Full and zero old conditions are supplied; other old terms
use only their named flatness input. Nilpotence turns flatness into freeness;
tex 4391–4414. -/
theorem ActualStageFamily.old_free (F : ActualStageFamily S₀ W α)
    [HasFullTwoTorsion K S₀ W] (hOld : F.NontrivialOldFlat)
    (i : ℕ) [NeZero i] (v : Places K S₀) (n : ℤ) :
    Module.Free (Acoef i) ((F.old i v).U.X n) := by
  have hnil := stageA_isNilpotent_maximalIdeal i
  have : Module.Free (Acoef i) (F.coefficient i) :=
    ZInQ.Manuscript.RC.Wiring.mcoef_free W i (F.character i) (F.fullTorsion i)
  have : Module.Flat (Acoef i) (F.coefficient i) := inferInstance
  by_cases hF : F.old i v =
      fullAt K (F.support i) (Acoef i) (F.coefficient i) ⟨v.1, Or.inr v.2⟩
  · rw [hF]
    exact ZInQ.Manuscript.RC.Wiring.fullAt_free hnil (F.coefficient i) _ n
  · by_cases hZ : F.old i v =
        zeroAt K (F.support i) (Acoef i) (F.coefficient i) ⟨v.1, Or.inr v.2⟩
    · rw [hZ]
      exact ZInQ.Manuscript.RC.Wiring.zeroAt_free (F.coefficient i) _ n
    · have : Module.Flat (Acoef i) ((F.old i v).U.X n) := hOld i v hF hZ n
      exact ZInQ.Manuscript.RC.Limits.flat_module_free hnil

/-- Kind: PROVED. Actual enlarged-support old-condition Selmer cochains have
flat terms from the existing continuous-cochain flatness theorem;
tex 4391–4414. -/
theorem ActualStageFamily.flat (F : ActualStageFamily S₀ W α)
    [HasFullTwoTorsion K S₀ W] (hS₀ : S₀.Finite) (hOld : F.NontrivialOldFlat) :
    ∀ i n, Module.Flat (StageA i) ((F.globalCx i).X n) := by
  intro i n
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    have : Subsingleton (StageA 0) := stageA_zero_subsingleton
    exact flat_over_zeroRing (StageA 0) ((F.globalCx 0).X n)
  · have : NeZero i := ⟨by omega⟩
    let : Fintype (Places K S₀) := hS₀.fintype
    have : ∀ v : Places K S₀, CompactSpace (Gloc K v.1) :=
      fun v => ZInQ.Manuscript.RC.FibreDuality.compactSpace_Gloc v.1
    have : Module.Free (Acoef i) (F.coefficient i) :=
      ZInQ.Manuscript.RC.Wiring.mcoef_free W i (F.character i) (F.fullTorsion i)
    have : Module.Flat (Acoef i) (F.coefficient i) := inferInstance
    exact flat_selmerCochains (stageA_isNilpotent_maximalIdeal i)
      (GKS K (F.support i)) (fun v : Places K S₀ => Gloc K v.1)
      (fun v => locMap K (F.support i) v.1) (F.coefficient i)
      (F.conditions i) (F.old_free hOld i) n

variable [HasFullTwoTorsion K S₀ W]
  (F : ActualStageFamily S₀ W α) (O : OldDualityData F) (i : ℕ) [NeZero i]

/-- Kind: GLUE. Precisely the remaining original arithmetic data at a positive
stage. Original cups and isotropy are inputs; the split projection, pairing,
trace, and global-duality quasi-isomorphism are not. Tex 4385–4451, 5035–5071. -/
structure StageArithmeticInput where
  /-- Kind: GLUE. The original same-condition old paired diagram;
  tex 4385–4388, 5055–5059. -/
  oldPair : SelPairData (F.datum i) (F.datum i)
  /-- Kind: definition. The original retained scalar local complex; tex 4385–4388. -/
  scalarLocal : GCx (Acoef i)
  /-- Kind: definition. The actual retained same-condition complex; tex 4859–4873. -/
  retainedCondition : GCx (Acoef i)
  /-- Kind: GLUE. Restriction in the original scalar cup target; tex 4385–4388. -/
  scalarRestriction : GHom oldPair.E scalarLocal
  /-- Kind: GLUE. The actual retained condition inclusion; tex 4859–4873. -/
  condition : GHom retainedCondition (F.localCx i)
  /-- Kind: GLUE. The actual retained local cup, before replacement; tex 5035–5043. -/
  localCup : GPair (F.localCx i) (F.localCx i) scalarLocal
  /-- Kind: GLUE. Actual localization compatibility and same-condition isotropy,
  with their full cochain identities; tex 4385–4388, 5035–5043. -/
  retained : RetainedPlaceInput (F.datum i) oldPair (F.localCx i)
    scalarLocal retainedCondition (F.restriction i) scalarRestriction condition localCup
  /-- Kind: GLUE. Actual original truncated isotropy; tex 4385–4388, 5055–5071. -/
  originalIsotropy : O.Isotropy i
  /-- Kind: GLUE. Only original old pairs not matching a supplied complement
  shape remain; tex 5055–5071. -/
  otherOld : O.OtherOldComplements i
  /-- Kind: GLUE. Only old derivative comparisons not matching the supplied
  strict/relaxed pair remain; tex 5055–5071. -/
  otherDerivatives : O.OtherDerivativeComplements i
  /-- Kind: GLUE. The one named original coefficient, conjugation, support,
  condition, and scalar-cone comparison; tex 4385–4388, 4438–4442, 5035–5071. -/
  originalComparison : OriginalDiagramComparison
    (allPlacePair (F.datum i) oldPair (F.localCx i) scalarLocal retainedCondition
      (F.restriction i) scalarRestriction condition localCup retained)
    (O.pair i originalIsotropy)
  /-- Kind: ELLIOT. Actual derivative action on the native localized module;
  tex 4809–4830, 4859–4868. -/
  trivialAction : ∀ (g : Gloc K (F.q i))
    (m : ResMod (locMap K (F.support i) (F.q i)) (F.coefficient i)), g • m = m
  /-- Kind: ELLIOT. Actual fixed local roots at the retained precision;
  tex 4809–4830, 4859–4868. -/
  fixedRoots : ∀ (g : Gal(AlgebraicClosure ((F.q i).adicCompletion K)/
      (F.q i).adicCompletion K)) (ζ : AlgebraicClosure ((F.q i).adicCompletion K)),
    ζ ^ (2 ^ i) = 1 → g ζ = ζ
  /-- Kind: GLUE. Actual local residual dimensions, not a coordinate,
  retraction, or pairing; tex 4859–4868. -/
  localDimensions : ∀ n : ℤ, Module.finrank (ResidueField (Acoef i))
    (residualCohomologyAt (F.localCx i) n) = splitLocalRank n

/-- Kind: GLUE. All genuine open inputs to the arithmetic retained producer
are collected here. No flatness of the assembled global complex, residual
finiteness, producer rank bound, split pairing, split trace, split duality,
finite model, retained diagram, or determinant is an input.
Tex 4391–4451, 4976–5135. -/
structure ArithmeticInputs (R : StandardOldReference S₀ W α) (width : ℕ) where
  /-- Kind: GLUE. The remaining old-condition term flatness; tex 4391–4414. -/
  oldFlat : F.NontrivialOldFlat
  /-- Kind: ELLIOT. The varying-support residual comparison; tex 4401–4406. -/
  residualSupport : ResidualSupportControl F R width
  /-- Kind: GLUE. Positive-stage original arithmetic inputs; tex 4385–4451, 5035–5071. -/
  stage : ∀ i [NeZero i], StageArithmeticInput F O i

end RemainingArithmetic

section SplitStages

variable {K : Type} [Field K] [NumberField K]
  {S₀ : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K} [W.IsElliptic]
  {α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ} [∀ i, IsOpenKer (α i)]

/-- Kind: definition. The retained localization is the actual old-Selmer
projection followed by actual local restriction and the produced split
projection; tex 4385–4388, 4859–4868. -/
def stageRes (F : ActualStageFamily S₀ W α) (i : ℕ)
    (p : GHom (F.localCx i) (splitLocalComplex (Acoef i))) :
    GHom (F.globalCx i) (splitLocalComplex (Acoef i)) :=
  ghomComp (ghomComp (projG (F.datum i)) (F.restriction i)) p

/-- Kind: definition. Produced split-stage data, with actual localization and
actual retained condition maps. This record is an output of the arithmetic
producer, not an arithmetic input; tex 4385–4451, 4859–4873. -/
structure SplitStage (F : ActualStageFamily S₀ W α) (i : ℕ)
    (Uq : GCx (Acoef i)) (ιq : GHom Uq (F.localCx i)) where
  /-- Kind: definition. The produced split projection; tex 4859–4868. -/
  projection : GHom (F.localCx i) (splitLocalComplex (Acoef i))
  /-- Kind: definition. The produced same-condition split pairing; tex 4385–4388. -/
  pairing : SelPairData
    (splitSelData (F.globalCx i) (stageRes F i projection) Uq (ghomComp ιq projection))
    (splitSelData (F.globalCx i) (stageRes F i projection) Uq (ghomComp ιq projection))
  /-- Kind: definition. The produced compact trace; tex 4385–4388. -/
  trace : (coneCx pairing.resE).X 3 →ₗ[Acoef i] Acoef i
  /-- Kind: PROVED. The produced trace kills coboundaries; tex 4385–4388. -/
  trace_kills : ∀ z, trace ((coneCx pairing.resE).d 2 3 rfl z) = 0
  /-- Kind: PROVED. The produced split global duality; tex 4385–4451, 5067–5071. -/
  duality : QuasiIso (GHom.toCC (globalDualityMap pairing trace trace_kills))

variable [HasFullTwoTorsion K S₀ W]
  {F : ActualStageFamily S₀ W α} {O : OldDualityData F} {i : ℕ} [NeZero i]

/-- Kind: PROVED. The normalized arithmetic supplier produces all split-stage
pairing and trace data. Original duality is supplied by the printed arithmetic
results and transported through the named original cochain comparison.
Tex 4385–4451, 4859–4873, 5035–5071. -/
theorem StageArithmeticInput.exists_split (S : StageArithmeticInput F O i)
    (p : ArithmeticPrints K) (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) :
    Nonempty (SplitStage F i S.retainedCondition S.condition) := by
  obtain ⟨trN, htrN, hGN, hLN⟩ := O.exists_original_trace_duality i p hK hS₀ h2
    S.otherOld S.otherDerivatives S.originalIsotropy
  let Qall := allPlacePair (F.datum i) S.oldPair (F.localCx i) S.scalarLocal
    S.retainedCondition (F.restriction i) S.scalarRestriction S.condition S.localCup S.retained
  let N := O.pair i S.originalIsotropy
  let trAll := pullScalarTrace Qall N S.originalComparison.scalar trN
  let htrAll := pullScalarTrace_kills Qall N S.originalComparison.scalar trN htrN
  have : Module.Injective (Acoef i) (Acoef i) := acoef_selfInjective i
  obtain ⟨hG, hL⟩ := OriginalDiagramComparison.duality Qall N S.originalComparison
    trN htrN hGN hLN
  obtain ⟨pr, Q, tr, htr, hdual⟩ := exists_stagePairing_trace W i (F.character i) (F.q i)
    (F.datum i) S.oldPair S.scalarLocal S.retainedCondition (F.restriction i)
    S.scalarRestriction S.condition S.localCup S.retained trAll htrAll
    (F.odd i) (F.fullTorsion i) S.trivialAction S.fixedRoots
    (F.local_residual_finite p.localFinite i) S.localDimensions hG hL
  exact ⟨⟨pr, Q, tr, htr, hdual⟩⟩

/-- Kind: definition. The zero coefficient stage requires no arithmetic
pairing or duality input; tex 4391–4406. -/
def zeroSplitStage (F : ActualStageFamily S₀ W α)
    (Uq : GCx (Acoef 0)) (ιq : GHom Uq (F.localCx 0)) : SplitStage F 0 Uq ιq where
  projection := zeroGHom _ _
  pairing := zeroTargetPair (splitSelData (F.globalCx 0)
    (stageRes F 0 (zeroGHom _ _)) Uq (ghomComp ιq (zeroGHom _ _)))
  trace := 0
  trace_kills _ := rfl
  duality := by
    have : Subsingleton (Acoef 0) := stageA_zero_subsingleton
    exact quasiIso_over_zeroRing _

variable {R : StandardOldReference S₀ W α} {width : ℕ}

/-- Kind: definition. The original retained conditions at positive stages,
with the zero complex at stage zero; tex 4391–4406, 4859–4873. -/
def retainedConditions (a : ArithmeticInputs F O R width) : ∀ i, GCx (Acoef i)
  | 0 => ZInQ.Manuscript.RC.SelmerComplex.zeroCx (Acoef 0)
  | i + 1 => (a.stage (i + 1)).retainedCondition

/-- Kind: definition. Actual retained condition maps at positive stages,
with the zero map at stage zero; tex 4391–4406, 4859–4873. -/
def retainedInclusions (a : ArithmeticInputs F O R width) :
    ∀ i, GHom (retainedConditions a i) (F.localCx i)
  | 0 => zeroGHom _ _
  | i + 1 => (a.stage (i + 1)).condition

/-- Kind: definition. The entire produced stage family has no arithmetic input
at stage zero. Every positive stage uses the normalized arithmetic pairing
supplier; tex 4385–4451, 4859–4873. -/
def producedStages (a : ArithmeticInputs F O R width) (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) :
    ∀ i, SplitStage F i (retainedConditions a i) (retainedInclusions a i)
  | 0 => zeroSplitStage F _ _
  | i + 1 => Classical.choice ((a.stage (i + 1)).exists_split p hK hS₀ h2)

end SplitStages

section RetainedProducer

open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Contrib.RC53Assist.InnerLimit (FibreInnerLimitPairingCertificate)

variable {K : Type} [Field K] [NumberField K]
  {S₀ : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K} [W.IsElliptic]
  {α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ} [∀ i, IsOpenKer (α i)]
  [HasFullTwoTorsion K S₀ W]
  {F : ActualStageFamily S₀ W α} {O : OldDualityData F}
  {R : StandardOldReference S₀ W α} {width : ℕ}

/-- Kind: definition. The precise conditional fibre-certificate conclusion.
Only identification of the retained local form with the prescribed arithmetic
form remains at a chosen fibre; tex 5035–5071. -/
def FibreCertificates {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (Cn : ActualConj K S₀) (hW : W.map (Cn.κ : K →+* K) = W)
    {C : ComplexStages (R := Lambda) stageIdeal U} (D : RetainedLimitPairingStages U C) : Prop :=
  ∀ (P : Ideal Lambda) [P.IsPrime] (ε₀ ε₂ ε σ : ResAt P),
    ε₂ ≠ 0 → ε ≠ 0 → σ ≠ 0 →
    localPairingOfMat (D.locK P) = transportedPairing ε₀ ε₂ ε σ (conjMatrix Cn W hW P) →
    FibreInnerLimitPairingCertificate U hU P C (D.resLimit hU P) ε σ
      (conjMatrix Cn W hW P)

/-- Kind: definition. The produced retained complex, pairing, homotopy-inverse
duality data, exact stage lifts, residual ranks, and conditional fibre
certificates. The certificate and retained data refer to the same complex and
localization; tex 4385–4451, 5035–5071. -/
structure AssembledLimit (a : ArithmeticInputs F O R width)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (Cn : ActualConj K S₀) (hW : W.map (Cn.κ : K →+* K) = W) where
  /-- Kind: definition. The produced uniform rank bound; tex 4401–4406. -/
  bound : ℕ
  /-- Kind: definition. The produced arithmetic split-stage family; tex 4385–4451. -/
  stages : ∀ i, SplitStage F i (retainedConditions a i) (retainedInclusions a i)
  /-- Kind: definition. The produced retained complex; tex 4401–4451. -/
  C : ComplexStages (R := Lambda) stageIdeal U
  /-- Kind: definition. The produced retained pairing and localization; tex 4385–4451. -/
  D : RetainedLimitPairingStages U C
  /-- Kind: definition. The produced retained inverse maps and homotopies; tex 4438–4451. -/
  E : RetainedGlobalDualityStages D
  /-- Kind: PROVED. The retained lower degree is zero; tex 4391–4406. -/
  low : C.low = 0
  /-- Kind: PROVED. The retained upper degree is three; tex 4391–4406. -/
  high : C.high = 3
  /-- Kind: PROVED. The retained ranks satisfy the produced bound; tex 4401–4406. -/
  rank_bound : ∀ n : ℤ, C.rank n ≤ bound
  /-- Kind: PROVED. The retained ranks are the actual residual ranks on one
  ultrafilter-large set; tex 4401–4406. -/
  residual_ranks : ∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i] (n : ℤ),
    C.rank n = Module.finrank (ResidueField (StageA i))
      (residualCohomologyAt (F.globalCx i) n)
  /-- Kind: PROVED. The retained local matrices lift the produced arithmetic
  stage trace cups, at every positive precision; tex 4385–4388, 4401–4406. -/
  local_lift : ∀ i, i ≠ 0 → ∀ a b,
    (D.loc a b i).map (stageMap i) = stageLocMat (stages i).pairing (stages i).trace a b
  /-- Kind: PROVED. Fibre certificates on this same retained diagram;
  tex 5035–5071. -/
  certificates : FibreCertificates hU Cn hW D

/-- Kind: PROVED. Assembly of the arithmetic retained inner-limit producer.
Every supplied finiteness, flatness, range, rank, normalized-pairing, trace,
and old-condition duality result is used at its exact coefficient and complex
type. The only non-setting hypotheses are the printed arithmetic statements
and `ArithmeticInputs`; tex 4391–4451, 4976–5135. -/
theorem assemble_inner_limit (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (a : ArithmeticInputs F O R width)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (Cn : ActualConj K S₀) (hW : W.map (Cn.κ : K →+* K) = W) :
    Nonempty (AssembledLimit a U hU Cn hW) := by
  let s := producedStages a p hK hS₀ h2
  obtain ⟨B, hbdd, hB⟩ := a.residualSupport.producerBounds p hK hS₀ h2
  obtain ⟨r₀, C, D, E, hrank, hlow, hhigh, hrankB, hev, hloc⟩ :=
    exists_retained_of_stageInputs U hU (fun i => F.globalCx i)
      (F.flat hS₀ a.oldFlat) (retainedConditions a)
      (fun i => stageRes F i (s i).projection)
      (fun i => ghomComp (retainedInclusions a i) (s i).projection)
      (fun i => (s i).pairing) (fun i => (s i).trace)
      (fun i => (s i).trace_kills) (fun i => (s i).duality)
      (a.residualSupport.residual_finite p hS₀ h2) 0 3 hbdd B hB
  refine ⟨⟨B, s, C, D, E, hlow, hhigh, ?_, ?_, hloc, ?_⟩⟩
  · intro n
    rw [hrank]
    exact hrankB n
  · filter_upwards [hev] with i hi
    intro _ n
    rw [hrank]
    exact hi n
  · intro P _ ε₀ ε₂ ε σ hε₂ hε hσ hl
    exact fibreInnerLimitPairingCertificate_of_retained hU E P Cn W hW
      ε₀ ε₂ ε σ hε₂ hε hσ hl

/-- Kind: PROVED. Direct instantiation of the certificate producer with the
same produced arithmetic stage inputs. No arithmetic split pairing, trace,
duality, residual finiteness, or rank bound is assumed; tex 4385–4451, 5035–5071. -/
theorem exists_certificate_actual_stages (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (a : ArithmeticInputs F O R width)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (Cn : ActualConj K S₀) (hW : W.map (Cn.κ : K →+* K) = W) :
    ∃ (C : ComplexStages (R := Lambda) stageIdeal U) (D : RetainedLimitPairingStages U C),
      (∀ i, i ≠ 0 → ∀ a' b', (D.loc a' b' i).map (stageMap i) =
        stageLocMat (producedStages a p hK hS₀ h2 i).pairing
          (producedStages a p hK hS₀ h2 i).trace a' b') ∧
      FibreCertificates hU Cn hW D := by
  let s := producedStages a p hK hS₀ h2
  obtain ⟨B, hbdd, hB⟩ := a.residualSupport.producerBounds p hK hS₀ h2
  exact exists_certificate_of_stageInputs (Cn := Cn) (W := W) (hW := hW) U hU
    (fun i => F.globalCx i) (F.flat hS₀ a.oldFlat) (retainedConditions a)
    (fun i => stageRes F i (s i).projection)
    (fun i => ghomComp (retainedInclusions a i) (s i).projection)
    (fun i => (s i).pairing) (fun i => (s i).trace)
    (fun i => (s i).trace_kills) (fun i => (s i).duality)
    (a.residualSupport.residual_finite p hS₀ h2) 0 3 hbdd B hB

end RetainedProducer

section DetectionOnAssembly

open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Manuscript.RC.PrintsArith (Qbar GalQ)
open ZInQ.Contrib.RC53Assist.InnerLimit (fibreLimitGlobal finiteLimitSide Vec2)
open ZInQ.Manuscript.RC.Uniform (finPlane)
open ZInQ.Contrib.RC53Assist.Detection

variable {K : Type} [Field K] [NumberField K]
  {S₀ : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K} [W.IsElliptic]
  {α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ} [∀ i, IsOpenKer (α i)]
  [HasFullTwoTorsion K S₀ W]
  {F : ActualStageFamily S₀ W α} {O : OldDualityData F}
  {R : StandardOldReference S₀ W α} {width : ℕ}
  {a : ArithmeticInputs F O R width} {U : Ultrafilter ℕ}
  {hU : (U : Filter ℕ) ≤ Filter.cofinite} {Cn : ActualConj K S₀}
  {hW : W.map (Cn.κ : K →+* K) = W}

/-- Kind: definition. Detection is applied to the actual finite side of this
retained diagram, not to a different abstract fibre complex;
tex 4997–5002, 5063–5065, 5087–5114. -/
def AssembledLimit.finiteFibre (L : AssembledLimit a U hU Cn hW)
    (P : Ideal Lambda) [P.IsPrime] : GCx (ResAt P) :=
  selCx (finiteLimitSide (fibreLimitGlobal U hU P L.C) (L.D.resLimit hU P)).Dside

/-- Kind: PROVED. A finite-dimensional term gives finite-dimensional
cohomology over a field; tex 4391–4451, 4984–4991. -/
theorem finiteDimensional_homology_of_term {k : Type} [Field k]
    (Q : GCx k) (n : ℤ) (h : Module.Finite k (Q.X n)) :
    FiniteDimensional k (Q.toCC.homology n) := by
  have := h
  exact (moduleFinite_homology_iff Q n).2 inferInstance

/-- Kind: PROVED. The produced finite fibre has finite-dimensional first
cohomology. This requirement of the detection supplier is not an additional
arithmetic input; tex 4391–4451, 4984–4991. -/
theorem AssembledLimit.finiteFibre_finiteDimensional (L : AssembledLimit a U hU Cn hW)
    (P : Ideal Lambda) [P.IsPrime] :
    FiniteDimensional (ResAt P) ((L.finiteFibre P).toCC.homology 1) := by
  have hG : Module.Finite (ResAt P) ((fibreLimitGlobal U hU P L.C).X 1) := by
    change Module.Finite (ResAt P) (Fin (L.C.rank 1) → ResAt P)
    infer_instance
  have hterm : Module.Finite (ResAt P) ((L.finiteFibre P).X 1) := by
    change Module.Finite (ResAt P) (((fibreLimitGlobal U hU P L.C).X 1) ×
      ↥(finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P))) × Vec2 (ResAt P))
    infer_instance
  exact finiteDimensional_homology_of_term (L.finiteFibre P) 1 hterm

end DetectionOnAssembly

section ArithmeticDetection

open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Manuscript.RC.PrintsArith (Qbar GalQ)
open ZInQ.Contrib.RC53Assist.Detection
open ZInQ.Manuscript.RC.LambdaCoef (IsContChar)
open ZInQ.Manuscript.RC.KummerMaps

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
  {S₀ : Set (HeightOneSpectrum (𝓞 K))}
  {E : WeierstrassCurve ℚ} [E.IsElliptic] [HasFullTwoTorsion K S₀ (E⁄K)]
  {α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ} [∀ i, IsOpenKer (α i)]
  {F : ActualStageFamily S₀ (E⁄K) α} {O : OldDualityData F}
  {R : StandardOldReference S₀ (E⁄K) α} {width : ℕ}
  {a : ArithmeticInputs F O R width} {U : Ultrafilter ℕ}
  {hU : (U : Filter ℕ) ≤ Filter.cofinite} {Cn : ActualConj K S₀}
  {hW : (E⁄K).map (Cn.κ : K →+* K) = E⁄K}

/-- Kind: PROVED. The detection supplier produces a partner, an actual kernel
sequence, and its detecting prime label on the produced finite fibre. No
nonzero determinant, partner, or kernel-detection assertion is an input.
The remaining coefficient dictionary, common scalar, matrix span, and retained
cochain comparison are displayed with their exact original types.
Tex 4997–5002, 5087–5114. -/
theorem detect_on_assembled_finite_fibre (L : AssembledLimit a U hU Cn hW)
    (hS₀ : S₀.Finite) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (χ : GKS K S₀ →* Lambdaˣ) [IsContChar χ]
    (P : Ideal Lambda) [P.IsPrime] (hP : P.height = 1) (hne : P ≠ Ideal.span {2})
    [DistribMulAction RationalSequences (FibrePair P)]
    [SMulCommClass RationalSequences (ResAt P) (FibrePair P)]
    (B : ℕ → IntermediateField ℚ Qbar) [∀ i, Normal ℚ (B i)]
    [∀ i, FiniteDimensional ℚ (B i)]
    (T : ℕ → IntermediateField ℚ Qbar) [∀ i, FiniteDimensional ℚ (T i)]
    (excl : ℕ → Finset ℕ) (hdegree : Module.finrank ℚ K = 2)
    {n : ℕ} (coeff : InducedCoefficientDictionary S₀ e χ E Cn U P)
    (scalar : ArithmeticCommonScalar S₀ e χ E P B) (span : CoefficientSpanWitness P)
    (V : RetainedEvaluation (S := S₀) (e := e) (α := χ) (E := E) (U := U) (P := P)
      n (L.finiteFibre P))
    (c : LinearMap.ker ((L.finiteFibre P).d 1 2 rfl))
    (hc : clsAt (L.finiteFibre P) 1 2 rfl c ≠ 0)
    (hdim : 1 < Module.finrank (ResAt P) ((L.finiteFibre P).toCC.homology 1)) :
    ∃ b : LinearMap.ker ((L.finiteFibre P).d 1 2 rfl),
      ∃ h : arithmeticSequenceKernel E S₀ e χ B,
        LinearIndependent (ResAt P)
          ![clsAt (L.finiteFibre P) 1 2 rfl c, clsAt (L.finiteFibre P) 1 2 rfl b] ∧
        let H := arithmeticKernelFamily E S₀ e χ h
        let X := basisArithmeticLabel S₀ hS₀ e χ E Cn V.original H (fun i => T i ⊔ B i)
          excl hdegree
        (∀ᶠ i in (U : Filter ℕ), (H i : GalQ) ≠ 1) ∧
        (Matrix.of ![basisValue P U V.original X.label.frob (V.coordinates c.val),
          basisValue P U V.original X.label.frob (V.coordinates b.val)]).det ≠ 0 := by
  have : FiniteDimensional (ResAt P) ((L.finiteFibre P).toCC.homology 1) :=
    L.finiteFibre_finiteDimensional P
  exact produce_arithmetic_detection (S := S₀) (hS := hS₀) (e := e) (α := χ)
    (E := E) (C := Cn) (U := U) (hU := hU) (P := P) (hP := hP) (hne := hne)
    (B := B) (F := T) (excl := excl) (hdegree := hdegree)
    (L.finiteFibre P) coeff scalar span V c hc hdim

end ArithmeticDetection

end ZInQ.Contrib.RC53Assist.RetainedAssembly
