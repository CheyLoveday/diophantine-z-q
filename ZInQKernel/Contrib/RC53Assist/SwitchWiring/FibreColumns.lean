import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.InnerLimitWiring
import ZInQKernel.Contrib.RC53Assist.InnerLimitMoving.Consumers

/-!
# Literal Selmer data of a retained switch

The finite and singular sides are identified before passing to cohomology.
The comparison uses the same retained complex and restriction as the pairing
certificate. A cohomology equivalence is not substituted for equality of
Selmer data. Sources: tex L4391–4451, L5040–5054, L5072–5086.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.SwitchWiring

open CategoryTheory Filter NumberField
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.RC53Assist.InnerLimit
open ZInQ.Contrib.RC53Assist.InnerLimitMoving
open ZInQ.Manuscript.RC.Limits (stageIdeal stageIdeal_tendsToZero)
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.FibreDuality (RetainedLimitPairingStages)
open ZInQ.Manuscript.RC.Wiring (ResAt resAt)
open scoped PowerSeries.WithPiTopology Matrix

section CochainColumns

/-- Kind: proved theorem. Cochain maps with equal source and target
complexes and equal component maps agree; tex L4391–4451. -/
theorem ghom_heq {k : Type} [Field k] {C C' D D' : GCx k}
    (hC : C = C') (hD : D = D') {f : GHom C D} {g : GHom C' D'}
    (hf : HEq f.f g.f) : HEq f g := by
  subst hC hD
  rcases f with ⟨f, hfc⟩
  rcases g with ⟨g, hgc⟩
  cases (eq_of_heq hf)
  rfl

variable {U : Ultrafilter ℕ}

/-- Kind: finite-stage cochain comparison structure. Equal integral ranks
and entrywise congruences of the original differentials and restrictions
are required before taking the integral limit. No equality of specialized
Selmer data is an input; tex L4391–4451, L5040–5054. -/
structure DiagramColumns
    (C M : ComplexStages (R := Lambda) stageIdeal U)
    (rC : MapStages C (fullLocalStages stageIdeal U))
    (rM : MapStages M (fullLocalStages stageIdeal U)) where
  /-- Kind: coefficient-basis input. The integral coordinate ranks agree;
  tex L4391–4451. -/
  ranks : C.rank = M.rank
  /-- Kind: finite-stage cochain input. The original differential columns
  agree at retained precision; tex L4391–4451. -/
  differential : ∀ a b (hab : a + 1 = b), ∀ᶠ i in (U : Filter ℕ), ∀ x y,
    C.d i a b hab x y - M.d i a b hab
      (Fin.cast (congrFun ranks b) x) (Fin.cast (congrFun ranks a) y) ∈ stageIdeal i
  /-- Kind: finite-stage cochain input. The original restriction columns
  agree at retained precision; tex L4391–4451, L5040–5054. -/
  localization : ∀ a, ∀ᶠ i in (U : Filter ℕ), ∀ x y,
    rC.f i a a rfl x y - rM.f i a a rfl x (Fin.cast (congrFun ranks a) y) ∈ stageIdeal i

/-- Kind: proved theorem. Original finite-stage column comparisons yield
literal equality of the specialized Selmer data, including both cochain
maps, not just equality of dimensions; tex L4391–4451, L5040–5054. -/
theorem DiagramColumns.data_eq (hU : (U : Filter ℕ) ≤ cofinite)
    (P : Ideal Lambda) [P.IsPrime]
    {C M : ComplexStages (R := Lambda) stageIdeal U}
    {rC : MapStages C (fullLocalStages stageIdeal U)}
    {rM : MapStages M (fullLocalStages stageIdeal U)}
    (T : DiagramColumns C M rC rM) (s : ConditionKind) :
    derivativeSideData stageIdeal_tendsToZero hU (algebraMap Lambda (ResAt P)) C rC s =
      derivativeSideData stageIdeal_tendsToZero hU (algebraMap Lambda (ResAt P)) M rM s := by
  rcases C with ⟨r, lo, hi, hb, d, hs⟩
  rcases M with ⟨r', lo', hi', hb', d', hs'⟩
  rcases T with ⟨hr, hd, hl⟩
  dsimp only at hr
  cases hr
  simp only [Fin.cast_refl] at hd hl
  have he (a b : ℤ) (hab : a + 1 = b) :
      ZInQ.Manuscript.RC.Limits.ulimMat U (fun i => d i a b hab) =
        ZInQ.Manuscript.RC.Limits.ulimMat U (fun i => d' i a b hab) :=
    ZInQ.Manuscript.RC.Limits.ulimMat_eq_of_sub_mem stageIdeal_tendsToZero hU (hd a b hab)
  have hf (a : ℤ) :
      ZInQ.Manuscript.RC.Limits.ulimMat U (fun i => rC.f i a a rfl) =
        ZInQ.Manuscript.RC.Limits.ulimMat U (fun i => rM.f i a a rfl) :=
    ZInQ.Manuscript.RC.Limits.ulimMat_eq_of_sub_mem stageIdeal_tendsToZero hU (hl a)
  have hG : scalarComplex stageIdeal_tendsToZero hU (algebraMap Lambda (ResAt P))
      ⟨r, lo, hi, hb, d, hs⟩ =
      scalarComplex stageIdeal_tendsToZero hU (algebraMap Lambda (ResAt P))
        ⟨r, lo', hi', hb', d', hs'⟩ := by
    unfold scalarComplex
    rw [GCx.mk.injEq]
    refine ⟨rfl, heq_of_eq ?_⟩
    funext a b hab
    rw [he a b hab]
  unfold derivativeSideData
  rw [SelData.mk.injEq]
  refine ⟨hG, rfl, rfl, ghom_heq hG rfl ?_, HEq.rfl⟩
  apply heq_of_eq
  funext a b hab
  subst hab
  apply LinearMap.ext
  intro x
  change fullLocalCoords (ResAt P) a
      (((ZInQ.Manuscript.RC.Limits.ulimMat U (fun i => rC.f i a a rfl)).map
        (algebraMap Lambda (ResAt P))) *ᵥ x) =
    fullLocalCoords (ResAt P) a
      (((ZInQ.Manuscript.RC.Limits.ulimMat U (fun i => rM.f i a a rfl)).map
        (algebraMap Lambda (ResAt P))) *ᵥ x)
  rw [hf a]

end CochainColumns

section LiteralData

variable {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite)
  (P : Ideal Lambda) [P.IsPrime]
  (C : ComplexStages (R := Lambda) stageIdeal U)
  (D : RetainedLimitPairingStages U C)

/-- Kind: definition. The Selmer datum computed from retained coefficient
matrices and the indicated local condition; tex L4391–4451, L5040–5054. -/
def retainedFibreData (s : ConditionKind) : SelData (ResAt P) :=
  derivativeSideData stageIdeal_tendsToZero hU (algebraMap Lambda (ResAt P))
    C (retainedRestrictionStages D) s

/-- Kind: proved theorem. The finite side is the literal retained finite
Selmer datum, including its cochain maps; tex L5040–5054, L5072–5086. -/
theorem finite_side_data :
    (finiteLimitSide (fibreLimitGlobal U hU P C) (D.resLimit hU P)).Dside =
      retainedFibreData hU P C D .finite := by
  have h := finiteSideData_eq stageIdeal_tendsToZero hU
    (algebraMap Lambda (Localization.AtPrime P)) C (retainedRestrictionStages D)
  rw [localizedResidue_comp, retainedRestriction_eq] at h
  exact h

/-- Kind: proved theorem. The singular side is the literal retained singular
Selmer datum, not just an isomorphic cohomology space;
tex L5040–5054, L5072–5086. -/
theorem singular_side_data :
    (singularLimitSide (fibreLimitGlobal U hU P C) (D.resLimit hU P)).Dside =
      retainedFibreData hU P C D .singular := by
  have h := singularSideData_eq stageIdeal_tendsToZero hU
    (algebraMap Lambda (Localization.AtPrime P)) C (retainedRestrictionStages D)
  rw [localizedResidue_comp, retainedRestriction_eq] at h
  exact h

end LiteralData

section StepData

variable {P : Ideal Lambda} [P.IsPrime] {F : Type} [Field F]
  {ι : Localization.AtPrime P →+* F} {S₀ S₁ : TwoTermStage ι}

/-- Kind: proved theorem. Conversion to a nonquadratic step preserves the
literal finite Selmer datum; tex L5027–5086. -/
theorem step_finite_side_data (X : InnerLimitStepData P S₀ S₁) :
    X.toStep.SF.Dside = retainedFibreData X.hU P X.C X.D .finite := by
  change (finiteLimitSide (fibreLimitGlobal X.U X.hU P X.C)
    (X.D.resLimit X.hU P)).Dside = _
  exact finite_side_data X.hU P X.C X.D

/-- Kind: proved theorem. Conversion to a nonquadratic step preserves the
literal singular Selmer datum; tex L5027–5086. -/
theorem step_singular_side_data (X : InnerLimitStepData P S₀ S₁) :
    X.toStep.SS.Dside = retainedFibreData X.hU P X.C X.D .singular := by
  change (singularLimitSide (fibreLimitGlobal X.U X.hU P X.C)
    (X.D.resLimit X.hU P)).Dside = _
  exact singular_side_data X.hU P X.C X.D

end StepData

section CoefficientFamily

variable {K : Type} [Field K] [NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
  (P : Ideal Lambda) [P.IsPrime]

/-- Kind: coefficient-family data structure. Every fibre is defined by its
original retained coefficient matrices and local-condition tag. Arithmetic
labels name family primes. This is a presentation of a family, not an
assumption that a produced switch side equals an arbitrary fibre;
tex L4391–4451, L4809–4830, L4976–5086. -/
structure FibreAtlas where
  /-- Kind: data. The configuration type; tex L4976–5086. -/
  Config : Type
  /-- Kind: data. The family prime type; tex L4809–4830, L5027–5086. -/
  Prime : Type
  /-- Kind: data. A produced arithmetic label names a family prime;
  tex L4809–4830, L5027–5032. -/
  primeOfLabel : ZInQ.Contrib.RC53Assist.InnerLimitArith.MovingLabel K S → Prime
  /-- Kind: data. The starting configuration; tex L4976–5003. -/
  actual : Config
  /-- Kind: data. The configuration change at a labelled prime;
  tex L5027–5086. -/
  next : Config → Prime → Config
  /-- Kind: original coefficient data. The retained global matrices at
  each configuration; tex L4391–4451, L4976–4996. -/
  diagram : Config → ComplexStages (R := Lambda) stageIdeal U
  /-- Kind: original coefficient data. The retained restrictions into
  the full local coordinate complex; tex L4391–4451, L5040–5054. -/
  restriction : ∀ c, MapStages (diagram c) (fullLocalStages stageIdeal U)
  /-- Kind: data. The local-condition tag, before passing to cohomology;
  tex L4834–4907, L5040–5054. -/
  kind : Config → ConditionKind
  /-- Kind: data. The moving parameter at the coefficient localization;
  tex L4976–5008. -/
  t : Localization.AtPrime P
  /-- Kind: original class data. The starting one-cochain;
  tex L4976–5003. -/
  zAct : (selCx (derivativeSideData stageIdeal_tendsToZero hU
    (algebraMap Lambda (ResAt P)) (diagram actual) (restriction actual)
    (kind actual))).toCC.X 1
  /-- Kind: hypothesis. The starting cochain is a cycle;
  tex L4976–5003. -/
  hzAct : ((selCx (derivativeSideData stageIdeal_tendsToZero hU
    (algebraMap Lambda (ResAt P)) (diagram actual) (restriction actual)
    (kind actual))).toCC.d 1 2).hom zAct = 0
  /-- Kind: original functional data. The starting paired functional;
  tex L4976–5003. -/
  lamAct : (selCx (derivativeSideData stageIdeal_tendsToZero hU
    (algebraMap Lambda (ResAt P)) (diagram actual) (restriction actual)
    (kind actual))).toCC.X 2 →ₗ[ResAt P] ResAt P
  /-- Kind: hypothesis. The original functional kills boundaries;
  tex L4976–5003. -/
  hlamAct : ∀ y, lamAct (((selCx (derivativeSideData stageIdeal_tendsToZero hU
    (algebraMap Lambda (ResAt P)) (diagram actual) (restriction actual)
    (kind actual))).toCC.d 1 2).hom y) = 0

variable {S U hU P}

/-- Kind: definition. The fibre is the Selmer datum of the specified
coefficient presentation, before any switch producer is invoked;
tex L4391–4451, L4976–4996. -/
def FibreAtlas.fibre (A : FibreAtlas S U hU P) (c : A.Config) : SelData (ResAt P) :=
  derivativeSideData stageIdeal_tendsToZero hU (algebraMap Lambda (ResAt P))
    (A.diagram c) (A.restriction c) (A.kind c)

/-- Kind: constructed family. The original configuration, class, functional,
and coefficient matrices define the switching family;
tex L4391–4451, L4976–5086. -/
def FibreAtlas.family (A : FibreAtlas S U hU P) :
    SwitchFamily (ResAt P) (Localization.AtPrime P) where
  Config := A.Config
  Prime := A.Prime
  actual := A.actual
  next := A.next
  fibre := A.fibre
  t := A.t
  zAct := A.zAct
  hzAct := A.hzAct
  lamAct := A.lamAct
  hlamAct := A.hlamAct

/-- Kind: starting-input structure. The unchanged family models, starting
link, nonquadratic specialization, and primitive classes. It contains none
of the retained, detecting, local-residue, or side-realization conclusions;
tex L4976–5003, L5072–5195. -/
structure FamilyFrame (A : FibreAtlas S U hU P) {F : Type} [Field F]
    (ι : Localization.AtPrime P →+* F) (u : F) where
  /-- Kind: data. The configuration stages; tex L4976–4996. -/
  stage : A.Config → TwoTermStage ι
  /-- Kind: original cochain-model input. Each stage models its independently
  specified family fibre; tex L4976–4996. -/
  model : ∀ c, HomotopyEquiv (selCx (A.fibre c)).toCC
    (twoTermFiberComplex (resAt P) (stage c))
  /-- Kind: original class identification. The starting cycle is the specified
  stage class; tex L4976–5003. -/
  hz0 : ((model A.actual).hom.f 1).hom A.zAct =
    fun i => resAt P ((stage A.actual).z i)
  /-- Kind: original functional identification. The starting functional is the
  specified stage row; tex L4976–5003. -/
  hw0 : ∀ y, A.lamAct y = (fun i => resAt P ((stage A.actual).w i)) ⬝ᵥ
    (((model A.actual).hom.f 2).hom y : Fin _ → ResAt P)
  /-- Kind: starting-coordinate input. The initial coordinate is the target;
  tex L4976–5003. -/
  hu0 : (stage A.actual).u = u
  /-- Kind: arithmetic hypothesis. The specialization is nonquadratic;
  tex L5005–5008. -/
  hnq : ¬ A.family.quadratic (resAt P)
  /-- Kind: primitive-class input. Reachable stage classes remain primitive;
  tex L5072–5195. -/
  primitive : ∀ c, Reach A.next A.actual c → ∃ i, resAt P ((stage c).z i) ≠ 0

end CoefficientFamily

end ZInQ.Contrib.RC53Assist.SwitchWiring
