import ZInQKernel.Contrib.RC53Assist.SwitchInterface.Model

/-!
# Non-vacuity above cohomology dimension three

The fixed family below has cohomology dimensions five, three and one. Its
two nonquadratic switches use the Selmer sides of `rankStep`, not merely
assumed dimension drops. The singular side of the first switch is linearly
isomorphic in first cohomology to the finite side of the second switch,
but the two Selmer data are unequal.

The example verifies the model-level interface. It does not provide the
number-field and retained-stage inputs of the arithmetic assembly.
Sources: tex L4997–5003, L5055–5086, L5137–5195.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.SwitchInterface

open CategoryTheory Module Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt resAt)
open scoped Matrix

section ZeroFibres

/-- Kind: model terms. A prescribed rank in degrees one and two, and zero
elsewhere; tex L4983–4996. -/
abbrev modelFibreTerms (m : ℕ) (a : ℤ) : ModuleCat.{0} ℚ :=
  ModuleCat.of ℚ (Fin (if a = 1 ∨ a = 2 then m else 0) → ℚ)

/-- Kind: model Selmer data. A prescribed two-term global fibre with
zero local condition and zero full local complex; tex L4983–4996. -/
def modelFibreData (m : ℕ) : SelData ℚ where
  G := zGCx (modelFibreTerms m)
  U := zGCx Zn
  L := zGCx Zn
  res := zHom fun _ => 0
  ι := zHom fun _ => 0

/-- Kind: proved theorem. The model fibre differential vanishes in every
degree; tex L4983–4996. -/
theorem modelFibre_d (m : ℕ) (i j : ℤ) : (selCx (modelFibreData m)).toCC.d i j = 0 := by
  by_cases h : i + 1 = j
  · ext x
    obtain ⟨a, b, c⟩ := x
    change (if h : i + 1 = j then ModuleCat.ofHom (selD (modelFibreData m) i j h)
      else 0).hom (a, b, c) = 0
    rw [dite_eq_left h]
    change selD (modelFibreData m) i j h (a, b, c) = 0
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · exact funext fun x => Fin.elim0 x
    · exact funext fun x => Fin.elim0 x
  · exact (selCx (modelFibreData m)).toCC.shape i j h

/-- Kind: finite-dimensionality theorem. All model cochain terms are
finite-dimensional; tex L4983–4996. -/
theorem modelFibre_finite (m : ℕ) (a : ℤ) :
    FiniteDimensional ℚ ((selCx (modelFibreData m)).toCC.X a) := by
  change FiniteDimensional ℚ ((Fin (if a = 1 ∨ a = 2 then m else 0) → ℚ) ×
    (Fin 0 → ℚ) × (Fin 0 → ℚ))
  infer_instance

/-- Kind: proved rank theorem. The model cochain ranks are prescribed
independently of any switching data; tex L4983–4996. -/
theorem modelFibre_finrank (m : ℕ) (a : ℤ) :
    finrank ℚ ((selCx (modelFibreData m)).toCC.X a) =
      if a = 1 ∨ a = 2 then m else 0 := by
  change finrank ℚ ((Fin (if a = 1 ∨ a = 2 then m else 0) → ℚ) ×
    (Fin 0 → ℚ) × (Fin 0 → ℚ)) = _
  rw [Module.finrank_prod, Module.finrank_prod]
  simp only [Module.finrank_fin_fun]
  simp

/-- Kind: proved rank theorem. The first cohomology of the prescribed
model fibre has its specified rank; tex L4983–4996. -/
theorem modelFibre_h1 (m : ℕ) :
    finrank ℚ ((selCx (modelFibreData m)).toCC.homology 1) = m := by
  rw [finrank_h1_of_d_zero _ (modelFibre_d m 0 1) (modelFibre_d m 1 2),
    modelFibre_finrank]
  simp

/-- Kind: proved support theorem. A two-term fibre vanishes outside
degrees one and two; tex L4983–4996. -/
theorem modelTwoTerm_outside (S : TwoTermStage (RingHom.id ℚ))
    (a : ℤ) (h1 : a ≠ 1) (h2 : a ≠ 2) :
    Subsingleton ((twoTermFiberComplex (RingHom.id ℚ) S).X a) := by
  by_cases h0 : a = 0
  · subst h0
    exact (inferInstance : Subsingleton PUnit)
  · exact threeTermX_subsingleton a h0 h1 h2

/-- Kind: finite-dimensionality theorem. The two-term model has finite
cochain terms in every degree; tex L4983–4996. -/
theorem modelTwoTerm_finite (S : TwoTermStage (RingHom.id ℚ)) (a : ℤ) :
    FiniteDimensional ℚ ((twoTermFiberComplex (RingHom.id ℚ) S).X a) := by
  by_cases h1 : a = 1
  · subst h1
    change FiniteDimensional ℚ (Fin (S.n + 1) → ℚ)
    infer_instance
  by_cases h2 : a = 2
  · subst h2
    change FiniteDimensional ℚ (Fin (S.n + 1) → ℚ)
    infer_instance
  have := modelTwoTerm_outside S a h1 h2
  exact finite_of_subsingleton

/-- Kind: proved rank theorem. A two-term fibre has rank `n + 1` in
both displayed degrees; tex L4983–4996. -/
theorem modelTwoTerm_finrank (S : TwoTermStage (RingHom.id ℚ)) (a : ℤ) :
    finrank ℚ ((twoTermFiberComplex (RingHom.id ℚ) S).X a) =
      if a = 1 ∨ a = 2 then S.n + 1 else 0 := by
  by_cases h1 : a = 1
  · subst h1
    change finrank ℚ (Fin (S.n + 1) → ℚ) = _
    simp only [Module.finrank_fin_fun]
    simp
  by_cases h2 : a = 2
  · subst h2
    change finrank ℚ (Fin (S.n + 1) → ℚ) = _
    simp only [Module.finrank_fin_fun]
    simp
  have := modelTwoTerm_outside S a h1 h2
  rw [Module.finrank_zero_of_subsingleton]
  simp [h1, h2]

/-- Kind: proved differential theorem. A zero stage matrix gives a
zero-differential two-term fibre; tex L4983–4996. -/
theorem modelTwoTerm_d (S : TwoTermStage (RingHom.id ℚ)) (hD : S.D = 0)
    (i j : ℤ) : (twoTermFiberComplex (RingHom.id ℚ) S).d i j = 0 := by
  by_cases h : i + 1 = j
  · subst h
    by_cases h0 : i = 0
    · subst h0
      change ModuleCat.ofHom (0 : PUnit.{1} →ₗ[ℚ] (Fin (S.n + 1) → ℚ)) = 0
      rfl
    by_cases h1 : i = 1
    · subst h1
      change ModuleCat.ofHom ((S.D.map (RingHom.id ℚ)).mulVecLin) = 0
      rw [show (S.D.map (RingHom.id ℚ)).mulVecLin = 0 from by
        rw [hD]
        apply LinearMap.ext
        intro x
        ext a
        simp]
      rfl
    · exact threeTermD_eq_zero _ _ i (i + 1) (fun h => h0 h.1) (fun h => h1 h.1)
  · exact (twoTermFiberComplex (RingHom.id ℚ) S).shape i j h

/-- Kind: constructed cochain isomorphism. A zero stage matrix models
the independently prescribed zero fibre of the same rank;
tex L4983–4996. -/
def modelZeroIso (S : TwoTermStage (RingHom.id ℚ)) (hD : S.D = 0) :
    (selCx (modelFibreData (S.n + 1))).toCC ≅
      twoTermFiberComplex (RingHom.id ℚ) S :=
  HomologicalComplex.Hom.isoOfComponents (fun a => by
    haveI := modelFibre_finite (S.n + 1) a
    haveI := modelTwoTerm_finite S a
    exact (LinearEquiv.ofFinrankEq _ _
      ((modelFibre_finrank (S.n + 1) a).trans (modelTwoTerm_finrank S a).symm)).toModuleIso)
    (fun i j _ => by rw [modelFibre_d, modelTwoTerm_d S hD]; simp)

end ZeroFibres

section ThreeConfigurations

/-- Kind: model stage. A five-dimensional zero matrix, a nonzero cycle,
a zero functional and coordinate one; tex L4983–4996. -/
def modelHighStage : TwoTermStage (RingHom.id ℚ) where
  n := 4
  D := 0
  z := Pi.single 0 1
  w := 0
  u := 1
  hz := Matrix.zero_mulVec _
  hw := Matrix.vecMul_zero _
  hu := by
    unfold ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
    rw [Matrix.map_zero _ (map_zero _), adjugate_zero, smul_zero]
    ext i j
    change ((Pi.single (0 : Fin 5) (1 : ℚ) : Fin 5 → ℚ) i) * 0 = 0
    exact mul_zero _

/-- Kind: fixed rank function. The three family fibres have prescribed
ranks five, three and one; tex L4997–5003. -/
def modelRank (c : Fin 3) : ℕ := if c = 0 then 5 else if c = 1 then 3 else 1

/-- Kind: stage family. Coordinates are one, minus one and one; matrices
have kernel dimensions five, three and one; tex L4997–5003, L5137–5153. -/
def modelStage (c : Fin 3) : TwoTermStage (RingHom.id ℚ) :=
  if c = 0 then modelHighStage else if c = 1 then exStage3 (-1) else exStage1 1

/-- Kind: proved rank theorem. The displayed stage sizes equal the fixed
family ranks; tex L4983–4996. -/
theorem modelStage_size (c : Fin 3) : (modelStage c).n + 1 = modelRank c := by
  fin_cases c <;> rfl

/-- Kind: proved matrix theorem. All three stage matrices vanish;
tex L4983–4996. -/
theorem modelStage_D (c : Fin 3) : (modelStage c).D = 0 := by
  fin_cases c <;> rfl

/-- Kind: proved fibre-rank theorem. All stage dimensions are computed,
not assumed; tex L4997–5003. -/
theorem modelStage_dim (c : Fin 3) :
    (modelStage c).fiberDim (RingHom.id ℚ) = modelRank c := by
  rw [fiberDim_zero_matrix (modelStage c) (modelStage_D c)]
  exact modelStage_size c

/-- Kind: proved primitive-class theorem. Every stage has a nonzero
reduced cycle; tex L4986–4992, L5154–5157. -/
theorem modelStage_primitive (c : Fin 3) :
    ∃ i, (RingHom.id ℚ) ((modelStage c).z i) ≠ 0 := by
  fin_cases c <;> refine ⟨0, ?_⟩ <;> change (1 : ℚ) ≠ 0 <;> exact one_ne_zero

/-- Kind: fixed model fibre family. The fibre ranks are specified before
constructing the switching inputs; tex L4976–4996. -/
def modelFibre (c : Fin 3) : SelData ℚ := modelFibreData (modelRank c)

/-- Kind: constructed family-model isomorphism. Each prescribed fibre is
isomorphic as a cochain complex to its displayed stage;
tex L4976–4996. -/
def modelIso (c : Fin 3) :
    (selCx (modelFibre c)).toCC ≅ twoTermFiberComplex (RingHom.id ℚ) (modelStage c) := by
  change (selCx (modelFibreData (modelRank c))).toCC ≅ _
  rw [← modelStage_size c]
  exact modelZeroIso (modelStage c) (modelStage_D c)

/-- Kind: fixed switching family. There are three configurations, one
prime, and successors zero to one and one to two. The actual nonzero
class is the inverse image of the starting stage cycle;
tex L4976–5003, L5137–5153. -/
def modelFamily : SwitchFamily ℚ ℚ where
  Config := Fin 3
  Prime := Unit
  actual := 0
  next c _ := if c = 0 then 1 else 2
  fibre := modelFibre
  t := 1
  zAct := ((modelIso 0).inv.f 1).hom ((modelStage 0).z)
  hzAct := by
    change ((selCx (modelFibreData (modelRank 0))).toCC.d 1 2).hom _ = 0
    rw [modelFibre_d]
    rfl
  lamAct := 0
  hlamAct _ := rfl

/-- Kind: proved specialization theorem. This family is nonquadratic;
tex L5005–5008. -/
theorem modelFamily_nonquadratic : ¬ modelFamily.quadratic (RingHom.id ℚ) := by
  change ¬ (RingHom.id ℚ) 1 * ((RingHom.id ℚ) 1 + 2) = 0
  norm_num

/-- Kind: constructed coordinate step. Unit normalizations give the
coordinate switch from one to minus one; tex L5137–5153. -/
def modelCoord01 : CoordStep (RingHom.id ℚ) (modelStage 0).u (modelStage 1).u where
  X := exSwitchCoordData 1 1
  mF := 1
  mS := 1
  σ₀ := 1
  hmF := isUnit_one
  hmS := isUnit_one
  hμF := rfl
  hμS := rfl
  hσ₀ := rfl
  hu := by
    change (1 : ℚ) = _
    rw [exSwitchCoordData_uF]
  hu' := by
    change (-1 : ℚ) = _
    rw [exSwitchCoordData_uS]

/-- Kind: constructed coordinate step. Unit normalizations give the
coordinate switch from minus one to one; tex L5137–5153. -/
def modelCoord12 : CoordStep (RingHom.id ℚ) (modelStage 1).u (modelStage 2).u where
  X := exSwitchCoordData (-1) (-1)
  mF := -1
  mS := -1
  σ₀ := 1
  hmF := (isUnit_one : IsUnit (1 : ℚ)).neg
  hmS := (isUnit_one : IsUnit (1 : ℚ)).neg
  hμF := rfl
  hμS := rfl
  hσ₀ := rfl
  hu := by
    change (-1 : ℚ) = _
    rw [exSwitchCoordData_uF]
  hu' := by
    change (1 : ℚ) = _
    rw [exSwitchCoordData_uS]
    norm_num

/-- Kind: constructed Selmer switch. The first switch has finite-side
cohomology dimension five and singular-side dimension three;
tex L4997–5003, L5055–5086. -/
def modelStep01 : QuasiNonquadStep (RingHom.id ℚ) (modelStage 0) (modelStage 1) :=
  rankStep 3 (modelStage 0) (modelStage 1)
    (by rw [modelStage_dim]; norm_num [modelRank])
    (by rw [modelStage_dim]; norm_num [modelRank])

/-- Kind: constructed Selmer switch. The second switch has finite-side
cohomology dimension three and singular-side dimension one;
tex L4997–5003, L5055–5086. -/
def modelStep12 : QuasiNonquadStep (RingHom.id ℚ) (modelStage 1) (modelStage 2) :=
  rankStep 1 (modelStage 1) (modelStage 2)
    (by rw [modelStage_dim]; norm_num [modelRank])
    (by rw [modelStage_dim]; norm_num [modelRank])

/-- Kind: constructed non-vacuity inputs. The fixed model family,
starting identifications, primitive classes and both exact Selmer switches
inhabit the weakened model-level interface; tex L4976–5195. -/
def modelInputs : NonquadSwitchInputsIso modelFamily (RingHom.id ℚ) (RingHom.id ℚ) 1 where
  stage := modelStage
  model c := HomotopyEquiv.ofIso (modelIso c)
  hz0 := by
    change ((modelIso 0).inv.f 1 ≫ (modelIso 0).hom.f 1).hom ((modelStage 0).z) = _
    rw [← HomologicalComplex.comp_f, (modelIso 0).inv_hom_id]
    rfl
  hw0 y := by
    change (0 : ℚ) = (fun i => (RingHom.id ℚ) ((modelStage 0).w i)) ⬝ᵥ _
    have hw : (fun i => (RingHom.id ℚ) ((modelStage 0).w i)) = 0 := by
      funext i
      rfl
    rw [hw]
    exact (zero_dotProduct _).symm
  hu0 := rfl
  hnq := modelFamily_nonquadratic
  primitive c _ := modelStage_primitive c
  step c _ h1 := by
    change Fin 3 at c
    fin_cases c
    · change ∃ p : Unit,
        Nonempty (CoordStep (RingHom.id ℚ) (modelStage 0).u (modelStage 1).u) ∧
        Nonempty (QuasiNonquadStep (RingHom.id ℚ) (modelStage 0) (modelStage 1))
      exact ⟨(), ⟨modelCoord01⟩, ⟨modelStep01⟩⟩
    · change ∃ p : Unit,
        Nonempty (CoordStep (RingHom.id ℚ) (modelStage 1).u (modelStage 2).u) ∧
        Nonempty (QuasiNonquadStep (RingHom.id ℚ) (modelStage 1) (modelStage 2))
      exact ⟨(), ⟨modelCoord12⟩, ⟨modelStep12⟩⟩
    · have h := modelStage_dim (2 : Fin 3)
      norm_num [modelRank] at h
      change 1 < (modelStage 2).fiberDim (RingHom.id ℚ) at h1
      omega

/-- Kind: proved non-vacuity rank theorem. The prescribed actual family
fibre has first cohomology dimension five, strictly above three;
tex L4997–5003. -/
theorem model_actual_h1 :
    finrank ℚ ((selCx (modelFamily.fibre modelFamily.actual)).toCC.homology 1) = 5 :=
  modelFibre_h1 5

/-- Kind: proved intermediate-rank theorem. The singular successor of
the first switch is nonterminal, with dimension three;
tex L4997–5003, L5154–5159. -/
theorem model_middle_dim : (modelInputs.stage (1 : Fin 3)).fiberDim (RingHom.id ℚ) = 3 := by
  change (modelStage 1).fiberDim (RingHom.id ℚ) = 3
  rw [modelStage_dim]
  norm_num [modelRank]

/-- Kind: constructed consecutive-side equivalence. The first singular
side and the next finite side share exactly the middle cohomology;
tex L4997–5003, L5072–5086. -/
def modelSuccessorH1 :
    (selCx modelStep01.SS.Dside).toCC.homology 1 ≃ₗ[ℚ]
      (selCx modelStep12.SF.Dside).toCC.homology 1 :=
  modelStep01.φ'.trans modelStep12.φ.symm

/-- Kind: proved strictness theorem. The consecutive sides have different
local inclusion images, despite their cohomology equivalence;
tex L5040–5054, L5072–5086. -/
theorem model_successor_not_literal : modelStep01.SS.Dside ≠ modelStep12.SF.Dside := by
  intro h
  have hr := ZInQ.Contrib.RC53Assist.SwitchWiring.fixedLocalRange h
  change LinearMap.range (LinearMap.id : (Fin (dimAt 2 1) → ℚ) →ₗ[ℚ]
    (Fin (dimAt 2 1) → ℚ)) =
    LinearMap.range (0 : (Fin (dimAt 2 1) → ℚ) →ₗ[ℚ] (Fin (dimAt 2 1) → ℚ)) at hr
  rw [LinearMap.range_id, LinearMap.range_zero] at hr
  have hx : (fun _ : Fin (dimAt 2 1) => (1 : ℚ)) ∈
      (⊤ : Submodule ℚ (Fin (dimAt 2 1) → ℚ)) := Submodule.mem_top
  have hz : (fun _ : Fin (dimAt 2 1) => (1 : ℚ)) = 0 :=
    (Submodule.mem_bot ℚ).mp (hr ▸ hx)
  exact one_ne_zero (congrFun hz (0 : Fin 2))

/-- Kind: proved non-vacuity theorem. The weakened model interface admits
a starting fibre of dimension five, a nonterminal singular successor,
and consecutive cohomologically isomorphic but unequal Selmer sides;
tex L4997–5003, L5072–5086, L5154–5159. -/
theorem model_nonvacuity :
    Nonempty (NonquadSwitchInputsIso modelFamily (RingHom.id ℚ) (RingHom.id ℚ) 1) ∧
    finrank ℚ ((selCx (modelFamily.fibre modelFamily.actual)).toCC.homology 1) = 5 ∧
    (modelInputs.stage (1 : Fin 3)).fiberDim (RingHom.id ℚ) = 3 ∧
    Nonempty ((selCx modelStep01.SS.Dside).toCC.homology 1 ≃ₗ[ℚ]
      (selCx modelStep12.SF.Dside).toCC.homology 1) ∧
    modelStep01.SS.Dside ≠ modelStep12.SF.Dside :=
  ⟨⟨modelInputs⟩, model_actual_h1, model_middle_dim, ⟨modelSuccessorH1⟩,
    model_successor_not_literal⟩

/-- Kind: proved regularity theorem. The original descent consumer is
exercised by the two-switch model, not replaced by an input conclusion;
tex L4976–5195. -/
theorem model_regular : ∃ a : ℚ, RingHom.id ℚ a = 1 :=
  regular_of_nonquadSwitchInputsIso (fun _ _ h => h) (fun x hx => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not] at hx
    simp [hx]) modelInputs

end ThreeConfigurations

section LiteralContrast

variable {P : Ideal Lambda} [P.IsPrime] {F : Type} [Field F]
  {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)}
  {ι : Localization.AtPrime P →+* F} {u : F}

/-- Kind: proved contrast theorem. At a large starting stage the weakened
inputs cannot be converted back into the original literal interface;
tex L4976–5003, L5027–5086. -/
theorem no_literal_of_large_iso (X : InnerLimitSwitchInputsIso P Φ ι u)
    (hlarge : 3 < (X.stage Φ.actual).fiberDim (resAt P)) :
    ¬ Nonempty (InnerLimitSwitchInputs P Φ ι u) :=
  ZInQ.Contrib.RC53Assist.SwitchWiring.no_inputs_of_large_actual_fibre (by
    rw [← X.toNonquadSwitchFrame.fiberDim_eq Φ.actual]
    exact hlarge)

end LiteralContrast

end ZInQ.Contrib.RC53Assist.SwitchInterface
