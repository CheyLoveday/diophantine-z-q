import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.NonVacuityModelQuad

/-!
# RC53 SwitchInputs: single-sign switches with a prescribed stage involution, and a switching
datum `3 → 3 → 1`

Proposition `ex:limits-uniform-lower-bound`, height-one regularity, tex L4976–5195: a stage of
fiber dimension `s > 1` whose cohomology carries one sign only switches (tex L5123–5136) to a stage
of the same dimension carrying both signs, which then switches with mixed signs (tex L5003–5122).
`NonVacuityModelQuad.lean` inhabits each quadratic step bundle separately; its single-sign example
has dimension two and cannot start a terminating chain. Here:

* `equivOfSignParts`, `equivOfSignParts_comm`: two involutions of finite-dimensional spaces (over a
  field with `2 ≠ 0`) whose `±1`-eigenspaces have the same dimensions are intertwined by a linear
  isomorphism (from the splittings `V = V₊ ⊕ V₋`).
* `singleModelStepWith`: a `SingleModelStep` whose new stage carries a GIVEN involution (so that
  two steps can share a middle stage): it only needs the sign dimensions of the new side to agree
  with those of the given involution, up to interchanging the names `+` and `−`.
* `coordStepOf`: coordinate steps between any two nonzero rational coordinates.
* `singleSignSwitchData Y hV3`: for every single-sign Selmer step `Y` whose finite side has
  dimension three, a quadratic `SelmerModelSwitchData` with stages `a` (dimension three, one sign),
  `b` (dimension three, both signs) and `c` (dimension one): `a` switches with one sign to `b`
  (`singleModelStepWith`, the middle involution being that of the mixed example), `b` switches
  with mixed signs to `c` (`mixedModelStepOf exQuadMixedStep`); regularity at every stage
  (`singleSignSwitch_regular`).

Classification: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Module Matrix ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53.UniformSwitch
  ZInQ.Contrib.CloudB3RC53.PairedFunctional

/-! ### Equivariant isomorphisms of involutions -/

section Equiv

variable {k : Type} [Field k] {V W : Type} [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

/-- The `±1`-eigenspaces of an involution are complementary (PROVED). -/
theorem isCompl_plus_minus (h2 : (2 : k) ≠ 0) {σ : V →ₗ[k] V} (hσ : σ ∘ₗ σ = LinearMap.id) :
    IsCompl (plusPart σ) (minusPart σ) := by
  obtain ⟨hinf, hsup, -⟩ := involutionSplitting_proof k V σ h2 hσ
  exact isCompl_iff.mpr ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩

/-- **An isomorphism intertwining two involutions with the same sign dimensions.** -/
def equivOfSignParts [FiniteDimensional k V] [FiniteDimensional k W] (h2 : (2 : k) ≠ 0)
    {σ : V →ₗ[k] V} {τ : W →ₗ[k] W} (hσ : σ ∘ₗ σ = LinearMap.id) (hτ : τ ∘ₗ τ = LinearMap.id)
    (hp : finrank k (plusPart σ) = finrank k (plusPart τ))
    (hm : finrank k (minusPart σ) = finrank k (minusPart τ)) : V ≃ₗ[k] W :=
  (Submodule.prodEquivOfIsCompl _ _ (isCompl_plus_minus h2 hσ)).symm.trans
    (((LinearEquiv.ofFinrankEq _ _ hp).prodCongr (LinearEquiv.ofFinrankEq _ _ hm)).trans
      (Submodule.prodEquivOfIsCompl _ _ (isCompl_plus_minus h2 hτ)))

/-- `equivOfSignParts` on a decomposed vector `a + b`, `a ∈ V₊`, `b ∈ V₋` (PROVED). -/
theorem equivOfSignParts_apply [FiniteDimensional k V] [FiniteDimensional k W] (h2 : (2 : k) ≠ 0)
    {σ : V →ₗ[k] V} {τ : W →ₗ[k] W} (hσ : σ ∘ₗ σ = LinearMap.id) (hτ : τ ∘ₗ τ = LinearMap.id)
    (hp : finrank k (plusPart σ) = finrank k (plusPart τ))
    (hm : finrank k (minusPart σ) = finrank k (minusPart τ)) (a : plusPart σ) (b : minusPart σ) :
    equivOfSignParts h2 hσ hτ hp hm ((a : V) + (b : V)) =
      ((LinearEquiv.ofFinrankEq _ _ hp a : plusPart τ) : W) +
        ((LinearEquiv.ofFinrankEq _ _ hm b : minusPart τ) : W) := by
  have h : (a : V) + (b : V) = Submodule.prodEquivOfIsCompl _ _ (isCompl_plus_minus h2 hσ) (a, b) := by
    rw [Submodule.coe_prodEquivOfIsCompl']
  rw [h, equivOfSignParts, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, Submodule.coe_prodEquivOfIsCompl']

/-- **The isomorphism `equivOfSignParts` intertwines the involutions** (PROVED). -/
theorem equivOfSignParts_comm [FiniteDimensional k V] [FiniteDimensional k W] (h2 : (2 : k) ≠ 0)
    {σ : V →ₗ[k] V} {τ : W →ₗ[k] W} (hσ : σ ∘ₗ σ = LinearMap.id) (hτ : τ ∘ₗ τ = LinearMap.id)
    (hp : finrank k (plusPart σ) = finrank k (plusPart τ))
    (hm : finrank k (minusPart σ) = finrank k (minusPart τ)) :
    (equivOfSignParts h2 hσ hτ hp hm).toLinearMap ∘ₗ σ =
      τ ∘ₗ (equivOfSignParts h2 hσ hτ hp hm).toLinearMap := by
  ext v
  obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl _ _ (isCompl_plus_minus h2 hσ)).surjective v
  rw [Submodule.coe_prodEquivOfIsCompl']
  have ha : σ a = a := mem_plusPart.mp a.2
  have hb : σ b = -b := mem_minusPart.mp b.2
  have hσv : σ ((a : V) + (b : V)) = (a : V) + ((-b : minusPart σ) : V) := by
    rw [map_add, ha, hb, Submodule.coe_neg]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hσv, equivOfSignParts_apply, equivOfSignParts_apply, map_add, map_neg, Submodule.coe_neg,
    mem_plusPart.mp (LinearEquiv.ofFinrankEq _ _ hp a).2,
    mem_minusPart.mp (LinearEquiv.ofFinrankEq _ _ hm b).2]

/-- The `+1`-eigenspace of `−τ` is the `−1`-eigenspace of `τ` (PROVED). -/
theorem plusPart_neg (τ : W →ₗ[k] W) : plusPart (-τ) = minusPart τ := by
  ext w; rw [mem_plusPart, mem_minusPart, LinearMap.neg_apply, neg_eq_iff_eq_neg]

/-- The `−1`-eigenspace of `−τ` is the `+1`-eigenspace of `τ` (PROVED). -/
theorem minusPart_neg (τ : W →ₗ[k] W) : minusPart (-τ) = plusPart τ := by
  ext w; rw [mem_minusPart, mem_plusPart, LinearMap.neg_apply, neg_inj]

/-- `−τ` is an involution with `τ` (PROVED). -/
theorem neg_inv {τ : W →ₗ[k] W} (hτ : τ ∘ₗ τ = LinearMap.id) : (-τ) ∘ₗ (-τ) = LinearMap.id := by
  rw [LinearMap.neg_comp, LinearMap.comp_neg, neg_neg, hτ]

end Equiv

/-! ### Single-sign model steps with a prescribed stage involution -/

section Step

variable {k : Type} [Field k] {A F : Type} [CommRing A] [Field F]

/-- **A single-sign model step whose new stage carries a given involution** (tex L5123–5136): the
finite side is identified with the old stage fiber (equal dimensions), and the singular side with
the new stage fiber by an isomorphism intertwining `σV'` with `σS'` or with `−σS'`, which exists as
soon as the sign dimensions agree up to interchanging `+` and `−` (`equivOfSignParts`). PROVED. -/
def singleModelStepWith {ι : A →+* F} (ρ : A →+* k) (Y : SelmerQuadSingleStep k)
    (S S' : TwoTermStage ι) (σS' : fiberH1 ρ S' →ₗ[k] fiberH1 ρ S')
    (hσS' : σS' ∘ₗ σS' = LinearMap.id)
    (h : finrank k ((selCx Y.X.SF.Dside).toCC.homology 1) = S.fiberDim ρ)
    (hsigns : (finrank k (plusPart Y.X.σV') = finrank k (plusPart σS') ∧
        finrank k (minusPart Y.X.σV') = finrank k (minusPart σS')) ∨
      (finrank k (plusPart Y.X.σV') = finrank k (minusPart σS') ∧
        finrank k (minusPart Y.X.σV') = finrank k (plusPart σS'))) :
    SingleModelStep ρ S S' σS' :=
  haveI := Y.X.fin_V
  haveI := Y.X.fin_V'
  haveI := fiberH1_finite ρ S'
  if hc : finrank k (plusPart Y.X.σV') = finrank k (plusPart σS') ∧
      finrank k (minusPart Y.X.σV') = finrank k (minusPart σS') then
    { Y := Y
      φ := fiberEquivOf ρ S h
      φ' := equivOfSignParts Y.h2 Y.X.hV' hσS' hc.1 hc.2
      hφ' := Or.inl (equivOfSignParts_comm Y.h2 Y.X.hV' hσS' hc.1 hc.2) }
  else
    have hc' := hsigns.resolve_left hc
    have hp : finrank k (plusPart Y.X.σV') = finrank k (plusPart (-σS')) := by
      rw [plusPart_neg]; exact hc'.1
    have hm : finrank k (minusPart Y.X.σV') = finrank k (minusPart (-σS')) := by
      rw [minusPart_neg]; exact hc'.2
    { Y := Y
      φ := fiberEquivOf ρ S h
      φ' := equivOfSignParts Y.h2 Y.X.hV' (neg_inv hσS') hp hm
      hφ' := Or.inr (equivOfSignParts_comm Y.h2 Y.X.hV' (neg_inv hσS') hp hm) }

end Step

/-! ### Coordinate steps between nonzero rational coordinates -/

/-- **A coordinate step from `a` to `−b`** for nonzero rationals `a`, `b` (the example coordinate
data `exSwitchCoordData a b`, whose coordinates are `u_F = a`, `u_S = −b`). PROVED. -/
def coordStepOf (a b u u' : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hu : u = a) (hu' : u' = -b) :
    CoordStep (RingHom.id ℚ) u u' where
  X := exSwitchCoordData a b
  mF := a
  mS := b
  σ₀ := 1
  hmF := isUnit_iff_ne_zero.mpr ha
  hmS := isUnit_iff_ne_zero.mpr hb
  hμF := rfl
  hμS := rfl
  hσ₀ := rfl
  hu := hu.trans (exSwitchCoordData_uF a b).symm
  hu' := hu'.trans (exSwitchCoordData_uS a b).symm

/-! ### A switching datum `3 → 3 → 1` -/

/-- The three stages: `a` (fiber dimension three, one sign), `b` (fiber dimension three, both
signs), `c` (fiber dimension one). -/
inductive Stage3 : Type
  | a | b | c

/-- The two-term models of the stages, with coordinates `1`, `−1`, `1`. -/
def stage3 : Stage3 → TwoTermStage (RingHom.id ℚ)
  | .a => exStage3 1
  | .b => exStage3 (-1)
  | .c => exStage1 1

theorem stage3_fiberDim_a : (stage3 .a).fiberDim (RingHom.id ℚ) = 3 := exStage3_fiberDim 1
theorem stage3_fiberDim_b : (stage3 .b).fiberDim (RingHom.id ℚ) = 3 := exStage3_fiberDim (-1)
theorem stage3_fiberDim_c : (stage3 .c).fiberDim (RingHom.id ℚ) = 1 := exStage1_fiberDim 1

theorem mixed_hb : finrank ℚ ((selCx exQuadMixedStep.X.SF.Dside).toCC.homology 1) =
    (stage3 .b).fiberDim (RingHom.id ℚ) := by
  change finrank ℚ ((selCx exSideF.Dside).toCC.homology 1) = _
  rw [stage3_fiberDim_b]; exact exSideF_h1

theorem mixed_hc : finrank ℚ ((selCx exQuadMixedStep.X.SS.Dside).toCC.homology 1) =
    (stage3 .c).fiberDim (RingHom.id ℚ) := by
  change finrank ℚ ((selCx exSideS.Dside).toCC.homology 1) = _
  rw [stage3_fiberDim_c]; exact exSideS_h1

section Chain

variable (Y : SelmerQuadSingleStep ℚ)
  (hV3 : finrank ℚ ((selCx Y.X.SF.Dside).toCC.homology 1) = 3)

/-- The fiber identification of the single-sign side with stage `a`. -/
def phiA : (selCx Y.X.SF.Dside).toCC.homology 1 ≃ₗ[ℚ] fiberH1 (RingHom.id ℚ) (stage3 .a) :=
  haveI := Y.X.fin_V
  fiberEquivOf (RingHom.id ℚ) (stage3 .a) (by rw [hV3, stage3_fiberDim_a])

/-- The stage involutions: at `a` the transport of the single-sign side involution, at `b`, `c` the
transports of the mixed example's side involutions. -/
def sigma3 : ∀ S : Stage3, fiberH1 (RingHom.id ℚ) (stage3 S) →ₗ[ℚ] fiberH1 (RingHom.id ℚ) (stage3 S)
  | .a => transportInv (phiA Y hV3) Y.X.σV
  | .b => transportInv (mixedφ (RingHom.id ℚ) exQuadMixedStep (stage3 .b) mixed_hb)
      exQuadMixedStep.X.σV
  | .c => transportInv (mixedφ' (RingHom.id ℚ) exQuadMixedStep (stage3 .c) mixed_hc)
      exQuadMixedStep.X.σV'

theorem sigma3_sq : ∀ S, sigma3 Y hV3 S ∘ₗ sigma3 Y hV3 S = LinearMap.id
  | .a => transportInv_sq _ Y.X.hV
  | .b => transportInv_sq _ exQuadMixedStep.X.hV
  | .c => transportInv_sq _ exQuadMixedStep.X.hV'

/-- Stage `a` carries one sign only: its `−1`-part is zero (`Y.hs0`). PROVED. -/
theorem sigma3_a_minus : finrank ℚ ↥(signPart (sigma3 Y hV3 .a) (-1 : ℚ)) = 0 := by
  change finrank ℚ ↥(signPart (transportInv (phiA Y hV3) Y.X.σV) (-1 : ℚ)) = 0
  rw [← finrank_signPart_of_equiv (phiA Y hV3) (transportInv_comm _ _) (-1)]
  exact Y.hs0.symm

/-- Stage `b` carries both signs (`exQ_both_signs` for the transported involution). PROVED. -/
theorem sigma3_b_both : 0 < finrank ℚ ↥(signPart (sigma3 Y hV3 .b) (1 : ℚ)) ∧
    0 < finrank ℚ ↥(signPart (sigma3 Y hV3 .b) (-1 : ℚ)) := by
  let Y' := exQuadMixedStep
  let φ := mixedφ (RingHom.id ℚ) Y' (stage3 .b) mixed_hb
  have := fiberH1_finite (RingHom.id ℚ) (stage3 .b)
  have hdet := Y'.hdet Y'.hcp Y'.hcm
  have hcp0 : Y'.cp ≠ 0 := fun h => hdet.1 (by rw [h, map_zero])
  have hcm0 : Y'.cm ≠ 0 := fun h => hdet.2 (by rw [h, map_zero])
  have key : ∀ c, sigma3 Y hV3 .b (φ c) = φ (Y'.X.σV c) := fun c =>
    (LinearMap.congr_fun (transportInv_comm φ Y'.X.σV) c).symm
  refine ⟨finrank_pos_of_mem _ (x := φ Y'.cp) ?_ (by simpa using hcp0),
    finrank_pos_of_mem _ (x := φ Y'.cm) ?_ (by simpa using hcm0)⟩
  · rw [mem_signPart, key, Y'.hcp, one_smul]
  · rw [mem_signPart, key, Y'.hcm, map_neg, neg_one_smul]

/-- The sign dimensions of stage `b` add up to three. PROVED. -/
theorem sigma3_b_sum : finrank ℚ ↥(plusPart (sigma3 Y hV3 .b)) +
    finrank ℚ ↥(minusPart (sigma3 Y hV3 .b)) = 3 := by
  have := fiberH1_finite (RingHom.id ℚ) (stage3 .b)
  rw [← (involutionSplitting_proof ℚ _ (sigma3 Y hV3 .b) two_ne_zero (sigma3_sq Y hV3 .b)).2.2
    this, finrank_h1_twoTermFiberComplex, stage3_fiberDim_b]

include hV3 in
/-- The new side of the single-sign step has sign dimensions `a, b ≥ 1` with `a + b = 3`
(`QuadSingleDims.result`, the finite side having dimension three and one sign). PROVED. -/
theorem single_signs : finrank ℚ ↥(plusPart Y.X.σV') + finrank ℚ ↥(minusPart Y.X.σV') = 3 ∧
    0 < finrank ℚ ↥(plusPart Y.X.σV') ∧ 0 < finrank ℚ ↥(minusPart Y.X.σV') := by
  have hres := (Y.X.toQuadSingleDims Y.h2 Y.ε Y.hε Y.hJ2 Y.ep Y.em Y.hp Y.hm Y.he Y.hU Y.cp Y.hcp
    Y.hdet Y.hs1 Y.hs0).result
  have := Y.X.fin_V
  have hs : finrank ℚ ↥(signPart Y.X.σV (1 : ℚ)) = 3 := by
    rw [← hV3, (involutionSplitting_proof ℚ _ Y.X.σV Y.h2 Y.X.hV).2.2 this,
      signPart_one_eq_plusPart, ← signPart_neg_one_eq_minusPart, ← Y.hs0, add_zero]
  rw [signPart_one_eq_plusPart, signPart_neg_one_eq_minusPart, hs] at hres
  exact hres

/-- **The single-sign model step from stage `a` to stage `b`** (PROVED). -/
def stepAB : SingleModelStep (RingHom.id ℚ) (stage3 .a) (stage3 .b) (sigma3 Y hV3 .b) :=
  singleModelStepWith (RingHom.id ℚ) Y (stage3 .a) (stage3 .b) (sigma3 Y hV3 .b)
    (sigma3_sq Y hV3 .b) (by rw [hV3, stage3_fiberDim_a]) (by
      have h1 := single_signs Y hV3
      have h2 := sigma3_b_sum Y hV3
      have h3 := sigma3_b_both Y hV3
      rw [signPart_one_eq_plusPart, signPart_neg_one_eq_minusPart] at h3
      omega)

/-- **The mixed model step from stage `b` to stage `c`** (`exQuadMixedStep`). PROVED. -/
def stepBC : MixedModelStep (RingHom.id ℚ) (stage3 .b) (stage3 .c) (sigma3 Y hV3 .b)
    (sigma3 Y hV3 .c) :=
  mixedModelStepOf (RingHom.id ℚ) exQuadMixedStep (stage3 .b) (stage3 .c) mixed_hb mixed_hc

/-- **A quadratic switching datum `3 → 3 → 1` with a single-sign switch** (tex L4976–5195): stage
`a` (dimension three, one sign) switches with one sign to stage `b` (dimension three, both signs),
which switches with mixed signs to stage `c` (dimension one). PROVED. -/
def singleSignSwitchData : SelmerModelSwitchData (k := ℚ) (RingHom.id ℚ) (RingHom.id ℚ) where
  Stage := Stage3
  stage := stage3
  σ := sigma3 Y hV3
  quadratic := True
  h2 _ := two_ne_zero
  hσ _ S := sigma3_sq Y hV3 S
  primitive S := by
    cases S
    · exact ⟨0, by simp [stage3, exStage3]⟩
    · exact ⟨0, by simp [stage3, exStage3]⟩
    · exact ⟨0, by simp [stage3, exStage1]⟩
  switch_mixed S hmix hs := by
    cases S
    · exfalso
      rcases hmix with h | h
      · exact h trivial
      · have := sigma3_a_minus Y hV3; omega
    · exact ⟨.c, ⟨coordStepOf (-1) (-1) _ _ (by norm_num) (by norm_num) rfl (by
          change (1 : ℚ) = -(-1); norm_num)⟩,
        fun _ => ⟨stepBC Y hV3⟩, fun h => absurd trivial h⟩
    · exfalso
      rw [stage3_fiberDim_c] at hs
      omega
  switch_single S _ hnot hs := by
    cases S
    · exact ⟨.b, ⟨coordStepOf 1 1 _ _ one_ne_zero one_ne_zero rfl (by
          change (-1 : ℚ) = -1; rfl)⟩, ⟨stepAB Y hV3⟩⟩
    · exact absurd (sigma3_b_both Y hV3) hnot
    · exfalso
      rw [stage3_fiberDim_c] at hs
      omega

/-- The chain switches as claimed: stage `a` has dimension three and one sign, stage `b` dimension
three and both signs, stage `c` dimension one. PROVED. -/
theorem singleSignSwitchData_chain :
    ((singleSignSwitchData Y hV3).stage .a).fiberDim (RingHom.id ℚ) = 3 ∧
      finrank ℚ ↥(signPart ((singleSignSwitchData Y hV3).σ .a) (-1 : ℚ)) = 0 ∧
      ((singleSignSwitchData Y hV3).stage .b).fiberDim (RingHom.id ℚ) = 3 ∧
      (0 < finrank ℚ ↥(signPart ((singleSignSwitchData Y hV3).σ .b) (1 : ℚ)) ∧
        0 < finrank ℚ ↥(signPart ((singleSignSwitchData Y hV3).σ .b) (-1 : ℚ))) ∧
      ((singleSignSwitchData Y hV3).stage .c).fiberDim (RingHom.id ℚ) = 1 :=
  ⟨stage3_fiberDim_a, sigma3_a_minus Y hV3, stage3_fiberDim_b, sigma3_b_both Y hV3,
    stage3_fiberDim_c⟩

/-- **Regularity from the single-sign switching datum** (RC16's regularity through
`regular_of_selmerModelSwitchData`). PROVED. -/
theorem singleSignSwitch_regular (S : Stage3) :
    ∃ a : ℚ, RingHom.id ℚ a = ((singleSignSwitchData Y hV3).stage S).u :=
  regular_of_selmerModelSwitchData (fun _ _ h => h) (fun x hx => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not] at hx
    simp [hx]) (singleSignSwitchData Y hV3) S

end Chain

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
