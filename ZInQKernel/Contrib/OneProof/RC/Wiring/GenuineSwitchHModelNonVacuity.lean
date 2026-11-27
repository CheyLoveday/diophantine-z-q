import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchHModelField

/-!
**Theorem 5.3: non-vacuity of the fibre models of the homology-level switching data**

Lemma `ex:limits-inner-limit` (tex 4391–4451) and the two-term models of the height-one switching
argument (tex 4976–4996). `FibreModels` (`GenuineSwitchHModelAssembly.lean`) asks for graded finite
free models (lane RC31's `GradedModel`) of the configurations' fibres with zero differential and
ranks concentrated in degrees one and two, equal to the stages' fibre dimensions. This file builds
one for batch 3's example family `exGenuineFamily` (one configuration, fibre `exFibreD`: `ℚ` in
degrees one and two with zero differential, stage `exGenStage` of fibre dimension one):

* `tmodExModel : GradedModel (selCx exFibreD)`: ranks `dim12` (one in degrees one and two), zero
  differential, inclusion `v ↦ (v, 0, 0)`, projection `(a, u, y) ↦ a`, homotopy `0`;
* `tmodExFibreModels : FibreModels exGenuineFamily id (fun _ => exGenStage)`;
* `tmodEx_model`: the derived switch model `HomotopyEquiv (selCx exFibreD).toCC
  (twoTermFiberComplex id exGenStage)`, and `tmodEx_h1`: `dim H¹ = 1`, forced through it;
* `tmodExFibreModelsOfConcentrated`: the same family satisfies the concentration hypotheses of
  `fibreModels_of_concentrated` (finite-dimensional cohomology, zero outside degrees one and two,
  `dim H¹ = dim H² = 1`), so the field splitting gives its fibre models;
  `exists_twoTerm_model_example`: `exists_twoTerm_model` applies to the example fibre.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Module Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SwitchInputs
  ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Manuscript.RC.Limits (GRetract GradedModel matCx)

/-- PROVED. The zero chain map of batch 3's example has zero components. -/
theorem tmodEx_zHom_zero {X Y : ℤ → ModuleCat.{0} ℚ} (i j : ℤ) (h : i = j) :
    (zHom (X := X) (Y := Y) fun _ => 0).f i j h = 0 := by
  subst h
  rfl

/-- PROVED. The squares of the zero model differentials vanish. -/
theorem tmodEx_hsq : ∀ a b c (_ : a + 1 = b) (_ : b + 1 = c),
    (0 : Matrix (Fin (dim12 c)) (Fin (dim12 b)) ℚ) * (0 : Matrix (Fin (dim12 b)) (Fin (dim12 a)) ℚ)
      = 0 :=
  fun _ _ _ _ _ => Matrix.zero_mul _

/-- The model complex `ℚ` in degrees one and two with zero differential. Kind: definition. -/
abbrev tmodExCx : GCx ℚ :=
  matCx dim12 (fun a b _ => (0 : Matrix (Fin (dim12 b)) (Fin (dim12 a)) ℚ)) tmodEx_hsq

/-- PROVED. The differentials of `selCx exFibreD` vanish (relation-indexed form). -/
theorem tmodEx_selD (i j : ℤ) (h : i + 1 = j) (x : (selCx exFibreD).X i) :
    (selCx exFibreD).d i j h x = 0 := by
  obtain ⟨a, u, y⟩ := x
  change ((zGCx X12).d i j h a, (zGCx Zn).d i j h u,
    (zHom (X := X12) (Y := Zn) fun _ => 0).f i (j - 1) (by omega) a -
      (zHom (X := Zn) (Y := Zn) fun _ => 0).f i (j - 1) (by omega) u -
        (zGCx Zn).d (i - 1) (j - 1) (by omega) y) = 0
  rw [tmodEx_zHom_zero, tmodEx_zHom_zero]
  refine Prod.ext (LinearMap.zero_apply a) (Prod.ext ?_ ?_)
  · exact Subsingleton.elim (α := Fin 0 → ℚ) _ _
  · exact Subsingleton.elim (α := Fin 0 → ℚ) _ _

/-- The inclusion `v ↦ (v, 0, 0)`. Kind: definition. -/
def tmodExI : GHom tmodExCx (selCx exFibreD) where
  f i j h := by
    subst h
    exact LinearMap.inl ℚ _ _
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    rw [tmodEx_selD]
    change ((Matrix.toLin' (0 : Matrix (Fin (dim12 i₁)) (Fin (dim12 i)) ℚ)) x, (0 : _ × _)) = 0
    rw [map_zero]
    rfl

/-- The projection `(a, u, y) ↦ a`. Kind: definition. -/
def tmodExP : GHom (selCx exFibreD) tmodExCx where
  f i j h := by
    subst h
    exact
      { toFun := fun c => (c : selT exFibreD i).1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    rw [tmodEx_selD]
    change (0 : Fin (dim12 i₁) → ℚ) =
      (Matrix.toLin' (0 : Matrix (Fin (dim12 i₁)) (Fin (dim12 i)) ℚ)) x.1
    rw [map_zero]
    rfl

/-- **The graded deformation retract of `selCx exFibreD` onto its model** (homotopy `0`). Kind:
definition (PROVED identities). -/
def tmodExRetract : GRetract (selCx exFibreD) tmodExCx where
  i := tmodExI
  p := tmodExP
  h _ _ _ := 0
  p_i _ _ := rfl
  homotopy n x := by
    simp only [LinearMap.zero_apply, map_zero, add_zero]
    rw [sub_eq_zero]
    exact Prod.ext rfl (Prod.ext (Subsingleton.elim (α := Fin 0 → ℚ) _ _)
      (Subsingleton.elim (α := Fin 0 → ℚ) _ _))
  h_h _ _ _ _ _ _ := rfl
  h_i _ _ _ _ := rfl
  p_h _ _ _ _ := map_zero _

/-- **A graded finite free model of the example fibre**: ranks `dim12`, zero differential. Kind:
definition. -/
def tmodExModel : GradedModel (selCx exFibreD) where
  rank := dim12
  dC _ _ _ := 0
  dC_sq := tmodEx_hsq
  retract := tmodExRetract

/-- **Non-vacuity of `FibreModels`** for batch 3's example family (stage `exGenStage`, fibre
dimension one). Kind: definition (PROVED fields). -/
def tmodExFibreModels :
    FibreModels exGenuineFamily (RingHom.id ℚ) (fun _ => exGenStage) where
  R _ := tmodExModel
  hdC _ _ _ _ := rfl
  h0 _ n h1 h2 := by
    change (if n = 1 ∨ n = 2 then 1 else 0) = 0
    split_ifs with hn
    · omega
    · rfl
  h1 _ := by
    rw [exGenStage_fiberDim]
    rfl
  h2 _ := by
    rw [exGenStage_fiberDim]
    rfl

/-- The derived switch model of the example (Kind: definition). -/
def tmodEx_model :
    HomotopyEquiv (selCx exFibreD).toCC (twoTermFiberComplex (RingHom.id ℚ) exGenStage) :=
  tmodExFibreModels.model ()

/-- PROVED. **`dim H¹ = 1` of the example fibre, forced through the derived model.** -/
theorem tmodEx_h1 : finrank ℚ ((selCx exFibreD).toCC.homology 1) = 1 := by
  rw [← exGenStage_fiberDim]
  exact tmodExFibreModels.finrank_h1 ()

/-- PROVED. The example fibre's Selmer complex has finite-dimensional cohomology (its cochains are
finite-dimensional). -/
theorem tmodEx_hfin (n : ℤ) : FiniteDimensional ℚ ((selCx exFibreD).toCC.homology n) := by
  have hX : ∀ m, FiniteDimensional ℚ ((selCx exFibreD).X m) := fun m =>
    inferInstanceAs (FiniteDimensional ℚ ((Fin (dim12 m) → ℚ) × (Fin 0 → ℚ) × (Fin 0 → ℚ)))
  have := ZInQ.Manuscript.RC.Limits.fsplit_hfin_of_finiteDimensional (selCx exFibreD) hX n
  exact LinearEquiv.finiteDimensional
    (ZInQ.Manuscript.RC.Limits.fsplitHomologyEquiv (selCx exFibreD) n).symm

/-- PROVED (non-vacuity of the concentration hypotheses). **Batch 3's example family satisfies the
hypotheses of `fibreModels_of_concentrated`**, so the field splitting gives its fibre models: the
cohomology of the fibre is finite-dimensional, vanishes outside degrees one and two, and has
`dim H¹ = dim H² = 1` (the stage's fibre dimension). -/
def tmodExFibreModelsOfConcentrated :
    FibreModels exGenuineFamily (RingHom.id ℚ) (fun _ => exGenStage) :=
  fibreModels_of_concentrated exGenuineFamily (RingHom.id ℚ) (fun _ => exGenStage)
    (fun _ n => tmodEx_hfin n)
    (fun _ n h1 h2 => tmod_homology_zero_of_equiv (exGenStage.D.map (RingHom.id ℚ)) tmodEx_model n
      h1 h2)
    (fun _ => tmod_h1_of_equiv (RingHom.id ℚ) exGenStage tmodEx_model)
    (fun _ => tmod_h2_of_equiv (RingHom.id ℚ) exGenStage tmodEx_model)

/-- PROVED (non-vacuity of `exists_twoTerm_model`). The example fibre is homotopy equivalent to a
square two-term complex. -/
theorem exists_twoTerm_model_example :
    ∃ (n : ℕ) (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ),
      finrank ℚ (LinearMap.ker D.mulVecLin) = finrank ℚ ((selCx exFibreD).toCC.homology 1) ∧
        Nonempty (HomotopyEquiv (selCx exFibreD).toCC (tmodCx D)) :=
  exists_twoTerm_model (selCx exFibreD) tmodEx_hfin
    (fun n h1 h2 => tmod_homology_zero_of_equiv (exGenStage.D.map (RingHom.id ℚ)) tmodEx_model n
      h1 h2)
    ((tmod_h2_of_equiv (RingHom.id ℚ) exGenStage tmodEx_model).trans
      (tmod_h1_of_equiv (RingHom.id ℚ) exGenStage tmodEx_model).symm)

end ZInQ.Manuscript.RC.Wiring
