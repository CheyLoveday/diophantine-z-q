import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitSwitchModel
import ZInQKernel.Contrib.RC53Assist.SwitchInterface.NonVacuity
import ZInQKernel.Contrib.OneProof.RC.Limits.GradedModel

/-!
Theorem 5.3, lane RC0 round 14: the side-model interface above fibre dimension three

Non-vacuity of `SwitchModelInputs` (side HOMOTOPY EQUIVALENCES of the step sides with the family
fibres) for a family with fibre dimensions five, three and one (tex 4976–5195).

* The rank sides of `rankStep` cannot serve here: their second cohomology has dimension two
  (finite side) or zero (singular side), while the fibres of the family have equal first and
  second cohomology dimensions. PROVED: `rankFinite_not_modelFibre`,
  `rankSingular_not_modelFibre`, `rankStep01_not_models`.
* `tdStep m`: the same switch with the global complex `ℚ^m` in degrees one AND two. Its finite
  side is isomorphic, as a complex, to the zero-differential fibre of rank `m + 2`
  (`tdFiniteIso`), and its singular side is a deformation retract onto the zero-differential
  fibre of rank `m` (`tdSingularRetract`).
* `tdInputs`: the inputs on the RC53 group's `modelFamily` (stages, fibres, models, class),
  with the steps `tdStep 3` and `tdStep 1` and the side homotopy equivalences.
* `switchModel_nonvacuity`: the inputs exist, the actual fibre has `H¹` of dimension five, the
  first successor has fibre dimension three, the consecutive sides are unequal Selmer data, and
  `regular_of_switchModelInputs_noDVR` applies.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring.SideModelExample

open CategoryTheory Module Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.RC53Assist.SwitchInterface
open ZInQ.Manuscript.RC.Uniform (finPlane singPlane mem_finPlane mem_singPlane)
open ZInQ.Manuscript.RC.Limits (GRetract)
open scoped Matrix

section Aux

/-- Zero-extension or truncation of coordinates. Kind: definition. -/
def padMap (p q : ℕ) : (Fin p → ℚ) →ₗ[ℚ] (Fin q → ℚ) where
  toFun x j := if h : (j : ℕ) < p then x ⟨j, h⟩ else 0
  map_add' x y := by
    funext j
    by_cases h : (j : ℕ) < p <;> simp [h]
  map_smul' c x := by
    funext j
    by_cases h : (j : ℕ) < p <;> simp [h]

/-- On equal sizes the padding is the identity. Kind: PROVED. -/
theorem padMap_self (p : ℕ) (x : Fin p → ℚ) : padMap p p x = x := by
  funext j
  change (if h : (j : ℕ) < p then x ⟨j, h⟩ else 0) = x j
  rw [dite_eq_left j.isLt]

/-- A relation-indexed chain map from degreewise maps commuting with the differentials.
Kind: definition. -/
def ghomOf {A B : GCx ℚ} (φ : ∀ n, A.X n →ₗ[ℚ] B.X n)
    (hφ : ∀ n (x : A.X n), φ (n + 1) (A.d n (n + 1) rfl x) = B.d n (n + 1) rfl (φ n x)) :
    GHom A B where
  f i j h := by subst h; exact φ i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj h₁
    exact hφ i x

/-- The model fibre terms vanish outside degrees one and two. Kind: PROVED. -/
theorem modelFibreTerms_subsingleton (m : ℕ) {n : ℤ} (h1 : n ≠ 1) (h2 : n ≠ 2) :
    Subsingleton (Fin (if n = 1 ∨ n = 2 then m else 0) → ℚ) := by
  rw [ite_eq_right (by omega)]
  infer_instance

/-- The side terms vanish outside degrees one and two. Kind: PROVED. -/
theorem tdTerms_subsingleton (m : ℕ) {n : ℤ} (h1 : n ≠ 1) (h2 : n ≠ 2) :
    Subsingleton ((Fin (if n = 1 ∨ n = 2 then m else 0) → ℚ) × (Fin (dimAt 2 n) → ℚ) ×
      (Fin (dimAt 2 (n - 1)) → ℚ)) := by
  have := modelFibreTerms_subsingleton m h1 h2
  have := subsingleton_dimAt 2 h1
  have := subsingleton_dimAt 2 (n := n - 1) (by omega)
  infer_instance

end Aux

section Sides

/-- Relaxed Selmer data: the global complex `ℚ^m` in degrees one and two (zero differential),
the rank-four relaxed condition and its singular projection; tex 5055–5078. Kind: definition. -/
def tdRelaxedData (m : ℕ) : SelData ℚ where
  G := zGCx (modelFibreTerms m)
  U := zGCx Qn
  L := zGCx (Pn 2)
  res := zHom fun _ => 0
  ι := zHom fun _ => LinearMap.snd ℚ _ _

/-- The relaxed localization with its standard coordinates; tex 5060–5075. Kind: definition. -/
def tdRelaxed (m : ℕ) : RelaxedLocalization ℚ where
  D := tdRelaxedData m
  Wrel := zGCx Qn
  gR := zHom fun _ => LinearMap.id
  eR := (eqvA 2).prodCongr (eqvA 2)
  hWrel := concDegOne_Qn

/-- The finite side; tex 5072–5083. Kind: definition (PROVED fields). -/
def tdFiniteSide (m : ℕ) :
    SwitchSide (tdRelaxed m) (finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) where
  U₁ := zGCx (Pn 2)
  Ustr := zGCx Zn
  W₁ := zGCx (Pn 2)
  W₂ := zGCx (Pn 2)
  f₁ := zHom fun _ => LinearMap.inl ℚ _ _
  g₂ := zHom fun _ => LinearMap.snd ℚ _ _
  fs := zHom fun _ => 0
  g₁ := zHom fun _ => LinearMap.id
  i := zHom fun _ => LinearMap.inl ℚ _ _
  p := zHom fun _ => LinearMap.snd ℚ _ _
  hfg₂ _ _ := rfl
  f₁_inj _ := LinearMap.inl_injective
  g₂_surj _ := LinearMap.snd_surjective
  ex₂ _ u h := ⟨u.1, Prod.ext rfl h.symm⟩
  hfg₁ _ _ := by change (0 : Fin _ → ℚ) = 0; rfl
  fs_inj _ := fun _ _ _ => Subsingleton.elim _ _
  g₁_surj _ := Function.surjective_id
  ex₁ _ u h := ⟨0, by change (0 : Fin _ → ℚ) = u; exact h.symm⟩
  hRF _ _ := rfl
  hpR _ _ := rfl
  hW₁ := concDegOne_Pn 2
  hW₂ := concDegOne_Pn 2
  i_inj := LinearMap.inl_injective
  ip_exact y := ⟨fun h => ⟨y.1, Prod.ext rfl h.symm⟩,
    fun ⟨x, hx⟩ => by rw [← hx]; rfl⟩
  hP := by
    ext z
    simp only [LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply, mem_finPlane]
    constructor
    · rintro ⟨x, rfl⟩
      change (eqvA 2) 0 = 0
      exact map_zero _
    · intro hz
      refine ⟨(eqvA 2).symm z.1, Prod.ext ?_ ?_⟩
      · change (eqvA 2) ((eqvA 2).symm z.1) = z.1
        exact LinearEquiv.apply_symm_apply _ _
      · change (eqvA 2) 0 = z.2
        rw [map_zero, hz]

/-- The singular side; tex 5072–5083. Kind: definition (PROVED fields). -/
def tdSingularSide (m : ℕ) :
    SwitchSide (tdRelaxed m) (singPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) where
  U₁ := zGCx (Pn 2)
  Ustr := zGCx Zn
  W₁ := zGCx (Pn 2)
  W₂ := zGCx (Pn 2)
  f₁ := zHom fun _ => LinearMap.inr ℚ _ _
  g₂ := zHom fun _ => LinearMap.fst ℚ _ _
  fs := zHom fun _ => 0
  g₁ := zHom fun _ => LinearMap.id
  i := zHom fun _ => LinearMap.inr ℚ _ _
  p := zHom fun _ => LinearMap.fst ℚ _ _
  hfg₂ _ _ := rfl
  f₁_inj _ := LinearMap.inr_injective
  g₂_surj _ := LinearMap.fst_surjective
  ex₂ _ u h := ⟨u.2, Prod.ext h.symm rfl⟩
  hfg₁ _ _ := by change (0 : Fin _ → ℚ) = 0; rfl
  fs_inj _ := fun _ _ _ => Subsingleton.elim _ _
  g₁_surj _ := Function.surjective_id
  ex₁ _ u h := ⟨0, by change (0 : Fin _ → ℚ) = u; exact h.symm⟩
  hRF _ _ := rfl
  hpR _ _ := rfl
  hW₁ := concDegOne_Pn 2
  hW₂ := concDegOne_Pn 2
  i_inj := LinearMap.inr_injective
  ip_exact y := ⟨fun h => ⟨y.2, Prod.ext h.symm rfl⟩,
    fun ⟨x, hx⟩ => by rw [← hx]; rfl⟩
  hP := by
    ext z
    simp only [LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply, mem_singPlane]
    constructor
    · rintro ⟨x, rfl⟩
      change (eqvA 2) 0 = 0
      exact map_zero _
    · intro hz
      refine ⟨(eqvA 2).symm z.2, Prod.ext ?_ ?_⟩
      · change (eqvA 2) 0 = z.1
        rw [map_zero, hz]
      · change (eqvA 2) ((eqvA 2).symm z.2) = z.2
        exact LinearEquiv.apply_symm_apply _ _

/-- The shared strict condition; tex 5072–5083. Kind: definition (PROVED fields). -/
def tdStrict (m : ℕ) : StrictIdentification (tdFiniteSide m) (tdSingularSide m) where
  e := idGHom (zGCx Zn)
  e' := idGHom (zGCx Zn)
  he'e _ _ := rfl
  hee' _ _ := rfl
  hι n x := by
    have hx : x = 0 := funext fun i => Fin.elim0 i
    subst hx
    exact (((tdFiniteSide m).Dstr.ι.f n n rfl).map_zero).trans
      (((tdSingularSide m).Dstr.ι.f n n rfl).map_zero).symm

end Sides

section Cohomology

/-- The finite-side differential vanishes in every degree; tex 5072–5078. Kind: PROVED. -/
theorem tdFinite_d (m : ℕ) (i j : ℤ) : (selCx (tdFiniteSide m).Dside).toCC.d i j = 0 := by
  by_cases hij : i + 1 = j
  · subst hij
    by_cases h1 : i = 1
    · subst h1
      ext c
      erw [GCx.toCC_d_hom _ 1 (1 + 1) rfl]
      obtain ⟨a, u, x⟩ := c
      refine Prod.ext rfl (Prod.ext rfl ?_)
      change (0 : _ →ₗ[ℚ] (Fin (dimAt 2 1) → ℚ)) a -
        (LinearMap.snd ℚ (Fin (dimAt 2 1) → ℚ) (Fin (dimAt 2 1) → ℚ))
          ((LinearMap.inl ℚ (Fin (dimAt 2 1) → ℚ) (Fin (dimAt 2 1) → ℚ)) u) - 0 = 0
      exact lin_sub_sub_zero _ rfl a _ rfl
    · by_cases h0 : i = 0
      · subst h0
        have : Subsingleton ((selCx (tdFiniteSide m).Dside).toCC.X 0) :=
          tdTerms_subsingleton m (n := 0) (by norm_num) (by norm_num)
        ext x
        rw [Subsingleton.elim x 0, map_zero]
        rfl
      · have : Subsingleton ((selCx (tdFiniteSide m).Dside).toCC.X (i + 1)) :=
          tdTerms_subsingleton m (n := i + 1) (by omega) (by omega)
        ext x
        exact Subsingleton.elim _ _
  · exact (selCx (tdFiniteSide m).Dside).toCC.shape i j hij

/-- The strict differential from degree one vanishes; tex 5072–5083. Kind: PROVED. -/
theorem tdStrict_d12 (m : ℕ) : (selCx (tdFiniteSide m).Dstr).toCC.d 1 2 = 0 := by
  ext c
  erw [GCx.toCC_d_hom _ 1 2 rfl]
  obtain ⟨a, u, x⟩ := c
  have hu : u = 0 := Subsingleton.elim (α := Fin 0 → ℚ) _ _
  subst hu
  refine Prod.ext rfl (Prod.ext rfl ?_)
  change (0 : _ →ₗ[ℚ] (Fin (dimAt 2 1) → ℚ)) a - _ - 0 = 0
  exact lin_sub_sub_zero _ rfl a _ (map_zero _)

/-- The common strict first cohomology has dimension `m`; tex 5065–5083. Kind: PROVED. -/
theorem tdStrict_h1 (m : ℕ) :
    finrank ℚ ((selCx (tdFiniteSide m).Dstr).toCC.homology 1) = m := by
  have h0 : Subsingleton ((tdFiniteSide m).Dstr.G.X 0 ×
      (tdFiniteSide m).Dstr.U.X 0 × (tdFiniteSide m).Dstr.L.X (0 - 1)) := by
    have := modelFibreTerms_subsingleton m (n := 0) (by norm_num) (by norm_num)
    have := subsingleton_dimAt 2 (n := 0 - 1) (by norm_num)
    change Subsingleton ((Fin (if (0 : ℤ) = 1 ∨ (0 : ℤ) = 2 then m else 0) → ℚ) ×
      (Fin 0 → ℚ) × (Fin (dimAt 2 (0 - 1)) → ℚ))
    infer_instance
  rw [finrank_h1_of_d_zero _ (selCx_d01_zero _ h0) (tdStrict_d12 m)]
  change finrank ℚ ((Fin (if (1 : ℤ) = 1 ∨ (1 : ℤ) = 2 then m else 0) → ℚ) × (Fin 0 → ℚ) ×
    (Fin (dimAt 2 (1 - 1)) → ℚ)) = m
  rw [Module.finrank_prod, Module.finrank_prod]
  simp only [Module.finrank_fin_fun]
  simp [dimAt]

/-- The finite-side first cohomology has dimension `m + 2`; tex 5072–5078. Kind: PROVED. -/
theorem tdFinite_h1 (m : ℕ) :
    finrank ℚ ((selCx (tdFiniteSide m).Dside).toCC.homology 1) = m + 2 := by
  rw [finrank_h1_of_d_zero _ (tdFinite_d m 0 1) (tdFinite_d m 1 2)]
  change finrank ℚ ((Fin (if (1 : ℤ) = 1 ∨ (1 : ℤ) = 2 then m else 0) → ℚ) ×
    (Fin (dimAt 2 1) → ℚ) × (Fin (dimAt 2 (1 - 1)) → ℚ)) = m + 2
  rw [Module.finrank_prod, Module.finrank_prod]
  simp only [Module.finrank_fin_fun]
  simp [dimAt]

/-- A relaxed cocycle has zero singular coordinate; tex 4997–5003, 5063–5075. Kind: PROVED. -/
theorem tdRelaxed_U_le (m : ℕ) :
    (tdRelaxed m).U ≤ finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) := by
  intro z hz
  obtain ⟨c, ⟨c', rfl⟩, rfl⟩ := hz
  set K := (selCx (tdRelaxed m).D).toCC
  obtain ⟨y, rfl⟩ : ∃ y, (K.homologyπ 1).hom y = c' :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance c'
  have hnat := congrArg (fun f => ModuleCat.Hom.hom f y)
    (HomologicalComplex.homologyπ_naturality
      (GHom.toCC (quotMap (tdRelaxed m).D (tdRelaxed m).gR)) 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [mem_finPlane]
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  rw [hnat, h1Equiv_apply]
  have hπ := congrArg (fun f => ModuleCat.Hom.hom f
    ((HomologicalComplex.cyclesMap
      (GHom.toCC (quotMap (tdRelaxed m).D (tdRelaxed m).gR)) 1).hom y))
    (homologyπ_h1Iso (tdRelaxed m).Wrel (tdRelaxed m).hWrel)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hπ
  rw [hπ]
  have hi := congrArg (fun f => ModuleCat.Hom.hom f y)
    (HomologicalComplex.cyclesMap_i
      (GHom.toCC (quotMap (tdRelaxed m).D (tdRelaxed m).gR)) 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hi
  rw [hi]
  have hd := congrArg (fun f => ModuleCat.Hom.hom f y) (K.iCycles_d 1 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at hd
  erw [GCx.toCC_d_hom _ 1 2 rfl] at hd
  generalize (K.iCycles 1).hom y = w at hd ⊢
  obtain ⟨a, u, x⟩ := w
  have h3 := congrArg (fun q => q.2.2) hd
  change (0 : _ →ₗ[ℚ] (Fin (dimAt 2 1) → ℚ)) a - u.2 - 0 = 0 at h3
  have h4 : (u : (Fin (dimAt 2 1) → ℚ) × (Fin (dimAt 2 1) → ℚ)).2 = 0 := by
    rw [LinearMap.zero_apply, zero_sub, sub_zero, neg_eq_zero] at h3
    exact h3
  change (eqvA 2) (u : (Fin (dimAt 2 1) → ℚ) × (Fin (dimAt 2 1) → ℚ)).2 = 0
  rw [h4, map_zero]

/-- Rank-two detection from the computed ranks; tex 4997–5003, 5072–5078. Kind: PROVED. -/
theorem tdRelaxed_U (m : ℕ) :
    (tdRelaxed m).U = finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) := by
  have : FiniteDimensional ℚ ((tdRelaxed m).D.G.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (if (1 : ℤ) = 1 ∨ (1 : ℤ) = 2 then m else 0) → ℚ))
  have : FiniteDimensional ℚ ((tdRelaxed m).D.L.X 0) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 0) → ℚ))
  have : FiniteDimensional ℚ ((tdFiniteSide m).U₁.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  have : FiniteDimensional ℚ ((tdSingularSide m).U₁.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  have h := (switchDims_of_selmerData (tdRelaxed m) (tdFiniteSide m) (tdSingularSide m)).1
  rw [tdFinite_h1, tdStrict_h1] at h
  have h2 : finrank ℚ ↥((tdRelaxed m).U ⊓ finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) =
      finrank ℚ ↥(finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) := by
    rw [finrank_finPlane_two]
    omega
  have hF : (tdRelaxed m).U ⊓ finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) =
      finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) :=
    Submodule.eq_of_le_of_finrank_eq inf_le_right h2
  exact le_antisymm (tdRelaxed_U_le m) (hF ▸ inf_le_left)

/-- The singular-side first cohomology has dimension `m`; tex 5072–5078. Kind: PROVED. -/
theorem tdSingular_h1 (m : ℕ) :
    finrank ℚ ((selCx (tdSingularSide m).Dside).toCC.homology 1) = m := by
  have : FiniteDimensional ℚ ((tdRelaxed m).D.G.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (if (1 : ℤ) = 1 ∨ (1 : ℤ) = 2 then m else 0) → ℚ))
  have : FiniteDimensional ℚ ((tdRelaxed m).D.L.X 0) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 0) → ℚ))
  have : FiniteDimensional ℚ ((tdFiniteSide m).U₁.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  have : FiniteDimensional ℚ ((tdSingularSide m).U₁.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  have hs : finrank ℚ ((selCx (tdSingularSide m).Dstr).toCC.homology 1) = m :=
    (tdStrict m).hk0.symm.trans (tdStrict_h1 m)
  have h := (switchDims_of_selmerData (tdRelaxed m) (tdFiniteSide m) (tdSingularSide m)).2
  rw [hs, tdRelaxed_U, finPlane_inf_singPlane, finrank_bot, add_zero] at h
  exact h

end Cohomology

section Step

/-- **The switch with two-degree global part** (tex 4997–5003, 5055–5086): the shared strict
condition, the duality `U = U^⊥` and detection `F ≤ U` from `U = F`, and the side-to-stage
cohomology isomorphisms from the computed ranks. Kind: definition (PROVED fields). -/
def tdStep (m : ℕ) (S₀ S₁ : TwoTermStage (RingHom.id ℚ))
    (h0 : S₀.fiberDim (RingHom.id ℚ) = m + 2) (h1 : S₁.fiberDim (RingHom.id ℚ) = m) :
    QuasiNonquadStep (RingHom.id ℚ) S₀ S₁ where
  R := (tdRelaxed m).toQuasi
  SF := (tdFiniteSide m).toQuasi
  SS := (tdSingularSide m).toQuasi
  hk0 := (tdStrict m).hk0
  ε := 1
  σ := 1
  J := J₀
  hε := one_ne_zero
  hσ := one_ne_zero
  hJ2 := J₀_sq
  hdual := by
    unfold LocalizationDualityInput
    rw [RelaxedLocalization.toQuasi_U, tdRelaxed_U]
    exact exLocalizationDuality 1 1 one_ne_zero one_ne_zero J₀ J₀_sq
  hdet := (tdRelaxed_U m).ge
  φ := by
    change (selCx (tdFiniteSide m).Dside).toCC.homology 1 ≃ₗ[ℚ] fiberH1 (RingHom.id ℚ) S₀
    have : FiniteDimensional ℚ ((tdRelaxed m).D.G.X 1) :=
      (inferInstance : FiniteDimensional ℚ
        (Fin (if (1 : ℤ) = 1 ∨ (1 : ℤ) = 2 then m else 0) → ℚ))
    have : FiniteDimensional ℚ ((tdRelaxed m).D.L.X 0) :=
      (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 0) → ℚ))
    have : FiniteDimensional ℚ ((tdFiniteSide m).U₁.X 1) :=
      (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
    haveI := finiteDimensional_side (tdFiniteSide m)
    exact fiberEquivOf (RingHom.id ℚ) S₀ ((tdFinite_h1 m).trans h0.symm)
  φ' := by
    change (selCx (tdSingularSide m).Dside).toCC.homology 1 ≃ₗ[ℚ] fiberH1 (RingHom.id ℚ) S₁
    have : FiniteDimensional ℚ ((tdRelaxed m).D.G.X 1) :=
      (inferInstance : FiniteDimensional ℚ
        (Fin (if (1 : ℤ) = 1 ∨ (1 : ℤ) = 2 then m else 0) → ℚ))
    have : FiniteDimensional ℚ ((tdRelaxed m).D.L.X 0) :=
      (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 0) → ℚ))
    have : FiniteDimensional ℚ ((tdSingularSide m).U₁.X 1) :=
      (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
    haveI := finiteDimensional_side (tdSingularSide m)
    exact fiberEquivOf (RingHom.id ℚ) S₁ ((tdSingular_h1 m).trans h1.symm)

end Step

section SideModels

/-- The finite-side cochain ranks; tex 5072–5078. Kind: PROVED. -/
theorem tdFinite_finrank (m : ℕ) (a : ℤ) :
    finrank ℚ ((selCx (tdFiniteSide m).Dside).toCC.X a) =
      if a = 1 ∨ a = 2 then m + 2 else 0 := by
  change finrank ℚ ((Fin (if a = 1 ∨ a = 2 then m else 0) → ℚ) × (Fin (dimAt 2 a) → ℚ) ×
    (Fin (dimAt 2 (a - 1)) → ℚ)) = _
  rw [Module.finrank_prod, Module.finrank_prod]
  simp only [Module.finrank_fin_fun]
  unfold dimAt
  split_ifs <;> omega

/-- The finite-side cochain terms are finite-dimensional. Kind: PROVED. -/
theorem tdFinite_finite (m : ℕ) (a : ℤ) :
    FiniteDimensional ℚ ((selCx (tdFiniteSide m).Dside).toCC.X a) := by
  change FiniteDimensional ℚ ((Fin (if a = 1 ∨ a = 2 then m else 0) → ℚ) ×
    (Fin (dimAt 2 a) → ℚ) × (Fin (dimAt 2 (a - 1)) → ℚ))
  infer_instance

/-- **The finite side models the fibre of rank `m + 2`**: both complexes have zero differential
and equal ranks in every degree, so they are isomorphic as cochain complexes (tex 4976–4996,
5072–5078). Kind: definition (PROVED). -/
def tdFiniteIso (m : ℕ) :
    (selCx (tdFiniteSide m).Dside).toCC ≅ (selCx (modelFibreData (m + 2))).toCC :=
  HomologicalComplex.Hom.isoOfComponents (fun a => by
    haveI := tdFinite_finite m a
    haveI := modelFibre_finite (m + 2) a
    exact (LinearEquiv.ofFinrankEq _ _
      ((tdFinite_finrank m a).trans (modelFibre_finrank (m + 2) a).symm)).toModuleIso)
    (fun i j _ => by rw [tdFinite_d, modelFibre_d]; simp)

/-- The projection of the singular side onto the global part. Kind: definition. -/
def tdProjLin (m : ℕ) (n : ℤ) :
    selT (tdSingularSide m).Dside n →ₗ[ℚ] selT (modelFibreData m) n :=
  (LinearMap.fst ℚ _ _).prod 0

/-- The inclusion of the global part into the singular side. Kind: definition. -/
def tdInclLin (m : ℕ) (n : ℤ) :
    selT (modelFibreData m) n →ₗ[ℚ] selT (tdSingularSide m).Dside n :=
  (LinearMap.fst ℚ _ _).prod 0

/-- The contraction `(a, u, x) ↦ (0, −x, 0)` of the singular side. Kind: definition. -/
def tdHtp (m : ℕ) (a b : ℤ) :
    ((Fin (if a = 1 ∨ a = 2 then m else 0) → ℚ) × (Fin (dimAt 2 a) → ℚ) ×
      (Fin (dimAt 2 (a - 1)) → ℚ)) →ₗ[ℚ]
    ((Fin (if b = 1 ∨ b = 2 then m else 0) → ℚ) × (Fin (dimAt 2 b) → ℚ) ×
      (Fin (dimAt 2 (b - 1)) → ℚ)) :=
  LinearMap.inr ℚ _ _ ∘ₗ LinearMap.inl ℚ _ _ ∘ₗ (-padMap (dimAt 2 (a - 1)) (dimAt 2 b)) ∘ₗ
    LinearMap.snd ℚ _ _ ∘ₗ LinearMap.snd ℚ _ _

/-- The projection is a chain map. Kind: definition (PROVED). -/
def tdProj (m : ℕ) : GHom (selCx (tdSingularSide m).Dside) (selCx (modelFibreData m)) :=
  ghomOf (tdProjLin m) (fun _ _ =>
    Prod.ext rfl (Prod.ext (Subsingleton.elim (α := Fin 0 → ℚ) _ _)
      (Subsingleton.elim (α := Fin 0 → ℚ) _ _)))

/-- The inclusion is a chain map. Kind: definition (PROVED). -/
def tdIncl (m : ℕ) : GHom (selCx (modelFibreData m)) (selCx (tdSingularSide m).Dside) :=
  ghomOf (tdInclLin m) (fun n x => by
    obtain ⟨a, u, y⟩ := x
    refine Prod.ext rfl (Prod.ext rfl ?_)
    by_cases hn : n = 1
    · subst hn
      change (0 : Fin (dimAt 2 1) → ℚ) = (0 : _ →ₗ[ℚ] (Fin (dimAt 2 1) → ℚ)) a -
        (LinearMap.snd ℚ (Fin (dimAt 2 1) → ℚ) (Fin (dimAt 2 1) → ℚ))
          ((LinearMap.inr ℚ (Fin (dimAt 2 1) → ℚ) (Fin (dimAt 2 1) → ℚ)) 0) - 0
      simp
    · have := subsingleton_dimAt 2 (n := n + 1 - 1) (by omega)
      exact Subsingleton.elim (α := Fin (dimAt 2 (n + 1 - 1)) → ℚ) _ _)

/-- **The singular side retracts onto the fibre of rank `m`** (tex 4423–4437: `p i = 1`,
`1 − i p = d h + h d`, `h² = 0`, `h i = 0`, `p h = 0`). Kind: definition (PROVED). -/
def tdSingularRetract (m : ℕ) :
    GRetract (selCx (tdSingularSide m).Dside) (selCx (modelFibreData m)) where
  i := tdIncl m
  p := tdProj m
  h a b _ := tdHtp m a b
  p_i _ _ := Prod.ext rfl (Prod.ext (Subsingleton.elim (α := Fin 0 → ℚ) _ _)
    (Subsingleton.elim (α := Fin 0 → ℚ) _ _))
  homotopy n x := by
    by_cases h1 : n = 1
    · subst h1
      change (Fin (if (1 : ℤ) = 1 ∨ (1 : ℤ) = 2 then m else 0) → ℚ) ×
        (Fin (dimAt 2 1) → ℚ) × (Fin (dimAt 2 0) → ℚ) at x
      obtain ⟨a, u, y⟩ := x
      have := subsingleton_dimAt 2 (n := 0) (by norm_num)
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · change a - a = 0 + 0
        rw [sub_self, add_zero]
      · change u - 0 = (0 : Fin (dimAt 2 1) → ℚ) + -(padMap (dimAt 2 1) (dimAt 2 1)
          ((0 : _ →ₗ[ℚ] (Fin (dimAt 2 1) → ℚ)) a -
            (LinearMap.snd ℚ (Fin (dimAt 2 1) → ℚ) (Fin (dimAt 2 1) → ℚ))
              ((LinearMap.inr ℚ (Fin (dimAt 2 1) → ℚ) (Fin (dimAt 2 1) → ℚ)) u) - 0))
        rw [LinearMap.zero_apply, LinearMap.snd_apply, LinearMap.inr_apply, padMap_self]
        simp
      · exact Subsingleton.elim (α := Fin (dimAt 2 0) → ℚ) _ _
    by_cases h2 : n = 2
    · subst h2
      change (Fin (if (2 : ℤ) = 1 ∨ (2 : ℤ) = 2 then m else 0) → ℚ) ×
        (Fin (dimAt 2 2) → ℚ) × (Fin (dimAt 2 1) → ℚ) at x
      obtain ⟨a, u, y⟩ := x
      have := subsingleton_dimAt 2 (n := 2) (by norm_num)
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · change a - a = 0 + 0
        rw [sub_self, add_zero]
      · exact Subsingleton.elim (α := Fin (dimAt 2 2) → ℚ) _ _
      · change y - 0 = ((0 : Fin (dimAt 2 1) → ℚ) -
          (LinearMap.snd ℚ (Fin (dimAt 2 1) → ℚ) (Fin (dimAt 2 1) → ℚ))
            ((LinearMap.inr ℚ (Fin (dimAt 2 1) → ℚ) (Fin (dimAt 2 1) → ℚ))
              (-(padMap (dimAt 2 1) (dimAt 2 1) y))) - 0) + 0
        rw [LinearMap.snd_apply, LinearMap.inr_apply, padMap_self]
        simp
    · have : Subsingleton ((selCx (tdSingularSide m).Dside).X n) :=
        tdTerms_subsingleton m (n := n) h1 h2
      exact Subsingleton.elim _ _
  h_h a b c _ _ _ := Prod.ext rfl (Prod.ext (by
    change -(padMap (dimAt 2 (b - 1)) (dimAt 2 c) 0) = 0
    rw [map_zero, neg_zero]) rfl)
  h_i a b _ _ := Prod.ext rfl (Prod.ext (by
    change -(padMap (dimAt 2 (a - 1)) (dimAt 2 b) 0) = 0
    rw [map_zero, neg_zero]) rfl)
  p_h _ _ _ _ := Prod.ext rfl (Prod.ext (Subsingleton.elim (α := Fin 0 → ℚ) _ _)
    (Subsingleton.elim (α := Fin 0 → ℚ) _ _))

/-- The finite side as a side model. Kind: definition (PROVED). -/
def tdFiniteModel (m : ℕ) :
    HomotopyEquiv (selCx (tdFiniteSide m).Dside).toCC (selCx (modelFibreData (m + 2))).toCC :=
  HomotopyEquiv.ofIso (tdFiniteIso m)

/-- The singular side as a side model. Kind: definition (PROVED). -/
def tdSingularModel (m : ℕ) :
    HomotopyEquiv (selCx (tdSingularSide m).Dside).toCC (selCx (modelFibreData m)).toCC :=
  (tdSingularRetract m).homotopyEquiv.symm

end SideModels

section Inputs

/-- The first switch, fibre dimension five to three. Kind: definition (PROVED). -/
def tdStep01 : QuasiNonquadStep (RingHom.id ℚ) (modelStage 0) (modelStage 1) :=
  tdStep 3 (modelStage 0) (modelStage 1)
    (by rw [modelStage_dim]; norm_num [modelRank])
    (by rw [modelStage_dim]; norm_num [modelRank])

/-- The second switch, fibre dimension three to one. Kind: definition (PROVED). -/
def tdStep12 : QuasiNonquadStep (RingHom.id ℚ) (modelStage 1) (modelStage 2) :=
  tdStep 1 (modelStage 1) (modelStage 2)
    (by rw [modelStage_dim]; norm_num [modelRank])
    (by rw [modelStage_dim]; norm_num [modelRank])

/-- **Switching inputs with side models** on the fixed family `modelFamily` (stages, fibres,
models and class of the RC53 group's example; tex 4976–5195). Kind: definition (PROVED). -/
def tdInputs : SwitchModelInputs modelFamily (RingHom.id ℚ) (RingHom.id ℚ) 1 where
  toSwitchModelFrame :=
    ZInQ.Manuscript.RC.Wiring.NonquadSwitchFrame.toModelFrame modelInputs.toNonquadSwitchFrame
  step c _ h1 := by
    change Fin 3 at c
    fin_cases c
    · change ∃ p : Unit,
        Nonempty (CoordStep (RingHom.id ℚ) (modelStage 0).u (modelStage 1).u) ∧
        ∃ N : QuasiNonquadStep (RingHom.id ℚ) (modelStage 0) (modelStage 1),
          Nonempty (HomotopyEquiv (selCx N.SF.Dside).toCC (selCx (modelFibreData 5)).toCC) ∧
          Nonempty (HomotopyEquiv (selCx N.SS.Dside).toCC (selCx (modelFibreData 3)).toCC)
      exact ⟨(), ⟨modelCoord01⟩, tdStep01, ⟨tdFiniteModel 3⟩, ⟨tdSingularModel 3⟩⟩
    · change ∃ p : Unit,
        Nonempty (CoordStep (RingHom.id ℚ) (modelStage 1).u (modelStage 2).u) ∧
        ∃ N : QuasiNonquadStep (RingHom.id ℚ) (modelStage 1) (modelStage 2),
          Nonempty (HomotopyEquiv (selCx N.SF.Dside).toCC (selCx (modelFibreData 3)).toCC) ∧
          Nonempty (HomotopyEquiv (selCx N.SS.Dside).toCC (selCx (modelFibreData 1)).toCC)
      exact ⟨(), ⟨modelCoord12⟩, tdStep12, ⟨tdFiniteModel 1⟩, ⟨tdSingularModel 1⟩⟩
    · have h := modelStage_dim (2 : Fin 3)
      norm_num [modelRank] at h
      change 1 < (modelStage 2).fiberDim (RingHom.id ℚ) at h1
      omega

/-- The first successor is nonterminal, of fibre dimension three. Kind: PROVED. -/
theorem tdInputs_middle_dim : (tdInputs.stage (1 : Fin 3)).fiberDim (RingHom.id ℚ) = 3 := by
  change (modelStage 1).fiberDim (RingHom.id ℚ) = 3
  rw [modelStage_dim]
  norm_num [modelRank]

/-- The singular side of the first switch and the finite side of the second are homotopy
equivalent (through the middle fibre). Kind: definition (PROVED). -/
def tdSuccessorModel :
    HomotopyEquiv (selCx tdStep01.SS.Dside).toCC (selCx tdStep12.SF.Dside).toCC :=
  (tdSingularModel 3).trans (tdFiniteModel 1).symm

/-- The consecutive sides are unequal Selmer data (different local inclusion images).
Kind: PROVED. -/
theorem td_successor_not_literal : tdStep01.SS.Dside ≠ tdStep12.SF.Dside := by
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

/-- The descent consumer without a DVR is exercised (`ℚ` is local, not a DVR). Kind: PROVED. -/
theorem td_regular : ∃ a : ℚ, RingHom.id ℚ a = 1 :=
  regular_of_switchModelInputs_noDVR (fun _ _ h => h) (fun x hx => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not] at hx
    simp [hx]) tdInputs

/-- **Non-vacuity of the side-model interface above dimension three** (tex 4976–5195): inputs
exist on a family whose actual fibre has `H¹` of dimension five and whose first successor has
fibre dimension three; the consecutive sides are homotopy equivalent but unequal; the descent
gives the regularity conclusion. Kind: PROVED. -/
theorem switchModel_nonvacuity :
    Nonempty (SwitchModelInputs modelFamily (RingHom.id ℚ) (RingHom.id ℚ) 1) ∧
    finrank ℚ ((selCx (modelFamily.fibre modelFamily.actual)).toCC.homology 1) = 5 ∧
    (tdInputs.stage (1 : Fin 3)).fiberDim (RingHom.id ℚ) = 3 ∧
    Nonempty (HomotopyEquiv (selCx tdStep01.SS.Dside).toCC (selCx tdStep12.SF.Dside).toCC) ∧
    tdStep01.SS.Dside ≠ tdStep12.SF.Dside ∧
    ∃ a : ℚ, RingHom.id ℚ a = 1 :=
  ⟨⟨tdInputs⟩, model_actual_h1, tdInputs_middle_dim, ⟨tdSuccessorModel⟩,
    td_successor_not_literal, td_regular⟩

end Inputs

section Obstruction

/-- `H²` is the cochain space when both differentials at degree two vanish. Kind: PROVED. -/
theorem finrank_h2_of_d_zero (K : CochainComplex (ModuleCat.{0} ℚ) ℤ) (h12 : K.d 1 2 = 0)
    (h23 : K.d 2 3 = 0) : finrank ℚ (K.homology 2) = finrank ℚ (K.X 2) :=
  LinearEquiv.finrank_eq
    ((K.isoHomologyπ 1 2 (by simp) h12).symm ≪≫ K.iCyclesIso 2 3 (by simp) h23).toLinearEquiv

/-- The model fibre of rank `n` has `H²` of dimension `n`. Kind: PROVED. -/
theorem modelFibre_h2 (n : ℕ) :
    finrank ℚ ((selCx (modelFibreData n)).toCC.homology 2) = n := by
  rw [finrank_h2_of_d_zero _ (modelFibre_d n 1 2) (modelFibre_d n 2 3), modelFibre_finrank]
  simp

/-- The finite side of `rankStep m` has `H²` of dimension two. Kind: PROVED. -/
theorem rankFinite_h2 (m : ℕ) :
    finrank ℚ ((selCx (rankFiniteSide m).Dside).toCC.homology 2) = 2 := by
  have h23 : (selCx (rankFiniteSide m).Dside).toCC.d 2 3 = 0 := by
    have : Subsingleton ((selCx (rankFiniteSide m).Dside).toCC.X 3) :=
      sub3 m 2 2 (n := 3) (m := 3 - 1) (by norm_num) (by norm_num)
    ext x
    exact Subsingleton.elim _ _
  rw [finrank_h2_of_d_zero _ (rankFinite_d12 m) h23]
  change finrank ℚ ((Fin (dimAt m 2) → ℚ) × (Fin (dimAt 2 2) → ℚ) ×
    (Fin (dimAt 2 (2 - 1)) → ℚ)) = 2
  rw [Module.finrank_prod, Module.finrank_prod]
  simp only [Module.finrank_fin_fun]
  simp [dimAt]

/-- The singular side of `rankStep m` has zero `H²`: its degree-one differential is onto.
Kind: PROVED. -/
theorem rankSingular_h2 (m : ℕ) :
    finrank ℚ ((selCx (rankSingularSide m).Dside).toCC.homology 2) = 0 := by
  set K := (selCx (rankSingularSide m).Dside).toCC
  have hex : K.ExactAt 2 := by
    rw [HomologicalComplex.exactAt_iff' K 1 2 3 (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    intro x₂ _
    change (Fin (dimAt m 2) → ℚ) × (Fin (dimAt 2 2) → ℚ) × (Fin (dimAt 2 1) → ℚ) at x₂
    obtain ⟨a, u, z⟩ := x₂
    refine ⟨((0 : Fin (dimAt m 1) → ℚ), -z, (0 : Fin (dimAt 2 0) → ℚ)), ?_⟩
    change (K.d 1 2).hom _ = _
    erw [GCx.toCC_d_hom _ 1 2 rfl]
    have := subsingleton_dimAt m (n := 2) (by norm_num)
    have := subsingleton_dimAt 2 (n := 2) (by norm_num)
    refine Prod.ext (Subsingleton.elim (α := Fin (dimAt m 2) → ℚ) _ _)
      (Prod.ext (Subsingleton.elim (α := Fin (dimAt 2 2) → ℚ) _ _) ?_)
    change (0 : (Fin (dimAt m 1) → ℚ) →ₗ[ℚ] (Fin (dimAt 2 1) → ℚ)) 0 -
      (LinearMap.snd ℚ (Fin (dimAt 2 1) → ℚ) (Fin (dimAt 2 1) → ℚ))
        ((LinearMap.inr ℚ (Fin (dimAt 2 1) → ℚ) (Fin (dimAt 2 1) → ℚ)) (-z)) - 0 = z
    simp
  have hz := (K.exactAt_iff_isZero_homology 2).mp hex
  have : Subsingleton (K.homology 2) := ModuleCat.isZero_iff_subsingleton.mp hz
  exact Module.finrank_zero_of_subsingleton

/-- A rank finite side models no zero-differential fibre of rank `n ≠ 2`. Kind: PROVED. -/
theorem rankFinite_not_modelFibre (m n : ℕ) (hn : n ≠ 2) :
    ¬ Nonempty (HomotopyEquiv (selCx (rankFiniteSide m).Dside).toCC
      (selCx (modelFibreData n)).toCC) := by
  rintro ⟨e⟩
  have h := (e.toHomologyIso 2).toLinearEquiv.finrank_eq
  rw [rankFinite_h2, modelFibre_h2] at h
  omega

/-- A rank singular side models no zero-differential fibre of rank `n ≠ 0`. Kind: PROVED. -/
theorem rankSingular_not_modelFibre (m n : ℕ) (hn : n ≠ 0) :
    ¬ Nonempty (HomotopyEquiv (selCx (rankSingularSide m).Dside).toCC
      (selCx (modelFibreData n)).toCC) := by
  rintro ⟨e⟩
  have h := (e.toHomologyIso 2).toLinearEquiv.finrank_eq
  rw [rankSingular_h2, modelFibre_h2] at h
  omega

/-- **The rank sides are not side models of the family**: neither side of the RC53 group's first
switch `modelStep01` is homotopy equivalent to the corresponding fibre of `modelFamily` (`H²`
of dimensions two against five, and zero against three). Kind: PROVED. -/
theorem rankStep01_not_models :
    ¬ Nonempty (HomotopyEquiv (selCx modelStep01.SF.Dside).toCC
      (selCx (modelFamily.fibre modelFamily.actual)).toCC) ∧
    ¬ Nonempty (HomotopyEquiv (selCx modelStep01.SS.Dside).toCC
      (selCx (modelFamily.fibre (modelFamily.next modelFamily.actual ()))).toCC) :=
  ⟨rankFinite_not_modelFibre 3 5 (by norm_num), rankSingular_not_modelFibre 3 3 (by norm_num)⟩

end Obstruction

end ZInQ.Manuscript.RC.Wiring.SideModelExample
