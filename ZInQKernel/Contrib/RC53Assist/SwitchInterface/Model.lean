import ZInQKernel.Contrib.RC53Assist.SwitchInterface.Interface
import ZInQKernel.Contrib.RC53Assist.SwitchWiring.Boundary

/-!
# A two-switch cohomological model

A finite-dimensional family over the rational numbers will have successive
cohomology dimensions five, three and one. Each switch uses genuine Selmer
cone data, exact change-of-condition sequences, a shared strict condition,
localization duality and rank-two detection. At the middle configuration
only the cohomology of consecutive sides is identified.

This is a model-level example, not a number-field realization of retained
arithmetic inputs. Sources: tex L4997–5003, L5055–5086, L5137–5195.
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
open ZInQ.Manuscript.RC.Uniform (Lambda finPlane singPlane mem_finPlane mem_singPlane)
open ZInQ.Manuscript.RC.Wiring (ResAt resAt)
open scoped Matrix

section RankModel

/-- Kind: model Selmer data. A strict global part of dimension `m`, a
rank-four relaxed condition, and its singular projection;
tex L5055–5078. -/
def rankRelaxedData (m : ℕ) : SelData ℚ where
  G := zGCx (Pn m)
  U := zGCx Qn
  L := zGCx (Pn 2)
  res := zHom fun _ => 0
  ι := zHom fun _ => LinearMap.snd ℚ _ _

/-- Kind: constructed relaxed localization. The relaxed quotient has its
standard finite and singular coordinates; tex L5060–5075. -/
def rankRelaxed (m : ℕ) : RelaxedLocalization ℚ where
  D := rankRelaxedData m
  Wrel := zGCx Qn
  gR := zHom fun _ => LinearMap.id
  eR := (eqvA 2).prodCongr (eqvA 2)
  hWrel := concDegOne_Qn

/-- Kind: constructed finite side. Both change-of-condition sequences and
the finite plane identification are explicit; tex L5072–5083. -/
def rankFiniteSide (m : ℕ) :
    SwitchSide (rankRelaxed m) (finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) where
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

/-- Kind: constructed singular side. The same strict condition is used,
but its local inclusion differs from the finite inclusion;
tex L5072–5083. -/
def rankSingularSide (m : ℕ) :
    SwitchSide (rankRelaxed m) (singPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) where
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

/-- Kind: constructed strict identification. The two strict Selmer
conditions and their inclusion maps agree; tex L5072–5083. -/
def rankStrict (m : ℕ) : StrictIdentification (rankFiniteSide m) (rankSingularSide m) where
  e := idGHom (zGCx Zn)
  e' := idGHom (zGCx Zn)
  he'e _ _ := rfl
  hee' _ _ := rfl
  hι n x := by
    have hx : x = 0 := funext fun i => Fin.elim0 i
    subst hx
    exact (((rankFiniteSide m).Dstr.ι.f n n rfl).map_zero).trans
      (((rankSingularSide m).Dstr.ι.f n n rfl).map_zero).symm

/-- Kind: proved theorem. The finite-side differential vanishes;
tex L5072–5078. -/
theorem rankFinite_d12 (m : ℕ) : (selCx (rankFiniteSide m).Dside).toCC.d 1 2 = 0 := by
  ext c
  erw [GCx.toCC_d_hom _ 1 2 rfl]
  obtain ⟨a, u, x⟩ := c
  refine Prod.ext rfl (Prod.ext rfl ?_)
  change (0 : (Fin (dimAt m 1) → ℚ) →ₗ[ℚ] _) a -
    (LinearMap.snd ℚ (Fin (dimAt 2 1) → ℚ) (Fin (dimAt 2 1) → ℚ))
      ((LinearMap.inl ℚ (Fin (dimAt 2 1) → ℚ) (Fin (dimAt 2 1) → ℚ)) u) - 0 = 0
  exact lin_sub_sub_zero _ rfl a _ rfl

/-- Kind: proved theorem. The finite-side first cohomology has dimension
`m + 2`, computed from the actual Selmer differential;
tex L5072–5078. -/
theorem rankFinite_h1 (m : ℕ) :
    finrank ℚ ((selCx (rankFiniteSide m).Dside).toCC.homology 1) = m + 2 := by
  rw [finrank_h1_of_d_zero _
    (selCx_d01_zero _ (sub3 m 2 2 (by norm_num) (by norm_num))) (rankFinite_d12 m)]
  change finrank ℚ ((Fin (dimAt m 1) → ℚ) × (Fin (dimAt 2 1) → ℚ) ×
    (Fin (dimAt 2 (1 - 1)) → ℚ)) = m + 2
  rw [Module.finrank_prod, Module.finrank_prod]
  simp only [Module.finrank_fin_fun]
  simp [dimAt]

/-- Kind: proved theorem. The strict differential vanishes;
tex L5072–5083. -/
theorem rankStrict_d12 (m : ℕ) : (selCx (rankFiniteSide m).Dstr).toCC.d 1 2 = 0 := by
  ext c
  erw [GCx.toCC_d_hom _ 1 2 rfl]
  obtain ⟨a, u, x⟩ := c
  have hu : u = 0 := Subsingleton.elim (α := Fin 0 → ℚ) _ _
  subst hu
  refine Prod.ext rfl (Prod.ext rfl ?_)
  change (0 : (Fin (dimAt m 1) → ℚ) →ₗ[ℚ] (Fin (dimAt 2 1) → ℚ)) a - _ - 0 = 0
  exact lin_sub_sub_zero _ rfl a _ (map_zero _)

/-- Kind: proved theorem. The common strict first cohomology has
dimension `m`; tex L5065–5083. -/
theorem rankStrict_h1 (m : ℕ) :
    finrank ℚ ((selCx (rankFiniteSide m).Dstr).toCC.homology 1) = m := by
  have h0 : Subsingleton ((rankFiniteSide m).Dstr.G.X 0 ×
      (rankFiniteSide m).Dstr.U.X 0 × (rankFiniteSide m).Dstr.L.X (0 - 1)) := by
    have := subsingleton_dimAt m (n := 0) (by norm_num)
    have := subsingleton_dimAt 2 (n := 0 - 1) (by norm_num)
    change Subsingleton ((Fin (dimAt m 0) → ℚ) × (Fin 0 → ℚ) ×
      (Fin (dimAt 2 (0 - 1)) → ℚ))
    infer_instance
  rw [finrank_h1_of_d_zero _ (selCx_d01_zero _ h0) (rankStrict_d12 m)]
  change finrank ℚ ((Fin (dimAt m 1) → ℚ) × (Fin 0 → ℚ) ×
    (Fin (dimAt 2 (1 - 1)) → ℚ)) = m
  rw [Module.finrank_prod, Module.finrank_prod]
  simp only [Module.finrank_fin_fun]
  simp [dimAt]

/-- Kind: proved theorem. A relaxed cocycle has zero singular coordinate;
tex L4997–5003, L5063–5075. -/
theorem rankRelaxed_U_le (m : ℕ) :
    (rankRelaxed m).U ≤ finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) := by
  intro z hz
  obtain ⟨c, ⟨c', rfl⟩, rfl⟩ := hz
  set K := (selCx (rankRelaxed m).D).toCC
  obtain ⟨y, rfl⟩ : ∃ y, (K.homologyπ 1).hom y = c' :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance c'
  have hnat := congrArg (fun f => ModuleCat.Hom.hom f y)
    (HomologicalComplex.homologyπ_naturality
      (GHom.toCC (quotMap (rankRelaxed m).D (rankRelaxed m).gR)) 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [mem_finPlane]
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  rw [hnat, h1Equiv_apply]
  have hπ := congrArg (fun f => ModuleCat.Hom.hom f
    ((HomologicalComplex.cyclesMap
      (GHom.toCC (quotMap (rankRelaxed m).D (rankRelaxed m).gR)) 1).hom y))
    (homologyπ_h1Iso (rankRelaxed m).Wrel (rankRelaxed m).hWrel)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hπ
  rw [hπ]
  have hi := congrArg (fun f => ModuleCat.Hom.hom f y)
    (HomologicalComplex.cyclesMap_i
      (GHom.toCC (quotMap (rankRelaxed m).D (rankRelaxed m).gR)) 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hi
  rw [hi]
  have hd := congrArg (fun f => ModuleCat.Hom.hom f y) (K.iCycles_d 1 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at hd
  erw [GCx.toCC_d_hom _ 1 2 rfl] at hd
  generalize (K.iCycles 1).hom y = w at hd ⊢
  obtain ⟨a, u, x⟩ := w
  have h3 := congrArg (fun q => q.2.2) hd
  change (0 : (Fin (dimAt m 1) → ℚ) →ₗ[ℚ] _) a - u.2 - 0 = 0 at h3
  have h0a : (0 : (Fin (dimAt m 1) → ℚ) →ₗ[ℚ] (Fin (dimAt 2 1) → ℚ)) a = 0 := rfl
  have h4 : (u : (Fin (dimAt 2 1) → ℚ) × (Fin (dimAt 2 1) → ℚ)).2 = 0 := by
    rw [h0a, zero_sub, sub_zero, neg_eq_zero] at h3
    exact h3
  change (eqvA 2) (u : (Fin (dimAt 2 1) → ℚ) × (Fin (dimAt 2 1) → ℚ)).2 = 0
  rw [h4, map_zero]

/-- Kind: proved theorem. The exact finite-side sequence and the computed
ranks prove rank-two detection, rather than assuming it;
tex L4997–5003, L5072–5078. -/
theorem rankRelaxed_U (m : ℕ) :
    (rankRelaxed m).U = finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) := by
  have : FiniteDimensional ℚ ((rankRelaxed m).D.G.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt m 1) → ℚ))
  have : FiniteDimensional ℚ ((rankRelaxed m).D.L.X 0) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 0) → ℚ))
  have : FiniteDimensional ℚ ((rankFiniteSide m).U₁.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  have : FiniteDimensional ℚ ((rankSingularSide m).U₁.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  have h := (switchDims_of_selmerData (rankRelaxed m) (rankFiniteSide m)
    (rankSingularSide m)).1
  rw [rankFinite_h1, rankStrict_h1] at h
  have h2 : finrank ℚ ↥((rankRelaxed m).U ⊓ finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) =
      finrank ℚ ↥(finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) := by
    rw [finrank_finPlane_two]
    omega
  have hF : (rankRelaxed m).U ⊓ finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) =
      finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) :=
    Submodule.eq_of_le_of_finrank_eq inf_le_right h2
  exact le_antisymm (rankRelaxed_U_le m) (hF ▸ inf_le_left)

/-- Kind: proved theorem. The singular-side exact sequence computes its
first cohomology rank as `m`; tex L5072–5078. -/
theorem rankSingular_h1 (m : ℕ) :
    finrank ℚ ((selCx (rankSingularSide m).Dside).toCC.homology 1) = m := by
  have : FiniteDimensional ℚ ((rankRelaxed m).D.G.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt m 1) → ℚ))
  have : FiniteDimensional ℚ ((rankRelaxed m).D.L.X 0) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 0) → ℚ))
  have : FiniteDimensional ℚ ((rankFiniteSide m).U₁.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  have : FiniteDimensional ℚ ((rankSingularSide m).U₁.X 1) :=
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  have hs : finrank ℚ ((selCx (rankSingularSide m).Dstr).toCC.homology 1) = m :=
    (rankStrict m).hk0.symm.trans (rankStrict_h1 m)
  have h := (switchDims_of_selmerData (rankRelaxed m) (rankFiniteSide m)
    (rankSingularSide m)).2
  rw [hs, rankRelaxed_U, finPlane_inf_singPlane, finrank_bot, add_zero] at h
  exact h

/-- Kind: constructed nonquadratic step. Actual Selmer sides, shared
strict cohomology, proved detection, local duality and rank-based
cohomology equivalences give a switch between the specified stages;
tex L4997–5003, L5055–5086. -/
def rankStep (m : ℕ) (S₀ S₁ : TwoTermStage (RingHom.id ℚ))
    (h0 : S₀.fiberDim (RingHom.id ℚ) = m + 2)
    (h1 : S₁.fiberDim (RingHom.id ℚ) = m) :
    QuasiNonquadStep (RingHom.id ℚ) S₀ S₁ where
  R := (rankRelaxed m).toQuasi
  SF := (rankFiniteSide m).toQuasi
  SS := (rankSingularSide m).toQuasi
  hk0 := (rankStrict m).hk0
  ε := 1
  σ := 1
  J := J₀
  hε := one_ne_zero
  hσ := one_ne_zero
  hJ2 := J₀_sq
  hdual := by
    unfold LocalizationDualityInput
    rw [RelaxedLocalization.toQuasi_U, rankRelaxed_U]
    exact exLocalizationDuality 1 1 one_ne_zero one_ne_zero J₀ J₀_sq
  hdet := (rankRelaxed_U m).ge
  φ := by
    change (selCx (rankFiniteSide m).Dside).toCC.homology 1 ≃ₗ[ℚ]
      fiberH1 (RingHom.id ℚ) S₀
    have : FiniteDimensional ℚ ((rankRelaxed m).D.G.X 1) :=
      (inferInstance : FiniteDimensional ℚ (Fin (dimAt m 1) → ℚ))
    have : FiniteDimensional ℚ ((rankRelaxed m).D.L.X 0) :=
      (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 0) → ℚ))
    have : FiniteDimensional ℚ ((rankFiniteSide m).U₁.X 1) :=
      (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
    haveI := finiteDimensional_side (rankFiniteSide m)
    exact fiberEquivOf (RingHom.id ℚ) S₀ ((rankFinite_h1 m).trans h0.symm)
  φ' := by
    change (selCx (rankSingularSide m).Dside).toCC.homology 1 ≃ₗ[ℚ]
      fiberH1 (RingHom.id ℚ) S₁
    have : FiniteDimensional ℚ ((rankRelaxed m).D.G.X 1) :=
      (inferInstance : FiniteDimensional ℚ (Fin (dimAt m 1) → ℚ))
    have : FiniteDimensional ℚ ((rankRelaxed m).D.L.X 0) :=
      (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 0) → ℚ))
    have : FiniteDimensional ℚ ((rankSingularSide m).U₁.X 1) :=
      (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
    haveI := finiteDimensional_side (rankSingularSide m)
    exact fiberEquivOf (RingHom.id ℚ) S₁ ((rankSingular_h1 m).trans h1.symm)

end RankModel

end ZInQ.Contrib.RC53Assist.SwitchInterface
