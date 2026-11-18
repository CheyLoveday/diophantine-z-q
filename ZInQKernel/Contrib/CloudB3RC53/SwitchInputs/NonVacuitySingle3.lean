import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.NonVacuityQuad

/-!
# RC53 SwitchInputs: a three-dimensional single-sign Selmer example

A variant of the single-sign example of `NonVacuityQuad.lean` (section `Single`) with global part
`G = ℚ²` in degree one (`zGCx (Pn 2)`) instead of `ℚ`. Everything else is unchanged: the relaxed
condition is `U_rel = F ⊕ S`, the full local complex is `L = F ⊕ S` with
`ι(x, y) = (anti x, anti y)`, `res = 0`, and the involutions are `(x, y) ↦ (J₀x, −J₀y)` on
`F ⊕ S`, `J₀` on `U_F = F`, `−J₀` on `U_S = S`, the identity on `G`.

* `exQuadSingleStep3 : SelmerQuadSingleStep ℚ`: the resulting single-sign step.
* `finrank_V3`: `V = H¹(C(U_F))` has dimension exactly `3` (all of sign `+`). The side complex has
  trivial degree-zero term, so `clsL` is a bijection from `ker d¹`, and
  `ker d¹ = {(a, u, 0) | anti u = 0}` is isomorphic to `G¹ × ℚ = ℚ² × ℚ`.
* `finrank_V'3`: likewise `V' = H¹(C(U_S))` has dimension exactly `3`.

Classification: PROVED (non-vacuity).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Matrix Module ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Uniform.QuadraticCase
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

section Single3

/-- **The relaxed Selmer data of the three-dimensional single-sign example**: `G = ℚ²` (`res = 0`),
`U_rel = F ⊕ S`, the full local complex `L = F ⊕ S` with `ι(x, y) = (anti x, anti y)`, all in
degree one. Relaxed
cocycles have `anti x = anti y = 0`, so `U = F(e₊) ⊕ S(e₊)`. -/
def exRelD3 : SelData ℚ where
  G := zGCx (Pn 2)
  U := zGCx Qn
  L := zGCx Qn
  res := zHom fun _ => 0
  ι := zHom fun n => antiQ n

/-- The relaxed localization of the three-dimensional single-sign model
(`W_rel = F ⊕ S`, `g_R = id`). -/
def exRelB3 : RelaxedLocalization ℚ where
  D := exRelD3
  Wrel := zGCx Qn
  gR := zHom fun _ => LinearMap.id
  eR := (eqvA 2).prodCongr (eqvA 2)
  hWrel := concDegOne_Qn

/-- The finite side: `U_F = F` (`f₁ = inl`), `W₂ = S` (`g₂ = snd`), `U_str = 0`, `W₁ = F`. -/
def exSideF3 : SwitchSide exRelB3 (finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) where
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
  ip_exact y := ⟨fun h => ⟨y.1, Prod.ext rfl h.symm⟩, fun ⟨x, hx⟩ => by rw [← hx]; rfl⟩
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

/-- The singular side: `U_S = S` (`f₁ = inr`), `W₂ = F` (`g₂ = fst`), `U_str = 0`, `W₁ = S`. -/
def exSideS3 : SwitchSide exRelB3 (singPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)) where
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
  ip_exact y := ⟨fun h => ⟨y.2, Prod.ext h.symm rfl⟩, fun ⟨x, hx⟩ => by rw [← hx]; rfl⟩
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

/-- The involution of the relaxed data: identity on `G = ℚ²`, `(x, y) ↦ (J₀x, −J₀y)` on
`U = F ⊕ S` and on `L = F ⊕ S`. -/
def selRelT3 : SupportChangeData ℚ where
  D := exRelD3
  Dp := exRelD3
  g := zHom fun _ => LinearMap.id
  lam := zHom fun n => pmQ n
  mu := zHom fun n => pmQ n
  r := zHom fun _ => 0
  hres i j h a := by
    subst h
    change (0 : V2 i →ₗ[ℚ] V2 i × V2 i) a =
      pmQ i ((0 : V2 i →ₗ[ℚ] V2 i × V2 i) a) + antiQ i ((0 : V2 i →ₗ[ℚ] V2 i × V2 i) a)
    erw [zero_apply']; simp; try rfl
  hι i j h u := by
    subst h
    exact antiQ_pmQ i u

/-- The involution of the finite side `C(U_F)`: `J₀` on `U_F = F`, identity on `G`. -/
def selFT3 : SupportChangeData ℚ where
  D := exSideF3.Dside
  Dp := exSideF3.Dside
  g := zHom fun _ => LinearMap.id
  lam := zHom fun n => pmQ n
  mu := zHom fun n => flipM (dimAt 2 n)
  r := zHom fun _ => 0
  hres i j h a := by
    subst h
    change (0 : V2 i →ₗ[ℚ] V2 i × V2 i) a =
      pmQ i ((0 : V2 i →ₗ[ℚ] V2 i × V2 i) a) +
        antiQ i (LinearMap.inl ℚ (V2 i) (V2 i) ((0 : V2 i →ₗ[ℚ] V2 i) a))
    erw [zero_apply']; simp; try rfl
  hι i j h u := by
    subst h
    change antiQ i (LinearMap.inl ℚ (V2 i) (V2 i) (flipM _ u)) =
      pmQ i (antiQ i (LinearMap.inl ℚ (V2 i) (V2 i) u))
    rw [← antiQ_pmQ]
    refine congrArg (antiQ i) (Prod.ext rfl ?_)
    change (0 : V2 i) = -flipM _ 0
    simp

/-- The involution of the singular side `C(U_S)`: `−J₀` on `U_S = S`, identity on `G`. -/
def selST3 : SupportChangeData ℚ where
  D := exSideS3.Dside
  Dp := exSideS3.Dside
  g := zHom fun _ => LinearMap.id
  lam := zHom fun n => pmQ n
  mu := zHom fun n => -flipM (dimAt 2 n)
  r := zHom fun _ => 0
  hres i j h a := by
    subst h
    change (0 : V2 i →ₗ[ℚ] V2 i × V2 i) a =
      pmQ i ((0 : V2 i →ₗ[ℚ] V2 i × V2 i) a) +
        antiQ i (LinearMap.inr ℚ (V2 i) (V2 i) ((0 : V2 i →ₗ[ℚ] V2 i) a))
    erw [zero_apply']; simp; try rfl
  hι i j h u := by
    subst h
    change antiQ i (LinearMap.inr ℚ (V2 i) (V2 i) ((-flipM _) u)) =
      pmQ i (antiQ i (LinearMap.inr ℚ (V2 i) (V2 i) u))
    rw [← antiQ_pmQ]
    refine congrArg (antiQ i) (Prod.ext ?_ rfl)
    change (0 : V2 i) = flipM _ 0
    simp

/-- The sign involution on `H¹(C_rel)`. -/
def σr3 : (selCx exRelD3).toCC.homology 1 →ₗ[ℚ] (selCx exRelD3).toCC.homology 1 :=
  H1 (supportMap selRelT3)

/-- The sign involution on `V = H¹(C(U_F))`. -/
def σV3 : (selCx exSideF3.Dside).toCC.homology 1 →ₗ[ℚ] (selCx exSideF3.Dside).toCC.homology 1 :=
  H1 (supportMap selFT3)

/-- The sign involution on `V' = H¹(C(U_S))`. -/
def σV'3 : (selCx exSideS3.Dside).toCC.homology 1 →ₗ[ℚ] (selCx exSideS3.Dside).toCC.homology 1 :=
  H1 (supportMap selST3)

/-- `σ_rel` is an involution. -/
theorem σr3_sq : σr3 ∘ₗ σr3 = LinearMap.id := by
  refine (H1_comp _ _).trans (H1_eq_id _ fun x => ?_)
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  change (a, pmQ 1 (pmQ 1 u + (0 : V2 1 →ₗ[ℚ] V2 1 × V2 1) a) + (0 : V2 1 →ₗ[ℚ] V2 1 × V2 1) a,
      pmQ (1 - 1) (pmQ (1 - 1) l)) = (a, u, l)
  erw [zero_apply']
  rw [add_zero, add_zero]
  exact Prod.ext rfl (Prod.ext (pmQ_pmQ 1 u) (pmQ_pmQ (1 - 1) l))

/-- `σ_V` is an involution. -/
theorem σV3_sq : σV3 ∘ₗ σV3 = LinearMap.id := by
  refine (H1_comp _ _).trans (H1_eq_id _ fun x => ?_)
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  change (a, flipM _ (flipM _ u + (0 : V2 1 →ₗ[ℚ] V2 1) a) + (0 : V2 1 →ₗ[ℚ] V2 1) a,
      pmQ (1 - 1) (pmQ (1 - 1) l)) = (a, u, l)
  erw [zero_apply']
  rw [add_zero, add_zero]
  exact Prod.ext rfl (Prod.ext (flipM_flipM _ u) (pmQ_pmQ (1 - 1) l))

/-- `σ_V'` is an involution. -/
theorem σV'3_sq : σV'3 ∘ₗ σV'3 = LinearMap.id := by
  refine (H1_comp _ _).trans (H1_eq_id _ fun x => ?_)
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  change (a, (-flipM _) ((-flipM _) u + (0 : V2 1 →ₗ[ℚ] V2 1) a) + (0 : V2 1 →ₗ[ℚ] V2 1) a,
      pmQ (1 - 1) (pmQ (1 - 1) l)) = (a, u, l)
  erw [zero_apply']
  rw [add_zero, add_zero]
  exact Prod.ext rfl (Prod.ext (negflip_negflip _ u) (pmQ_pmQ (1 - 1) l))

/-- `β_F [(a, u, l)] = u` (in `ℚ²`). -/
theorem βF_cls3 (x : LinearMap.ker ((selCx exSideF3.Dside).toCC.d 1 2).hom) :
    exSideF3.βF (clsL _ x) = eqvA 2 x.1.2.1 := by
  unfold SwitchSide.βF
  rw [LinearMap.comp_apply]
  erw [H1_cls']
  rw [LinearEquiv.coe_coe, LinearEquiv.trans_apply, h1Equiv_cls]
  rfl

/-- `β_S [(a, u, l)] = u` (in `ℚ²`). -/
theorem βS_cls3 (x : LinearMap.ker ((selCx exSideS3.Dside).toCC.d 1 2).hom) :
    exSideS3.βS (clsL _ x) = eqvA 2 x.1.2.1 := by
  unfold SwitchSide.βS
  rw [LinearMap.comp_apply]
  erw [H1_cls']
  rw [LinearEquiv.coe_coe, LinearEquiv.trans_apply, h1Equiv_cls]
  rfl

/-- The relaxed localization of a class `[(a, (x, y), l)]` is `(x, y)`. -/
theorem lam_cls3 (x : LinearMap.ker ((selCx exRelD3).toCC.d 1 2).hom) :
    exRelB3.lam (clsL _ x) = (eqvA 2 x.1.2.1.1, eqvA 2 x.1.2.1.2) := by
  unfold RelaxedLocalization.lam
  rw [LinearMap.comp_apply]
  erw [H1_cls']
  rw [LinearEquiv.coe_coe, LinearEquiv.trans_apply, h1Equiv_cls]
  rfl

/-- `σ_V` fixes the image of the strict cohomology on the finite side. -/
theorem fixF3 : σV3 ∘ₗ H1 (changeMap exSideF3.Dside exSideF3.fs) =
    H1 (changeMap exSideF3.Dside exSideF3.fs) := by
  unfold σV3
  refine (H1_comp _ _).trans (H1_congr _ _ fun x => ?_)
  obtain ⟨⟨a, s, l⟩, hx⟩ := x
  have hs : s = 0 := Subsingleton.elim (α := Fin 0 → ℚ) _ _
  subst hs
  refine Prod.ext rfl (Prod.ext ?_ (subsingleton_Q0.elim _ _))
  change flipM _ ((0 : (Fin 0 → ℚ) →ₗ[ℚ] V2 1) 0) + (0 : V2 1 →ₗ[ℚ] V2 1) a =
    (0 : (Fin 0 → ℚ) →ₗ[ℚ] V2 1) 0
  simp only [map_zero, zero_add]
  rfl

/-- `σ_V'` fixes the image of the strict cohomology on the singular side. -/
theorem fixS3 : σV'3 ∘ₗ H1 (changeMap exSideS3.Dside exSideS3.fs) =
    H1 (changeMap exSideS3.Dside exSideS3.fs) := by
  unfold σV'3
  refine (H1_comp _ _).trans (H1_congr _ _ fun x => ?_)
  obtain ⟨⟨a, s, l⟩, hx⟩ := x
  have hs : s = 0 := Subsingleton.elim (α := Fin 0 → ℚ) _ _
  subst hs
  refine Prod.ext rfl (Prod.ext ?_ (subsingleton_Q0.elim _ _))
  change (-flipM _) ((0 : (Fin 0 → ℚ) →ₗ[ℚ] V2 1) 0) + (0 : V2 1 →ₗ[ℚ] V2 1) a =
    (0 : (Fin 0 → ℚ) →ₗ[ℚ] V2 1) 0
  simp only [map_zero, zero_add]
  rfl

/-- `H¹(f₁)` intertwines `σ_V` and `σ_rel` on the finite side. -/
theorem γF3 : H1 (changeMap exRelD3 exSideF3.f₁) ∘ₗ σV3 =
    σr3 ∘ₗ H1 (changeMap exRelD3 exSideF3.f₁) := by
  unfold σV3 σr3
  refine (H1_comp _ _).trans ((H1_congr _ _ fun x => ?_).trans (H1_comp _ _).symm)
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  change LinearMap.inl ℚ (V2 1) (V2 1) (flipM _ u + (0 : V2 1 →ₗ[ℚ] V2 1) a) =
    pmQ 1 (LinearMap.inl ℚ (V2 1) (V2 1) u) + (0 : V2 1 →ₗ[ℚ] V2 1 × V2 1) a
  refine Prod.ext rfl ?_
  change (0 : V2 1) = -flipM _ 0 + 0
  simp

/-- `H¹(f₁)` intertwines `σ_V'` and `σ_rel` on the singular side. -/
theorem γS3 : H1 (changeMap exRelD3 exSideS3.f₁) ∘ₗ σV'3 =
    σr3 ∘ₗ H1 (changeMap exRelD3 exSideS3.f₁) := by
  unfold σV'3 σr3
  refine (H1_comp _ _).trans ((H1_congr _ _ fun x => ?_).trans (H1_comp _ _).symm)
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  change LinearMap.inr ℚ (V2 1) (V2 1) ((-flipM _) u + (0 : V2 1 →ₗ[ℚ] V2 1) a) =
    pmQ 1 (LinearMap.inr ℚ (V2 1) (V2 1) u) + (0 : V2 1 →ₗ[ℚ] V2 1 × V2 1) a
  refine Prod.ext ?_ rfl
  change (0 : V2 1) = flipM _ 0 + 0
  simp

/-- `β_F` is `J₀`-equivariant. -/
theorem βF3_equiv : exSideF3.βF ∘ₗ σV3 = J₀L ∘ₗ exSideF3.βF := by
  ext1 v
  obtain ⟨x, rfl⟩ := clsL_surjective _ v
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  unfold σV3
  erw [H1_cls']
  rw [βF_cls3, βF_cls3]
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  change eqvA 2 (flipM _ u + (0 : V2 1 →ₗ[ℚ] V2 1) a) = J₀L (eqvA 2 u)
  erw [zero_apply', add_zero]
  exact eqvA_flip u

/-- `β_S` is `(−J₀)`-equivariant. -/
theorem βS3_equiv : exSideS3.βS ∘ₗ σV'3 = (-J₀L) ∘ₗ exSideS3.βS := by
  ext1 v
  obtain ⟨x, rfl⟩ := clsL_surjective _ v
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  unfold σV'3
  erw [H1_cls']
  rw [βS_cls3, βS_cls3, LinearMap.neg_apply]
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  change eqvA 2 ((-flipM _) u + (0 : V2 1 →ₗ[ℚ] V2 1) a) = -J₀L (eqvA 2 u)
  erw [zero_apply', add_zero]
  exact eqvA_negflip u

/-- The relaxed localization is equivariant for the local involution `(x, y) ↦ (J₀x, −J₀y)`. -/
theorem lam3_equiv : exRelB3.lam ∘ₗ σr3 = localInv J₀L ∘ₗ exRelB3.lam := by
  ext1 v
  obtain ⟨x, rfl⟩ := clsL_surjective _ v
  change exRelB3.lam (H1 (supportMap selRelT3) (clsL _ x)) = localInv J₀L (exRelB3.lam (clsL _ x))
  erw [H1_cls']
  rw [lam_cls3 x, localInv_apply]
  refine (lam_cls3 ⟨_, _⟩).trans ?_
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  change (eqvA 2 (pmQ 1 u + (0 : V2 1 →ₗ[ℚ] V2 1 × V2 1) a).1,
      eqvA 2 (pmQ 1 u + (0 : V2 1 →ₗ[ℚ] V2 1 × V2 1) a).2) =
    (J₀L (eqvA 2 u.1), -J₀L (eqvA 2 u.2))
  erw [zero_apply', add_zero]
  refine Prod.ext (eqvA_flip u.1) ?_
  change eqvA 2 (-(flipM _ u.2)) = -J₀L (eqvA 2 u.2)
  rw [map_neg]
  exact congrArg Neg.neg (eqvA_flip u.2)

/-- The degree-zero strict cochains vanish. -/
theorem str3_h0 : Subsingleton ((Fin (dimAt 2 0) → ℚ) × (Fin 0 → ℚ) ×
    (V2 (0 - 1) × V2 (0 - 1))) := by
  have := subsingleton_dimAt 2 (n := 0) (by norm_num)
  have := subsingleton_dimAt 2 (n := 0 - 1) (by norm_num)
  infer_instance

/-- The strict complex of the finite side has `d¹ = 0`. -/
theorem exSideF3_str_d12 : (selCx exSideF3.Dstr).toCC.d 1 2 = 0 := by
  ext c
  erw [GCx.toCC_d_hom _ 1 2 rfl]
  obtain ⟨a, u, x⟩ := c
  have hu : u = 0 := Subsingleton.elim (α := Fin 0 → ℚ) _ _
  subst hu
  refine Prod.ext rfl (Prod.ext rfl ?_)
  change (0 : V2 1 →ₗ[ℚ] V2 1 × V2 1) a - antiQ 1 (LinearMap.inl ℚ (V2 1) (V2 1)
    ((0 : (Fin 0 → ℚ) →ₗ[ℚ] V2 1) 0)) - 0 = 0
  erw [zero_apply']
  simp

/-- The strict complex of the singular side has `d¹ = 0`. -/
theorem exSideS3_str_d12 : (selCx exSideS3.Dstr).toCC.d 1 2 = 0 := by
  ext c
  erw [GCx.toCC_d_hom _ 1 2 rfl]
  obtain ⟨a, u, x⟩ := c
  have hu : u = 0 := Subsingleton.elim (α := Fin 0 → ℚ) _ _
  subst hu
  refine Prod.ext rfl (Prod.ext rfl ?_)
  change (0 : V2 1 →ₗ[ℚ] V2 1 × V2 1) a - antiQ 1 (LinearMap.inr ℚ (V2 1) (V2 1)
    ((0 : (Fin 0 → ℚ) →ₗ[ℚ] V2 1) 0)) - 0 = 0
  erw [zero_apply']
  simp

/-- The degree-zero strict cochains of the singular side vanish. -/
theorem strS3_h0 :
    Subsingleton (exSideS3.Dstr.G.X 0 × exSideS3.Dstr.U.X 0 × exSideS3.Dstr.L.X (0 - 1)) := by
  have := subsingleton_dimAt 2 (n := 0) (by norm_num)
  have := subsingleton_dimAt 2 (n := 0 - 1) (by norm_num)
  change Subsingleton ((Fin (dimAt 2 0) → ℚ) × (Fin 0 → ℚ) × (V2 (0 - 1) × V2 (0 - 1)))
  infer_instance

/-- The degree-zero strict cochains of the finite side vanish. -/
theorem strF3_h0 :
    Subsingleton (exSideF3.Dstr.G.X 0 × exSideF3.Dstr.U.X 0 × exSideF3.Dstr.L.X (0 - 1)) := by
  have := subsingleton_dimAt 2 (n := 0) (by norm_num)
  have := subsingleton_dimAt 2 (n := 0 - 1) (by norm_num)
  change Subsingleton ((Fin (dimAt 2 0) → ℚ) × (Fin 0 → ℚ) × (V2 (0 - 1) × V2 (0 - 1)))
  infer_instance

/-- The strict complex of the singular side has `d⁰ = 0`. -/
theorem strS3_d01 : (selCx exSideS3.Dstr).toCC.d 0 1 = 0 := selCx_d01_zero _ strS3_h0

/-- The strict complex of the finite side has `d⁰ = 0`. -/
theorem strF3_d01 : (selCx exSideF3.Dstr).toCC.d 0 1 = 0 := selCx_d01_zero _ strF3_h0

/-- The common degree-one strict cochain module `G¹ × 0 × L⁰`. -/
abbrev Tstr3 : Type := (Fin (dimAt 2 1) → ℚ) × (Fin 0 → ℚ) × (V2 (1 - 1) × V2 (1 - 1))

/-- The strict cohomology of the singular side is its degree-one cochain module. -/
noncomputable def eStrS3 : (selCx exSideS3.Dstr).toCC.homology 1 ≃ₗ[ℚ] Tstr3 :=
  (h1IsoOfZero _ strS3_d01 exSideS3_str_d12).toLinearEquiv

/-- The strict cohomology of the finite side is its degree-one cochain module. -/
noncomputable def eStrF3 : (selCx exSideF3.Dstr).toCC.homology 1 ≃ₗ[ℚ] Tstr3 :=
  (h1IsoOfZero _ strF3_d01 exSideF3_str_d12).toLinearEquiv

/-- The identification of the two strict cohomology groups of the single-sign model. -/
noncomputable def eK3 : (selCx exSideS3.Dstr).toCC.homology 1 ≃ₗ[ℚ]
    (selCx exSideF3.Dstr).toCC.homology 1 :=
  eStrS3.trans eStrF3.symm

/-- **`SelmerQuadSwitch` for the single-sign model** (`J = J₀`, genuine involutions). -/
noncomputable def exQuadSwitch3 : SelmerQuadSwitch ℚ J₀L where
  R := exRelB3
  SF := exSideF3
  SS := exSideS3
  fG := (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  fL := (inferInstance : FiniteDimensional ℚ (V2 0 × V2 0))
  fF := (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  fS := (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
  eK := eK3
  σK := LinearMap.id
  σV := σV3
  σV' := σV'3
  σr := σr3
  hK := LinearMap.id_comp _
  hV := σV3_sq
  hV' := σV'3_sq
  hr := σr3_sq
  hα' := LinearMap.ext fun v => (LinearMap.congr_fun fixF3 v).symm
  hβ' := βF3_equiv
  hγ' := γF3
  hα'' := LinearMap.ext fun v => (LinearMap.congr_fun fixS3 (eK3.symm v)).symm
  hβ'' := βS3_equiv
  hγ'' := γS3
  hl := lam3_equiv


/-- The cocycle equation of the finite side forces `anti u = 0`. -/
theorem anti_of_eqF3 (u : V2 1)
    (h : (0 : V2 1 →ₗ[ℚ] V2 1 × V2 1) 0 - antiQ 1 (LinearMap.inl ℚ (V2 1) (V2 1) u) -
      (0 : V2 (1 - 1) × V2 (1 - 1) →ₗ[ℚ] V2 1 × V2 1) 0 = 0) : antiM _ u = 0 := by
  have := congrArg Prod.fst h
  simpa using this

/-- The relaxed cocycle equation forces `anti x = anti y = 0`. -/
theorem anti_of_eqR3 (u : V2 1 × V2 1)
    (h : (0 : V2 1 →ₗ[ℚ] V2 1 × V2 1) 0 - antiQ 1 u -
      (0 : V2 (1 - 1) × V2 (1 - 1) →ₗ[ℚ] V2 1 × V2 1) 0 = 0) : antiQ 1 u = 0 := by
  simpa using h

/-- The cocycle condition of the finite side of the single-sign model: `anti u = 0`. -/
theorem cycleF3 (x : LinearMap.ker ((selCx exSideF3.Dside).toCC.d 1 2).hom) :
    antiM _ x.1.2.1 = 0 := by
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  have hd := LinearMap.mem_ker.mp hx
  erw [GCx.toCC_d_hom _ 1 2 rfl] at hd
  have h3 := congrArg (fun q => q.2.2) hd
  change (0 : V2 1 →ₗ[ℚ] V2 1 × V2 1) a - antiQ 1 (LinearMap.inl ℚ (V2 1) (V2 1) u) -
    (0 : V2 (1 - 1) × V2 (1 - 1) →ₗ[ℚ] V2 1 × V2 1) l = 0 at h3
  exact anti_of_eqF3 u h3

/-- The cocycle condition of the relaxed single-sign model: `anti x = anti y = 0`. -/
theorem cycleR3 (x : LinearMap.ker ((selCx exRelD3).toCC.d 1 2).hom) :
    antiQ 1 x.1.2.1 = 0 := by
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  have hd := LinearMap.mem_ker.mp hx
  erw [GCx.toCC_d_hom _ 1 2 rfl] at hd
  have h3 := congrArg (fun q => q.2.2) hd
  change (0 : V2 1 →ₗ[ℚ] V2 1 × V2 1) a - antiQ 1 u -
    (0 : V2 (1 - 1) × V2 (1 - 1) →ₗ[ℚ] V2 1 × V2 1) l = 0 at h3
  exact anti_of_eqR3 u h3

/-- The relaxed cochain `(0, u, 0)`. -/
def mkR3 (u : V2 1 × V2 1) : (selCx exRelD3).toCC.X 1 :=
  ((0 : V2 1), u, (0 : V2 (1 - 1) × V2 (1 - 1)))

/-- **The relaxed image of the single-sign model** is `F(e₊) ⊕ S(e₊)`. -/
theorem exRelB3_U_iff (z : (Fin 2 → ℚ) × (Fin 2 → ℚ)) : z ∈ exRelB3.U ↔ z.1 1 = 0 ∧ z.2 1 = 0 := by
  rw [← RelaxedLocalization.range_lam]
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨x, rfl⟩ := clsL_surjective (selCx exRelD3).toCC v
    have hc := cycleR3 x
    exact ⟨(congrArg (fun p => p.1 1) (lam_cls3 x)).trans
        (eqvA_one_of_anti (congrArg Prod.fst hc)),
      (congrArg (fun p => p.2 1) (lam_cls3 x)).trans (eqvA_one_of_anti (congrArg Prod.snd hc))⟩
  · rintro ⟨h1, h2⟩
    let u : V2 1 × V2 1 := ((eqvA 2).symm z.1, (eqvA 2).symm z.2)
    have hmem : mkR3 u ∈ LinearMap.ker ((selCx exRelD3).toCC.d 1 2).hom := by
      refine LinearMap.mem_ker.mpr ?_
      erw [GCx.toCC_d_hom _ 1 2 rfl]
      refine Prod.ext rfl (Prod.ext rfl ?_)
      change (0 : V2 1 →ₗ[ℚ] V2 1 × V2 1) 0 - antiQ 1 u -
        (0 : V2 (1 - 1) × V2 (1 - 1) →ₗ[ℚ] V2 1 × V2 1) 0 = 0
      rw [map_zero, map_zero, zero_sub, sub_zero, neg_eq_zero]
      exact Prod.ext (anti_of_eqvA_one h1) (anti_of_eqvA_one h2)
    refine ⟨clsL (selCx exRelD3).toCC ⟨_, hmem⟩, (lam_cls3 ⟨_, hmem⟩).trans ?_⟩
    exact Prod.ext (LinearEquiv.apply_symm_apply _ _) (LinearEquiv.apply_symm_apply _ _)

/-- `F(e₊) ⊕ S(e₊)` is Lagrangian for the local pairing. -/
theorem exRelB3_lagrangian (u : (Fin 2 → ℚ) × (Fin 2 → ℚ)) :
    u ∈ exRelB3.U ↔ ∀ w ∈ exRelB3.U, localPair 1 J₀L u w = 0 := by
  have key : ∀ w : (Fin 2 → ℚ) × (Fin 2 → ℚ), w.1 1 = 0 → w.2 1 = 0 →
      localPair 1 J₀L u w = -(u.1 1 * w.2 0) - w.1 0 * u.2 1 := by
    intro w hw1 hw2
    simp only [localPair, crossPair, e₂_apply, J₀L_apply_zero, J₀L_apply_one, hw1, hw2]
    ring
  rw [exRelB3_U_iff]
  constructor
  · rintro ⟨h1, h2⟩ w hw
    rw [exRelB3_U_iff] at hw
    rw [key w hw.1 hw.2, h1, h2]
    ring
  · intro h
    have hA := h (![1, 0], 0) ((exRelB3_U_iff _).mpr ⟨rfl, rfl⟩)
    have hB := h (0, ![1, 0]) ((exRelB3_U_iff _).mpr ⟨rfl, rfl⟩)
    rw [key _ rfl rfl] at hA hB
    simp at hA hB
    exact ⟨hB, hA⟩

/-- The degree-zero term of the finite side complex vanishes. -/
theorem exSideF3_X0 : Subsingleton ((selCx exSideF3.Dside).toCC.X 0) := by
  have := subsingleton_dimAt 2 (n := 0) (by norm_num)
  have := subsingleton_dimAt 2 (n := 0) (by norm_num)
  have := subsingleton_dimAt 2 (n := 0 - 1) (by norm_num)
  change Subsingleton ((Fin (dimAt 2 0) → ℚ) × V2 0 × (V2 (0 - 1) × V2 (0 - 1)))
  infer_instance

/-- A cocycle `(a, u, 0)` of the finite side with `anti u = 0`. -/
def cycF3 (a : V2 1) (u : V2 1) (hu : antiM _ u = 0) :
    LinearMap.ker ((selCx exSideF3.Dside).toCC.d 1 2).hom :=
  ⟨((a, u, (0 : V2 (1 - 1) × V2 (1 - 1))) : (selCx exSideF3.Dside).toCC.X 1), by
    refine LinearMap.mem_ker.mpr ?_
    erw [GCx.toCC_d_hom _ 1 2 rfl]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    change (0 : V2 1 →ₗ[ℚ] V2 1 × V2 1) a - antiQ 1 (LinearMap.inl ℚ (V2 1) (V2 1) u) -
      (0 : V2 (1 - 1) × V2 (1 - 1) →ₗ[ℚ] V2 1 × V2 1) 0 = 0
    rw [LinearMap.zero_apply, LinearMap.zero_apply, zero_sub, sub_zero, neg_eq_zero]
    exact Prod.ext hu (map_zero (antiM (dimAt 2 1)))⟩

/-- `σ` acts trivially on `V = H¹(C(U_F))` in the single-sign model (all classes have sign `+`). -/
theorem σV3_eq_id : σV3 = LinearMap.id :=
  H1_eq_id _ fun x => by
    have hc := cycleF3 x
    obtain ⟨⟨a, u, l⟩, hx⟩ := x
    change (a, flipM _ u + (0 : V2 1 →ₗ[ℚ] V2 1) a, pmQ (1 - 1) l) = (a, u, l)
    erw [zero_apply']
    rw [add_zero, flipM_eq_self_of_anti _ hc]
    exact Prod.ext rfl (Prod.ext rfl (subsingleton_Q0.elim _ _))

/-- The relaxed localization of `[(a, u, 0)]` from the finite side is `(u, 0)`. -/
theorem loc3_cycF3 (a : V2 1) (u : V2 1) (hu : antiM _ u = 0) :
    (exRelB3.lam ∘ₗ H1 (changeMap exRelB3.D exSideF3.f₁)) (clsL _ (cycF3 a u hu)) =
      (eqvA 2 u, 0) := by
  change exRelB3.lam (H1 (changeMap exRelD3 exSideF3.f₁) (clsL _ (cycF3 a u hu))) = _
  erw [H1_cls']
  refine (lam_cls3 ⟨_, _⟩).trans ?_
  change (eqvA 2 (LinearMap.inl ℚ (V2 1) (V2 1) u).1,
    eqvA 2 (LinearMap.inl ℚ (V2 1) (V2 1) u).2) = _
  simp

/-! ### Exact dimension of `V` and `V'` -/

/-- When the degree-zero term vanishes, `H¹` has the dimension of the degree-one cocycles
(`clsL` is a bijection). -/
theorem finrank_H1_eq_ker (K : CochainComplex (ModuleCat.{0} ℚ) ℤ) (h0 : Subsingleton (K.X 0)) :
    finrank ℚ (K.homology 1) = finrank ℚ (LinearMap.ker (K.d 1 2).hom) :=
  (LinearEquiv.ofBijective (clsL K) ⟨clsL_injective K h0, clsL_surjective K⟩).finrank_eq.symm

/-- A vector of `F = ℚ²` with vanishing `e₋`-coordinate is a multiple of `u₊`. -/
theorem eq_smul_uP {u : V2 1} (hu : antiM _ u = 0) : (eqvA 2 u 0) • uP = u := by
  apply (eqvA 2).injective
  rw [map_smul, uP, LinearEquiv.apply_symm_apply]
  have h1 := eqvA_one_of_anti hu
  ext i
  fin_cases i
  · simp [eP]
  · simp [eP, h1]

/-- The `e₊`-coordinate of `t • u₊` is `t`. -/
theorem eqvA_smul_uP (t : ℚ) : eqvA 2 (t • uP) 0 = t := by
  rw [map_smul, uP, LinearEquiv.apply_symm_apply]
  simp [eP]

/-- Multiples of `u₊` have vanishing `e₋`-coordinate. -/
theorem anti_smul_uP (t : ℚ) : antiM _ (t • uP) = 0 := by
  rw [map_smul, anti_uP, smul_zero]

/-- **The degree-one cocycles of the finite side** are `{(a, t • u₊, 0)} ≅ G¹ × ℚ`. -/
noncomputable def kerEquivF3 :
    LinearMap.ker ((selCx exSideF3.Dside).toCC.d 1 2).hom ≃ₗ[ℚ] V2 1 × ℚ where
  toFun x := (x.1.1, eqvA 2 x.1.2.1 0)
  invFun p := cycF3 p.1 (p.2 • uP) (anti_smul_uP p.2)
  map_add' x y := by
    obtain ⟨⟨a, u, l⟩, hx⟩ := x
    obtain ⟨⟨a', u', l'⟩, hy⟩ := y
    exact Prod.ext rfl (congrFun (map_add (eqvA 2) u u') 0)
  map_smul' c x := by
    obtain ⟨⟨a, u, l⟩, hx⟩ := x
    exact Prod.ext rfl (congrFun (map_smul (eqvA 2) c u) 0)
  left_inv x := by
    have hc := cycleF3 x
    obtain ⟨⟨a, u, l⟩, hx⟩ := x
    apply Subtype.ext
    change (a, (eqvA 2 u 0) • uP, (0 : V2 (1 - 1) × V2 (1 - 1))) = (a, u, l)
    rw [eq_smul_uP hc]
    exact Prod.ext rfl (Prod.ext rfl (subsingleton_Q0.elim _ _))
  right_inv p := Prod.ext rfl (eqvA_smul_uP p.2)

/-- `dim (G¹ × ℚ) = 3`. -/
theorem finrank_G1_prod : finrank ℚ (V2 1 × ℚ) = 3 := by
  rw [Module.finrank_prod, Module.finrank_fin_fun, dimAt_one, Module.finrank_self]

/-- **`V = H¹(C(U_F))` is three-dimensional.** -/
theorem finrank_side3 : finrank ℚ ((selCx exSideF3.Dside).toCC.homology 1) = 3 := by
  rw [finrank_H1_eq_ker _ exSideF3_X0, kerEquivF3.finrank_eq, finrank_G1_prod]

/-- The cocycle condition of the singular side: `anti u = 0`. -/
theorem anti_of_eqS3 (u : V2 1)
    (h : (0 : V2 1 →ₗ[ℚ] V2 1 × V2 1) 0 - antiQ 1 (LinearMap.inr ℚ (V2 1) (V2 1) u) -
      (0 : V2 (1 - 1) × V2 (1 - 1) →ₗ[ℚ] V2 1 × V2 1) 0 = 0) : antiM _ u = 0 := by
  have := congrArg Prod.snd h
  simpa using this

/-- The cocycle condition of the singular side of the single-sign model: `anti u = 0`. -/
theorem cycleS3 (x : LinearMap.ker ((selCx exSideS3.Dside).toCC.d 1 2).hom) :
    antiM _ x.1.2.1 = 0 := by
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  have hd := LinearMap.mem_ker.mp hx
  erw [GCx.toCC_d_hom _ 1 2 rfl] at hd
  have h3 := congrArg (fun q => q.2.2) hd
  change (0 : V2 1 →ₗ[ℚ] V2 1 × V2 1) a - antiQ 1 (LinearMap.inr ℚ (V2 1) (V2 1) u) -
    (0 : V2 (1 - 1) × V2 (1 - 1) →ₗ[ℚ] V2 1 × V2 1) l = 0 at h3
  exact anti_of_eqS3 u h3

/-- A cocycle `(a, u, 0)` of the singular side with `anti u = 0`. -/
def cycS3 (a : V2 1) (u : V2 1) (hu : antiM _ u = 0) :
    LinearMap.ker ((selCx exSideS3.Dside).toCC.d 1 2).hom :=
  ⟨((a, u, (0 : V2 (1 - 1) × V2 (1 - 1))) : (selCx exSideS3.Dside).toCC.X 1), by
    refine LinearMap.mem_ker.mpr ?_
    erw [GCx.toCC_d_hom _ 1 2 rfl]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    change (0 : V2 1 →ₗ[ℚ] V2 1 × V2 1) a - antiQ 1 (LinearMap.inr ℚ (V2 1) (V2 1) u) -
      (0 : V2 (1 - 1) × V2 (1 - 1) →ₗ[ℚ] V2 1 × V2 1) 0 = 0
    rw [LinearMap.zero_apply, LinearMap.zero_apply, zero_sub, sub_zero, neg_eq_zero]
    exact Prod.ext (map_zero (antiM (dimAt 2 1))) hu⟩

/-- The degree-zero term of the singular side complex vanishes. -/
theorem exSideS3_X0 : Subsingleton ((selCx exSideS3.Dside).toCC.X 0) := by
  have := subsingleton_dimAt 2 (n := 0) (by norm_num)
  have := subsingleton_dimAt 2 (n := 0 - 1) (by norm_num)
  change Subsingleton ((Fin (dimAt 2 0) → ℚ) × V2 0 × (V2 (0 - 1) × V2 (0 - 1)))
  infer_instance

/-- **The degree-one cocycles of the singular side** are `{(a, t • u₊, 0)} ≅ G¹ × ℚ`. -/
noncomputable def kerEquivS3 :
    LinearMap.ker ((selCx exSideS3.Dside).toCC.d 1 2).hom ≃ₗ[ℚ] V2 1 × ℚ where
  toFun x := (x.1.1, eqvA 2 x.1.2.1 0)
  invFun p := cycS3 p.1 (p.2 • uP) (anti_smul_uP p.2)
  map_add' x y := by
    obtain ⟨⟨a, u, l⟩, hx⟩ := x
    obtain ⟨⟨a', u', l'⟩, hy⟩ := y
    exact Prod.ext rfl (congrFun (map_add (eqvA 2) u u') 0)
  map_smul' c x := by
    obtain ⟨⟨a, u, l⟩, hx⟩ := x
    exact Prod.ext rfl (congrFun (map_smul (eqvA 2) c u) 0)
  left_inv x := by
    have hc := cycleS3 x
    obtain ⟨⟨a, u, l⟩, hx⟩ := x
    apply Subtype.ext
    change (a, (eqvA 2 u 0) • uP, (0 : V2 (1 - 1) × V2 (1 - 1))) = (a, u, l)
    rw [eq_smul_uP hc]
    exact Prod.ext rfl (Prod.ext rfl (subsingleton_Q0.elim _ _))
  right_inv p := Prod.ext rfl (eqvA_smul_uP p.2)

/-- **`V' = H¹(C(U_S))` is three-dimensional.** -/
theorem finrank_sideS3 : finrank ℚ ((selCx exSideS3.Dside).toCC.homology 1) = 3 := by
  rw [finrank_H1_eq_ker _ exSideS3_X0, kerEquivS3.finrank_eq, finrank_G1_prod]

/-- **`SelmerQuadSingleStep` is inhabited by a three-dimensional example**: the single-sign model
with `G = ℚ²`, `U = F(e₊) ⊕ S(e₊)` (Lagrangian), the genuine sign involutions of `exQuadSwitch3`,
`V = H¹(C(U_F))` three-dimensional of sign `+` only, and `c₊ = [(0, e₊)]` with nonzero localization
`(e₊, 0)`. -/
noncomputable def exQuadSingleStep3 : SelmerQuadSingleStep ℚ where
  h2 := two_ne_zero_ℚ
  ε := 1
  hε := one_ne_zero
  J := J₀L
  hJ2 := J₀L_sq
  ep := eP
  em := eM
  hp := J₀L_eP
  hm := J₀L_eM
  he := e₂_eP_eM_ne
  X := exQuadSwitch3
  hU u := exRelB3_lagrangian u
  cp := clsL _ (cycF3 0 uP anti_uP)
  hcp := by change σV3 _ = _; rw [σV3_eq_id]; rfl
  hdet _ := by
    change (exRelB3.lam ∘ₗ H1 (changeMap exRelB3.D exSideF3.f₁)) (clsL _ (cycF3 0 uP anti_uP)) ≠ 0
    rw [loc3_cycF3]
    simp only [uP, LinearEquiv.apply_symm_apply]
    exact pair_ne_zero eP_ne
  hs1 := by
    change 1 < finrank ℚ ↥(signPart σV3 (1 : ℚ))
    have : signPart σV3 (1 : ℚ) = ⊤ := by
      ext v; simp [mem_signPart, σV3_eq_id]
    rw [this, finrank_top, finrank_side3]
    norm_num
  hs0 := by
    change 0 = finrank ℚ ↥(signPart σV3 (-1 : ℚ))
    have : signPart σV3 (-1 : ℚ) = ⊥ := by
      ext v
      simp only [mem_signPart, σV3_eq_id, LinearMap.id_apply, neg_smul, one_smul,
        Submodule.mem_bot]
      constructor
      · intro h
        have h2 : (2 : ℚ) • v = 0 := by rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel v
        exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
      · rintro rfl; simp
    rw [this, finrank_bot]

/-- **The finite-side cohomology of `exQuadSingleStep3` is exactly three-dimensional.** -/
theorem finrank_V3 :
    finrank ℚ ((selCx exQuadSingleStep3.X.SF.Dside).toCC.homology 1) = 3 :=
  finrank_side3

/-- **The singular-side cohomology of `exQuadSingleStep3` is exactly three-dimensional.** -/
theorem finrank_V'3 :
    finrank ℚ ((selCx exQuadSingleStep3.X.SS.Dside).toCC.homology 1) = 3 :=
  finrank_sideS3

end Single3

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
