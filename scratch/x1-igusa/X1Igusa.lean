import ZInQKernel.Contrib.OneProof.R16IsJ1Dict
import ZInQKernel.Contrib.RLeaf.IgusaSL2
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange

/-! # x1-igusa (scratch): `X1PointsConjugate` from Igusa's theorem in its printed form -/

noncomputable section

namespace X1Igusa

open LeafModCurves WeierstrassCurve ZInQ.RLeaf X1Belyi

/-! ## 0. `X1PointsConjugate` is `IgusaTransitive` -/

theorem x1PointsConjugate_iff_igusaTransitive :
    R16IsJ1Dict.X1PointsConjugate ↔ ZInQ.RLeaf.IgusaTransitive := Iff.rfl

/-- From Igusa's theorem on the kernel's model `E_j = ofJNe0Or1728 j` (the former leaf H-117). -/
theorem x1PointsConjugate_of_igusaGL2 (h : IgusaGL2) : R16IsJ1Dict.X1PointsConjugate :=
  igusaTransitive_of_igusaGL2 h

/-! ## 1. Igusa's theorem for any model over `ℚ(j)` and the transitivity it gives -/

/-- Igusa's theorem (Galois image `GL₂(ℤ/N)` on `W'[N]`, every basis) for a Weierstrass curve `W'` over `ℚ(j)`. -/
def IgusaGL2For (W' : WeierstrassCurve Qj) : Prop :=
  ∀ N : ℕ, 0 < N → ∀ (e : (ZMod N × ZMod N) ≃+ nTors (W'.baseChange Kbar) N)
    (g : GL (Fin 2) (ZMod N)), ∃ σ : Kbar ≃ₐ[Qj] Kbar,
      ∀ v : ZMod N × ZMod N,
        Affine.Point.map (W' := W') σ.toAlgHom (e v : (W'.baseChange Kbar).toAffine.Point) =
          (e (matAct (g : Matrix (Fin 2) (Fin 2) (ZMod N)) v) : (W'.baseChange Kbar).toAffine.Point)

theorem igusaGL2_iff_for : IgusaGL2 ↔ IgusaGL2For Ej := Iff.rfl

theorem xCoord_map_for (W' : WeierstrassCurve Qj) (σ : Kbar ≃ₐ[Qj] Kbar)
    (P : (W'.baseChange Kbar).toAffine.Point) :
    xCoord (Affine.Point.map (W' := W') σ.toAlgHom P) = σ (xCoord P) := by
  cases P with
  | zero => exact (map_zero σ).symm
  | some h => rfl

/-- **Transitivity on `x`-coordinates from Igusa's theorem, for any elliptic model over `ℚ(j)`.** The basis
comes from leaf T36 (proved: `t36_torsionStructure`), transitivity from `exists_SL2_first_column`. -/
theorem xTransitive_of_igusaGL2For (W' : WeierstrassCurve Qj) [W'.IsElliptic] (h : IgusaGL2For W')
    (N : ℕ) (Q Q' : (W'.baseChange Kbar).toAffine.Point) (hN : 0 < N) (hQ : addOrderOf Q = N)
    (hQ' : addOrderOf Q' = N) : ∃ σ : Kbar ≃ₐ[Qj] Kbar, σ (xCoord Q) = xCoord Q' := by
  obtain ⟨e⟩ := t36_torsionStructure Kbar (W'.baseChange Kbar) N hN
  have hmem : ∀ {R : (W'.baseChange Kbar).toAffine.Point}, addOrderOf R = N → R ∈ nTors (W'.baseChange Kbar) N :=
    fun {R} hR => by show N • R = 0; rw [← hR]; exact addOrderOf_nsmul_eq_zero R
  have hord : ∀ {R : (W'.baseChange Kbar).toAffine.Point} (hR : addOrderOf R = N),
      addOrderOf (e ⟨R, hmem hR⟩) = N := fun {R} hR => by
    rw [AddEquiv.addOrderOf_eq, AddSubgroup.addOrderOf_mk, hR]
  obtain ⟨g, hg⟩ := exists_SL2_first_column hN _ (hord hQ)
  obtain ⟨g', hg'⟩ := exists_SL2_first_column hN _ (hord hQ')
  obtain ⟨σ, hσ⟩ := h N hN e.symm (Matrix.SpecialLinearGroup.toGL g)
  obtain ⟨σ', hσ'⟩ := h N hN e.symm (Matrix.SpecialLinearGroup.toGL g')
  have h1 := congrArg xCoord (hσ ((1 : ZMod N), (0 : ZMod N)))
  have h2 := congrArg xCoord (hσ' ((1 : ZMod N), (0 : ZMod N)))
  rw [xCoord_map_for] at h1 h2
  have e1 : matAct ((Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))
      ((1 : ZMod N), (0 : ZMod N)) = e ⟨Q, hmem hQ⟩ := hg
  have e2 : matAct ((Matrix.SpecialLinearGroup.toGL g' : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))
      ((1 : ZMod N), (0 : ZMod N)) = e ⟨Q', hmem hQ'⟩ := hg'
  rw [e1, AddEquiv.symm_apply_apply] at h1
  rw [e2, AddEquiv.symm_apply_apply] at h2
  refine ⟨σ.symm.trans σ', ?_⟩
  rw [AlgEquiv.trans_apply, ← h1, AlgEquiv.symm_apply_apply, h2]

/-! ## 2. Diamond–Shurman's model `E_j : y² = 4x³ − g x − g`, `g = 27j/(j − 1728)` -/

/-- `g_j = 27 j / (j − 1728)` (Diamond–Shurman §7.5). -/
def gDS : Qj := 27 * RatFunc.X / (RatFunc.X - 1728)

/-- Diamond–Shurman's `E_j : y² = 4x³ − g_j x − g_j` over `ℚ(j)`, written in Mathlib's normalized Weierstrass form
by `y = 2y'`: `y'² = x³ − (g_j/4) x − g_j/4`. The two plane cubics are isomorphic over `ℚ(j)` by `(x, y) ↦ (x, y/2)`,
which fixes the point at infinity and the `x`-coordinate, so it is an isomorphism of groups commuting with Galois. -/
def EDS : WeierstrassCurve Qj := ⟨0, 0, 0, -(gDS / 4), -(gDS / 4)⟩

/-- `E_j` (Diamond–Shurman's model) over `\overline{ℚ(j)}`. -/
abbrev EDSBar : WeierstrassCurve Kbar := EDS.baseChange Kbar

theorem X_ne_zero' : (RatFunc.X : Qj) ≠ 0 := RatFunc.X_ne_zero

theorem gDS_sub : gDS - 27 = 27 * 1728 / (RatFunc.X - 1728) := by
  have := X_sub_1728_ne_zero
  unfold gDS
  field_simp
  ring

theorem EDS_Δ : EDS.Δ = gDS ^ 2 * (gDS - 27) := by
  simp only [EDS, Δ, b₂, b₄, b₆, b₈]
  ring

instance : EDS.IsElliptic := by
  rw [isElliptic_iff, EDS_Δ, gDS_sub]
  have h1 := X_sub_1728_ne_zero
  have h0 : gDS ≠ 0 := by
    unfold gDS
    exact div_ne_zero (mul_ne_zero (by norm_num) X_ne_zero') h1
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 h0) (div_ne_zero (by norm_num) h1))

/-- `j(E_j) = j` for Diamond–Shurman's model. -/
theorem EDS_j : EDS.j = RatFunc.X := by
  have h1 := X_sub_1728_ne_zero
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, coe_Δ', EDS_Δ]
  simp only [EDS, c₄, b₂, b₄]
  have h0 : gDS ≠ 0 := by
    unfold gDS
    exact div_ne_zero (mul_ne_zero (by norm_num) X_ne_zero') h1
  have h2 : gDS - 27 ≠ 0 := by
    rw [gDS_sub]; exact div_ne_zero (by norm_num) h1
  field_simp
  unfold gDS
  field_simp
  ring

/-! ## 3. The leaf: Igusa's theorem as printed (Diamond–Shurman's model) -/

/-- The Galois action on the points of Diamond–Shurman's `E_j` over `\overline{ℚ(j)}`. -/
abbrev galPtDS (σ : Kbar ≃ₐ[Qj] Kbar) : EDSBar.toAffine.Point →+ EDSBar.toAffine.Point :=
  Affine.Point.map (W' := EDS) σ.toAlgHom

/-- **LEAF (Igusa's theorem, printed form).** ... -/
def IgusaGL2DS : Prop :=
  ∀ N : ℕ, 0 < N → ∀ (e : (ZMod N × ZMod N) ≃+ nTors EDSBar N) (g : GL (Fin 2) (ZMod N)),
    ∃ σ : Kbar ≃ₐ[Qj] Kbar, ∀ v : ZMod N × ZMod N,
      galPtDS σ (e v : EDSBar.toAffine.Point) =
        (e (matAct (g : Matrix (Fin 2) (Fin 2) (ZMod N)) v) : EDSBar.toAffine.Point)

theorem igusaGL2DS_iff_for : IgusaGL2DS ↔ IgusaGL2For EDS := Iff.rfl

/-! ## 4. The change of variables `E_j(DS) ≅ E_j(kernel)` over `\overline{ℚ(j)}` -/

/-- A change of variables `C • W₂ = W₁` gives a group isomorphism `W₁(F) ≃ W₂(F)` with `x ↦ u²x + r`. -/
theorem exists_addEquiv_xCoord {F : Type*} [Field F] [DecidableEq F] (W₁ W₂ : WeierstrassCurve F)
    (C : VariableChange F) (h : C • W₂ = W₁) :
    ∃ e : W₁.toAffine.Point ≃+ W₂.toAffine.Point,
      ∀ P : W₁.toAffine.Point, P ≠ 0 → xCoord (e P) = (C.u : F) ^ 2 * xCoord P + C.r := by
  subst h
  refine ⟨Affine.Point.addEquivVariableChange W₂ C, ?_⟩
  rintro (_ | ⟨x, y, hxy⟩) hP
  · exact absurd rfl hP
  · rw [Affine.Point.coe_addEquivVariableChange, Affine.Point.equivVariableChange_some]
    rfl

/-- `j − 1728` in `\overline{ℚ(j)}`. -/
abbrev mb : Kbar := algebraMap Qj Kbar (RatFunc.X - 1728)

theorem mb_ne_zero : mb ≠ 0 := by
  rw [mb, ne_eq, map_eq_zero_iff _ (algebraMap Qj Kbar).injective]
  exact X_sub_1728_ne_zero

/-- The scale `u² = −18/(j − 1728)²`, an element of `ℚ(j)`. -/
def alpha : Qj := -18 / (RatFunc.X - 1728) ^ 2

theorem alpha_ne_zero : alpha ≠ 0 :=
  div_ne_zero (by norm_num) (pow_ne_zero 2 X_sub_1728_ne_zero)

theorem exists_u : ∃ u : Kbar, u ^ 2 = algebraMap Qj Kbar alpha :=
  IsAlgClosed.exists_pow_nat_eq _ (by norm_num)

/-- The change of variables `(u, r, s, t) = (u, −3/2, (j − 1728)u/2, 0)`. -/
def cDS (u : Kbar) (hu : u ≠ 0) : VariableChange Kbar :=
  ⟨Units.mk0 u hu, algebraMap Qj Kbar (-3 / 2), mb * u / 2, 0⟩

theorem cDS_smul (u : Kbar) (hu2 : u ^ 2 = algebraMap Qj Kbar alpha) (hu : u ≠ 0) :
    cDS u hu • EDSBar = EjBar := by
  have hm := mb_ne_zero
  have hα : algebraMap Qj Kbar alpha = -18 / mb ^ 2 := by
    simp only [alpha, mb, map_div₀, map_neg, map_pow, map_ofNat]
  rw [hα] at hu2
  have hu2' : u ^ 2 * mb ^ 2 = -18 := by rw [hu2]; field_simp
  have hg : algebraMap Qj Kbar gDS = 27 * (mb + 1728) / mb := by
    simp only [gDS, mb, map_div₀, map_mul, map_sub, map_ofNat]
    ring
  have hr : algebraMap Qj Kbar (-3 / 2) = -3 / 2 := by
    simp only [map_div₀, map_neg, map_ofNat]
  have hEj : EjBar = ⟨mb, 0, 0, -36 * mb ^ 3, -mb ^ 5⟩ := by
    simp only [EjBar, Ej, ofJNe0Or1728, baseChange, map, mb, map_zero, map_mul, map_neg, map_pow,
      map_sub, map_ofNat]
  rw [hEj]
  ext <;> simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, cDS, EDSBar, EDS, baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
    Units.val_inv_eq_inv_val, Units.val_mk0, map_zero, map_neg, map_div₀, hg, hr, map_ofNat]
  all_goals field_simp
  · ring
  · linear_combination (-1 : Kbar) * hu2'
  · ring
  · linear_combination 576 * (u ^ 2 * mb ^ 2 - 18) * hu2'
  · linear_combination 32 * ((u ^ 2 * mb ^ 2) ^ 2 - 18 * (u ^ 2 * mb ^ 2) + 324) * hu2'

/-! ## 5. `X1PointsConjugate` from the printed leaf -/

/-- **`X1PointsConjugate` from Igusa's theorem as printed (Diamond–Shurman's model).** Points of exact order `N`
of the kernel's `E_j` go to points of exact order `N` of Diamond–Shurman's `E_j` under the change of variables
`cDS` over `\overline{ℚ(j)}`, which acts on `x`-coordinates by `x ↦ αx − 3/2` with `α ∈ ℚ(j)^×`; Igusa's theorem
on Diamond–Shurman's model gives `σ` matching the images, and `σ` fixes `α` and `−3/2`. -/
theorem x1PointsConjugate_of_igusaGL2DS (h : IgusaGL2DS) : R16IsJ1Dict.X1PointsConjugate := by
  intro N P P' hN hP hP'
  obtain ⟨u, hu2⟩ := exists_u
  have hu : u ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, map_eq_zero_iff _ (algebraMap Qj Kbar).injective] at hu2
    exact alpha_ne_zero hu2
  obtain ⟨ψ, hψ⟩ := exists_addEquiv_xCoord EjBar EDSBar (cDS u hu) (cDS_smul u hu2 hu)
  by_cases h0 : P = 0
  · have hN1 : N = 1 := by rw [← hP, h0, addOrderOf_zero]
    have h0' : P' = 0 := by rw [← AddMonoid.addOrderOf_eq_one_iff, hP', hN1]
    exact ⟨AlgEquiv.refl, by rw [h0, h0']; rfl⟩
  have h0' : P' ≠ 0 := by
    intro h0'
    apply h0
    rw [← AddMonoid.addOrderOf_eq_one_iff, hP, ← hP', h0', addOrderOf_zero]
  obtain ⟨σ, hσ⟩ := xTransitive_of_igusaGL2For EDS h N (ψ P) (ψ P') hN
    (by rw [AddEquiv.addOrderOf_eq, hP]) (by rw [AddEquiv.addOrderOf_eq, hP'])
  rw [hψ P h0, hψ P' h0'] at hσ
  refine ⟨σ, ?_⟩
  have hc : ((cDS u hu).u : Kbar) ^ 2 = algebraMap Qj Kbar alpha := hu2
  have hr : (cDS u hu).r = algebraMap Qj Kbar (-3 / 2) := rfl
  rw [hc, hr, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes] at hσ
  have hα : algebraMap Qj Kbar alpha ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap Qj Kbar).injective]; exact alpha_ne_zero
  exact mul_left_cancel₀ hα (add_right_cancel hσ)


#print axioms X1Igusa.x1PointsConjugate_of_igusaGL2
#print axioms X1Igusa.xTransitive_of_igusaGL2For
#print axioms X1Igusa.EDS_j
#print axioms X1Igusa.cDS_smul
#print axioms X1Igusa.x1PointsConjugate_of_igusaGL2DS

end X1Igusa
