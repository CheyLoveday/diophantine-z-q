import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilJacobi
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.HeegnerCd
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_isUniformization_toPoint
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_discriminant_ne_zero

/-!
# heegner-32: the points of the parametrization of `C_d` as twisted sums of points of `X₀(32)`

For `d ≡ 5 (mod 8)` squarefree, `g = gaussD d` (`g² = d`), `L` a period lattice of `C_d : y² = x³ − d²x` and
`τ ∈ ℍ`:

`weierPt C_d L (2 Φ_d(τ)) = S_{λg}(Z(τ)) + S_{λ̄g}(Z(τ))`,  `Z(τ) = Σ_{a mod d} (a/d) · (x(τ + a/d), y(τ + a/d))`,

where `(x, y)` is x0-32's eta-quotient parametrization `X0.phiC` of `X₀(32) = 32a1 : y² = x³ + 4x`,
`λ = (1 + i)/2`, and `S_μ(x, y) = (μ²x, μ³y)` maps `32a1` to `C_d` when `4μ⁴ = −d²`.
-/

noncomputable section

open UpperHalfPlane Complex WeierstrassCurve Filter Topology
open scoped WeierstrassCurve.Affine

namespace ZInQ.Heegner32

open ZInQ.GZWeil (eichlerCd gaussD scalePP mem_scalePP g₂_scalePP g₃_scalePP isPeriodLattice_cd_iff)
open ZInQ.GZTheta (jacobiChar)
open ZInQ.Contrib.TYZGenus (X0.xC X0.yC X0.fC X0.phiC X0.curveAC)
open ZInQ.Contrib.TYZDecomp.CurveA (curveA)

/-! ## §1. Additivity of `weierPt` for short Weierstrass curves (from the uniformization theorem) -/

theorem fun_add_of_eq (L : PeriodPair) {W : WeierstrassCurve ℂ} (h : L.weierstrassCurve = W)
    (F : ℂ → W.toAffine.Point) (hF0 : ∀ z ∈ L.lattice, F z = 0)
    (hF1 : ∀ z ∉ L.lattice, ∃ hns, F z = .some (L.weierstrassP z) (L.derivWeierstrassP z / 2) hns)
    (z w : ℂ) : F (z + w) = F z + F w := by
  subst h
  have hD := L.discriminant_ne_zero
  have hF : F = L.toPoint hD := by
    funext u
    by_cases hu : u ∈ L.lattice
    · rw [hF0 u hu, L.toPoint_of_mem hD hu]
    · obtain ⟨hns, e⟩ := hF1 u hu
      rw [e, L.toPoint_of_notMem hD hu]
  rw [hF]
  exact (L.isUniformization_toPoint hD).1 z w

theorem short_b₂ (A : ℚ) : ((shortCurve A)⁄ℂ).b₂ = 0 := by
  simp [WeierstrassCurve.b₂, shortCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map]

theorem short_a₁ (A : ℚ) : ((shortCurve A)⁄ℂ).a₁ = 0 := by
  simp [shortCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map]

theorem short_a₃ (A : ℚ) : ((shortCurve A)⁄ℂ).a₃ = 0 := by
  simp [shortCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map]

/-- For a period lattice of `y² = x³ + Ax`, the curve of `L` is `E⁄ℂ`. -/
theorem weierstrassCurve_eq_short {A : ℚ} {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve A) L) : L.weierstrassCurve = (shortCurve A)⁄ℂ := by
  obtain ⟨h2, h3⟩ := hL
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.baseChange, WeierstrassCurve.map, shortCurve] at h2 h3
  push_cast at h2 h3
  ext <;> simp [PeriodPair.weierstrassCurve, shortCurve, WeierstrassCurve.baseChange,
    WeierstrassCurve.map, h2, h3] <;> ring

/-- **`weierPt E L` is additive** for `E : y² = x³ + Ax` (the uniformization theorem, vendored). -/
theorem weierPt_short_add {A : ℚ} [(shortCurve A).IsElliptic] {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve A) L) (z w : ℂ) :
    ZInQ.GZHL3.weierPt (shortCurve A) L (z + w) =
      ZInQ.GZHL3.weierPt (shortCurve A) L z + ZInQ.GZHL3.weierPt (shortCurve A) L w := by
  refine fun_add_of_eq L (weierstrassCurve_eq_short hL) _ (fun u hu => ?_) (fun u hu => ?_) z w
  · exact ZInQ.GZHeegner.weierPt_eq_zero _ L hu
  · rw [ZInQ.GZHeegner.weierPt_eq_some _ hL hu]
    have hx : L.weierstrassP u - ((shortCurve A)⁄ℂ).b₂ / 12 = L.weierstrassP u := by
      rw [short_b₂]; ring
    have hy : (L.derivWeierstrassP u - ((shortCurve A)⁄ℂ).a₁ *
        (L.weierstrassP u - ((shortCurve A)⁄ℂ).b₂ / 12) - ((shortCurve A)⁄ℂ).a₃) / 2 =
        L.derivWeierstrassP u / 2 := by
      rw [short_a₁, short_a₃]; ring
    have hns := ZInQ.GZHL3.weierPt_some (shortCurve A) hL hu
    rw [hx, hy] at hns
    exact ⟨hns, by simp only [Affine.Point.some.injEq]; exact ⟨hx, hy⟩⟩

/-- `weierPt E L` as an additive map. -/
def weierHom {A : ℚ} [(shortCurve A).IsElliptic] {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve A) L) : ℂ →+ ((shortCurve A)⁄ℂ).toAffine.Point :=
  AddMonoidHom.mk' (ZInQ.GZHL3.weierPt (shortCurve A) L) (weierPt_short_add hL)

theorem weierHom_apply {A : ℚ} [(shortCurve A).IsElliptic] {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve A) L) (z : ℂ) :
    weierHom hL z = ZInQ.GZHL3.weierPt (shortCurve A) L z := rfl

/-! ## §2. Scaling of lattices and the maps `S_μ` -/

theorem isScale_scalePP (L : PeriodPair) {μ : ℂ} (hμ : μ ≠ 0) : T5Glue.IsScale (scalePP L μ hμ) L μ := by
  refine ⟨hμ, ?_⟩
  ext x
  simp only [SetLike.mem_coe, Set.mem_smul_set, smul_eq_mul]
  rw [mem_scalePP]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩

instance (d : ℕ) [NeZero d] : (shortCurve (-(d : ℚ) ^ 2)).IsElliptic :=
  ZInQ.GZDecomp.shortCurve_cd_isElliptic (NeZero.ne d)

instance : (shortCurve (4 : ℚ)).IsElliptic := shortCurve_isElliptic (by norm_num)

/-- `S_μ(x, y) = (μ²x, μ³y)` from `32a1 : y² = x³ + 4x` to `C_d : y² = x³ − d²x`, for `4μ⁴ = −d²`. -/
def sMap (d : ℕ) [NeZero d] (μ : ℂ) (hμ : 4 * μ ^ 4 = -(d : ℂ) ^ 2) :
    ((shortCurve (4 : ℚ))⁄ℂ).toAffine.Point → ((shortCurve (-(d : ℚ) ^ 2))⁄ℂ).toAffine.Point
  | .zero => 0
  | .some x y h => .some (μ ^ 2 * x) (μ ^ 3 * y) (by
      rw [← Affine.equation_iff_nonsingular]
      have he := (Affine.equation_iff_nonsingular.mpr h)
      rw [Affine.equation_iff] at he ⊢
      simp only [shortCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero, zero_mul,
        add_zero, mul_zero, zero_add] at he ⊢
      push_cast at he ⊢
      linear_combination μ ^ 6 * he + μ ^ 2 * x * hμ)

instance : curveA.IsElliptic := by unfold curveA; exact shortCurve_isElliptic (by norm_num)

theorem sMap_zero (d : ℕ) [NeZero d] (μ : ℂ) (hμ : 4 * μ ^ 4 = -(d : ℂ) ^ 2) : sMap d μ hμ 0 = 0 := rfl

theorem isPeriodLattice_scale {d : ℕ} [NeZero d] {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L) {μ : ℂ} (hμ0 : μ ≠ 0)
    (hμ : 4 * μ ^ 4 = -(d : ℂ) ^ 2) :
    ZInQ.GZHL3.IsPeriodLattice curveA (scalePP L μ hμ0) := by
  obtain ⟨h2, h3⟩ := (isPeriodLattice_cd_iff d L).1 hL
  have hd2 : (d : ℂ) ^ 2 = -4 * μ ^ 4 := by linear_combination -hμ
  have hμ4 : μ ^ 4 ≠ 0 := pow_ne_zero 4 hμ0
  refine ⟨?_, ?_⟩
  · rw [g₂_scalePP, h2, hd2]
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, curveA, shortCurve,
      WeierstrassCurve.baseChange, WeierstrassCurve.map]
    push_cast
    field_simp
    ring
  · rw [g₃_scalePP, h3]
    simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      curveA, shortCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map]
    push_cast
    ring

/-- **Scaling.** `weierPt C_d L z = S_μ(weierPt 32a1 (μL) (μz))`. -/
theorem weierPt_scale {d : ℕ} [NeZero d] {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L) {μ : ℂ} (hμ0 : μ ≠ 0)
    (hμ : 4 * μ ^ 4 = -(d : ℂ) ^ 2) (z : ℂ) :
    ZInQ.GZHL3.weierPt (shortCurve (-(d : ℚ) ^ 2)) L z =
      sMap d μ hμ (ZInQ.GZHL3.weierPt curveA (scalePP L μ hμ0) (μ * z)) := by
  have hs := isScale_scalePP L hμ0
  have hL' := isPeriodLattice_scale hL hμ0 hμ
  by_cases hz : z ∈ L.lattice
  · have hz' : μ * z ∈ (scalePP L μ hμ0).lattice := hs.mul_mem hz
    rw [ZInQ.GZHeegner.weierPt_eq_zero _ L hz, ZInQ.GZHeegner.weierPt_eq_zero _ _ hz', sMap_zero]
  · have hz' : μ * z ∉ (scalePP L μ hμ0).lattice := by
      rw [hs.mem_iff, inv_mul_cancel_left₀ hμ0]; exact hz
    rw [ZInQ.GZHeegner.weierPt_eq_some _ hL hz, ZInQ.GZHeegner.weierPt_eq_some _ hL' hz']
    simp only [sMap, Affine.Point.some.injEq]
    have hw := hs.weierstrassP z
    have hw' := hs.derivWeierstrassP z
    have e1 : ((shortCurve (-(d : ℚ) ^ 2))⁄ℂ).b₂ = 0 := short_b₂ _
    have e2 : ((shortCurve (-(d : ℚ) ^ 2))⁄ℂ).a₁ = 0 := short_a₁ _
    have e3 : ((shortCurve (-(d : ℚ) ^ 2))⁄ℂ).a₃ = 0 := short_a₃ _
    have f1 : (curveA⁄ℂ).b₂ = 0 := short_b₂ 4
    have f2 : (curveA⁄ℂ).a₁ = 0 := short_a₁ 4
    have f3 : (curveA⁄ℂ).a₃ = 0 := short_a₃ 4
    rw [e1, e2, e3, f1, f2, f3, hw, hw']
    constructor <;> field_simp

/-! ## §3. `x0-32`'s parametrization is `℘` of a lattice of `32a1` at `Φ₁ + c₀` -/

/-- For a period lattice `L` of `32a1`, `(x(σ), y(σ)) = weierPt 32a1 L (Φ₁(σ) + c₀)` on `ℍ`. -/
theorem exists_c0 {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice curveA L) :
    ∃ c₀ : ℂ, ∀ σ : ℍ, ZInQ.GZHL3.weierPt curveA L (eichlerCd 1 σ + c₀) = X0.phiC σ := by
  have hg2 : L.g₂ = -16 := by
    rw [hL.1]
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, curveA, shortCurve,
      WeierstrassCurve.baseChange, WeierstrassCurve.map]
    push_cast; ring
  have hg3 : L.g₃ = 0 := by
    rw [hL.2]
    simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      curveA, shortCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map]
    push_cast; ring
  set τ0 : ℍ := UpperHalfPlane.I
  obtain ⟨z1, hz1, hx1⟩ := ZInQ.GZWeil.weierstrassP_surjective L (X0.xC τ0)
  have hrel := ZInQ.GZWeil.relation_A L hg2 hg3 hz1
  have heqτ := ZInQ.Contrib.TYZGenus.Shimura.etaModelEquation τ0
  obtain ⟨z0, hz0, hx, hy⟩ : ∃ z0, z0 ∉ L.lattice ∧ L.weierstrassP z0 = X0.xC τ0 ∧
      L.derivWeierstrassP z0 = 2 * X0.yC τ0 := by
    have hsq : (L.derivWeierstrassP z1 - 2 * X0.yC τ0) * (L.derivWeierstrassP z1 + 2 * X0.yC τ0) = 0 := by
      rw [hx1] at hrel
      linear_combination hrel - 4 * heqτ
    rcases mul_eq_zero.mp hsq with h | h
    · exact ⟨z1, hz1, hx1, by linear_combination h⟩
    · refine ⟨-z1, fun h' => hz1 (by simpa using neg_mem h'), by rw [L.weierstrassP_neg, hx1], ?_⟩
      rw [L.derivWeierstrassP_neg]; linear_combination -h
  set c0 := z0 - eichlerCd 1 τ0 with hc0
  refine ⟨c0, fun σ => ?_⟩
  have hD := ZInQ.GZWeil.etaModelDifferential
  have hG := fun {s : ℂ} (hs : 0 < s.im) => ZInQ.GZWeil.global_eq L hg2 hg3 hD τ0 hz0 hx hy hs
  obtain ⟨hnot, hxeq⟩ := hG σ.im_pos
  -- `℘'(Φ₁(σ) + c₀) = 2 y(σ)`, by differentiating `℘(Φ₁ + c₀) = x` near `σ`
  have hcomp : HasDerivAt (fun s => L.weierstrassP (eichlerCd 1 s + c0))
      (L.derivWeierstrassP (eichlerCd 1 σ + c0) * (2 * Real.pi * Complex.I * X0.fC σ)) σ :=
    (ZInQ.GZWeil.hasDerivAt_wp L hnot).comp (σ : ℂ)
      ((ZInQ.GZWeil.hasDerivAt_eichlerCd_one σ.im_pos).add_const c0)
  have hev : X0.xC =ᶠ[𝓝 (σ : ℂ)] fun s => L.weierstrassP (eichlerCd 1 s + c0) := by
    filter_upwards [ZInQ.GZWeil.U_open.mem_nhds σ.im_pos] with s hs
    exact (hG hs).2.symm
  have hxd := hcomp.congr_of_eventuallyEq hev
  have huniq := hxd.unique (hD σ)
  have hf : (2 * Real.pi * Complex.I * X0.fC σ : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero) (X0.fC_ne_zero σ)
    exact_mod_cast Real.pi_ne_zero
  have hyeq : L.derivWeierstrassP (eichlerCd 1 σ + c0) = 2 * X0.yC σ := by
    apply mul_right_cancel₀ hf
    linear_combination huniq
  rw [ZInQ.GZHeegner.weierPt_eq_some _ hL hnot]
  have hns : curveAC.toAffine.Nonsingular (X0.xC σ) (X0.yC σ) := by
    have h := ZInQ.GZHL3.weierPt_some curveA hL hnot
    have e1 : (curveA⁄ℂ).b₂ = 0 := short_b₂ 4
    have e2 : (curveA⁄ℂ).a₁ = 0 := short_a₁ 4
    have e3 : (curveA⁄ℂ).a₃ = 0 := short_a₃ 4
    rw [e1, e2, e3, hxeq, hyeq] at h
    convert h using 1 <;> ring
  unfold X0.phiC
  rw [dif_pos hns]
  simp only [Affine.Point.some.injEq]
  have e1 : (curveA⁄ℂ).b₂ = 0 := short_b₂ 4
  have e2 : (curveA⁄ℂ).a₁ = 0 := short_a₁ 4
  have e3 : (curveA⁄ℂ).a₃ = 0 := short_a₃ 4
  rw [e1, e2, e3, hxeq, hyeq]
  constructor <;> ring

/-! ## §4. The twisted sum `Z(τ)` and the main identity -/

/-- `τ + a/d ∈ ℍ`. -/
def shiftH (d : ℕ) [NeZero d] (τ : ℍ) (a : ZMod d) : ℍ :=
  ⟨(τ : ℂ) + (a.val : ℂ) / d, by
    have : ((a.val : ℂ) / d).im = 0 := by
      rw [show ((a.val : ℂ) / d) = (((a.val : ℝ) / d : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_im _
    rw [Complex.add_im, this, add_zero]; exact τ.im_pos⟩

theorem coe_shiftH (d : ℕ) [NeZero d] (τ : ℍ) (a : ZMod d) :
    ((shiftH d τ a : ℍ) : ℂ) = (τ : ℂ) + (a.val : ℂ) / d := rfl

/-- **The twisted sum** `Z(τ) = Σ_{a mod d} (a/d) · (x(τ + a/d), y(τ + a/d)) ∈ 32a1(ℂ)`. -/
def zTw (d : ℕ) [NeZero d] (τ : ℍ) : X0.PtAC :=
  ∑ a : ZMod d, (jacobiSym (a.val : ℤ) d) • X0.phiC (shiftH d τ a)

theorem jacobiChar_apply (d : ℕ) [NeZero d] (a : ZMod d) :
    jacobiChar d a = ((jacobiSym (a.val : ℤ) d : ℤ) : ℂ) := rfl

theorem jacobiChar_ne_one {d : ℕ} [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) (hd1 : d ≠ 1) :
    jacobiChar d ≠ 1 := by
  intro h
  have hp := ZInQ.GZWeil.jacobiChar_isPrimitive (d := d) (Nat.odd_iff.mpr (by omega)) hsq
  rw [h] at hp
  have := hp
  unfold DirichletCharacter.IsPrimitive at this
  rw [DirichletCharacter.conductor_one (NeZero.ne d)] at this
  exact hd1 this.symm

theorem sum_jacobiChar {d : ℕ} [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) (hd1 : d ≠ 1) :
    ∑ a : ZMod d, jacobiChar d a = 0 :=
  MulChar.sum_eq_zero_of_ne_one (jacobiChar_ne_one hd4 hsq hd1)

/-- `Σ_a (a/d) Φ₁(τ + a/d) = g Φ_d(τ)` (gz-weil's twist formula and Gauss sum). -/
theorem sum_char_eichler {d : ℕ} [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) (τ : ℍ) :
    ∑ a : ZMod d, jacobiChar d a * eichlerCd 1 ((shiftH d τ a : ℍ) : ℂ) =
      gaussD d * eichlerCd d τ := by
  have hg := ZInQ.GZWeil.gaussD_ne_zero hd4 hsq
  have hT := ZInQ.GZWeil.twist_formula d τ.im_pos
  simp_rw [ZInQ.GZWeil.dft_jacobiChar hd4 hsq] at hT
  have hg2 := ZInQ.GZWeil.gaussD_sq hd4 hsq
  apply mul_left_cancel₀ hg
  rw [Finset.mul_sum]
  have : ∑ a : ZMod d, gaussD d * (jacobiChar d a * eichlerCd 1 ((shiftH d τ a : ℍ) : ℂ)) =
      ∑ a : ZMod d, jacobiChar d a * gaussD d * eichlerCd 1 ((τ : ℂ) + (a.val : ℂ) / d) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coe_shiftH]; ring
  rw [this, ← hT, ← hg2]; ring

/-- `weierPt 32a1 L' (Σ_a (a/d) Φ₁(τ + a/d)) = Z(τ)` for a period lattice `L'` of `32a1`. -/
theorem weierPt_sum_eq_zTw {d : ℕ} [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) (hd1 : d ≠ 1)
    {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice curveA L) (τ : ℍ) :
    ZInQ.GZHL3.weierPt curveA L
      (∑ a : ZMod d, jacobiChar d a * eichlerCd 1 ((shiftH d τ a : ℍ) : ℂ)) = zTw d τ := by
  obtain ⟨c0, hc0⟩ := exists_c0 hL
  have hsum : ∑ a : ZMod d, jacobiChar d a * eichlerCd 1 ((shiftH d τ a : ℍ) : ℂ) =
      ∑ a : ZMod d, (jacobiSym (a.val : ℤ) d) • (eichlerCd 1 ((shiftH d τ a : ℍ) : ℂ) + c0) := by
    have h0 : ∑ a : ZMod d, jacobiChar d a * c0 = 0 := by
      rw [← Finset.sum_mul, sum_jacobiChar hd4 hsq hd1, zero_mul]
    rw [← sub_zero (∑ a : ZMod d, jacobiChar d a * eichlerCd 1 ((shiftH d τ a : ℍ) : ℂ)), ← h0,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [zsmul_eq_mul, ← jacobiChar_apply]; ring
  rw [hsum]
  have := weierHom_apply (A := 4) hL
  show weierHom (A := 4) hL _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_zsmul, weierHom_apply]
  exact congrArg _ (hc0 (shiftH d τ a))

/-- `λ = (1 + i)/2`, `λ̄ = (1 − i)/2`. -/
def lam : ℂ := (1 + Complex.I) / 2
def lamb : ℂ := (1 - Complex.I) / 2

theorem lam_pow_four : lam ^ 4 = -1 / 4 := by
  unfold lam
  ring_nf; rw [show Complex.I ^ 4 = 1 by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul]; simp,
    Complex.I_sq, show Complex.I ^ 3 = -Complex.I by rw [pow_succ, Complex.I_sq]; ring]; ring

theorem lamb_pow_four : lamb ^ 4 = -1 / 4 := by
  unfold lamb
  ring_nf; rw [show Complex.I ^ 4 = 1 by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul]; simp,
    Complex.I_sq, show Complex.I ^ 3 = -Complex.I by rw [pow_succ, Complex.I_sq]; ring]; ring

theorem lam_mul_lamb : lam * lamb = 1 / 2 := by
  unfold lam lamb
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (-1 / 4 : ℂ) * hI

theorem lam_ne_zero : lam ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp [lam] at this

theorem lamb_ne_zero : lamb ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp [lamb] at this

theorem mu_pow {d : ℕ} [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) {l : ℂ}
    (hl : l ^ 4 = -1 / 4) : 4 * (l * gaussD d) ^ 4 = -(d : ℂ) ^ 2 := by
  have hg2 := ZInQ.GZWeil.gaussD_sq hd4 hsq
  rw [mul_pow, hl, show gaussD d ^ 4 = (gaussD d ^ 2) ^ 2 by ring, hg2]; ring

/-- **The parametrization of `C_d` at `2Φ_d(τ)` as a twisted sum on `X₀(32)`.** -/
theorem weierPt_two_eichlerCd {d : ℕ} [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) (hd1 : d ≠ 1)
    {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L) (τ : ℍ) :
    ZInQ.GZHL3.weierPt (shortCurve (-(d : ℚ) ^ 2)) L (2 * eichlerCd d τ) =
      sMap d (lam * gaussD d) (mu_pow hd4 hsq lam_pow_four) (zTw d τ) +
        sMap d (lamb * gaussD d) (mu_pow hd4 hsq lamb_pow_four) (zTw d τ) := by
  have hg := ZInQ.GZWeil.gaussD_ne_zero hd4 hsq
  set w := ∑ a : ZMod d, jacobiChar d a * eichlerCd 1 ((shiftH d τ a : ℍ) : ℂ) with hw
  have hwg : w = gaussD d * eichlerCd d τ := sum_char_eichler hd4 hsq τ
  have h1 : lam * gaussD d ≠ 0 := mul_ne_zero lam_ne_zero hg
  have h2 : lamb * gaussD d ≠ 0 := mul_ne_zero lamb_ne_zero hg
  have hsplit : 2 * eichlerCd d τ = 2 * lamb / gaussD d * w + 2 * lam / gaussD d * w := by
    rw [hwg]; field_simp
    have : lam + lamb = 1 := by unfold lam lamb; ring
    linear_combination (-(2 : ℂ) * gaussD d * eichlerCd d τ) * this
  rw [hsplit, weierPt_short_add hL,
    weierPt_scale hL h1 (mu_pow hd4 hsq lam_pow_four) (2 * lamb / gaussD d * w),
    weierPt_scale hL h2 (mu_pow hd4 hsq lamb_pow_four) (2 * lam / gaussD d * w)]
  have e1 : lam * gaussD d * (2 * lamb / gaussD d * w) = w := by
    field_simp; linear_combination (2 * w) * lam_mul_lamb
  have e2 : lamb * gaussD d * (2 * lam / gaussD d * w) = w := by
    field_simp; linear_combination (2 * w) * lam_mul_lamb
  rw [e1, e2, weierPt_sum_eq_zTw hd4 hsq hd1 (isPeriodLattice_scale hL h1 _),
    weierPt_sum_eq_zTw hd4 hsq hd1 (isPeriodLattice_scale hL h2 _)]

end ZInQ.Heegner32
