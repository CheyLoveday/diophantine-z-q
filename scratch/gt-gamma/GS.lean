import ZInQKernel.OneProof.H.TailZ3

set_option linter.ambiguousOpen false

noncomputable section

namespace HDec.GammaStarArea

open LeafQCheck LeafQCheck.QMglue PkgI1
open UpperHalfPlane (num denom denom_ne_zero)
open HSyn.G0Split.FibreQM.PeriodGlue (x4 x6)

local notation "p0" => HSyn.G0Split.FibreQM.PeriodMap.tau3


theorem p0_coe : ((p0 : UpperHalfPlane) : ℂ) = (√3 : ℂ) * Complex.I := rfl

theorem p0_im : (p0 : UpperHalfPlane).im = √3 := by
  show ((p0 : UpperHalfPlane) : ℂ).im = √3
  rw [p0_coe]; simp

theorem p0_re : (p0 : UpperHalfPlane).re = 0 := by
  show ((p0 : UpperHalfPlane) : ℂ).re = 0
  rw [p0_coe]; simp

/-- `F(z) = |z - p|² / Im z`, `p = i√3`; `cosh d(z, p) = 1 + F(z)/(2√3)`. -/
def Fp (z : UpperHalfPlane) : ℝ := Complex.normSq ((z : ℂ) - (p0 : ℂ)) / z.im

theorem sqrt3_pos : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)

theorem cosh_dist_p0 (z : UpperHalfPlane) : Real.cosh (dist z p0) = 1 + Fp z / (2 * √3) := by
  rw [UpperHalfPlane.cosh_dist, p0_im, Fp, Complex.dist_eq, Complex.sq_norm]
  have := z.im_pos
  have := sqrt3_pos
  field_simp

theorem dist_le_iff (z w : UpperHalfPlane) : dist z p0 ≤ dist w p0 ↔ Fp z ≤ Fp w := by
  have h := Real.cosh_le_cosh (x := dist z p0) (y := dist w p0)
  rw [abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg] at h
  rw [← h, cosh_dist_p0, cosh_dist_p0, add_le_add_iff_left]
  exact div_le_div_iff_of_pos_right (by have := sqrt3_pos; positivity)

theorem dist_eq_iff (z w : UpperHalfPlane) : dist z p0 = dist w p0 ↔ Fp z = Fp w := by
  constructor
  · intro h; exact le_antisymm ((dist_le_iff z w).1 h.le) ((dist_le_iff w z).1 h.ge)
  · intro h; exact le_antisymm ((dist_le_iff z w).2 h.le) ((dist_le_iff w z).2 h.ge)

/-! ## The action of `ι(y)` -/

/-- `P = 4a₁² + 12a₃²`, `R = a₀a₁ − 3a₂a₃`, `S = a₀a₃ + a₁a₂` for `y = a₀ + a₁i + a₂j + a₃k`. -/
def Pq (y : B) : ℝ := 4 * (y.imI : ℝ) ^ 2 + 12 * (y.imK : ℝ) ^ 2
def Rq (y : B) : ℝ := (y.re : ℝ) * y.imI - 3 * (y.imJ : ℝ) * y.imK
def Sq (y : B) : ℝ := (y.re : ℝ) * y.imK + (y.imI : ℝ) * y.imJ

/-- `U = |w|² − 3`, `X = 6 Re w`. -/
def Uq (w : UpperHalfPlane) : ℝ := Complex.normSq (w : ℂ) - 3
def Xq (w : UpperHalfPlane) : ℝ := 6 * w.re

/-- `Φ_y(w) = P(U + 6) + 2√2 (RU − SX)`: `F(ι(y) w) = F(w) + Φ_y(w)/(nrd(y) Im w)`. -/
def Phi (y : B) (w : UpperHalfPlane) : ℝ :=
  Pq y * (Uq w + 6) + 2 * √2 * (Rq y * Uq w - Sq y * Xq w)

theorem det_pos_of {g : GL (Fin 2) ℝ} {y : B} (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = iota y)
    (hn : 0 < nrd y) : 0 < g.det.val := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, hg, det_iota_eq]; exact_mod_cast hn

theorem Fp_smul {g : GL (Fin 2) ℝ} {y : B} (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = iota y)
    (hn : 0 < nrd y) (w : UpperHalfPlane) :
    Fp (g • w) = Fp w + Phi y w / ((nrd y : ℝ) * w.im) := by
  have hdet := det_pos_of hg hn
  have hdet' : g.det.val = (nrd y : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hg, det_iota_eq]
  have hD := denom_ne_zero g w
  have hDn : Complex.normSq (denom g w) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  have hc := UpperHalfPlane.coe_smul_of_det_pos hdet w
  have him := UpperHalfPlane.im_smul_eq_div_normSq g w
  rw [abs_of_pos hdet, hdet'] at him
  have hsub : ((g • w : UpperHalfPlane) : ℂ) - (p0 : ℂ) =
      (num g w - (p0 : ℂ) * denom g w) / denom g w := by
    rw [hc]; field_simp
  have hwim := w.im_pos
  have hnr : (0 : ℝ) < nrd y := by exact_mod_cast hn
  have key : Complex.normSq (num g w - (p0 : ℂ) * denom g w) =
      (nrd y : ℝ) * Complex.normSq ((w : ℂ) - (p0 : ℂ)) + Phi y w := by
    have e00 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = (y.re : ℝ) + y.imI * √2 := by
      rw [hg, iota_apply]; simp
    have e01 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = -3 * (y.imJ : ℝ) - 3 * √2 * y.imK := by
      rw [hg, iota_apply]; simp
    have e10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = (y.imJ : ℝ) - √2 * y.imK := by
      rw [hg, iota_apply]; simp
    have e11 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (y.re : ℝ) - y.imI * √2 := by
      rw [hg, iota_apply]; simp
    simp only [num, denom, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, p0_coe,
      Complex.I_re, Complex.I_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, e00, e01, e10, e11]
    simp only [Phi, Pq, Rq, Sq, Uq, Xq, Complex.normSq_apply, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im, nrd]
    push_cast
    have hs : √2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have ht : √3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    set s := √2
    set t := √3
    set x := w.re
    set yy := w.im
    set a0 := (y.re : ℝ)
    set a1 := (y.imI : ℝ)
    set a2 := (y.imJ : ℝ)
    set a3 := (y.imK : ℝ)
    linear_combination (9*a3^2 + a1^2*t^2 + 6*yy*a3^2*t + 2*yy*a1^2*t + yy^2*a3^2*t^2 + yy^2*a1^2 +
      (-6)*x*a1*a3 + 2*x*a1*a3*t^2 + x^2*a3^2*t^2 + x^2*a1^2) * hs +
      (6*a3^2 + (-3)*a2^2 + 4*a1^2 + (-2)*a0*a1*s + 2*yy^2*a3^2 + (-2)*yy^2*a2*a3*s + yy^2*a2^2 +
      4*x*a1*a3 + (-2)*x*a1*a2*s + (-2)*x*a0*a3*s + 2*x*a0*a2 + 2*x^2*a3^2 + (-2)*x^2*a2*a3*s +
      x^2*a2^2) * ht
  unfold Fp
  rw [hsub, Complex.normSq_div, key, him]
  field_simp


/-! ## Isometries -/

/-- A matrix of positive determinant acts on `ℍ` by an isometry. -/
theorem dist_smul_pos {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (z w : UpperHalfPlane) :
    dist (g • z) (g • w) = dist z w := by
  set c : ℝ := √(g.det.val) with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 hg
  have hcsq : c ^ 2 = g.det.val := Real.sq_sqrt hg.le
  let g' : Matrix.SpecialLinearGroup (Fin 2) ℝ := ⟨c⁻¹ • (g : Matrix (Fin 2) (Fin 2) ℝ), by
    rw [Matrix.det_smul, Fintype.card_fin, ← Matrix.GeneralLinearGroup.val_det_apply, ← hcsq]
    field_simp⟩
  have key : ∀ u : UpperHalfPlane, g' • u = g • u := by
    intro u
    have e : Matrix.SpecialLinearGroup.mapGL ℝ g' =
        Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c⁻¹ (inv_ne_zero hc0.ne')) * g := by
      ext i j
      rw [Units.val_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.GeneralLinearGroup.coe_scalar]
      simp [g', Matrix.scalar_apply, Matrix.diagonal_mul]
      rfl
    rw [MulAction.compHom_smul_def, e, mul_smul, UpperHalfPlane.glScalar_smul]
  rw [← key, ← key, dist_smul]

/-! ## `cosh d(p, ι(y) p) = 1 + P/nrd` -/

theorem Fp_p0 : Fp p0 = 0 := by simp [Fp]

theorem Uq_p0 : Uq p0 = 0 := by
  simp only [Uq, p0_coe, Complex.normSq_apply]; simp
theorem Xq_p0 : Xq p0 = 0 := by simp [Xq, p0_re]

theorem cosh_dist_smul_p0 {g : GL (Fin 2) ℝ} {y : B} (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = iota y)
    (hn : 0 < nrd y) : Real.cosh (dist (g • p0) p0) = 1 + Pq y / nrd y := by
  rw [cosh_dist_p0, Fp_smul hg hn, Fp_p0, Phi, Uq_p0, Xq_p0, p0_im]
  have := sqrt3_pos
  have hnr : (0 : ℝ) < nrd y := by exact_mod_cast hn
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  field_simp
  linear_combination (-2 : ℝ) * Pq y * h3

theorem Pq_nonneg (y : B) : 0 ≤ Pq y := by unfold Pq; positivity

/-! ## Elements of `Γ*` as `ι(y)` with `y ∈ 𝒪`, `nrd y ∈ {1, 2, 3, 6}` -/

theorem inO_rep (i : Fin 4) : InO (rep i) := by
  have h1 : InO (1 : B) := (inO_iff _).2 ⟨1, 0, 0, 0, by ext <;> norm_num⟩
  have h4 : InO x4 := (inO_iff _).2 ⟨0, 1, 2, 0, by ext <;> norm_num [x4]⟩
  have h6 : InO x6 := (inO_iff _).2 ⟨-2, 0, 1, 0, by
    ext <;> norm_num [x6]⟩
  fin_cases i
  · simpa [rep] using h1
  · simpa [rep] using h4
  · simpa [rep] using h6
  · simpa [rep] using inO_mul h4 h6

/-- The Möbius map of `γ ∈ Γ*` is that of `ι(y)`, `y ∈ 𝒪`, `nrd y ∈ {1, 2, 3, 6}` (from `cover_mob`). -/
theorem cover_y {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γs) :
    ∃ y : B, InO y ∧ (nrd y = 1 ∨ nrd y = 2 ∨ nrd y = 3 ∨ nrd y = 6) ∧
      ∃ g : GL (Fin 2) ℝ, (g : Matrix (Fin 2) (Fin 2) ℝ) = iota y ∧ ∀ z : UpperHalfPlane, γ • z = g • z := by
  obtain ⟨i, h, hh, hz⟩ := cover_mob hγ
  obtain ⟨u, hu, hhu, hnu⟩ := gamma1_iff.1 hh
  refine ⟨rep i * u, inO_mul (inO_rep i) hu, ?_, g4 i * h, ?_, fun z => by rw [hz, mul_smul]⟩
  · rw [nrd_mul, hnu, mul_one, nrd_rep]
    fin_cases i <;> simp
  · rw [Units.val_mul, g4_coe, hhu, iota_mul]

theorem nrd_pos_of {y : B} (h : nrd y = 1 ∨ nrd y = 2 ∨ nrd y = 3 ∨ nrd y = 6) : 0 < nrd y := by
  rcases h with h | h | h | h <;> rw [h] <;> norm_num

theorem nrd_le_six {y : B} (h : nrd y = 1 ∨ nrd y = 2 ∨ nrd y = 3 ∨ nrd y = 6) : nrd y ≤ 6 := by
  rcases h with h | h | h | h <;> rw [h] <;> norm_num

theorem isom {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γs) (z w : UpperHalfPlane) :
    dist (γ • z) (γ • w) = dist z w :=
  dist_smul_pos (by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact det_pos_of_mem hγ) z w

/-! ## Finiteness -/

/-- The Möbius map of `ι(y)` (identity if `nrd y = 0`). -/
def mobOf (y : B) : UpperHalfPlane → UpperHalfPlane :=
  fun z => (if h : nrd y ≠ 0 then glOf y h else 1) • z

theorem mobOf_eq {g : GL (Fin 2) ℝ} {y : B} (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = iota y)
    (hn : nrd y ≠ 0) : (fun z => g • z) = mobOf y := by
  have : g = glOf y hn := by ext1; rw [coe_glOf, hg]
  funext z; simp [mobOf, hn, this]

theorem abs_le_of_sq_le {A : ℤ} {G : ℝ} (h : (A : ℝ) ^ 2 ≤ G) : |A| ≤ ⌈G⌉ := by
  have h1 : (|A| : ℤ) ≤ A ^ 2 := by
    rcases eq_or_ne A 0 with h0 | h0
    · simp [h0]
    · have : 1 ≤ |A| := Int.one_le_abs h0
      calc |A| = |A| * 1 := by ring
        _ ≤ |A| * |A| := by gcongr
        _ = A ^ 2 := by rw [← abs_mul, abs_mul_self, sq]
  have h2 : ((|A| : ℤ) : ℝ) ≤ G := le_trans (by exact_mod_cast h1) h
  exact Int.cast_le.1 (le_trans h2 (Int.le_ceil G))

theorem finite_O (D : ℝ) : {y : B | InO y ∧ nrd y ≤ 6 ∧ Pq y ≤ D}.Finite := by
  set M : ℤ := ⌈4 * D + 24⌉
  let f : ℤ × ℤ × ℤ × ℤ → B := fun v =>
    ⟨(v.1 : ℚ) + (v.2.2.1 : ℚ) / 2, (v.2.1 : ℚ) + (v.2.2.2 : ℚ) / 2, (v.2.2.1 : ℚ) / 2,
      (v.2.2.2 : ℚ) / 2⟩
  refine ((((Set.finite_Icc (-M) M).prod ((Set.finite_Icc (-M) M).prod
    ((Set.finite_Icc (-M) M).prod (Set.finite_Icc (-M) M))))).image f).subset ?_
  rintro y ⟨hy, hn6, hP⟩
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff y).1 hy
  simp only [Pq] at hP
  simp only [nrd] at hn6
  have hn6' : ((n0 : ℝ) + n2 / 2) ^ 2 - 2 * ((n1 : ℝ) + n3 / 2) ^ 2 + 3 * ((n2 : ℝ) / 2) ^ 2 -
      6 * ((n3 : ℝ) / 2) ^ 2 ≤ 6 := by exact_mod_cast hn6
  push_cast at hP
  have b3 : ((n3 : ℤ) : ℝ) ^ 2 ≤ 4 * D + 24 := by nlinarith
  have b1 : ((2 * n1 + n3 : ℤ) : ℝ) ^ 2 ≤ 4 * D + 24 := by push_cast; nlinarith
  have b2 : ((n2 : ℤ) : ℝ) ^ 2 ≤ 4 * D + 24 := by nlinarith
  have b0 : ((2 * n0 + n2 : ℤ) : ℝ) ^ 2 ≤ 4 * D + 24 := by push_cast; nlinarith
  have a3 := abs_le_of_sq_le b3
  have a1 := abs_le_of_sq_le b1
  have a2 := abs_le_of_sq_le b2
  have a0 := abs_le_of_sq_le b0
  refine ⟨(n0, n1, n2, n3), ⟨?_, ?_, ?_, ?_⟩, rfl⟩ <;> simp only [Set.mem_Icc] <;>
    constructor <;> (try rw [abs_le] at a0 a1 a2 a3) <;> omega

/-- Only finitely many Möbius maps of `Γ*` move `p` by at most `C`. -/
theorem finite_mob (C : ℝ) : {f : UpperHalfPlane → UpperHalfPlane | ∃ γ ∈ Γs,
    f = (fun z => γ • z) ∧ dist (γ • p0) p0 ≤ C}.Finite := by
  refine ((finite_O (6 * Real.cosh C)).image mobOf).subset ?_
  rintro f ⟨γ, hγ, rfl, hC⟩
  obtain ⟨y, hy, hn, g, hg, hz⟩ := cover_y hγ
  have hpos := nrd_pos_of hn
  have hnr : (0 : ℝ) < nrd y := by exact_mod_cast hpos
  have hn6 : (nrd y : ℝ) ≤ 6 := by exact_mod_cast nrd_le_six hn
  refine ⟨y, ⟨hy, nrd_le_six hn, ?_⟩, ?_⟩
  · have h1 := cosh_dist_smul_p0 hg hpos
    rw [← hz] at h1
    have h2 : Real.cosh (dist (γ • p0) p0) ≤ Real.cosh C := by
      rw [Real.cosh_le_cosh, abs_of_nonneg dist_nonneg]
      exact hC.trans (le_abs_self C)
    have h3 : Pq y / nrd y ≤ Real.cosh C - 1 := by linarith
    have h4 : Pq y ≤ (Real.cosh C - 1) * nrd y := (div_le_iff₀ hnr).1 h3
    have h5 : 1 ≤ Real.cosh C := Real.one_le_cosh C
    nlinarith
  · rw [← mobOf_eq hg hpos.ne']; funext z; exact (hz z).symm

theorem properlyDiscontinuous (K : Set UpperHalfPlane) (hK : IsCompact K) :
    {f : UpperHalfPlane → UpperHalfPlane | ∃ γ ∈ Γs, f = (fun z => γ • z) ∧
      (f '' K ∩ K).Nonempty}.Finite := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall p0
  refine (finite_mob (r + r)).subset ?_
  rintro f ⟨γ, hγ, rfl, ⟨_, ⟨k, hk, rfl⟩, hk'⟩⟩
  refine ⟨γ, hγ, rfl, ?_⟩
  have h1 := hr hk
  have h2 := hr hk'
  rw [Metric.mem_closedBall] at h1 h2
  calc dist (γ • p0) p0 ≤ dist (γ • p0) (γ • k) + dist (γ • k) p0 := dist_triangle _ _ _
    _ = dist p0 k + dist (γ • k) p0 := by rw [isom hγ]
    _ ≤ r + r := by rw [dist_comm]; exact add_le_add h1 h2

/-- A point of the orbit of `z` closest to `p`. -/
theorem exists_min (z : UpperHalfPlane) :
    ∃ γ₀ ∈ Γs, ∀ γ ∈ Γs, dist (γ₀ • z) p0 ≤ dist (γ • z) p0 := by
  set S := {f : UpperHalfPlane → UpperHalfPlane | ∃ γ ∈ Γs, f = (fun z => γ • z) ∧
    dist (f z) p0 ≤ dist z p0} with hS
  have hfin : S.Finite := by
    refine (finite_mob (dist z p0 + dist z p0)).subset ?_
    rintro f ⟨γ, hγ, rfl, hd⟩
    refine ⟨γ, hγ, rfl, ?_⟩
    calc dist (γ • p0) p0 ≤ dist (γ • p0) (γ • z) + dist (γ • z) p0 := dist_triangle _ _ _
      _ = dist p0 z + dist (γ • z) p0 := by rw [isom hγ]
      _ ≤ dist z p0 + dist z p0 := by rw [dist_comm p0 z]; exact add_le_add le_rfl hd
  have hne : S.Nonempty := ⟨fun z => (1 : GL (Fin 2) ℝ) • z, 1, gs_one, rfl, by simp⟩
  obtain ⟨f, ⟨γ₀, hγ₀, rfl, hd₀⟩, hmin⟩ := Set.exists_min_image S (fun f => dist (f z) p0) hfin hne
  refine ⟨γ₀, hγ₀, fun γ hγ => ?_⟩
  by_cases hγz : dist (γ • z) p0 ≤ dist z p0
  · exact hmin _ ⟨γ, hγ, rfl, hγz⟩
  · push Not at hγz; exact hd₀.trans hγz.le


/-! ## The stabilizer of `p` acts on `(X, U)` linearly -/

theorem coe_smul_eq {g : GL (Fin 2) ℝ} (hdet : 0 < g.det.val) (w : UpperHalfPlane) :
    ((g • w : UpperHalfPlane) : ℂ) = num g w / denom g w :=
  UpperHalfPlane.coe_smul_of_det_pos hdet w

/-- For `y = a₀ + a₂ j`: `|cw+d|² U(ι(y)w) = αU − 2βX`, `|cw+d|² X(ι(y)w) = αX + 6βU`, `α = a₀² − 3a₂²`,
`β = a₀a₂`. -/
theorem cone_smul {g : GL (Fin 2) ℝ} {y : B} (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = iota y)
    (hn : 0 < nrd y) (hI : y.imI = 0) (hK : y.imK = 0) (w : UpperHalfPlane) :
    Complex.normSq (denom g w) * Uq (g • w) =
        ((y.re : ℝ) ^ 2 - 3 * (y.imJ : ℝ) ^ 2) * Uq w - 2 * ((y.re : ℝ) * y.imJ) * Xq w ∧
      Complex.normSq (denom g w) * Xq (g • w) =
        ((y.re : ℝ) ^ 2 - 3 * (y.imJ : ℝ) ^ 2) * Xq w + 6 * ((y.re : ℝ) * y.imJ) * Uq w := by
  have hdet := det_pos_of hg hn
  have hD := denom_ne_zero g w
  have hDn : Complex.normSq (denom g w) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  have e00 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = (y.re : ℝ) := by rw [hg, iota_apply]; simp [hI]
  have e01 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = -3 * (y.imJ : ℝ) := by rw [hg, iota_apply]; simp [hK]
  have e10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = (y.imJ : ℝ) := by rw [hg, iota_apply]; simp [hK]
  have e11 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (y.re : ℝ) := by rw [hg, iota_apply]; simp [hI]
  have hU : Uq (g • w) = Complex.normSq (num g w) / Complex.normSq (denom g w) - 3 := by
    rw [Uq, coe_smul_eq hdet, Complex.normSq_div]
  have hX : Xq (g • w) = 6 * (((num g w).re * (denom g w).re + (num g w).im * (denom g w).im) /
      Complex.normSq (denom g w)) := by
    rw [Xq, ← UpperHalfPlane.coe_re, coe_smul_eq hdet, Complex.div_re]; ring
  rw [hU, hX]
  constructor
  · field_simp
    simp only [num, denom, Uq, Xq, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
      e00, e01, e10, e11]
    ring
  · field_simp
    simp only [num, denom, Uq, Xq, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
      e00, e01, e10, e11]
    ring

theorem Phi_stab {y : B} (hI : y.imI = 0) (hK : y.imK = 0) (w : UpperHalfPlane) : Phi y w = 0 := by
  simp [Phi, Pq, Rq, Sq, hI, hK]

theorem dist_stab {g : GL (Fin 2) ℝ} {y : B} (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = iota y)
    (hn : 0 < nrd y) (hI : y.imI = 0) (hK : y.imK = 0) (w : UpperHalfPlane) :
    dist (g • w) p0 = dist w p0 := by
  rw [dist_eq_iff, Fp_smul hg hn, Phi_stab hI hK]; simp

/-- The cone step for one stabilizer element. -/
theorem cone_of {g : GL (Fin 2) ℝ} {y : B} (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = iota y)
    (hn : 0 < nrd y) (hI : y.imI = 0) (hK : y.imK = 0) (w : UpperHalfPlane)
    (h1 : ((y.re : ℝ) ^ 2 - 3 * (y.imJ : ℝ) ^ 2) * Xq w + 6 * ((y.re : ℝ) * y.imJ) * Uq w ≤
      ((y.re : ℝ) ^ 2 - 3 * (y.imJ : ℝ) ^ 2) * Uq w - 2 * ((y.re : ℝ) * y.imJ) * Xq w)
    (h2 : -(((y.re : ℝ) ^ 2 - 3 * (y.imJ : ℝ) ^ 2) * Xq w + 6 * ((y.re : ℝ) * y.imJ) * Uq w) ≤
      ((y.re : ℝ) ^ 2 - 3 * (y.imJ : ℝ) ^ 2) * Uq w - 2 * ((y.re : ℝ) * y.imJ) * Xq w) :
    Xq (g • w) ≤ Uq (g • w) ∧ -Xq (g • w) ≤ Uq (g • w) ∧ dist (g • w) p0 = dist w p0 := by
  obtain ⟨hu, hx⟩ := cone_smul hg hn hI hK w
  have hm : 0 < Complex.normSq (denom g w) := Complex.normSq_pos.2 (denom_ne_zero g w)
  refine ⟨?_, ?_, dist_stab hg hn hI hK w⟩
  · by_contra h; push Not at h
    have := mul_lt_mul_of_pos_left h hm
    linarith
  · by_contra h; push Not at h
    have := mul_lt_mul_of_pos_left h hm
    linarith

/-! ### Six elements of the stabilizer of `p` in `Γ*` -/

/-- `u₊ = (1 + j)/2`, `u₋ = (1 − j)/2` (norm one). -/
def uP : B := ⟨1 / 2, 0, 1 / 2, 0⟩
def uM : B := ⟨1 / 2, 0, -1 / 2, 0⟩

theorem nrd_uP : nrd uP = 1 := by norm_num [nrd, uP]
theorem nrd_uM : nrd uM = 1 := by norm_num [nrd, uM]
theorem inO_uP : InO uP := (inO_iff _).2 ⟨0, 0, 1, 0, by ext <;> norm_num [uP]⟩
theorem inO_uM : InO uM := (inO_iff _).2 ⟨1, 0, -1, 0, by ext <;> norm_num [uM]⟩

/-- A norm-one element of `𝒪` gives an element of `Γ*`. -/
theorem mem_of_norm_one {u : B} (hu : InO u) (hn : nrd u = 1) :
    glOf u (by rw [hn]; norm_num) ∈ Γs :=
  gamma1_sub (gamma1_iff.2 ⟨u, hu, coe_glOf _ _, hn⟩)

theorem x6_uM : x6 * uM = (⟨0, 0, 1, 0⟩ : B) := by
  ext <;> norm_num [x6, uM]

theorem rep2 : rep 2 = x6 := by simp [rep]
theorem repi2 : repi 2 = x6i := by simp [repi]

theorem cone_step (w : UpperHalfPlane) : ∃ γ ∈ Γs,
    Xq (γ • w) ≤ Uq (γ • w) ∧ -Xq (γ • w) ≤ Uq (γ • w) ∧ dist (γ • w) p0 = dist w p0 := by
  set U := Uq w
  set X := Xq w
  have h6 : (0 : ℚ) < nrd x6 := by norm_num [nrd, x6]
  have h6i : (0 : ℚ) < nrd x6i := by norm_num [nrd, x6i]
  have hx6 : ((g4 2 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = iota x6 := by rw [g4_coe, rep2]
  have hx6i : (((g4 2)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = iota x6i := by
    rw [inv_coe (g4_coe 2) (rep_repi 2), repi2]
  rcases le_total X U with hXU | hUX <;> rcases le_total (-X) U with hXU' | hUX'
  · -- cone A
    exact ⟨1, gs_one, by simpa using hXU, by simpa using hXU', by simp⟩
  · -- `U ≤ -X`, `X ≤ U`: split by the sign of `U`
    rcases le_total 0 U with hU | hU
    · -- cone B: `x₆⁻¹`
      refine ⟨(g4 2)⁻¹, gs_inv (g4_mem 2), cone_of hx6i h6i (by simp [x6i]) (by simp [x6i]) w ?_ ?_⟩ <;>
        norm_num [x6i] <;> linarith
    · -- cone C: `u₊`
      refine ⟨_, mem_of_norm_one inO_uP nrd_uP,
        cone_of (coe_glOf _ _) (by rw [nrd_uP]; norm_num) (by simp [uP]) (by simp [uP]) w ?_ ?_⟩ <;>
        norm_num [uP] <;> linarith
  · rcases le_total 0 U with hU | hU
    · -- cone F: `x₆`
      refine ⟨g4 2, g4_mem 2, cone_of hx6 h6 (by simp [x6]) (by simp [x6]) w ?_ ?_⟩ <;>
        norm_num [x6] <;> linarith
    · -- cone E: `u₋`
      refine ⟨_, mem_of_norm_one inO_uM nrd_uM,
        cone_of (coe_glOf _ _) (by rw [nrd_uM]; norm_num) (by simp [uM]) (by simp [uM]) w ?_ ?_⟩ <;>
        norm_num [uM] <;> linarith
  · -- cone D: `j = x₆ u₋`
    have hj : ((g4 2 * glOf uM (by rw [nrd_uM]; norm_num) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        iota (⟨0, 0, 1, 0⟩ : B) := by
      rw [Units.val_mul, hx6, coe_glOf, ← iota_mul, x6_uM]
    refine ⟨_, gs_mul (g4_mem 2) (mem_of_norm_one inO_uM nrd_uM),
      cone_of hj (by norm_num [nrd]) rfl rfl w ?_ ?_⟩ <;> norm_num <;> linarith

/-! ## `ι(μ)`, `μ = 2j + ij`, lies in `Γ*` -/

theorem muInv_mul_mu : PkgI1.muInv * PkgI1.mu = 1 := by
  ext <;> simp [PkgI1.mu, PkgI1.muInv] <;> norm_num

theorem conj_mu : ∀ w, InO w → InO (PkgI1.mu * w * PkgI1.muInv) ∧ InO (PkgI1.muInv * w * PkgI1.mu) := by
  intro w hw
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff w).1 hw
  constructor
  · refine (inO_iff _).2 ⟨n0 - n2 + 2 * n3, -n1 - n2 + n3, 3 * n2 - 4 * n3, 2 * n2 - 3 * n3, ?_⟩
    ext <;> simp [PkgI1.mu, PkgI1.muInv] <;> ring
  · refine (inO_iff _).2 ⟨n0 - n2 + 2 * n3, -n1 - n2 + n3, 3 * n2 - 4 * n3, 2 * n2 - 3 * n3, ?_⟩
    ext <;> simp [PkgI1.mu, PkgI1.muInv] <;> ring

theorem nrd_mu : nrd PkgI1.mu = 6 := by norm_num [nrd, PkgI1.mu]

/-- `σ = ι(μ)`: the half-turn about `i√(9 + 6√2)`. -/
def sigma : GL (Fin 2) ℝ := glOf PkgI1.mu (by rw [nrd_mu]; norm_num)

theorem sigma_mem : sigma ∈ Γs :=
  ⟨PkgI1.mu, ⟨PkgI1.muInv, PkgI1.mu_mul_muInv, muInv_mul_mu, conj_mu⟩, coe_glOf _ _, by
    rw [sigma, coe_glOf, det_iota_eq, nrd_mu]; norm_num⟩

/-! ## The fundamental triangle and the covering -/

/-- The triangle `T` with vertices `i√3`, `±(1+√2) + i(2+√2)`. -/
def Tset : Set UpperHalfPlane := {w | Xq w ≤ Uq w ∧ -Xq w ≤ Uq w ∧ Uq w ≤ 6 + 6 * √2}

theorem cover_T (z : UpperHalfPlane) : ∃ γ ∈ Γs, γ • z ∈ Tset := by
  obtain ⟨γ₀, hγ₀, hmin⟩ := exists_min z
  obtain ⟨g, hg, h1, h2, hd⟩ := cone_step (γ₀ • z)
  refine ⟨g * γ₀, gs_mul hg hγ₀, ?_⟩
  set w := (g * γ₀) • z with hw
  have hw' : w = g • γ₀ • z := mul_smul _ _ _
  rw [← hw'] at h1 h2 hd
  refine ⟨h1, h2, ?_⟩
  have hle : dist w p0 ≤ dist (sigma • w) p0 := by
    rw [hd, hw, ← mul_smul]
    exact hmin _ (gs_mul sigma_mem (gs_mul hg hγ₀))
  rw [dist_le_iff, Fp_smul (g := sigma) (y := PkgI1.mu) (coe_glOf _ _) (by rw [nrd_mu]; norm_num)] at hle
  have hpos : 0 < ((nrd PkgI1.mu : ℚ) : ℝ) * w.im := by
    rw [nrd_mu]; have := w.im_pos; positivity
  have hPhi : 0 ≤ Phi PkgI1.mu w := by
    by_contra h; push Not at h
    have := div_neg_of_neg_of_pos h hpos
    linarith
  simp only [Phi, Pq, Rq, Sq, PkgI1.mu] at hPhi
  norm_num at hPhi
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : 1 < √2 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  nlinarith

end HDec.GammaStarArea
