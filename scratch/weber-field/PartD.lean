import ZInQKernel.Contrib.OneProof.X1Igusa
import ZInQKernel.Contrib.OneProof.RingClassLattice
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_isUniformization_toPoint
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Torsion.Roots
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Coprimality

noncomputable section

namespace X1Igusa.Weber

open LeafModCurves WeierstrassCurve T5Glue UpperHalfPlane

/-! ## D. Analysis on the upper half plane -/

/-- The upper half plane as a subset of `ℂ`. -/
def Hs : Set ℂ := {z : ℂ | 0 < z.im}

theorem isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem isPreconnected_Hs : IsPreconnected Hs := (convex_halfSpace_im_gt 0).isPreconnected

/-- Identity theorem on `ℍ`. -/
theorem eq_zero_of_eventually {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Hs) {z₀ : ℂ} (hz₀ : z₀ ∈ Hs)
    (h : f =ᶠ[nhds z₀] 0) : ∀ z ∈ Hs, f z = 0 := fun _ hz =>
  (hf.analyticOnNhd isOpen_Hs).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Hs hz₀ h hz

/-- Holomorphic functions on `ℍ` form a domain. -/
theorem eq_zero_or_eq_zero {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f Hs) (hg : DifferentiableOn ℂ g Hs)
    (h : ∀ z ∈ Hs, f z * g z = 0) : (∀ z ∈ Hs, f z = 0) ∨ (∀ z ∈ Hs, g z = 0) := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨a, ha, hfa⟩, ⟨b, hb, hgb⟩⟩ := hc
  have hgc : ContinuousAt g b := (hg.differentiableAt (isOpen_Hs.mem_nhds hb)).continuousAt
  have hev : ∀ᶠ z in nhds b, g z ≠ 0 ∧ z ∈ Hs :=
    (hgc.eventually_ne hgb).and (isOpen_Hs.mem_nhds hb)
  have hf0 : f =ᶠ[nhds b] 0 := hev.mono fun z hz => by
    have := h z hz.2
    rcases mul_eq_zero.1 this with h1 | h1
    · exact h1
    · exact absurd h1 hz.1
  exact hfa (eq_zero_of_eventually hf hb hf0 a ha)

theorem ofComplex_coe {z : ℂ} (hz : z ∈ Hs) : ((ofComplex z : UpperHalfPlane) : ℂ) = z := by
  rw [ofComplex_apply_of_im_pos hz]

/-! ### `g₂`, `g₃`, `Δ`, `j` on `ℍ` -/

def G2f (z : ℂ) : ℂ := (pp (ofComplex z)).g₂
def G3f (z : ℂ) : ℂ := (pp (ofComplex z)).g₃
def Dlf (z : ℂ) : ℂ := discL (pp (ofComplex z))
def Jf (z : ℂ) : ℂ := jL (pp (ofComplex z))

theorem diffOn_E {k : ℕ} (hk : 3 ≤ k) :
    DifferentiableOn ℂ ((ModularForm.E hk : UpperHalfPlane → ℂ) ∘ ofComplex) Hs :=
  UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo _)

theorem diffOn_G2f : DifferentiableOn ℂ G2f Hs := by
  have h : G2f = fun z => 60 * (2 * riemannZeta ((4 : ℕ) : ℂ) *
      ((ModularForm.E (k := 4) (by norm_num) : UpperHalfPlane → ℂ) ∘ ofComplex) z) := by
    funext z
    simp only [G2f, PeriodPair.g₂, Function.comp]
    rw [← G_eq_E]; rfl
  rw [h]; exact ((diffOn_E _).const_mul _).const_mul _

theorem diffOn_G3f : DifferentiableOn ℂ G3f Hs := by
  have h : G3f = fun z => 140 * (2 * riemannZeta ((6 : ℕ) : ℂ) *
      ((ModularForm.E (k := 6) (by norm_num) : UpperHalfPlane → ℂ) ∘ ofComplex) z) := by
    funext z
    simp only [G3f, PeriodPair.g₃, Function.comp]
    rw [← G_eq_E]; rfl
  rw [h]; exact ((diffOn_E _).const_mul _).const_mul _

theorem Dlf_eq (z : ℂ) : Dlf z = G2f z ^ 3 - 27 * G3f z ^ 2 := rfl

theorem Dlf_ne (z : ℂ) : Dlf z ≠ 0 := disc_ppD_ne_zero (ofComplex z)

theorem Jf_eq (z : ℂ) : Jf z = 1728 * G2f z ^ 3 / Dlf z := rfl

theorem diffOn_Dlf : DifferentiableOn ℂ Dlf Hs := by
  have : Dlf = fun z => G2f z ^ 3 - 27 * G3f z ^ 2 := rfl
  rw [this]; exact (diffOn_G2f.pow 3).sub ((diffOn_G3f.pow 2).const_mul 27)

theorem diffOn_Jf : DifferentiableOn ℂ Jf Hs := by
  have : Jf = fun z => 1728 * G2f z ^ 3 / Dlf z := rfl
  rw [this]; exact ((diffOn_G2f.pow 3).const_mul 1728).div diffOn_Dlf fun z _ => Dlf_ne z

/-! ### `℘_τ(c)` is holomorphic in `τ` -/

/-- The lattice term `1/(c − ω)² − 1/ω²`, `ω = v₀w + v₁`. -/
def wTerm (c : ℂ) (v : Fin 2 → ℤ) (w : ℂ) : ℂ :=
  1 / (c - ((v 0 : ℂ) * w + v 1)) ^ 2 - 1 / ((v 0 : ℂ) * w + v 1) ^ 2

theorem weierstrassP_pp_eq (τ : UpperHalfPlane) (c : ℂ) :
    (pp τ).weierstrassP c = ∑' v : Fin 2 → ℤ, wTerm c v τ := by
  show (ppD τ).weierstrassP c = _
  rw [PeriodPair.weierstrassP, ← (latEquiv τ).tsum_eq]
  congr 1; funext v; rw [latEquiv_apply]; rfl

theorem lin_ne_zero {v : Fin 2 → ℤ} (hv : v ≠ 0) {w : ℂ} (hw : w ∈ Hs) :
    (v 0 : ℂ) * w + v 1 ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
    add_zero, Complex.zero_im] at him
  have hw' : 0 < w.im := hw
  have h0 : v 0 = 0 := by
    rcases mul_eq_zero.1 him with h1 | h1
    · exact_mod_cast h1
    · exact absurd h1 hw'.ne'
  rw [h0] at h
  simp only [Int.cast_zero, zero_mul, zero_add, Int.cast_eq_zero] at h
  exact hv (by ext i; fin_cases i <;> simp [h0, h])

theorem shift_ne_zero {c : ℝ} (hcZ : ∀ m : ℤ, c ≠ m) (v : Fin 2 → ℤ) {w : ℂ} (hw : w ∈ Hs) :
    (c : ℂ) - ((v 0 : ℂ) * w + v 1) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, zero_mul, add_zero, Complex.zero_im, zero_sub, neg_eq_zero] at him
  have hw' : 0 < w.im := hw
  have h0 : v 0 = 0 := by
    rcases mul_eq_zero.1 him with h1 | h1
    · exact_mod_cast h1
    · exact absurd h1 hw'.ne'
  rw [h0] at h
  simp only [Int.cast_zero, zero_mul, zero_add, sub_eq_zero] at h
  exact hcZ (v 1) (by exact_mod_cast h)

theorem diffOn_wTerm {c : ℝ} (hcZ : ∀ m : ℤ, c ≠ m) (v : Fin 2 → ℤ) :
    DifferentiableOn ℂ (wTerm c v) Hs := by
  by_cases hv : v = 0
  · subst hv
    have : wTerm c 0 = fun _ => 1 / (c : ℂ) ^ 2 := by
      funext w; simp [wTerm]
    rw [this]; exact differentiableOn_const _
  · unfold wTerm
    refine DifferentiableOn.sub ?_ ?_
    · refine (differentiableOn_const _).div ?_ fun w hw => pow_ne_zero 2 (shift_ne_zero hcZ v hw)
      exact ((differentiableOn_const _).sub
        (((differentiableOn_const _).mul differentiableOn_id).add (differentiableOn_const _))).pow 2
    · refine (differentiableOn_const _).div ?_ fun w hw => pow_ne_zero 2 (lin_ne_zero hv hw)
      exact (((differentiableOn_const _).mul differentiableOn_id).add (differentiableOn_const _)).pow 2

/-- The cancellation estimate `‖1/δ² − 1/ω²‖ ≤ 4(2/a³ + 1/a⁴)` for `δ + ω = c`, `‖c‖ ≤ 1`. -/
theorem key_bound {c ω δ : ℂ} {a : ℝ} (ha : 0 < a) (hω : a ≤ ‖ω‖) (hδ : a ≤ 2 * ‖δ‖)
    (hsum : δ + ω = c) (hc : ‖c‖ ≤ 1) : ‖1 / δ ^ 2 - 1 / ω ^ 2‖ ≤ 4 * (2 / a ^ 3 + 1 / a ^ 4) := by
  have hX : 0 < ‖ω‖ := lt_of_lt_of_le ha hω
  have hY : 0 < ‖δ‖ := by linarith
  have hω0 : ω ≠ 0 := norm_pos_iff.mp hX
  have hδ0 : δ ≠ 0 := norm_pos_iff.mp hY
  have e : 1 / δ ^ 2 - 1 / ω ^ 2 = (2 * ω - c) * c / (δ ^ 2 * ω ^ 2) := by
    rw [← hsum]; field_simp; ring
  rw [e, norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
  have h1 : ‖2 * ω - c‖ ≤ 2 * ‖ω‖ + 1 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]; norm_num; linarith
  have h2 : ‖2 * ω - c‖ * ‖c‖ ≤ 2 * ‖ω‖ + 1 := by
    calc ‖2 * ω - c‖ * ‖c‖ ≤ (2 * ‖ω‖ + 1) * 1 := by
          gcongr
      _ = 2 * ‖ω‖ + 1 := by ring
  have h3 : (a / 2) ^ 2 * ‖ω‖ ^ 2 ≤ ‖δ‖ ^ 2 * ‖ω‖ ^ 2 := by
    gcongr; linarith
  calc ‖2 * ω - c‖ * ‖c‖ / (‖δ‖ ^ 2 * ‖ω‖ ^ 2) ≤ (2 * ‖ω‖ + 1) / ((a / 2) ^ 2 * ‖ω‖ ^ 2) := by
        gcongr
    _ = 4 * (2 / (a ^ 2 * ‖ω‖) + 1 / (a ^ 2 * ‖ω‖ ^ 2)) := by field_simp; ring
    _ ≤ 4 * (2 / (a ^ 2 * a) + 1 / (a ^ 2 * a ^ 2)) := by gcongr
    _ = 4 * (2 / a ^ 3 + 1 / a ^ 4) := by ring

theorem norm_vec_eq (v : Fin 2 → ℤ) : ‖v‖ = max |(v 0 : ℝ)| |(v 1 : ℝ)| := by
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp [Nat.cast_natAbs]

theorem one_le_norm_vec {v : Fin 2 → ℤ} (hv : v ≠ 0) : 1 ≤ ‖v‖ := by
  rw [norm_vec_eq]
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1; exact hv (by ext i; fin_cases i <;> simp [h0, h1])
    have : (1 : ℝ) ≤ |(v 1 : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h1
    exact le_max_of_le_right this
  · have : (1 : ℝ) ≤ |(v 0 : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h0
    exact le_max_of_le_left this

/-- `r(τ)‖v‖ ≤ 2‖c − (v₀τ + v₁)‖` for `|c| ≤ 1/2`. -/
theorem shift_bound (τ : UpperHalfPlane) {v : Fin 2 → ℤ} (hv : v ≠ 0) {c : ℝ} (hc : |c| ≤ 1 / 2) :
    EisensteinSeries.r τ * ‖v‖ ≤ 2 * ‖(c : ℂ) - ((v 0 : ℂ) * τ + v 1)‖ := by
  have hr := EisensteinSeries.r_pos τ
  have hn : ‖(c : ℂ) - ((v 0 : ℂ) * τ + v 1)‖ = ‖(v 0 : ℂ) * τ + ((v 1 - c : ℝ) : ℂ)‖ := by
    rw [← norm_neg]; congr 1; push_cast; ring
  rw [hn, norm_vec_eq]
  rcases le_total |(v 1 : ℝ)| |(v 0 : ℝ)| with h | h
  · rw [max_eq_left h]
    have h0 : (v 0 : ℝ) ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at h
      have h1 : (v 1 : ℝ) = 0 := abs_nonpos_iff.mp h
      have h0' : v 0 = 0 := by exact_mod_cast h0
      have h1' : v 1 = 0 := by exact_mod_cast h1
      exact hv (by ext i; fin_cases i <;> simp [h0', h1'])
    have hb := EisensteinSeries.auxbound1 τ (c := 1) (((v 1 : ℝ) - c) / v 0) (by norm_num)
    have he : (v 0 : ℂ) * τ + ((v 1 - c : ℝ) : ℂ) =
        ((v 0 : ℝ) : ℂ) * (((1 : ℝ) : ℂ) * τ + (((v 1 - c) / v 0 : ℝ) : ℂ)) := by
      have : (v 0 : ℂ) ≠ 0 := by exact_mod_cast h0
      push_cast; field_simp
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : |(v 0 : ℝ)| * EisensteinSeries.r τ ≤
        |(v 0 : ℝ)| * ‖((1 : ℝ) : ℂ) * τ + (((v 1 - c) / v 0 : ℝ) : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    nlinarith [abs_nonneg (v 0 : ℝ)]
  · rw [max_eq_right h]
    have h1 : (v 1 : ℝ) ≠ 0 := by
      intro h1
      rw [h1, abs_zero] at h
      have h0 : (v 0 : ℝ) = 0 := abs_nonpos_iff.mp h
      have h0' : v 0 = 0 := by exact_mod_cast h0
      have h1' : v 1 = 0 := by exact_mod_cast h1
      exact hv (by ext i; fin_cases i <;> simp [h0', h1'])
    have hv1 : (1 : ℝ) ≤ |(v 1 : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs (by exact_mod_cast h1)
    have hd : |(v 1 : ℝ)| ≤ 2 * |(v 1 : ℝ) - c| := by
      have := abs_sub_abs_le_abs_sub (v 1 : ℝ) c
      linarith
    have hd0 : (v 1 : ℝ) - c ≠ 0 := by
      intro h'; rw [h', abs_zero] at hd; linarith
    have hb := EisensteinSeries.auxbound2 τ ((v 0 : ℝ) / ((v 1 : ℝ) - c)) (d := 1) (by norm_num)
    have he : (v 0 : ℂ) * τ + ((v 1 - c : ℝ) : ℂ) =
        (((v 1 : ℝ) - c : ℝ) : ℂ) * ((((v 0 : ℝ) / ((v 1 : ℝ) - c) : ℝ) : ℂ) * τ + ((1 : ℝ) : ℂ)) := by
      have : (v 1 : ℂ) - (c : ℂ) ≠ 0 := by exact_mod_cast hd0
      push_cast; field_simp
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : |(v 1 : ℝ) - c| * EisensteinSeries.r τ ≤
        |(v 1 : ℝ) - c| * ‖(((v 0 : ℝ) / ((v 1 : ℝ) - c) : ℝ) : ℂ) * τ + ((1 : ℝ) : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    nlinarith [abs_nonneg ((v 1 : ℝ) - c)]

end X1Igusa.Weber
