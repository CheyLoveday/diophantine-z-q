import ZInQKernel.Contrib.GZTheta.TripleProduct
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Liouville

/-! theta-wp8, part A: the odd-type theta function `s(z) = θ(z + (1+w)/2; w)`, its exact
quasi-periods, its zeros (exactly the lattice `ℤ + ℤw`) and their simplicity. -/

open Complex Filter
open scoped Real Topology

noncomputable section

namespace ThetaWP8

open ZInQ.GZTheta

variable {w : ℂ}

/-- `s(z) = θ(z + (1+w)/2; w)`; its zeros are exactly `ℤ + ℤw`. -/
def sF (w z : ℂ) : ℂ := jacobiTheta₂ (z + (1 + w) / 2) w

theorem sF_add_one (z : ℂ) : sF w (z + 1) = sF w z := by
  unfold sF; rw [show z + 1 + (1 + w) / 2 = z + (1 + w) / 2 + 1 by ring, jacobiTheta₂_add_left]

theorem sF_add_w (z : ℂ) : sF w (z + w) = cexp (-π * I * (2 * w + 2 * z + 1)) * sF w z := by
  unfold sF
  rw [show z + w + (1 + w) / 2 = z + (1 + w) / 2 + w by ring, jacobiTheta₂_add_left']
  congr 2; ring

theorem differentiable_sF (hw : 0 < w.im) : Differentiable ℂ (sF w) := by
  intro z
  exact (differentiableAt_jacobiTheta₂_fst _ hw).comp z (by fun_prop)

/-- `eJ ((1+w)/2) = -q`. -/
theorem eJ_half_add (w : ℂ) : eJ ((1 + w) / 2) = -qJ w := by
  unfold eJ qJ
  rw [show 2 * (π : ℂ) * I * ((1 + w) / 2) = π * I + π * I * w by ring, Complex.exp_add,
    Complex.exp_pi_mul_I]; ring

/-- `B((1+w)/2) = A`. -/
theorem jtpB_half_add (w : ℂ) : jtpB w ((1 + w) / 2) = jtpA w := by
  unfold jtpB jtpA
  refine tprod_congr fun n => ?_
  rw [eJ_half_add]; ring

/-- `s(y) = (1 − e(−y)) · G(y)`, `G(y) = A · B(y + (1+w)/2) · B(−y + (1+w)/2)`. -/
def gF (w y : ℂ) : ℂ := jtpA w * jtpB w (y + (1 + w) / 2) * jtpB w (-y + (1 + w) / 2)

theorem sF_eq_factor (hw : 0 < w.im) (y : ℂ) : sF w y = (1 - eJ (-y)) * gF w y := by
  unfold sF gF
  rw [jacobiTheta₂_eq_jtpP hw]
  unfold jtpP
  have h := jtpB_neg_sub_tau hw (y + (1 - w) / 2)
  rw [show y + (1 - w) / 2 + w = y + (1 + w) / 2 by ring] at h
  rw [h]
  have e1 : (qJ w)⁻¹ * eJ (-(y + (1 - w) / 2)) = -eJ (-y) := by
    have : eJ (-(y + (1 - w) / 2)) = eJ (-y) * eJ (-((1 + w) / 2)) * eJ w := by
      rw [← eJ_add, ← eJ_add]; congr 1; ring
    rw [this, eJ_neg ((1 + w) / 2), eJ_half_add, eJ_tau w]
    have := qJ_ne_zero w
    field_simp
  have e2 : jtpB w (-(y + (1 - w) / 2)) = jtpB w (-y + (1 + w) / 2) := by
    rw [← jtpB_add_one w (-(y + (1 - w) / 2))]; congr 1; ring
  rw [e1, e2]; ring

theorem gF_zero (w : ℂ) : gF w 0 = jtpA w ^ 3 := by
  unfold gF; simp only [zero_add, neg_zero, jtpB_half_add]; ring

theorem differentiable_gF (hw : 0 < w.im) : Differentiable ℂ (gF w) := by
  unfold gF
  have h := differentiable_jtpB hw
  exact ((differentiable_const _).mul (h.comp (by fun_prop))).mul (h.comp (by fun_prop))

theorem sF_zero (hw : 0 < w.im) : sF w 0 = 0 := by
  rw [sF_eq_factor hw]; simp [eJ]

theorem hasDerivAt_sF_zero (hw : 0 < w.im) :
    HasDerivAt (sF w) (2 * π * I * jtpA w ^ 3) 0 := by
  have h1 : HasDerivAt (fun y : ℂ => 1 - eJ (-y)) (2 * π * I) 0 := by
    have : HasDerivAt (fun y : ℂ => cexp (2 * π * I * (-y))) (cexp (2 * π * I * (-0)) * (2 * π * I * (-1))) 0 :=
      (((hasDerivAt_id (0 : ℂ)).neg).const_mul (2 * π * I)).cexp |>.congr_deriv (by simp)
    have h2 := this.const_sub 1
    unfold eJ
    convert h2 using 1; simp
  have h3 := h1.mul ((differentiable_gF hw) 0).hasDerivAt
  have e : sF w = (fun y => (1 - eJ (-y)) * gF w y) := funext (sF_eq_factor hw)
  rw [e]
  convert h3 using 1
  simp [eJ, gF_zero]

theorem deriv_sF_zero_ne (hw : 0 < w.im) : deriv (sF w) 0 ≠ 0 := by
  rw [(hasDerivAt_sF_zero hw).deriv]
  have := jtpA_ne_zero hw
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [this, hpi, I_ne_zero]

/-! ### Zeros -/

theorem jtpB_ne_zero_of (hw : 0 < w.im) {x : ℂ} (hx : ∀ n : ℕ, 1 + qJ w ^ (2 * n + 1) * eJ x ≠ 0) :
    jtpB w x ≠ 0 :=
  tprod_one_add_ne_zero_of_summable hx (summable_jtpB_term hw x)

theorem qJ_pow_odd (w : ℂ) (n : ℕ) : qJ w ^ (2 * n + 1) = eJ ((2 * n + 1) * w / 2) := by
  unfold qJ eJ; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

theorem eJ_eq_one_iff (x : ℂ) : eJ x = 1 ↔ ∃ m : ℤ, x = m := by
  unfold eJ
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    apply mul_left_cancel₀ hpi
    rw [hm]; ring
  · rintro ⟨m, rfl⟩; exact ⟨m, by ring⟩

/-- `1 + q^{2n+1} e(x) = 0` forces `x + (2n+1)w/2 − 1/2 ∈ ℤ`. -/
theorem factor_zero {x : ℂ} {n : ℕ} (h : 1 + qJ w ^ (2 * n + 1) * eJ x = 0) :
    ∃ m : ℤ, x = m - (2 * n + 1) * w / 2 + 1 / 2 := by
  rw [qJ_pow_odd] at h
  have h1 : eJ (x + (2 * n + 1) * w / 2 - 1 / 2) = 1 := by
    have : eJ (x + (2 * n + 1) * w / 2 - 1 / 2) = -(eJ ((2 * n + 1) * w / 2) * eJ x) := by
      rw [sub_eq_add_neg, eJ_add, eJ_add, eJ_neg, show (1 / 2 : ℂ) = 1 / 2 from rfl]
      have : eJ (1 / 2) = -1 := eJ_half
      rw [this]; ring
    rw [this]; linear_combination -h
  obtain ⟨m, hm⟩ := (eJ_eq_one_iff _).1 h1
  exact ⟨m, by linear_combination hm⟩

/-- The lattice `ℤ + ℤw` as a predicate. -/
def InLat (w z : ℂ) : Prop := ∃ m n : ℤ, z = m + n * w

theorem sF_ne_zero (hw : 0 < w.im) {y : ℂ} (hy : ¬ InLat w y) : sF w y ≠ 0 := by
  unfold sF
  rw [jacobiTheta₂_eq_jtpP hw]
  unfold jtpP
  refine mul_ne_zero (mul_ne_zero (jtpA_ne_zero hw) ?_) ?_
  · refine jtpB_ne_zero_of hw fun n hn => hy ?_
    obtain ⟨m, hm⟩ := factor_zero hn
    exact ⟨m, -(n + 1), by push_cast; linear_combination hm⟩
  · refine jtpB_ne_zero_of hw fun n hn => hy ?_
    obtain ⟨m, hm⟩ := factor_zero hn
    exact ⟨-m - 1, n, by push_cast; linear_combination -hm⟩

/-! ### Quasi-periodicity along the lattice and simple zeros -/

theorem sF_add_int (z : ℂ) (m : ℤ) : sF w (z + m) = sF w z := by
  induction m using Int.induction_on generalizing z with
  | zero => simp
  | succ k ih =>
    rw [show z + ((k + 1 : ℤ) : ℂ) = (z + k) + 1 by push_cast; ring, sF_add_one]; exact_mod_cast ih z
  | pred k ih =>
    rw [← sF_add_one (z + ((-(k : ℤ) - 1 : ℤ) : ℂ)),
      show z + ((-(k : ℤ) - 1 : ℤ) : ℂ) + 1 = z + ((-(k : ℤ)) : ℤ) by push_cast; ring, ih]

/-- `s(z + p) = e^{a + bz} s(z)`. -/
def QP (w p : ℂ) : Prop := ∃ a b : ℂ, ∀ z, sF w (z + p) = cexp (a + b * z) * sF w z

theorem qp_add_w {p : ℂ} (h : QP w p) : QP w (p + w) := by
  obtain ⟨a, b, h⟩ := h
  refine ⟨a + b * w + (-π * I * (2 * w + 1)), b + (-π * I * 2), fun z => ?_⟩
  rw [show z + (p + w) = (z + w) + p by ring, h, sF_add_w, ← mul_assoc, ← Complex.exp_add]
  congr 2; ring

theorem qp_sub_w {p : ℂ} (h : QP w p) : QP w (p - w) := by
  obtain ⟨a, b, h⟩ := h
  refine ⟨a - b * w - (-π * I * (2 * w + 2 * (-w) + 1)), b - (-π * I * 2), fun z => ?_⟩
  have h' := sF_add_w (w := w) (z - w)
  rw [sub_add_cancel] at h'
  have hz : sF w (z - w) = cexp (-(-π * I * (2 * w + 2 * (z - w) + 1))) * sF w z := by
    rw [h', ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  rw [show z + (p - w) = (z - w) + p by ring, h, hz, ← mul_assoc, ← Complex.exp_add]
  congr 2; ring

theorem sF_add_lat (m n : ℤ) : QP w (m + n * w) := by
  induction n using Int.induction_on with
  | zero => exact ⟨0, 0, fun z => by simp [sF_add_int]⟩
  | succ k ih =>
    have := qp_add_w ih
    rwa [show (m : ℂ) + (k : ℤ) * w + w = m + ((k + 1 : ℤ) : ℂ) * w by push_cast; ring] at this
  | pred k ih =>
    have := qp_sub_w ih
    rwa [show (m : ℂ) + ((-(k : ℤ)) : ℤ) * w - w = m + ((-(k : ℤ) - 1 : ℤ) : ℂ) * w by
      push_cast; ring] at this

theorem sF_lat (hw : 0 < w.im) {l : ℂ} (hl : InLat w l) : sF w l = 0 := by
  obtain ⟨m, n, rfl⟩ := hl
  obtain ⟨a, b, h⟩ := sF_add_lat (w := w) m n
  have := h 0
  rw [zero_add] at this
  rw [this, sF_zero hw, mul_zero]

/-- Simple zero at every lattice point: `s(z) = (z − l) g(z)` with `g` entire, `g(l) ≠ 0`. -/
theorem sF_simple (hw : 0 < w.im) {l : ℂ} (hl : InLat w l) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g l ≠ 0 ∧ ∀ z, sF w z = (z - l) * g z := by
  obtain ⟨m, n, rfl⟩ := hl
  obtain ⟨a, b, h⟩ := sF_add_lat (w := w) m n
  set l := (m : ℂ) + n * w
  have hd0 : Differentiable ℂ (dslope (sF w) 0) := by
    have := (Complex.differentiableOn_dslope (s := Set.univ) (c := 0) (f := sF w)
      Filter.univ_mem).2 (differentiable_sF hw).differentiableOn
    exact fun z => (this z (Set.mem_univ z)).differentiableAt Filter.univ_mem
  refine ⟨fun z => cexp (a + b * (z - l)) * dslope (sF w) 0 (z - l), ?_, ?_, ?_⟩
  · exact ((by fun_prop : Differentiable ℂ fun z => cexp (a + b * (z - l)))).mul
      (hd0.comp (by fun_prop))
  · simp only [sub_self, dslope_same]
    exact mul_ne_zero (Complex.exp_ne_zero _) (deriv_sF_zero_ne hw)
  · intro z
    have e := h (z - l)
    rw [sub_add_cancel] at e
    rw [e]
    have hs := sub_smul_dslope (sF w) 0 (z - l)
    rw [sF_zero hw, sub_zero, sub_zero, smul_eq_mul] at hs
    rw [← hs]; ring

end ThetaWP8
