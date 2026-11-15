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

/-! ## Part B. Removable singularities and Liouville for doubly periodic functions -/

section Liouville

/-- The regularization `H(x) = lim_{y → x, y ≠ x} h(y)`. -/
def reg (h : ℂ → ℂ) (x : ℂ) : ℂ := limUnder (𝓝[≠] x) h

/-- If `h` agrees near `x` (punctured) with a function analytic at `x`, the regularization agrees
with it on a neighbourhood of `x`. -/
theorem reg_eventuallyEq {h g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) (hhg : h =ᶠ[𝓝[≠] x] g) :
    reg h =ᶠ[𝓝 x] g := by
  have h1 : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, z ≠ x → h z = g z :=
    (eventually_nhdsWithin_iff.1 hhg).eventually_nhds
  have h2 : ∀ᶠ y in 𝓝 x, AnalyticAt ℂ g y := hg.eventually_analyticAt
  filter_upwards [h1, h2] with y hy hgy
  unfold reg
  apply Tendsto.limUnder_eq
  by_cases hyx : y = x
  · subst hyx
    exact (hgy.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
      (hhg.mono fun z hz => hz.symm)
  · have hev : h =ᶠ[𝓝 y] g := by
      filter_upwards [hy, isOpen_ne.mem_nhds hyx] with z hz hzx using hz hzx
    exact (hgy.continuousAt.tendsto.congr' hev.symm).mono_left nhdsWithin_le_nhds

theorem reg_analyticAt {h g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) (hhg : h =ᶠ[𝓝[≠] x] g) :
    AnalyticAt ℂ (reg h) x :=
  hg.congr (reg_eventuallyEq hg hhg).symm

theorem reg_eq {h g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) (hhg : h =ᶠ[𝓝[≠] x] g) :
    reg h x = g x :=
  (reg_eventuallyEq hg hhg).eq_of_nhds

theorem reg_eq_self {h : ℂ → ℂ} {x : ℂ} (hh : AnalyticAt ℂ h x) : reg h x = h x :=
  reg_eq hh (Eventually.of_forall fun _ => rfl)

theorem reg_add_period {h : ℂ → ℂ} {p : ℂ} (hp : ∀ u, h (u + p) = h u) (x : ℂ) :
    reg h (x + p) = reg h x := by
  unfold reg
  have e : 𝓝[≠] (x + p) = Filter.map (fun u => u + p) (𝓝[≠] x) := by
    simp
  rw [e]
  have : h ∘ (fun u => u + p) = h := funext hp
  simp only [limUnder, Filter.map_map, this]

/-- A continuous function with periods `1` and `w` (`Im w > 0`) is bounded. -/
theorem isBounded_range_of_periodic {F : ℂ → ℂ} {w : ℂ} (hw : 0 < w.im) (hF : Continuous F)
    (h1 : ∀ u, F (u + 1) = F u) (hw' : ∀ u, F (u + w) = F u) : Bornology.IsBounded (Set.range F) := by
  set P : ℝ × ℝ → ℂ := fun st => (st.1 : ℂ) + st.2 * w
  have hP : Continuous P := by fun_prop
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hb : Bornology.IsBounded (F '' (P '' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))) :=
    ((hK.image hP).image hF).isBounded
  refine hb.subset ?_
  rintro _ ⟨z, rfl⟩
  have hp1 : Function.Periodic F 1 := h1
  have hpw : Function.Periodic F w := hw'
  set n : ℤ := ⌊z.im / w.im⌋
  set z1 : ℂ := z - n * w
  set t : ℝ := z1.im / w.im
  set m : ℤ := ⌊z1.re - t * w.re⌋
  set z2 : ℂ := z1 - m
  have ht : t = z.im / w.im - n := by
    simp only [t, z1, sub_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero]
    field_simp
  have ht0 : 0 ≤ t := by rw [ht]; linarith [Int.floor_le (z.im / w.im)]
  have ht1 : t ≤ 1 := by rw [ht]; linarith [Int.lt_floor_add_one (z.im / w.im)]
  set s : ℝ := z1.re - t * w.re - m
  have hs0 : 0 ≤ s := by simp only [s]; linarith [Int.floor_le (z1.re - t * w.re)]
  have hs1 : s ≤ 1 := by simp only [s]; linarith [Int.lt_floor_add_one (z1.re - t * w.re)]
  have hz2 : z2 = P (s, t) := by
    apply Complex.ext
    · simp only [z2, P, s, sub_re, intCast_re, add_re, ofReal_re, mul_re, ofReal_im, zero_mul,
        sub_zero]
      ring
    · simp only [z2, P, sub_im, intCast_im, sub_zero, add_im, ofReal_im, mul_im, ofReal_re,
        zero_mul, add_zero, zero_add, t]
      field_simp
  have hFz : F z = F z2 := by
    simp only [z2, z1]
    have e1 := (hp1.int_mul m).sub_eq (z - n * w)
    have e2 := (hpw.int_mul n).sub_eq z
    rw [mul_one] at e1
    rw [e1, e2]
  refine ⟨P (s, t), ⟨(s, t), ⟨⟨hs0, hs1⟩, ⟨ht0, ht1⟩⟩, rfl⟩, ?_⟩
  rw [hFz, hz2]

end Liouville

/-! ## Part C. The elliptic function `h(u) = (℘(u) − ℘(c)) s(u)² / (s(u − c) s(u + c))` is constant -/

section WP

variable (L : PeriodPair) {w : ℂ}

theorem inLat_add {a b : ℂ} (ha : InLat w a) (hb : InLat w b) : InLat w (a + b) := by
  obtain ⟨m, n, rfl⟩ := ha; obtain ⟨m', n', rfl⟩ := hb
  exact ⟨m + m', n + n', by push_cast; ring⟩

theorem inLat_neg {a : ℂ} (ha : InLat w a) : InLat w (-a) := by
  obtain ⟨m, n, rfl⟩ := ha
  exact ⟨-m, -n, by push_cast; ring⟩

theorem inLat_sub {a b : ℂ} (ha : InLat w a) (hb : InLat w b) : InLat w (a - b) := by
  rw [sub_eq_add_neg]; exact inLat_add ha (inLat_neg hb)

theorem inLat_zero : InLat w 0 := ⟨0, 0, by simp⟩

variable {L}

theorem mem_lattice_iff (h1 : L.ω₁ = 1) (h2 : L.ω₂ = w) {x : ℂ} : x ∈ L.lattice ↔ InLat w x := by
  rw [PeriodPair.mem_lattice, h1, h2]
  constructor
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by ring⟩
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by ring⟩

theorem wp_add_lat (h1 : L.ω₁ = 1) (h2 : L.ω₂ = w) (u : ℂ) {l : ℂ} (hl : InLat w l) :
    L.weierstrassP (u + l) = L.weierstrassP u :=
  L.weierstrassP_add_coe u ⟨l, (mem_lattice_iff h1 h2).2 hl⟩

variable (L w) in
/-- `h(u) = (℘(u) − ℘(c)) s(u)² / (s(u − c) s(u + c))`. -/
def hF (c u : ℂ) : ℂ :=
  (L.weierstrassP u - L.weierstrassP c) * sF w u ^ 2 / (sF w (u - c) * sF w (u + c))

theorem hF_add_one (h1 : L.ω₁ = 1) (h2 : L.ω₂ = w) (c u : ℂ) : hF L w c (u + 1) = hF L w c u := by
  unfold hF
  rw [wp_add_lat h1 h2 u ⟨1, 0, by simp⟩, sF_add_one,
    show u + 1 - c = (u - c) + 1 by ring, sF_add_one, show u + 1 + c = (u + c) + 1 by ring, sF_add_one]

theorem hF_add_w (h1 : L.ω₁ = 1) (h2 : L.ω₂ = w) (c u : ℂ) : hF L w c (u + w) = hF L w c u := by
  unfold hF
  rw [wp_add_lat h1 h2 u ⟨0, 1, by simp⟩, sF_add_w,
    show u + w - c = (u - c) + w by ring, sF_add_w, show u + w + c = (u + c) + w by ring, sF_add_w]
  set E := cexp (-π * I * (2 * w + 2 * u + 1))
  set E1 := cexp (-π * I * (2 * w + 2 * (u - c) + 1))
  set E2 := cexp (-π * I * (2 * w + 2 * (u + c) + 1))
  have hE : E1 * E2 = E ^ 2 := by
    simp only [E, E1, E2]
    rw [← Complex.exp_add, sq, ← Complex.exp_add]; congr 1; ring
  have hE0 : E1 * E2 ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  rw [show (E * sF w u) ^ 2 = (E1 * E2) * sF w u ^ 2 by rw [hE]; ring]
  rw [show (L.weierstrassP u - L.weierstrassP c) * ((E1 * E2) * sF w u ^ 2) /
      (E1 * sF w (u - c) * (E2 * sF w (u + c))) =
      (E1 * E2) * ((L.weierstrassP u - L.weierstrassP c) * sF w u ^ 2) /
      ((E1 * E2) * (sF w (u - c) * sF w (u + c))) by ring]
  exact mul_div_mul_left _ _ hE0

theorem analyticAt_wp (h1 : L.ω₁ = 1) (h2 : L.ω₂ = w) {x : ℂ} (hx : ¬ InLat w x) :
    AnalyticAt ℂ L.weierstrassP x :=
  L.analyticOnNhd_weierstrassP x (by rw [Set.mem_compl_iff, SetLike.mem_coe, mem_lattice_iff h1 h2]; exact hx)

theorem analyticAt_dslope_wp (h1 : L.ω₁ = 1) (h2 : L.ω₂ = w) {x : ℂ} (hx : ¬ InLat w x) :
    AnalyticAt ℂ (dslope L.weierstrassP x) x := by
  have hU : (L.lattice : Set ℂ)ᶜ ∈ 𝓝 x :=
    L.isClosed_lattice.isOpen_compl.mem_nhds
      (by rw [Set.mem_compl_iff, SetLike.mem_coe, mem_lattice_iff h1 h2]; exact hx)
  exact ((Complex.differentiableOn_dslope hU).2 L.differentiableOn_weierstrassP).analyticAt hU

theorem analyticAt_sF (hw : 0 < w.im) (x : ℂ) : AnalyticAt ℂ (sF w) x :=
  (differentiable_sF hw).analyticAt x

/-- Local analytic representatives of `h` at every point; nonvanishing at `0`. -/
theorem hF_local (hw : 0 < w.im) (h1 : L.ω₁ = 1) (h2 : L.ω₂ = w) {c : ℂ} (hc : ¬ InLat w c)
    (h2c : ¬ InLat w (2 * c)) (x : ℂ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g x ∧ hF L w c =ᶠ[𝓝[≠] x] g ∧ (x = 0 → g x ≠ 0) := by
  have hs := analyticAt_sF hw
  by_cases hx : InLat w x
  · -- a pole of `℘`, a double zero of `s²`
    obtain ⟨gx, hgx, hgx0, hsx⟩ := sF_simple hw hx
    have hxc : ¬ InLat w (x - c) := fun h => hc (by
      have := inLat_sub hx h; rwa [sub_sub_cancel] at this)
    have hxc' : ¬ InLat w (x + c) := fun h => hc (by
      have := inLat_sub h hx; rwa [add_sub_cancel_left] at this)
    have hD : sF w (x - c) * sF w (x + c) ≠ 0 := mul_ne_zero (sF_ne_zero hw hxc) (sF_ne_zero hw hxc')
    refine ⟨fun u => ((L.weierstrassPExcept x u - 1 / x ^ 2 - L.weierstrassP c) * (u - x) ^ 2 + 1) *
      gx u ^ 2 / (sF w (u - c) * sF w (u + c)), ?_, ?_, ?_⟩
    · refine AnalyticAt.div ?_ ((hs _).comp (by fun_prop) |>.mul ((hs _).comp (by fun_prop))) hD
      have : AnalyticAt ℂ (L.weierstrassPExcept x) x := L.analyticAt_weierstrassPExcept x
      have hg : AnalyticAt ℂ gx x := hgx.analyticAt x
      fun_prop
    · filter_upwards [self_mem_nhdsWithin] with u (hu : u ≠ x)
      have hux : u - x ≠ 0 := sub_ne_zero.2 hu
      have e := L.weierstrassPExcept_add ⟨x, (mem_lattice_iff h1 h2).2 hx⟩ u
      simp only at e
      unfold hF
      rw [← e, hsx u]
      congr 1
      field_simp
      ring
    · intro _
      simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        zero_add, one_mul]
      exact div_ne_zero (pow_ne_zero _ hgx0) hD
  by_cases hx1 : InLat w (x - c)
  · obtain ⟨g', hg', hg'0, hsg'⟩ := sF_simple hw hx1
    have hxc' : ¬ InLat w (x + c) := fun h => h2c (by
      have := inLat_sub h hx1; rwa [show x + c - (x - c) = 2 * c by ring] at this)
    have hwx : L.weierstrassP x = L.weierstrassP c := by
      have := wp_add_lat h1 h2 c hx1; rwa [add_sub_cancel] at this
    refine ⟨fun u => dslope L.weierstrassP x u * sF w u ^ 2 / (g' (u - c) * sF w (u + c)), ?_, ?_, ?_⟩
    · refine AnalyticAt.div ?_ ?_ (mul_ne_zero (by simpa using hg'0) (sF_ne_zero hw hxc'))
      · have := analyticAt_dslope_wp h1 h2 hx
        have := hs x
        fun_prop
      · exact ((hg'.analyticAt _).comp (by fun_prop)).mul ((hs _).comp (by fun_prop))
    · filter_upwards [self_mem_nhdsWithin] with u (hu : u ≠ x)
      have hux : u - x ≠ 0 := sub_ne_zero.2 hu
      have hd := sub_smul_dslope L.weierstrassP x u
      rw [smul_eq_mul, hwx] at hd
      unfold hF
      rw [← hd, hsg' (u - c), show u - c - (x - c) = u - x by ring]
      rw [show (u - x) * dslope L.weierstrassP x u * sF w u ^ 2 =
          (u - x) * (dslope L.weierstrassP x u * sF w u ^ 2) by ring,
        show (u - x) * g' (u - c) * sF w (u + c) = (u - x) * (g' (u - c) * sF w (u + c)) by ring]
      exact mul_div_mul_left _ _ hux
    · intro h0; exact absurd (h0 ▸ inLat_zero) hx
  by_cases hx2 : InLat w (x + c)
  · obtain ⟨g', hg', hg'0, hsg'⟩ := sF_simple hw hx2
    have hxc : ¬ InLat w (x - c) := fun h => h2c (by
      have := inLat_sub hx2 h; rwa [show x + c - (x - c) = 2 * c by ring] at this)
    have hwx : L.weierstrassP x = L.weierstrassP c := by
      have := wp_add_lat h1 h2 (-c) hx2
      rw [show -c + (x + c) = x by ring, L.weierstrassP_neg] at this
      exact this
    refine ⟨fun u => dslope L.weierstrassP x u * sF w u ^ 2 / (sF w (u - c) * g' (u + c)), ?_, ?_, ?_⟩
    · refine AnalyticAt.div ?_ ?_ (mul_ne_zero (sF_ne_zero hw hxc) (by simpa using hg'0))
      · have := analyticAt_dslope_wp h1 h2 hx
        have := hs x
        fun_prop
      · exact ((hs _).comp (by fun_prop)).mul ((hg'.analyticAt _).comp (by fun_prop))
    · filter_upwards [self_mem_nhdsWithin] with u (hu : u ≠ x)
      have hux : u - x ≠ 0 := sub_ne_zero.2 hu
      have hd := sub_smul_dslope L.weierstrassP x u
      rw [smul_eq_mul, hwx] at hd
      unfold hF
      rw [← hd, hsg' (u + c), show u + c - (x + c) = u - x by ring]
      rw [show (u - x) * dslope L.weierstrassP x u * sF w u ^ 2 =
          (u - x) * (dslope L.weierstrassP x u * sF w u ^ 2) by ring,
        show sF w (u - c) * ((u - x) * g' (u + c)) = (u - x) * (sF w (u - c) * g' (u + c)) by ring]
      exact mul_div_mul_left _ _ hux
    · intro h0; exact absurd (h0 ▸ inLat_zero) hx
  · refine ⟨hF L w c, ?_, Eventually.of_forall fun _ => rfl, fun h0 => absurd (h0 ▸ inLat_zero) hx⟩
    unfold hF
    refine AnalyticAt.div ?_ ((hs _).comp (by fun_prop) |>.mul ((hs _).comp (by fun_prop)))
      (mul_ne_zero (sF_ne_zero hw hx1) (sF_ne_zero hw hx2))
    have := analyticAt_wp h1 h2 hx
    have := hs x
    fun_prop

/-- **`h` is a nonzero constant** off its singular set. -/
theorem hF_const (hw : 0 < w.im) (h1 : L.ω₁ = 1) (h2 : L.ω₂ = w) {c : ℂ} (hc : ¬ InLat w c)
    (h2c : ¬ InLat w (2 * c)) :
    ∃ K : ℂ, K ≠ 0 ∧ ∀ u, ¬ InLat w u → ¬ InLat w (u - c) → ¬ InLat w (u + c) → hF L w c u = K := by
  choose g hga hgh hg0 using hF_local hw h1 h2 hc h2c
  set H := reg (hF L w c)
  have hHa : ∀ x, AnalyticAt ℂ H x := fun x => reg_analyticAt (hga x) (hgh x)
  have hHd : Differentiable ℂ H := fun x => (hHa x).differentiableAt
  have hb := isBounded_range_of_periodic hw hHd.continuous
    (reg_add_period (hF_add_one h1 h2 c)) (reg_add_period (hF_add_w h1 h2 c))
  refine ⟨H 0, ?_, fun u hu hu1 hu2 => ?_⟩
  · show reg (hF L w c) 0 ≠ 0
    rw [reg_eq (hga 0) (hgh 0)]; exact hg0 0 rfl
  · rw [← hHd.apply_eq_apply_of_bounded hb u 0]
    symm
    apply reg_eq_self
    have hs := analyticAt_sF hw
    unfold hF
    refine AnalyticAt.div ?_ ((hs _).comp (by fun_prop) |>.mul ((hs _).comp (by fun_prop)))
      (mul_ne_zero (sF_ne_zero hw hu1) (sF_ne_zero hw hu2))
    have := analyticAt_wp h1 h2 hu
    have := hs u
    fun_prop

end WP

end ThetaWP8
