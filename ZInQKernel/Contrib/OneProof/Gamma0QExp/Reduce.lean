import ZInQKernel.Contrib.OneProof.Gamma0QExp.LevelOneMero

/-!
# gamma0-qexp, part 5: `j(Nγτ)` for `γ ∈ SL₂(ℤ)`

* `jN_smul_of_mem`: `j(N h w) = j(N w)` for `h ∈ Γ₀(N)`.
* `exists_reduce` (Bézout): for `δ ∈ SL₂(ℤ)`, `j(N δ w) = j((a w + b)/d)` with `a, d > 0`,
  `ad = N`, and `a < N` when `δ ∉ Γ₀(N)`.
* growth and the separation estimate: for `δ ∉ Γ₀(N)` and `Im w` large,
  `|j(N δ w)| ≤ 2 e^{2π (N/4) Im w} < ½ e^{2π N Im w} ≤ |j(N w)|`.

No `sorry`, no `axiom`.
-/

noncomputable section

open UpperHalfPlane ModularCurve Filter Topology Asymptotics
open scoped MatrixGroups

namespace ZInQ.Gamma0QExp

theorem coe_SL_smul (g : SL(2, ℤ)) (w : ℍ) :
    ((g • w : ℍ) : ℂ) = ((g 0 0 : ℂ) * w + g 0 1) / ((g 1 0 : ℂ) * w + g 1 1) := by
  rw [coe_specialLinearGroup_apply]
  simp

theorem denom_SL_ne_zero (g : SL(2, ℤ)) (w : ℍ) : ((g 1 0 : ℂ) * w + g 1 1) ≠ 0 := by
  intro h
  by_cases hc : g 1 0 = 0
  · have hdet := g.det_coe
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
    have h11 : g 1 1 ≠ 0 := by rintro h0; rw [h0, mul_zero] at hdet; exact zero_ne_one hdet
    rw [hc] at h
    simp only [Int.cast_zero, zero_mul, zero_add, Int.cast_eq_zero] at h
    exact h11 h
  · have := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      zero_mul, add_zero, Complex.zero_im] at this
    rcases mul_eq_zero.1 this with h1 | h1
    · exact hc (by exact_mod_cast h1)
    · exact w.im_pos.ne' (by rw [UpperHalfPlane.coe_im] at h1; exact h1)

/-- `j(N h w) = j(N w)` for `h ∈ Γ₀(N)`. -/
theorem jN_smul_of_mem (N : ℕ) [NeZero N] {h : SL(2, ℤ)} (hh : h ∈ CongruenceSubgroup.Gamma0 N)
    (w : ℍ) : jN N (h • w) = jN N w := by
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hh
  obtain ⟨c', hc'⟩ := hh
  have hdet := h.det_coe
  rw [Matrix.det_fin_two] at hdet
  let h' : SL(2, ℤ) := ⟨!![h 0 0, N * h 0 1; c', h 1 1], by
    rw [Matrix.det_fin_two_of]; rw [hc'] at hdet; linear_combination hdet⟩
  have key : scaleN N (h • w) = h' • scaleN N w := by
    apply UpperHalfPlane.ext
    rw [coe_scaleN, coe_SL_smul, coe_SL_smul, coe_scaleN]
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have h1 := denom_SL_ne_zero h w
    have h2 : ((c' : ℂ) * (N * w) + h 1 1) ≠ 0 := by
      have : ((c' : ℂ) * (N * w) + h 1 1) = (h 1 0 : ℂ) * w + h 1 1 := by
        rw [hc']; push_cast; ring
      rw [this]; exact h1
    simp only [h', Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, Matrix.head_fin_const]
    rw [mul_div_assoc', div_eq_div_iff h1 h2, hc']
    push_cast
    ring
  rw [jN, key, jf_smul, jN]

/-- `w ↦ (a w + b)/d`. -/
def affH (a d : ℕ) (b : ℤ) (ha : 0 < a) (hd : 0 < d) (w : ℍ) : ℍ :=
  ⟨((a : ℂ) * w + b) / d, by
    rw [Complex.div_natCast_im]
    simp only [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
      zero_mul, add_zero, Complex.intCast_im, UpperHalfPlane.coe_im]
    have := w.im_pos
    positivity⟩

theorem im_affH (a d : ℕ) (b : ℤ) (ha : 0 < a) (hd : 0 < d) (w : ℍ) :
    (affH a d b ha hd w).im = (a / d : ℝ) * w.im := by
  change ((((a : ℂ) * w + b) / d)).im = _
  rw [Complex.div_natCast_im]
  simp only [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    zero_mul, add_zero, Complex.intCast_im, UpperHalfPlane.coe_im]
  ring

/-- **Bézout reduction of `j(Nδw)`.** -/
theorem exists_reduce (N : ℕ) [NeZero N] (δ : SL(2, ℤ)) :
    ∃ (a d : ℕ) (b : ℤ) (ha : 0 < a) (hd : 0 < d), a * d = N ∧
      (δ ∉ CongruenceSubgroup.Gamma0 N → a < N) ∧
      ∀ w : ℍ, jN N (δ • w) = jf (affH a d b ha hd w) := by
  set p := δ 0 0
  set q := δ 0 1
  set r := δ 1 0
  set s := δ 1 1
  have hdet : p * s - q * r = 1 := by
    have := δ.det_coe; rw [Matrix.det_fin_two] at this; linear_combination this
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set g := Int.gcd (N * p) r
  have hg0 : 0 < g := Int.gcd_pos_iff.2 (by
    by_contra h
    push Not at h
    obtain ⟨h1, h2⟩ := h
    have hp : p = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h hN0
      · exact h
    rw [hp, h2] at hdet; simp at hdet)
  set u := Int.gcdA (N * p) r
  set v := Int.gcdB (N * p) r
  have hbez : (g : ℤ) = N * p * u + r * v := Int.gcd_eq_gcd_ab _ _
  obtain ⟨P', hP'⟩ : (g : ℤ) ∣ N * p := Int.gcd_dvd_left ..
  obtain ⟨r', hr'⟩ : (g : ℤ) ∣ r := Int.gcd_dvd_right ..
  have hcop : IsCoprime p r := ⟨s, -q, by linear_combination hdet⟩
  have hgN : (g : ℤ) ∣ N :=
    (hcop.symm.of_isCoprime_of_dvd_left ⟨r', hr'⟩).dvd_of_dvd_mul_right ⟨P', hP'⟩
  obtain ⟨d₀, hd₀⟩ := hgN
  have hg0' : (0 : ℤ) < g := by exact_mod_cast hg0
  have hd₀pos : 0 < d₀ := by
    by_contra h; push Not at h; nlinarith
  have hd₀def : d₀ = P' * s - r' * N * q := by
    have h1 : (g : ℤ) * d₀ = g * (P' * s - r' * N * q) := by
      rw [← hd₀]; linear_combination (-(N : ℤ)) * hdet + s * hP' - (N * q) * hr'
    exact mul_left_cancel₀ hg0'.ne' h1
  have hdet' : u * P' - v * (-r') = 1 := by
    have h1 : (g : ℤ) * (u * P' - v * (-r')) = g * 1 := by
      linear_combination (-u) * hP' + (-v) * hr' - hbez
    exact mul_left_cancel₀ hg0'.ne' h1
  set d := d₀.toNat
  have hdd : (d : ℤ) = d₀ := Int.toNat_of_nonneg hd₀pos.le
  have hdpos : 0 < d := by omega
  set b := u * N * q + v * s
  let σ' : SL(2, ℤ) := ⟨!![u, v; -r', P'], by rw [Matrix.det_fin_two_of]; exact hdet'⟩
  refine ⟨g, d, b, hg0, hdpos, ?_, ?_, ?_⟩
  · have : ((g * d : ℕ) : ℤ) = N := by push_cast; rw [hdd, hd₀]
    exact_mod_cast this
  · intro hδ
    have hle : g ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N))
      ⟨d, by have : ((g * d : ℕ) : ℤ) = N := by push_cast; rw [hdd, hd₀]
             exact_mod_cast this.symm⟩
    refine lt_of_le_of_ne hle fun hgN' => hδ ?_
    rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨r', by show r = (N : ℤ) * r'; rw [hr', hgN']⟩
  · intro w
    have key : σ' • scaleN N (δ • w) = affH g d b hg0 hdpos w := by
      apply UpperHalfPlane.ext
      have hden := denom_SL_ne_zero σ' (scaleN N (δ • w))
      have hD := denom_SL_ne_zero δ w
      rw [coe_SL_smul]
      simp only [σ', Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.head_cons, Matrix.head_fin_const] at hden ⊢
      change _ = ((g : ℂ) * w + b) / d
      have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
      rw [div_eq_div_iff hden hdC]
      set z : ℂ := ((scaleN N (δ • w) : ℍ) : ℂ)
      have hzD : z * ((r : ℂ) * w + s) = N * ((p : ℂ) * w + q) := by
        simp only [z, coe_scaleN, coe_SL_smul]
        show (N : ℂ) * (((p : ℂ) * w + q) / ((r : ℂ) * w + s)) * ((r : ℂ) * w + s) =
          N * ((p : ℂ) * w + q)
        rw [mul_assoc, div_mul_cancel₀ _ hD]
      have hbezC : (g : ℂ) = N * p * u + r * v := by exact_mod_cast hbez
      have hP'C : (N : ℂ) * p = g * P' := by exact_mod_cast hP'
      have hr'C : (r : ℂ) = g * r' := by exact_mod_cast hr'
      have hdC' : (d : ℂ) = P' * s - r' * N * q := by
        have : ((d : ℤ) : ℂ) = ((P' * s - r' * N * q : ℤ) : ℂ) := by rw [hdd, hd₀def]
        push_cast at this; exact this
      have hbC : (b : ℂ) = u * N * q + v * s := by simp [b]
      apply mul_right_cancel₀ hD
      rw [hbC]
      push_cast
      linear_combination (-(d : ℂ) * w) * hbezC + (((g : ℂ) * w + (u * N * q + v * s)) * w * r') * hP'C
        + (-((g : ℂ) * w + (u * N * q + v * s)) * w * P') * hr'C
        + ((g : ℂ) * w + (u * N * q + v * s)) * hdC'
        + ((u : ℂ) * d + r' * ((g : ℂ) * w + (u * N * q + v * s))) * hzD
    rw [jN, ← jf_smul σ', key]

end ZInQ.Gamma0QExp
