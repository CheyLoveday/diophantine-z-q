import ZInQKernel.Contrib.OneProof.RC.ParamAtScale.Coordinates
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-! Rational Taylor coefficients for the regular part of the lattice
uniformization, on-the-spot (c) for tex 1785–1787. -/

noncomputable section

open Filter Topology
open ZInQ.Contrib.CloudB3RC53.CST

namespace ZInQ.Manuscript.RC.ModFnField

/-- The analytic part of `℘` at its pole at zero. -/
abbrev regularPart (L : PeriodPair) : ℂ → ℂ := L.weierstrassPExcept 0

theorem weierstrassP_split (L : PeriodPair) (z : ℂ) :
    L.weierstrassP z = regularPart L z + 1 / z ^ 2 := by
  simpa using (L.weierstrassPExcept_add (0 : L.lattice) z).symm

theorem derivWeierstrassP_split (L : PeriodPair) (z : ℂ) :
    L.derivWeierstrassP z = L.derivWeierstrassPExcept 0 z - 2 / z ^ 3 := by
  simpa only [ZeroMemClass.coe_zero, sub_zero] using
    (eq_sub_of_add_eq (L.derivWeierstrassPExcept_def (0 : L.lattice) z).symm)

private theorem deriv_weierstrass_second (L : PeriodPair) {z : ℂ}
    (hz : z ∉ L.lattice) (hv : L.derivWeierstrassP z ≠ 0) :
    deriv L.derivWeierstrassP z = 6 * L.weierstrassP z ^ 2 - L.g₂ / 2 := by
  have heq : (fun w => L.derivWeierstrassP w ^ 2) =ᶠ[𝓝 z]
      fun w => 4 * L.weierstrassP w ^ 3 - L.g₂ * L.weierstrassP w - L.g₃ := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact L.derivWeierstrassP_sq w hw
  have hP := (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  have hD := (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt
  have hd := heq.deriv_eq
  have hR := ((((hP.fun_pow 3).const_mul 4).sub (hP.const_mul L.g₂)).sub_const L.g₃)
  change HasDerivAt (fun w => 4 * L.weierstrassP w ^ 3 - L.g₂ * L.weierstrassP w - L.g₃)
    _ z at hR
  rw [(hD.fun_pow 2).deriv, hR.deriv, congrFun L.deriv_weierstrassP z] at hd
  norm_num at hd
  apply mul_right_cancel₀ hv
  linear_combination hd / 2

/-- The regular part satisfies the pole-cleared second order equation. -/
private theorem regularPart_ode (L : PeriodPair) :
    (fun z : ℂ => z ^ 2 * deriv (deriv (regularPart L)) z) =ᶠ[𝓝 0]
      fun z => 12 * regularPart L z + z ^ 2 * (6 * regularPart L z ^ 2 - L.g₂ / 2) := by
  have ha := L.analyticAt_weierstrassPExcept 0
  have hb := L.analyticAt_derivWeierstrassPExcept 0
  have hA : ContinuousAt (fun z : ℂ => z ^ 3 * L.derivWeierstrassPExcept 0 z - 2) 0 :=
    (((analyticAt_id.pow 3).mul hb).sub analyticAt_const).continuousAt
  have hB : ∀ᶠ z : ℂ in 𝓝 0, z ^ 3 * L.derivWeierstrassPExcept 0 z - 2 ≠ 0 :=
    hA (isOpen_ne.mem_nhds (show (0 : ℂ) ^ 3 * L.derivWeierstrassPExcept 0 0 - 2 ≠ 0 by simp))
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds (0 : ℂ), hB] with z hz hBz
  by_cases h0 : z = 0
  · simp [h0, regularPart]
  have hLat : z ∉ L.lattice := by simpa [h0] using hz
  have hv : L.derivWeierstrassP z ≠ 0 := by
    intro hv
    apply hBz
    have he := derivWeierstrassP_split L z
    rw [hv, eq_sub_iff_add_eq] at he
    rw [← he, zero_add, mul_div_cancel₀ _ (pow_ne_zero 3 h0), sub_self]
  have hDer : deriv (regularPart L) =ᶠ[𝓝 z] L.derivWeierstrassPExcept 0 := by
    filter_upwards [L.isOpen_compl_lattice_sdiff.mem_nhds hz] with w hw
    exact L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 hw
  have hDer' : deriv L.derivWeierstrassP z =
      deriv (L.derivWeierstrassPExcept 0) z + 6 / z ^ 4 := by
    have he := derivWeierstrassP_split L
    rw [funext he]
    have ha' := (L.analyticOnNhd_derivWeierstrassPExcept 0 z hz).differentiableAt
    have hp : HasDerivAt (fun w : ℂ => 2 / w ^ 3) (-6 / z ^ 4) z := by
      convert ((hasDerivAt_zpow (-3) z (Or.inl h0)).const_mul (2 : ℂ)) using 1
      · ext w
        simp [div_eq_mul_inv]
      · norm_num [_root_.zpow_neg, div_eq_mul_inv] <;> ring
    have hd := ha'.hasDerivAt.sub hp
    change HasDerivAt (fun x => L.derivWeierstrassPExcept 0 x - 2 / x ^ 3) _ z at hd
    rw [hd.deriv]
    ring
  have he := deriv_weierstrass_second L hLat hv
  rw [hDer', ← hDer.deriv_eq, weierstrassP_split L z] at he
  linear_combination (norm := (field_simp [h0] <;> ring)) z ^ 2 * he

/-- Differentiating a double zero shifts the Taylor coefficients by two. -/
private theorem iteratedDeriv_mul_sq (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    iteratedDeriv (n + 2) (fun z : ℂ => z ^ 2 * f z) 0 =
      ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) * iteratedDeriv n f 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hf.contDiffAt]
  rw [Finset.sum_eq_single 2]
  swap
  · intro j _ hj
    rw [iteratedDeriv_fun_pow_zero, ite_eq_right hj]
    norm_num
  swap
  · intro h
    exact (h (by simp)).elim
  simp only [iteratedDeriv_fun_pow_zero, ite_true]
  have hn : n + 2 - 2 = n := by omega
  rw [hn]
  have hchoose := Nat.choose_mul_factorial_mul_factorial (n := n + 2) (k := 2) (by omega)
  rw [hn, Nat.factorial_succ n.succ, Nat.factorial_succ n] at hchoose
  have hc : (n + 2).choose 2 * 2 = (n + 2) * (n + 1) := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos n)
    simpa [mul_assoc] using hchoose
  have hc' : (((n + 2).choose 2 : ℕ) : ℂ) * 2 =
      ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) := by exact_mod_cast hc
  change (((n + 2).choose 2 : ℕ) : ℂ) * 2 * iteratedDeriv n f 0 = _
  rw [hc']

/-- All derivatives of the regular part of `℘` at the origin are rational
for the period lattice of the specified rational Weierstrass model. -/
theorem regularPart_derivatives_rational (E : WeierstrassCurve ℚ) {L : PeriodPair}
    (hL : IsLatticeOf E L) (n : ℕ) :
    iteratedDeriv n (regularPart L) 0 ∈ (Rat.castHom ℂ).fieldRange := by
  let K := (Rat.castHom ℂ).fieldRange
  have h2 : L.g₂ ∈ K := ⟨E.c₄ / 12, by
    change ((E.c₄ / 12 : ℚ) : ℂ) = L.g₂
    push_cast
    exact hL.1.symm⟩
  have h3 : L.g₃ ∈ K := ⟨E.c₆ / 216, by
    change ((E.c₆ / 216 : ℚ) : ℂ) = L.g₃
    push_cast
    exact hL.2.symm⟩
  have ha := L.analyticAt_weierstrassPExcept 0
  change iteratedDeriv n (regularPart L) 0 ∈ K
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simp [regularPart]
    · have hodd := L.G_eq_zero_of_odd 3 (by decide)
      rw [L.iteratedDeriv_weierstrassPExcept_self, L.sumInvPow_zero, hodd]
      simp
    by_cases hn : n = 2
    · subst n
      have h4 : iteratedDeriv 4 (regularPart L) 0 = (6 / 7 : ℂ) * L.g₃ := by
        rw [L.iteratedDeriv_weierstrassPExcept_self, L.sumInvPow_zero, PeriodPair.g₃]
        norm_num
        ring
      rw [h4]
      exact K.mul_mem (K.div_mem (natCast_mem K 6) (natCast_mem K 7)) h3
    let f := regularPart L
    let J := fun z : ℂ => 6 * f z ^ 2 - L.g₂ / 2
    have hf : AnalyticAt ℂ f 0 := ha
    have hJ : AnalyticAt ℂ J 0 :=
      (analyticAt_const.mul (hf.pow 2)).sub analyticAt_const
    have hDiff : AnalyticAt ℂ (deriv (deriv f)) 0 := hf.deriv.deriv
    have hrec := (regularPart_ode L).iteratedDeriv_eq (n + 2)
    change iteratedDeriv (n + 2) (fun z : ℂ => z ^ 2 * deriv (deriv f) z) 0 =
      iteratedDeriv (n + 2) (fun z : ℂ => 12 * f z + z ^ 2 * J z) 0 at hrec
    have hleft : AnalyticAt ℂ (fun z : ℂ => 12 * f z) 0 := analyticAt_const.mul hf
    have hright : AnalyticAt ℂ (fun z : ℂ => z ^ 2 * J z) 0 := (analyticAt_id.pow 2).mul hJ
    rw [iteratedDeriv_mul_sq _ hDiff, iteratedDeriv_fun_add hleft.contDiffAt hright.contDiffAt,
      iteratedDeriv_mul_sq _ hJ, iteratedDeriv_const_mul_field,
      ← iteratedDeriv_succ', ← iteratedDeriv_succ'] at hrec
    have hJmem : iteratedDeriv n J 0 ∈ K := by
      have hJ₁ : AnalyticAt ℂ (fun z : ℂ => 6 * (f z * f z)) 0 := analyticAt_const.mul (hf.mul hf)
      rw [show J = fun z => 6 * (f z * f z) - L.g₂ / 2 by funext z; simp [J, pow_two],
        iteratedDeriv_fun_sub hJ₁.contDiffAt contDiffAt_const,
        iteratedDeriv_const_mul_field, iteratedDeriv_fun_mul hf.contDiffAt hf.contDiffAt]
      apply K.sub_mem
      · exact K.mul_mem (natCast_mem K 6) (K.sum_mem fun i hi =>
          K.mul_mem (K.mul_mem (natCast_mem K _) (ih i (by simp at hi; omega)))
            (ih (n - i) (by omega)))
      · by_cases h0 : n = 0
        · simpa [h0] using K.div_mem h2 (natCast_mem K 2)
        · simp [iteratedDeriv_const, h0]
    have hh : (((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) - 12) ≠ 0 := by
      have hk : (n + 2) * (n + 1) ≠ 12 := by
        intro he
        have hle : n ≤ 2 := by
          by_contra! hl
          have := Nat.mul_le_mul (show 5 ≤ n + 2 by omega) (show 4 ≤ n + 1 by omega)
          omega
        interval_cases n <;> simp_all
      exact sub_ne_zero.mpr (by exact_mod_cast hk)
    have he : iteratedDeriv (n + 2) f 0 =
        (((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) * iteratedDeriv n J 0) /
          (((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) - 12) := by
      apply (eq_div_iff hh).mpr
      linear_combination hrec
    rw [he]
    exact K.div_mem (K.mul_mem (K.mul_mem (natCast_mem K _) (natCast_mem K _)) hJmem)
      (K.sub_mem (K.mul_mem (natCast_mem K _) (natCast_mem K _)) (natCast_mem K 12))

#print axioms weierstrassP_split
#print axioms derivWeierstrassP_split
#print axioms deriv_weierstrass_second
#print axioms regularPart_ode
#print axioms iteratedDeriv_mul_sq
#print axioms regularPart_derivatives_rational

end ZInQ.Manuscript.RC.ModFnField
