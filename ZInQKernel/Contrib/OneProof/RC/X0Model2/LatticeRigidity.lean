import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-! The Weierstrass invariants determine the period lattice. The proof uses
the differential equation for the Weierstrass function and its principal
part at zero (on the spot, provenance (c), tex 2915–2919). -/

noncomputable section

open Filter
open scoped Topology

namespace ZInQ.Manuscript.RC.X0Model2

private theorem weierstrassP_principal (L : PeriodPair) (z : ℂ) :
    L.weierstrassP z = L.weierstrassPExcept 0 z + 1 / z ^ 2 := by
  simpa using (L.weierstrassPExcept_add (0 : L.lattice) z).symm

private theorem weierstrassP_deriv_principal (L : PeriodPair) (z : ℂ)
    (hz : z ∈ ((L.lattice : Set ℂ) \ {0})ᶜ) :
    L.derivWeierstrassP z = deriv (L.weierstrassPExcept 0) z - 2 / z ^ 3 := by
  have h := L.derivWeierstrassPExcept_sub (0 : L.lattice) z
  rw [ZeroMemClass.coe_zero] at h
  simpa only [sub_zero, ← L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 hz]
    using h.symm

/-- The invariants determine the punctured germ at zero. A first nonzero
term of the difference of two regular parts of degree `n > 0` would
contribute `-4n` and `12` times its coefficient on the two sides of the
difference of the differential equations. -/
private theorem weierstrassP_germ_eq (L M : PeriodPair)
    (h₂ : L.g₂ = M.g₂) (h₃ : L.g₃ = M.g₃) :
    L.weierstrassP =ᶠ[𝓝[≠] (0 : ℂ)] M.weierstrassP := by
  let f := L.weierstrassPExcept 0
  let g := M.weierstrassPExcept 0
  let d := fun z => f z - g z
  have hf : AnalyticAt ℂ f 0 := L.analyticAt_weierstrassPExcept 0
  have hg : AnalyticAt ℂ g 0 := M.analyticAt_weierstrassPExcept 0
  have hd : AnalyticAt ℂ d 0 := hf.sub hg
  have hd0 : d 0 = 0 := by simp [d, f, g]
  suffices he : d =ᶠ[𝓝 (0 : ℂ)] 0 by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds] with z hz
    simp only [d, Pi.zero_apply, sub_eq_zero] at hz
    rw [weierstrassP_principal, weierstrassP_principal]
    exact congrArg (fun x => x + 1 / z ^ 2) hz
  by_contra! hn
  have hn' : analyticOrderAt d 0 ≠ ⊤ := fun h => hn (analyticOrderAt_eq_top.mp h)
  obtain ⟨a, ha, ha0, hda⟩ := hd.analyticOrderAt_ne_top.mp hn'
  let n := analyticOrderNatAt d 0
  have he : d =ᶠ[𝓝 (0 : ℂ)] fun z => z ^ n * a z := by
    simpa [n, smul_eq_mul] using hda
  have hn0 : n ≠ 0 := by
    intro h
    apply ha0
    simpa [h, hd0] using he.eq_of_nhds.symm
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  rw [hm] at he
  let u := fun z => 1 + z ^ 2 * f z
  let v := fun z => 1 + z ^ 2 * g z
  let l := fun z => -4 + z ^ 3 * (deriv f z + deriv g z)
  let r := fun z => 4 * (u z ^ 2 + u z * v z + v z ^ 2) - L.g₂ * z ^ 4
  let b := fun z => (m + 1 : ℂ) * a z + z * deriv a z
  have hf' : AnalyticAt ℂ (deriv f) 0 := hf.deriv
  have hg' : AnalyticAt ℂ (deriv g) 0 := hg.deriv
  have ha' : AnalyticAt ℂ (deriv a) 0 := ha.deriv
  have hbl : AnalyticAt ℂ (fun z => b z * l z) 0 := by dsimp [b, l]; fun_prop
  have har : AnalyticAt ℂ (fun z => a z * r z) 0 := by dsimp [r, u, v]; fun_prop
  have hder : ∀ᶠ z in 𝓝 0, deriv d z = z ^ m * b z := by
    filter_upwards [he.deriv, ha.eventually_analyticAt] with z hz hz'
    rw [hz]
    have hd' := ((hasDerivAt_pow (m + 1) z).mul hz'.differentiableAt.hasDerivAt).deriv
    change deriv ((fun x : ℂ => x ^ (m + 1)) * a) z = _
    rw [hd']
    simp only [b, Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, pow_succ]
    ring
  have hdiff : ∀ᶠ z in 𝓝 0, deriv d z = deriv f z - deriv g z := by
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with z hzf hzg
    exact (hzf.differentiableAt.hasDerivAt.sub hzg.differentiableAt.hasDerivAt).deriv
  have hp : (fun z => b z * l z) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => a z * r z) := by
    have hn0' : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 := eventually_mem_nhdsWithin
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, hder.filter_mono nhdsWithin_le_nhds,
      hdiff.filter_mono nhdsWithin_le_nhds,
      mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
      mem_nhdsWithin_of_mem_nhds (M.compl_lattice_sdiff_singleton_mem_nhds 0), hn0']
      with z hd₁ hd₂ hd₃ hL hM hz
    have hL' : z ∉ L.lattice := fun h => hL ⟨h, hz⟩
    have hM' : z ∉ M.lattice := fun h => hM ⟨h, hz⟩
    have h := L.derivWeierstrassP_sq z hL'
    have h' := M.derivWeierstrassP_sq z hM'
    rw [← h₂, ← h₃] at h'
    let P := L.weierstrassP z
    let Q := M.weierstrassP z
    let P' := L.derivWeierstrassP z
    let Q' := M.derivWeierstrassP z
    have hsub : (P' - Q') * (P' + Q') =
        (P - Q) * (4 * (P ^ 2 + P * Q + Q ^ 2) - L.g₂) := by
      change P' ^ 2 = 4 * P ^ 3 - L.g₂ * P - L.g₃ at h
      change Q' ^ 2 = 4 * Q ^ 3 - L.g₂ * Q - L.g₃ at h'
      linear_combination h - h'
    have hP : z ^ 2 * P = u z := by
      dsimp [P, u, f]
      rw [weierstrassP_principal]
      field_simp
      ring
    have hQ : z ^ 2 * Q = v z := by
      dsimp [Q, v, g]
      rw [weierstrassP_principal]
      field_simp
      ring
    have hl : z ^ 3 * (P' + Q') = l z := by
      dsimp [P', Q', l, f, g]
      rw [weierstrassP_deriv_principal L z hL, weierstrassP_deriv_principal M z hM]
      field_simp
      ring
    have hr : z ^ 4 * (4 * (P ^ 2 + P * Q + Q ^ 2) - L.g₂) = r z := by
      rw [show r z = 4 * (u z ^ 2 + u z * v z + v z ^ 2) - L.g₂ * z ^ 4 from rfl,
        ← hP, ← hQ]
      ring
    have hePQ : P - Q = z ^ (m + 1) * a z := by
      dsimp only [P, Q]
      rw [weierstrassP_principal, weierstrassP_principal]
      change f z - g z = z ^ (m + 1) * a z at hd₁
      linear_combination hd₁
    have hePQ' : P' - Q' = z ^ m * b z := by
      dsimp only [P', Q']
      rw [weierstrassP_deriv_principal L z hL, weierstrassP_deriv_principal M z hM]
      linear_combination hd₃.symm.trans hd₂
    apply mul_left_cancel₀ (pow_ne_zero (m + 1) hz)
    calc
      z ^ (m + 1) * (b z * l z) = z ^ 4 * ((P' - Q') * (P' + Q')) := by
        rw [← hl, hePQ', pow_succ]
        ring
      _ = z ^ (m + 1) * (a z * r z) := by rw [hsub, hePQ, ← hr]; ring
  have hzero := ((hbl.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    har.continuousAt).mp hp).eq_of_nhds
  have hcoeff : ((m : ℂ) + 1) * a 0 * (-4) = a 0 * 12 := by
    norm_num [b, l, r, u, v] at hzero ⊢
    exact hzero
  have hre := congrArg Complex.re (mul_left_cancel₀ ha0 (show
    a 0 * (((m : ℂ) + 1) * (-4)) = a 0 * 12 from by linear_combination hcoeff))
  simp [Complex.mul_re, Complex.add_re] at hre
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- Two period lattices with identical Weierstrass invariants coincide.
The elliptic functions agree on punctured neighborhoods by the meromorphic
identity theorem, so their sets of double poles agree. -/
theorem lattice_eq_of_weierstrass_invariants (L M : PeriodPair)
    (h₂ : L.g₂ = M.g₂) (h₃ : L.g₃ = M.g₃) : L.lattice = M.lattice := by
  let d := L.weierstrassP - M.weierstrassP
  have hd : Meromorphic d := L.meromorphic_weierstrassP.sub M.meromorphic_weierstrassP
  have h0 : meromorphicOrderAt d 0 = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [weierstrassP_germ_eq L M h₂ h₃] with z hz
    change L.weierstrassP z - M.weierstrassP z = 0
    rw [hz, sub_self]
  ext z
  have hz : meromorphicOrderAt d z = ⊤ :=
    hd.meromorphicOn.meromorphicOrderAt_eq_top_of_isPreconnected
      isPreconnected_univ (Set.mem_univ 0) (Set.mem_univ z) h0
  have he : L.weierstrassP =ᶠ[𝓝[≠] z] M.weierstrassP := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp hz] with w hw
    exact sub_eq_zero.mp hw
  constructor
  · intro hzL
    by_contra hzM
    have hp := L.order_weierstrassP z hzL
    rw [meromorphicOrderAt_congr he] at hp
    have := (M.analyticOnNhd_weierstrassP z hzM).meromorphicOrderAt_nonneg
    rw [hp] at this
    exact (show ¬ (0 : WithTop ℤ) ≤ -2 by decide) this
  · intro hzM
    by_contra hzL
    have hp := M.order_weierstrassP z hzM
    rw [meromorphicOrderAt_congr he.symm] at hp
    have := (L.analyticOnNhd_weierstrassP z hzL).meromorphicOrderAt_nonneg
    rw [hp] at this
    exact (show ¬ (0 : WithTop ℤ) ≤ -2 by decide) this


end ZInQ.Manuscript.RC.X0Model2
