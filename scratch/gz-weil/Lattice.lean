import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilJacobi

noncomputable section

open Complex Filter Topology
open scoped Real

namespace ZInQ.GZWeil

/-! ## L1. A lattice with `g₃ = 0`, `g₂ ≠ 0` -/

/-- The square lattice `ℤ + ℤi`. -/
def squarePP : PeriodPair where
  ω₁ := 1
  ω₂ := I
  indep := by
    have := Complex.basisOneI.linearIndependent
    rwa [Complex.coe_basisOneI] at this

theorem G_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) (n : ℕ) : L.G n = L'.G n := by
  let e : L.lattice ≃ L'.lattice :=
    { toFun := fun l => ⟨l, h ▸ l.2⟩
      invFun := fun l => ⟨l, h.symm ▸ l.2⟩
      left_inv := fun l => rfl
      right_inv := fun l => rfl }
  rw [PeriodPair.G, PeriodPair.G, ← e.tsum_eq]
  rfl

theorem squarePP_lattice_I : (scalePP squarePP I I_ne_zero).lattice = squarePP.lattice := by
  ext x
  rw [mem_scalePP]
  simp only [PeriodPair.mem_lattice, squarePP]
  constructor
  · rintro ⟨y, ⟨m, n, rfl⟩, rfl⟩
    refine ⟨-n, m, ?_⟩
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  · rintro ⟨m, n, rfl⟩
    refine ⟨n * 1 + (-m) * I, ⟨n, -m, by push_cast; ring⟩, ?_⟩
    ring_nf
    rw [Complex.I_sq]
    ring

theorem g₃_squarePP : squarePP.g₃ = 0 := by
  have h := g₃_scalePP squarePP I_ne_zero
  rw [PeriodPair.g₃, PeriodPair.g₃, G_congr squarePP_lattice_I] at h
  have hI6 : (I ^ 6)⁻¹ = (-1 : ℂ) := by
    rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, Complex.I_sq]; norm_num
  rw [hI6] at h
  rw [PeriodPair.g₃]
  linear_combination h / 2

/-- **`(g₂, g₃) ≠ (0, 0)` for every lattice**: if both vanished, `℘'² = 4℘³`, and at a zero of
`℘` (`℘` is onto) the orders of vanishing would satisfy `2(n − 1) = 3n`. -/
theorem g₂_ne_zero_of_g₃_eq_zero (L : PeriodPair) (h3 : L.g₃ = 0) : L.g₂ ≠ 0 := by
  intro h2
  obtain ⟨z1, hz1, hp⟩ := weierstrassP_surjective L 0
  have hrel : ∀ z ∉ L.lattice, L.derivWeierstrassP z ^ 2 = 4 * L.weierstrassP z ^ 3 := by
    intro z hz; rw [L.derivWeierstrassP_sq z hz, h2, h3]; ring
  have ha : AnalyticAt ℂ L.weierstrassP z1 := L.analyticOnNhd_weierstrassP z1 hz1
  have hev : ∀ᶠ z in 𝓝 z1, z ∉ L.lattice :=
    L.isClosed_lattice.isOpen_compl.mem_nhds hz1
  -- order of `℘` at `z₁`
  rcases hord : analyticOrderAt L.weierstrassP z1 with _ | n
  · -- `℘ ≡ 0` near `z₁`, hence on the connected `ℂ ∖ L`
    have h0 : ∀ᶠ z in 𝓝 z1, L.weierstrassP z = 0 := analyticOrderAt_eq_top.mp hord
    apply weierstrassP_not_const L
    refine ⟨0, fun z hz => ?_⟩
    have := L.analyticOnNhd_weierstrassP.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isConnected_compl_lattice L).isPreconnected hz1 h0 hz
    simpa using this
  · have hn0 : n ≠ 0 := by
      rintro rfl
      exact ((ha.analyticOrderAt_eq_zero).mp (by rw [hord]; rfl)) hp
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hd : analyticOrderAt (deriv L.weierstrassP) z1 = m :=
      analyticOrderAt_deriv_of_pos ha (by rw [hord]; rfl)
    rw [L.deriv_weierstrassP] at hd
    have hda : AnalyticAt ℂ L.derivWeierstrassP z1 := L.analyticOnNhd_derivWeierstrassP z1 hz1
    have heq : (fun z => L.derivWeierstrassP z ^ 2) =ᶠ[𝓝 z1] fun z => 4 * L.weierstrassP z ^ 3 := by
      filter_upwards [hev] with z hz using hrel z hz
    have h1 := analyticOrderAt_congr heq
    rw [show (fun z => L.derivWeierstrassP z ^ 2) = L.derivWeierstrassP ^ 2 from rfl,
      analyticOrderAt_pow hda, hd] at h1
    have h4 : analyticOrderAt (fun z => (4 : ℂ) * L.weierstrassP z ^ 3) z1 =
        analyticOrderAt L.weierstrassP z1 * 3 := by
      have := analyticOrderAt_mul (f := fun _ => (4 : ℂ)) (g := L.weierstrassP ^ 3)
        analyticAt_const (ha.pow 3)
      rw [show (fun z => (4 : ℂ) * L.weierstrassP z ^ 3) = (fun _ => (4 : ℂ)) *
        L.weierstrassP ^ 3 from rfl, this, analyticOrderAt_pow ha,
        (analyticAt_const.analyticOrderAt_eq_zero).mpr (by norm_num), zero_add]
      rw [nsmul_eq_mul, mul_comm]; norm_num
    rw [h4, hord] at h1
    have hc : (some m.succ : ℕ∞) = ((m + 1 : ℕ) : ℕ∞) := rfl
    rw [hc, nsmul_eq_mul] at h1
    have : ((2 * m : ℕ) : ℕ∞) = (((m + 1) * 3 : ℕ) : ℕ∞) := by push_cast; exact h1
    have := Nat.cast_injective this
    omega

end ZInQ.GZWeil
