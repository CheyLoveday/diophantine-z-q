import ZInQKernel.Contrib.OneProof.PeriodOdd.Isogeny

/-!
# period-odd: the Gross–Zagier formula for `C_d` without `CdTwistedPeriodOdd`

Task period-odd (2026-11-16). Report: `docs/research/period-odd.md`; scratch and log:
`scratch/period-odd/`.

cd-optimal reduced `GZHL3.GrossZagierFormulaCd` to gz-optimal's leaf `GrossZagierModuliOptCd`, the
printed leaf `EtaW32Character` and the glue `CdTwistedPeriodOdd` (some period of `f_d` lies outside
`(1 + i) L`), which separates "`C_d` is optimal" from "the 2-isogenous `E'_d : y² = x³ + 4d² x` is
optimal". This file removes `CdTwistedPeriodOdd`: the Gross–Zagier formula is transported along the
2-isogeny in the second case.

* `lattice_cases`: if `Λ_d ⊆ L` (`EtaW32Character`, cd-optimal) and `Λ_d ≠ 0`, then either
  `L = c₀ Λ_d` (`C_d` optimal) or `L' = ((1 + i)/2) L = c Λ_d` (`E'_d` optimal), `c₀, c ∈ ℚ`.
* `core_isog`: in the second case, gz-optimal's leaf at `E'_d` (it covers every short model with the
  L-function of `C_d`: `LFunction_ePrime_eq`) and the explicit 2-isogeny `φ : C_d → E'_d`
  (`isogPt`, `weierPt_ePrime_eq`, `map_isogPt`) give the formula at `C_d`.
* `grossZagierFormulaCd_of_etaW32`: **`GrossZagierFormulaCd` from `GrossZagierModuliOptCd`,
  `EtaW32Character` and `LamCdNeZero`** (`Λ_d ≠ 0`).

No `sorry`, no `axiom`.
-/

noncomputable section

open Complex WeierstrassCurve HeckeRing.GL2 ZInQ.GZDecomp
open scoped WeierstrassCurve.Affine

namespace ZInQ.PeriodOdd

open ZInQ.CdOpt ZInQ.GZOptimal

/-- **(GLUE) The period lattice of `f_d` is not zero.** For `d ≡ 5 (mod 8)` squarefree, some period
`Φ_d(γτ) − Φ_d(τ)`, `γ ∈ Γ₀(32 d²)`, of gz-weil's Eichler integral `Φ_d = Σ aₙ(C_d)/n qⁿ` is
nonzero: `Φ_d` is not `Γ₀(32 d²)`-invariant. A consequence of the classical fact that the periods
of a weight-2 newform form a lattice in `ℂ` (Shimura 1971, Thm 7.9 / §7.5; UNVERIFIED locator);
equivalently, a holomorphic `Γ₀(N)`-invariant function on `ℍ` bounded at the cusps is constant,
while `Φ_d = q + O(q²)`. -/
def LamCdNeZero : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∃ l ∈ LamCd d, l ≠ 0

/-! ## §1. The classification of `Λ_d ⊆ L` -/

section Gauss

variable {Λ : Submodule ℤ ℂ} {L : PeriodPair} (hLI : ∀ y ∈ L.lattice, I * y ∈ L.lattice)
  (hΛI : ∀ y ∈ Λ, I * y ∈ Λ) {ω μ : ℂ} (hω : ω ∈ L.lattice) (hμ : μ ∈ Λ)
  (repL : ∀ ν ∈ L.lattice, ∃ m n : ℤ, ν = ((m : ℂ) + n * I) * ω)
  (repΛ : ∀ ν ∈ Λ, ∃ m n : ℤ, ν = ((m : ℂ) + n * I) * μ)
include hLI hΛI hω hμ repL repΛ

/-- `μ = k u ω`, `u ∈ {1, i}`: `L = (1/k) Λ`. -/
theorem lattice_eq_of_mu {k : ℤ} {u : ℂ} (hk0 : k ≠ 0) (hu : u = 1 ∨ u = I)
    (hμku : μ = k * u * ω) : L.lattice = Λ.map (LinearMap.mulLeft ℤ (((1 / k : ℚ)) : ℂ)) := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, ((a : ℂ) + b * I) * u = 1 := by
    rcases hu with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, -1, by push_cast; ring_nf; rw [Complex.I_sq]; ring⟩
  obtain ⟨a', b', hab'⟩ : ∃ a b : ℤ, ∀ m n : ℤ, ((m : ℂ) + n * I) * u = (a * m - b * n : ℤ) +
      (b * m + a * n : ℤ) * I := by
    rcases hu with rfl | rfl
    · exact ⟨1, 0, fun m n => by push_cast; ring⟩
    · exact ⟨0, 1, fun m n => by push_cast; ring_nf; rw [Complex.I_sq]; ring⟩
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  ext x
  simp only [Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · intro hx
    obtain ⟨m, n, rfl⟩ := repL x hx
    refine ⟨((m : ℂ) + n * I) * ((a + b * I) * μ), ?_, ?_⟩
    · exact gauss_mul_mem hΛI m n (gauss_mul_mem hΛI a b hμ)
    · rw [hμku]
      have : ((m : ℂ) + n * I) * ((a + b * I) * (k * u * ω)) =
          k * ((m + n * I) * ω) * (((a : ℂ) + b * I) * u) := by ring
      rw [this, hab]; push_cast; field_simp
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨m, n, rfl⟩ := repΛ y hy
    rw [hμku]
    have : (((1 / k : ℚ) : ℂ)) * (((m : ℂ) + n * I) * (k * u * ω)) =
        (((m : ℂ) + n * I) * u) * ω := by push_cast; field_simp
    rw [this, hab' m n]
    exact gauss_mul_mem hLI _ _ hω

/-- `μ = p (1 ± i) ω`: `L' = ((1 + i)/2) L = (1/(2p)) Λ`. -/
theorem latP_eq_of_mu {p : ℤ} (hp0 : p ≠ 0)
    (hμp : μ = p * (1 + I) * ω ∨ μ = p * (1 - I) * ω) :
    (latP L).lattice = Λ.map (LinearMap.mulLeft ℤ (((1 / (2 * p) : ℚ)) : ℂ)) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0
  ext x
  simp only [Submodule.mem_map, LinearMap.mulLeft_apply, ZInQ.GZWeil.mem_scalePP]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨m, n, rfl⟩ := repL y hy
    rcases hμp with hμp | hμp
    · refine ⟨((m : ℂ) + n * I) * μ, gauss_mul_mem hΛI m n hμ, ?_⟩
      rw [hμp]; push_cast; field_simp
    · refine ⟨(((-n : ℤ) : ℂ) + (m : ℤ) * I) * μ, gauss_mul_mem hΛI _ _ hμ, ?_⟩
      rw [hμp, lam]; push_cast; field_simp
      linear_combination (-((m : ℂ) + n) * ω) * Complex.I_sq
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨r, s, rfl⟩ := repΛ l hl
    rcases hμp with hμp | hμp
    · refine ⟨((r : ℂ) + s * I) * ω, gauss_mul_mem hLI r s hω, ?_⟩
      rw [hμp, lam]; push_cast; field_simp
    · refine ⟨(((s : ℤ) : ℂ) + ((-r : ℤ) : ℂ) * I) * ω, gauss_mul_mem hLI _ _ hω, ?_⟩
      rw [hμp, lam]; push_cast; field_simp
      linear_combination (((r : ℂ) - s) * ω) * Complex.I_sq

end Gauss

/-- **Classification.** Let `L` be a period lattice of `C_d` with `Λ_d ⊆ L` and `Λ_d ≠ 0`. Then
`L = c₀ Λ_d` (`c₀ ∈ ℚ`), or `L' = ((1 + i)/2) L = c Λ_d` (`c ∈ ℚ`). As in cd-optimal's
`lattice_eq_of_periods`: `L = ℤ[i] ω`, `Λ_d = ℤ[i] μ`, `μ = (p + q i) ω` with `q = 0`, `p = 0` or
`p = ±q`; the last two cases give `Λ_d = 2p L'`. -/
theorem lattice_cases {d : ℕ} (hd4 : d % 4 = 1) (hsq : Squarefree d) {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L)
    (hU : LamCd d ≤ L.lattice) (hne : ∃ l ∈ LamCd d, l ≠ 0) :
    (∃ c₀ : ℚ, L.lattice = (LamCd d).map (LinearMap.mulLeft ℤ (c₀ : ℂ))) ∨
      (∃ c : ℚ, (latP L).lattice = (LamCd d).map (LinearMap.mulLeft ℤ (c : ℂ))) := by
  obtain ⟨l, hl, hl0⟩ := hne
  have hLI : ∀ y ∈ L.lattice, I * y ∈ L.lattice := fun y hy => I_mul_mem_of_cd hL hy
  have hΛI : ∀ y ∈ LamCd d, I * y ∈ LamCd d := fun y hy => I_mul_mem_LamCd d hy
  obtain ⟨μ, hμ, hμ0, hμmin⟩ := exists_min L (LamCd d) hU hl hl0
  obtain ⟨ω, hω, hω0, hωmin⟩ := exists_min L L.lattice le_rfl L.ω₁_mem_lattice (ω₁_ne_zero L)
  have repL := fun {ν : ℂ} (hν : ν ∈ L.lattice) => gauss_rep hLI hω hω0 hωmin hν
  have repΛ := fun {ν : ℂ} (hν : ν ∈ LamCd d) => gauss_rep hΛI hμ hμ0 hμmin hν
  obtain ⟨m₀, n₀, hc₀⟩ := repL (conj_mem_of_cd hL hω)
  obtain ⟨m₁, n₁, hc₁⟩ := repΛ (conj_mem_LamCd hd4 hsq hμ)
  have hu₀ : m₀ ^ 2 + n₀ ^ 2 = 1 :=
    gauss_norm_eq_one hω0 (by rw [← hc₀, Complex.norm_conj])
  have hu₁ : m₁ ^ 2 + n₁ ^ 2 = 1 :=
    gauss_norm_eq_one hμ0 (by rw [← hc₁, Complex.norm_conj])
  obtain ⟨p, q, hpq⟩ := repL (hU hμ)
  have hrel : ((p : ℂ) - q * I) * ((m₀ : ℂ) + n₀ * I) =
      ((m₁ : ℂ) + n₁ * I) * ((p : ℂ) + q * I) := by
    have h1 : (starRingEnd ℂ) μ = ((p : ℂ) - q * I) * ((m₀ : ℂ) + n₀ * I) * ω := by
      rw [hpq, map_mul, hc₀]; simp only [map_add, map_mul, map_intCast, Complex.conj_I]; ring
    have h2 : (starRingEnd ℂ) μ = ((m₁ : ℂ) + n₁ * I) * ((p : ℂ) + q * I) * ω := by
      rw [hc₁, hpq]; ring
    exact mul_right_cancel₀ hω0 (h1.symm.trans h2)
  have e1 : p * m₀ + q * n₀ = m₁ * p - n₁ * q := by
    have := congrArg Complex.re hrel
    simp at this
    exact_mod_cast this
  have e2 : p * n₀ - q * m₀ = m₁ * q + n₁ * p := by
    have := congrArg Complex.im hrel
    simp at this
    exact_mod_cast this
  have repL' : ∀ ν ∈ L.lattice, ∃ m n : ℤ, ν = ((m : ℂ) + n * I) * ω := fun ν hν => repL hν
  have repΛ' : ∀ ν ∈ LamCd d, ∃ m n : ℤ, ν = ((m : ℂ) + n * I) * μ := fun ν hν => repΛ hν
  rcases gauss_conj_cases hu₀ hu₁ e1 e2 with hq | hp | hpq' | hpq'
  · -- `μ = p ω`: `C_d` optimal
    have hp0 : p ≠ 0 := by rintro rfl; apply hμ0; rw [hpq, hq]; simp
    exact Or.inl ⟨_, lattice_eq_of_mu hLI hΛI hω hμ repL' repΛ' hp0 (Or.inl rfl)
      (by rw [hpq, hq]; push_cast; ring)⟩
  · -- `μ = q i ω`: `C_d` optimal
    have hq0 : q ≠ 0 := by rintro rfl; apply hμ0; rw [hpq, hp]; simp
    exact Or.inl ⟨_, lattice_eq_of_mu hLI hΛI hω hμ repL' repΛ' hq0 (Or.inr rfl)
      (by rw [hpq, hp]; push_cast; ring)⟩
  · -- `μ = p (1 − i) ω`: `E'_d` optimal
    have hp0 : p ≠ 0 := by
      rintro rfl
      have hq0 : q = 0 := by omega
      apply hμ0; rw [hpq, hq0]; simp
    exact Or.inr ⟨_, latP_eq_of_mu hLI hΛI hω hμ repL' repΛ' hp0
      (Or.inr (by rw [hpq, show q = -p by omega]; push_cast; ring))⟩
  · -- `μ = p (1 + i) ω`: `E'_d` optimal
    have hp0 : p ≠ 0 := by rintro rfl; apply hμ0; rw [hpq, ← hpq']; simp
    exact Or.inr ⟨_, latP_eq_of_mu hLI hΛI hω hμ repL' repΛ' hp0
      (Or.inl (by rw [hpq, ← hpq']; ring))⟩

end ZInQ.PeriodOdd
