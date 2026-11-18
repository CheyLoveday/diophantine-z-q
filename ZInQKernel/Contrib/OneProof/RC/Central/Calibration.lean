import Mathlib

/-!
# Lane RC15 (central): the determinant and isogeny bookkeeping of (4.6)

Proposition `ex:arith-central-calibration` of the 11/5 manuscript (`diophantine_zq.tex`,
lines 3987–4141): at known simple zeros,

  `v₂ u_prim(0) = 2 j_rc(h,k) − 4ω(h) − s(h) − s(hk) − Σ_{p ∣ k} t_p + O_{E,π}(1)`.   (4.6)

This file proves the exact algebra of the proof (tex 4051–4140) from its inputs, which enter as
hypotheses with their kinds:

* the class and functional free coefficients have valuation `j_rc + v₂(L m_i)` (PROVED in
  `CentralSpecialization.lean`);
* the torsion lengths `g_A, s_A, g_A` of the ordinary Kummer complex in degrees one, two, three
  (ELLIOT, tex 4006–4015, 4054–4057: universal coefficients and self-duality);
* the sign rule: a torsion disk with cokernel of length `e` in degree `i` contributes
  `(−1)^{i+1} e` (tex 4058–4060; `diskContribution`, the convention of the coordinate, see
  `Coordinate.lean`);
* the local quotient lengths: `v₂ N_i` at each of the two places above the moving prime
  (ELLIOT, tex 4066–4071; `v₂ N_i = v₂ m_i` is PROVED in `EulerFactors.lean`) and `2` at each of
  the two places above an active prime (GLUE, `dim_{𝔽₂} E[2]^{Fr_p} = 2`, tex 4032–4036, 4076–4078);
* the regulator ratio of the **real** regulators `Reg_A`, `Reg_B` (canonical heights of free
  generators at rank one) from dual isogenies with `ψφ = [2]`: the height adjunction read on
  generators, `α Reg_B = β Reg_A`, and `αβ = 2` are the hypotheses of `regulator_ratio`, PROVED for
  the genuine canonical heights by lane RC19 (`Height/SumDifference.lean`,
  `regulator_ratio_sumDiff`, which applies `regulator_ratio` to them; `Height/Discharge.lean`,
  `regulator_inputs_sumDiff`); that `Reg_B/Reg_A = 2/I²` is a rational number is then derived
  (`regulator_eq_ratCast_mul`, `regulator_ratio_div`), not assumed;
* the pullbacks `φ^*ω_B = a ω_A`, `ψ^*ω_A = b ω_B` with `ab = 4`, the real change of variables
  `|a| Ω_A = (|ker φ_ℝ| / |coker φ_ℝ|) Ω_B` with both orders at most four (GLUE, tex 4093–4104);
* **Cassels' isogeny invariance in Milne's form** (PRINT: J. S. Milne, *Arithmetic Duality
  Theorems*, 2nd ed., BookSurge 2006, Chapter I, §7, Theorem 7.3, p. 97, and its proof,
  pp. 97–99, which reduces the invariance of the Birch–Swinnerton-Dyer quotient to the duality
  identity (7.3.1), p. 98; read in the author's electronic edition; tex 4024–4027, 4105–4112),
  stated as `MilneIsogenyInvariance` and converted to the valuation identity
  `s_A − s_B = 2g_A − 2g_B + v₂(Reg_B/Reg_A) + v₂(Ω_B/Ω_A) + v₂(C_B/C_A)` by
  `milne_valuation_form`;
* the component numbers: cancellation at split primes, `c_p(A) = 1` (connected Weil restriction)
  and `c_p(E^{(hk)}) = |E[2]^{Fr_p}| = 2^{t_p}` at `p ∣ k` (PRINT: B. Edixhoven, "Néron models and
  tame ramification", Compositio Math. 81 (1992) 291–306, Theorem 5.3, pp. 299–300, and
  Remark 5.4.1, p. 300: the component group of the Néron model over `D` is the group of connected
  components of `(A'_k)^{μ_n}`; read; tex 4119–4124; the print leaf is lane RC9's; the
  identification of the `μ₂`-action with `[−1]` for a quadratic twist is Elliot's step);
* the rational torsion of `B = E^{(h)} × E^{(hk)}` is bounded by a constant (ELLIOT, tex 4114–4115).

Every declaration in this file is `PROVED`, except the definition `MilneIsogenyInvariance`, which
states the print (PRINT).

* `MilneIsogenyInvariance` (PRINT), `milne_valuation_form` (tex 4105–4112).
* `isogenyIndex_mul`, `isogenyIndex_ne_zero`, `regulator_ratio` (over `ℝ`),
  `regulator_eq_ratCast_mul`, `regulator_ratio_div`, `padicValRat_regulator_ratio`
  (tex 4082–4090): `IJ = 2`, `Reg_B α² = 2 Reg_A`, `Reg_B / Reg_A = 2/α² = 2/I² ∈ ℚ`,
  `v₂(Reg_B/Reg_A) = ±1`.
* `milne_valuation_form_of_adjunction` (tex 4082–4112): Milne's identity at real regulators related
  by the adjunction, in valuation form with `v₂(2/α²)`; `regulator_hypotheses_satisfiable`:
  non-vacuity, with the irrational regulator `Reg_A = π`.
* `pullback_values` (tex 4093–4096): `ab = 4 ⇒ a ∈ {±1, ±2, ±4}`.
* `padicValRat_period_ratio` (tex 4096–4104): `|v₂(Ω_B/Ω_A)| ≤ 4`.
* `padicValRat_component_ratio` (tex 4118–4135): `v₂(C_B/C_A) = Σ_{p ∣ k} t_p`.
* `torsion_contribution`, `local_contribution` (tex 4054–4064, 4066–4078).
* `calibration_46`: (4.6) with the explicit error `ε = 2v₂L + 2g_B − v₂(Reg_B/Reg_A) − v₂(Ω_B/Ω_A)`,
  `|ε| ≤ 2v₂L + 2G₀ + 5`, independent of `h` and `k`.
-/

namespace ZInQ.Manuscript.RC.Central

open scoped BigOperators

/-! ### Cassels–Milne isogeny invariance -/

/-- **Milne, *Arithmetic Duality Theorems*, I.7.3 and (7.3.1)** (PRINT, abstract interface: the
Birch–Swinnerton-Dyer invariants of abelian varieties over `ℚ` are not in Mathlib). For isogenous
abelian varieties `A`, `B` over `ℚ` with finite Tate–Shafarevich groups, the quotient
`|Ш| · Reg · Ω · C / (|tors| · |tors^t|)` is the same for `A` and `B` (the proof of Theorem 7.3,
pp. 97–99, establishes this from duality, (7.3.1), without assuming the conjectural equality with
the leading term; tex 4024–4027). Here `shaX = |Ш(X)|`, `tX = |X(ℚ)_tors|`, `tXd = |X^t(ℚ)_tors|`,
`CX` the product of the component numbers, `RegX`, `ΩX` the regulator and period for the chosen
Néron differentials. -/
def MilneIsogenyInvariance (shaA shaB tA tAd tB tBd CA CB : ℕ) (RegA RegB ΩA ΩB : ℝ) : Prop :=
  (shaA : ℝ) * RegA * ΩA * CA / (tA * tAd) = (shaB : ℝ) * RegB * ΩB * CB / (tB * tBd)

/-- **The two-adic form of the isogeny invariance** (tex 4105–4112). With self-dual torsion
counts (`|A^t(ℚ)_tors| = |A(ℚ)_tors|`, `A` and `B` principally polarized: GLUE), rational ratios
`Reg_B = ρ_Reg Reg_A`, `Ω_B = ρ_Ω Ω_A`, and `s_X = v₂ |Ш(X)|`, `g_X = v₂ |X(ℚ)_tors|`:
`s_A − s_B = 2g_A − 2g_B + v₂ ρ_Reg + v₂ ρ_Ω + v₂(C_B/C_A)`. The rationality of `Reg_B/Reg_A` is
not an input of the calibration: `milne_valuation_form_of_adjunction` derives it from the height
adjunction on the real regulators (tex 4088–4090) and then applies this lemma. PROVED. -/
theorem milne_valuation_form {shaA shaB tA tB CA CB : ℕ} {RegA ΩA : ℝ} {ρReg ρΩ : ℚ}
    (hshaA : shaA ≠ 0) (hshaB : shaB ≠ 0) (htA : tA ≠ 0) (htB : tB ≠ 0) (hCA : CA ≠ 0)
    (hCB : CB ≠ 0) (hRegA : RegA ≠ 0) (hΩA : ΩA ≠ 0) (hρReg : ρReg ≠ 0) (hρΩ : ρΩ ≠ 0)
    (h : MilneIsogenyInvariance shaA shaB tA tA tB tB CA CB RegA ((ρReg : ℝ) * RegA) ΩA
      ((ρΩ : ℝ) * ΩA)) :
    (padicValNat 2 shaA : ℤ) - padicValNat 2 shaB =
      2 * (padicValNat 2 tA : ℤ) - 2 * padicValNat 2 tB + padicValRat 2 ρReg +
        padicValRat 2 ρΩ + padicValRat 2 ((CB : ℚ) / CA) := by
  unfold MilneIsogenyInvariance at h
  have htA' : (tA : ℝ) ≠ 0 := by exact_mod_cast htA
  have htB' : (tB : ℝ) ≠ 0 := by exact_mod_cast htB
  -- cancel `Reg_A Ω_A` and pass to `ℚ`
  have hR : ((shaA * CA * tB ^ 2 : ℚ) : ℝ) = ((shaB * ρReg * ρΩ * CB * tA ^ 2 : ℚ) : ℝ) := by
    field_simp at h
    push_cast
    linear_combination h
  have hQ : (shaA * CA * tB ^ 2 : ℚ) = shaB * ρReg * ρΩ * CB * tA ^ 2 := by exact_mod_cast hR
  have hv := congrArg (padicValRat 2) hQ
  have n1 : (shaA : ℚ) ≠ 0 := by exact_mod_cast hshaA
  have n2 : (shaB : ℚ) ≠ 0 := by exact_mod_cast hshaB
  have n3 : (tA : ℚ) ≠ 0 := by exact_mod_cast htA
  have n4 : (tB : ℚ) ≠ 0 := by exact_mod_cast htB
  have n5 : (CA : ℚ) ≠ 0 := by exact_mod_cast hCA
  have n6 : (CB : ℚ) ≠ 0 := by exact_mod_cast hCB
  rw [padicValRat.mul (by positivity) (by positivity), padicValRat.mul n1 n5,
    padicValRat.pow _ , padicValRat.mul (by positivity) (by positivity),
    padicValRat.mul (by simp [n2, hρReg, hρΩ]) n6, padicValRat.mul (by simp [n2, hρReg]) hρΩ,
    padicValRat.mul n2 hρReg, padicValRat.pow _] at hv
  rw [padicValRat.div n6 n5]
  simp only [padicValRat.of_nat] at hv ⊢
  push_cast at hv ⊢
  linarith

/-! ### The regulator ratio

The regulators `Reg_A`, `Reg_B` are **real** numbers: the determinants of the canonical
(Néron–Tate) height pairings on the free parts of `A(ℚ)` and `B(ℚ)`; at rank one, the canonical
heights of free generators. The text derives that their ratio is the rational number `2/I²`
(tex 4082–4090), and only then takes its two-adic valuation (tex 4108–4112). Here too the
rationality is a consequence (`regulator_eq_ratCast_mul`, `regulator_ratio_div`), not an input. -/

/-- **`ψφ = [2]` on rank-one free lattices**: with `φ(g_A) = α g_B` and `ψ(g_B) = β g_A`,
`αβ = 2`; the indices `I = |α|`, `J = |β|` satisfy `IJ = 2` (tex 4082–4088). PROVED. -/
theorem isogenyIndex_mul {α β : ℤ} (h : α * β = 2) : α.natAbs * β.natAbs = 2 := by
  rw [← Int.natAbs_mul, h]; rfl

/-- `αβ = 2` forces `α ≠ 0`: the index `I = |α|` is positive (tex 4082–4088). PROVED. -/
theorem isogenyIndex_ne_zero {α β : ℤ} (h : α * β = 2) : α ≠ 0 := by
  rintro rfl
  simp at h

/-- **`Reg_B α² = 2 Reg_A`, the text's `Reg_B / Reg_A = 2 / I²`** (tex 4022–4025, 4082–4090), for
real `Reg_A`, `Reg_B`. With the height adjunction `⟨φ x, y⟩_B = ⟨x, ψ y⟩_A` ("the sum/difference
isogenies are dual", tex 4022–4023) read on free generators `g_A`, `g_B` of the two rank-one
lattices (`φ g_A ≡ α g_B`, `ψ g_B ≡ β g_A` modulo torsion, `Reg_A = ĥ_A(g_A)`, `Reg_B = ĥ_B(g_B)`)
as `α Reg_B = β Reg_A`, and `αβ = 2` (`ψφ = [2]`), one has `Reg_B α² = 2 Reg_A`. No `Reg_A ≠ 0` is
assumed; the quotient form `Reg_B / Reg_A = 2/α² = 2/I²` (`I = |α|`) is `regulator_ratio_div`.
Both hypotheses are PROVED for the genuine canonical heights by lane RC19
(`ZInQ.Manuscript.RC.Height.regulator_ratio_sumDiff`, which applies this theorem to them). In the
reduction it is applied, through `regulator_eq_ratCast_mul` and
`milne_valuation_form_of_adjunction`, to the real regulators `RegA`, `RegB` of
`Wiring.CalibrationModel`, which `Wiring.CalibrationModelR.nonempty_model` fills with the genuine
canonical heights; no rational stand-in for the regulators is used. PROVED. -/
theorem regulator_ratio {α β : ℤ} {RegA RegB : ℝ} (h : α * β = 2)
    (hadj : (α : ℝ) * RegB = (β : ℝ) * RegA) : RegB * (α : ℝ) ^ 2 = 2 * RegA := by
  have h' : (α : ℝ) * β = 2 := by exact_mod_cast h
  linear_combination (α : ℝ) * hadj + RegA * h'

/-- **The regulator ratio is the rational number `2/α²`** (tex 4088–4090): under the hypotheses of
`regulator_ratio`, `Reg_B = (2/α²) · Reg_A` with `2/α² ∈ ℚ`, for every real `Reg_A`. That
`Reg_B/Reg_A` is rational is derived here from the adjunction and `αβ = 2`; it is not assumed.
PROVED. -/
theorem regulator_eq_ratCast_mul {α β : ℤ} {RegA RegB : ℝ} (h : α * β = 2)
    (hadj : (α : ℝ) * RegB = (β : ℝ) * RegA) : RegB = ((2 / (α : ℚ) ^ 2 : ℚ) : ℝ) * RegA := by
  have hα : (α : ℝ) ≠ 0 := by exact_mod_cast isogenyIndex_ne_zero h
  have hr := regulator_ratio h hadj
  push_cast
  field_simp
  linear_combination hr

/-- **`Reg_B / Reg_A = 2 / I²`, a rational number** (tex 4088–4090): under the hypotheses of
`regulator_ratio` and `Reg_A ≠ 0`, the ratio of the real regulators is the rational number `2/α²`,
and it is `2/I²` for the index `I = |α| = [B(ℚ)_free : φ A(ℚ)_free]` (the text's form). PROVED. -/
theorem regulator_ratio_div {α β : ℤ} {RegA RegB : ℝ} (h : α * β = 2)
    (hadj : (α : ℝ) * RegB = (β : ℝ) * RegA) (hRegA : RegA ≠ 0) :
    RegB / RegA = ((2 / (α : ℚ) ^ 2 : ℚ) : ℝ) ∧
      RegB / RegA = 2 / ((α.natAbs : ℕ) : ℝ) ^ 2 := by
  have h1 : RegB / RegA = ((2 / (α : ℚ) ^ 2 : ℚ) : ℝ) := by
    rw [regulator_eq_ratCast_mul h hadj, mul_div_assoc, div_self hRegA, mul_one]
  refine ⟨h1, ?_⟩
  rw [h1, Nat.cast_natAbs, Int.cast_abs, sq_abs]
  push_cast
  rfl

/-- **`v₂(Reg_B / Reg_A) = v₂(2/I²) = ±1`** (tex 4088–4090, 4110): the two-adic valuation of
the rational number `2/α²`, which is `Reg_B/Reg_A` by `regulator_ratio_div`. PROVED. -/
theorem padicValRat_regulator_ratio {α β : ℤ} (h : α * β = 2) :
    padicValRat 2 (2 / ((α : ℚ) ^ 2)) = 1 ∨ padicValRat 2 (2 / ((α : ℚ) ^ 2)) = -1 := by
  have hdvd : α ∣ 2 := ⟨β, h.symm⟩
  have hle : α.natAbs ≤ 2 := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    exact Nat.le_of_dvd (by norm_num) this
  have h0 : α ≠ 0 := by rintro rfl; simp at h
  have hcases : α = 1 ∨ α = -1 ∨ α = 2 ∨ α = -2 := by omega
  have h22 : padicValRat 2 (2 : ℚ) = 1 := by simpa using padicValRat.self (p := 2) (by norm_num)
  rcases hcases with rfl | rfl | rfl | rfl
  · left; norm_num [h22]
  · left; norm_num [h22]
  · right
    rw [show ((2 : ℤ) : ℚ) ^ 2 = 2 * 2 by norm_num, div_mul_eq_div_div, div_self (by norm_num),
      padicValRat.div (by norm_num) (by norm_num), padicValRat.one, h22]
    norm_num
  · right
    rw [show ((-2 : ℤ) : ℚ) ^ 2 = 2 * 2 by norm_num, div_mul_eq_div_div, div_self (by norm_num),
      padicValRat.div (by norm_num) (by norm_num), padicValRat.one, h22]
    norm_num

/-- **The two-adic isogeny identity at the real regulators** (tex 4082–4112). Milne's identity for
real regulators `Reg_A ≠ 0`, `Reg_B` related by the height adjunction on generators
(`α Reg_B = β Reg_A`, `αβ = 2`, as in `regulator_ratio`), periods `Ω_A ≠ 0`, `Ω_B = ρ_Ω Ω_A`, and
self-dual torsion counts, gives
`s_A − s_B = 2g_A − 2g_B + v₂(2/α²) + v₂ ρ_Ω + v₂(C_B/C_A)` with `2/α² = Reg_B/Reg_A`
(`regulator_ratio_div`) and `v₂(2/α²) = ±1` (`padicValRat_regulator_ratio`). The regulator ratio
enters as the rational number derived from the adjunction, not as an input; the regulators
themselves are arbitrary reals (see `regulator_hypotheses_satisfiable`). PROVED, from Milne's print
(`MilneIsogenyInvariance`) through `milne_valuation_form`. -/
theorem milne_valuation_form_of_adjunction {shaA shaB tA tB CA CB : ℕ} {RegA RegB ΩA : ℝ}
    {ρΩ : ℚ} {α β : ℤ} (hαβ : α * β = 2) (hadj : (α : ℝ) * RegB = (β : ℝ) * RegA)
    (hshaA : shaA ≠ 0) (hshaB : shaB ≠ 0) (htA : tA ≠ 0) (htB : tB ≠ 0) (hCA : CA ≠ 0)
    (hCB : CB ≠ 0) (hRegA : RegA ≠ 0) (hΩA : ΩA ≠ 0) (hρΩ : ρΩ ≠ 0)
    (h : MilneIsogenyInvariance shaA shaB tA tA tB tB CA CB RegA RegB ΩA ((ρΩ : ℝ) * ΩA)) :
    (padicValNat 2 shaA : ℤ) - padicValNat 2 shaB =
        2 * (padicValNat 2 tA : ℤ) - 2 * padicValNat 2 tB + padicValRat 2 (2 / (α : ℚ) ^ 2) +
          padicValRat 2 ρΩ + padicValRat 2 ((CB : ℚ) / CA) ∧
      (padicValRat 2 (2 / (α : ℚ) ^ 2) = 1 ∨ padicValRat 2 (2 / (α : ℚ) ^ 2) = -1) := by
  have hα : (α : ℚ) ≠ 0 := by exact_mod_cast isogenyIndex_ne_zero hαβ
  have hρ0 : (2 / (α : ℚ) ^ 2) ≠ 0 := div_ne_zero two_ne_zero (pow_ne_zero 2 hα)
  rw [regulator_eq_ratCast_mul hαβ hadj] at h
  exact ⟨milne_valuation_form hshaA hshaB htA htB hCA hCB hRegA hΩA hρ0 hρΩ h,
    padicValRat_regulator_ratio hαβ⟩

/-- **Non-vacuity of the regulator hypotheses, with an irrational regulator** (PROVED). The
hypotheses of `regulator_ratio`, `regulator_eq_ratCast_mul`, `regulator_ratio_div` and
`milne_valuation_form_of_adjunction` are jointly satisfiable with `Reg_A = π`: `α = 1`, `β = 2`,
`Reg_B = 2π`, `Ω_A = 1`, `ρ_Ω = 1`, `|Ш(A)| = 2`, every other order `1`, and Milne's identity
`2 · π · 1 · 1 / (1 · 1) = 1 · 2π · 1 · 1 / (1 · 1)`. So the real carrier is genuinely used: the
regulators are not forced to be rational, only their ratio is. -/
theorem regulator_hypotheses_satisfiable :
    ∃ (α β : ℤ) (RegA RegB : ℝ), α * β = 2 ∧ (α : ℝ) * RegB = (β : ℝ) * RegA ∧ RegA ≠ 0 ∧
      Irrational RegA ∧
      MilneIsogenyInvariance 2 1 1 1 1 1 1 1 RegA RegB 1 (((1 : ℚ) : ℝ) * 1) := by
  refine ⟨1, 2, Real.pi, 2 * Real.pi, by norm_num, by push_cast; ring, Real.pi_ne_zero,
    irrational_pi, ?_⟩
  simp only [MilneIsogenyInvariance]
  push_cast
  ring

/-! ### Pullbacks and the period ratio -/

/-- **`ab = 4 ⇒ a ∈ {±1, ±2, ±4}`** (tex 4093–4096). PROVED. -/
theorem pullback_values {a b : ℤ} (h : a * b = 4) :
    a = 1 ∨ a = -1 ∨ a = 2 ∨ a = -2 ∨ a = 4 ∨ a = -4 := by
  have hdvd : a ∣ 4 := ⟨b, h.symm⟩
  have hle : a.natAbs ≤ 4 := Nat.le_of_dvd (by norm_num) (Int.natAbs_dvd_natAbs.mpr hdvd)
  have h0 : a ≠ 0 := by rintro rfl; simp at h
  have h3 : a ≠ 3 := by rintro rfl; omega
  have h3' : a ≠ -3 := by rintro rfl; omega
  omega

/-- `v₂ x ≤ 2` for `1 ≤ x ≤ 4`. PROVED. -/
theorem padicValNat_le_two_of_le_four {x : ℕ} (h1 : 1 ≤ x) (h4 : x ≤ 4) :
    padicValNat 2 x ≤ 2 := by
  by_contra hc
  rw [not_le] at hc
  have hd : 2 ^ padicValNat 2 x ∣ x := pow_padicValNat_dvd
  have hle : 2 ^ padicValNat 2 x ≤ x := Nat.le_of_dvd (by omega) hd
  have h8 : 2 ^ 3 ≤ 2 ^ padicValNat 2 x := Nat.pow_le_pow_right (by norm_num) hc
  omega

/-- **The period ratio has bounded two-adic valuation** (tex 4096–4104): with
`|a| Ω_A = (κ/γ) Ω_B` (`κ = |ker φ_ℝ|`, `γ = |coker φ_ℝ|`, both in `[1, 4]`) and
`a ∈ {±1, ±2, ±4}`, the rational ratio `Ω_B / Ω_A = |a| γ / κ` has `|v₂| ≤ 4`. PROVED. -/
theorem padicValRat_period_ratio {a : ℤ} {γ κ : ℕ} {ΩA ΩB : ℝ} (hΩA : ΩA ≠ 0)
    (ha : a = 1 ∨ a = -1 ∨ a = 2 ∨ a = -2 ∨ a = 4 ∨ a = -4)
    (hγ : 1 ≤ γ ∧ γ ≤ 4) (hκ : 1 ≤ κ ∧ κ ≤ 4)
    (hcv : (|a| : ℝ) * ΩA = ((κ : ℝ) / γ) * ΩB) :
    ΩB / ΩA = (((a.natAbs * γ : ℕ) : ℚ) / κ : ℚ) ∧
      |padicValRat 2 (((a.natAbs * γ : ℕ) : ℚ) / κ)| ≤ 4 := by
  have hγ0 : (γ : ℝ) ≠ 0 := by exact_mod_cast (show γ ≠ 0 by omega)
  have hκ0 : (κ : ℝ) ≠ 0 := by exact_mod_cast (show κ ≠ 0 by omega)
  have habs : (|(a : ℝ)|) = ((a.natAbs : ℕ) : ℝ) := by simp [Nat.cast_natAbs]
  refine ⟨?_, ?_⟩
  · have hmul : (κ : ℝ) / γ * ΩB * γ = κ * ΩB := by field_simp
    have hcv' : ((a.natAbs : ℕ) : ℝ) * ΩA * γ = κ * ΩB := by
      rw [← hmul, ← hcv, habs]
    push_cast
    rw [div_eq_div_iff hΩA hκ0]
    linear_combination (-1 : ℝ) * hcv'
  · have hA : 1 ≤ a.natAbs ∧ a.natAbs ≤ 4 := by omega
    have hAg : (a.natAbs * γ : ℕ) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    rw [padicValRat.div (by exact_mod_cast hAg) (by exact_mod_cast (show κ ≠ 0 by omega)),
      padicValRat.of_nat, padicValRat.of_nat, padicValNat.mul (by omega) (by omega)]
    have v1 := padicValNat_le_two_of_le_four hA.1 hA.2
    have v2 := padicValNat_le_two_of_le_four hγ.1 hγ.2
    have v3 := padicValNat_le_two_of_le_four hκ.1 hκ.2
    rw [abs_le]
    constructor <;> omega

/-! ### The component numbers -/

/-- **`v₂(C_B / C_A) = Σ_{p ∣ k} t_p`** (tex 4118–4135): over a finite set `S` of primes, with
`c_p(A) = c_p(B)` at every `p ∉ T` (cancellation at split primes, `1` at good primes),
`c_p(A) = 1` at `p ∈ T` (connected special fiber of the Weil restriction) and
`c_p(B) = 2^{t_p}` at `p ∈ T = {p ∣ k}` (Edixhoven: `Φ(E₀^{(k)}) ≅ Ẽ₀[2]`). PROVED. -/
theorem padicValRat_component_ratio {S T : Finset ℕ} (hTS : T ⊆ S) (cA cB t : ℕ → ℕ)
    (hpos : ∀ p ∈ S, 0 < cA p) (hcancel : ∀ p ∈ S, p ∉ T → cA p = cB p)
    (hA1 : ∀ p ∈ T, cA p = 1) (hB : ∀ p ∈ T, cB p = 2 ^ t p) :
    padicValRat 2 ((∏ p ∈ S, (cB p : ℚ)) / ∏ p ∈ S, (cA p : ℚ)) = ∑ p ∈ T, (t p : ℤ) := by
  classical
  have hratio : (∏ p ∈ S, (cB p : ℚ)) / ∏ p ∈ S, (cA p : ℚ) = 2 ^ (∑ p ∈ T, t p) := by
    rw [← Finset.prod_div_distrib, ← Finset.prod_sdiff hTS]
    have h1 : ∏ p ∈ S \ T, (cB p : ℚ) / cA p = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      obtain ⟨hpS, hpT⟩ := Finset.mem_sdiff.mp hp
      rw [← hcancel p hpS hpT, div_self]
      exact_mod_cast (hpos p hpS).ne'
    have h2 : ∏ p ∈ T, (cB p : ℚ) / cA p = ∏ p ∈ T, (2 : ℚ) ^ t p := by
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [hA1 p hp, hB p hp]; push_cast; ring
    rw [h1, h2, one_mul, Finset.prod_pow_eq_pow_sum]
  have h22 : padicValRat 2 (2 : ℚ) = 1 := by simpa using padicValRat.self (p := 2) (by norm_num)
  rw [hratio, padicValRat.pow 2, h22, mul_one]
  push_cast; rfl

/-- In the full rational two-torsion case, `c_p(E^{(hk)}) = |E[2]^{Fr_p}| = 4 = 2^{t_p}` with
`t_p = 2` (tex 4036–4040, 4136). PROVED. -/
theorem tp_eq_two {c : ℕ} (h : c = 4) : c = 2 ^ 2 := by rw [h]; norm_num

/-! ### The torsion and local contributions -/

/-- The sign rule (tex 4058–4060): a torsion disk with cokernel of length `e` in degree `i`
contributes `(−1)^{i+1} e` to the inverse determinant coordinate. -/
def diskContribution (i : ℕ) (e : ℤ) : ℤ := (-1) ^ (i + 1) * e

/-- **The Kummer torsion contributes `2g_A − s_A`** (tex 4054–4064): lengths `g_A, s_A, g_A` in
degrees one, two, three. PROVED. -/
theorem torsion_contribution (gA sA : ℤ) :
    diskContribution 1 gA + diskContribution 2 sA + diskContribution 3 gA = 2 * gA - sA := by
  simp [diskContribution]; ring

/-- **The local quotients contribute `−2 v₂ N_i − 4ω(h)`** (tex 4066–4078): two places above the
moving prime with degree-two length `v₂ N_i`, and two places above each of the `ω(h)` active
primes with degree-two length `2`. PROVED. -/
theorem local_contribution (vN ω : ℤ) :
    2 * diskContribution 2 vN + ω * (2 * diskContribution 2 2) = -2 * vN - 4 * ω := by
  simp [diskContribution]; ring

/-! ### (4.6) -/

/-- **The calibration (4.6), with its explicit error** (tex 4044–4047, 4051–4140). Inputs (all
integers): `j = j_rc(h,k)`; `vL = v₂ L`, `vm = v₂ m_i`, `vN = v₂ N_i`; the class and functional
free coefficients have valuation `j + vL + vm` each; `hprim`: the primitive coordinate's valuation
is the sum of the class, functional, Kummer torsion and local quotient contributions
(ELLIOT: determinant multiplicativity in the support triangles, tex 4058–4078); `hvN`:
`v₂ N_i = v₂ m_i` (PROVED as `padicValInt_movingNorm`); `hMilne`: Cassels' isogeny invariance
(PRINT, Milne ADT I.7.3 (7.3.1)); `hsB`: `s_B = s(h) + s(hk)`; `hReg`, `hΩ`, `hvC`: the three
ratios computed above; `hgB`: `0 ≤ g_B ≤ G₀` (ELLIOT, tex 4114–4115). Conclusion:
`v₂ u_prim(0) = 2j − 4ω(h) − s(h) − s(hk) − Σ t_p + ε` with
`ε = 2 v₂L + 2 g_B − v₂(Reg_B/Reg_A) − v₂(Ω_B/Ω_A)` and `|ε| ≤ 2 v₂L + 2G₀ + 5`; the bound does not
depend on `h` or `k`. PROVED. -/
theorem calibration_46 {j vL vm vN ω gA sA gB sB sh shk vReg vΩ vC T vprim G₀ : ℤ}
    (hprim : vprim = (j + vL + vm) + (j + vL + vm) +
      (diskContribution 1 gA + diskContribution 2 sA + diskContribution 3 gA) +
      (2 * diskContribution 2 vN + ω * (2 * diskContribution 2 2)))
    (hvN : vN = vm) (hMilne : sA - sB = 2 * gA - 2 * gB + vReg + vΩ + vC)
    (hsB : sB = sh + shk) (hvC : vC = T) (hReg : vReg = 1 ∨ vReg = -1) (hΩ : |vΩ| ≤ 4)
    (hgB : 0 ≤ gB ∧ gB ≤ G₀) (hvL : 0 ≤ vL) :
    vprim = 2 * j - 4 * ω - sh - shk - T + (2 * vL + 2 * gB - vReg - vΩ) ∧
      |2 * vL + 2 * gB - vReg - vΩ| ≤ 2 * vL + 2 * G₀ + 5 := by
  rw [torsion_contribution, local_contribution] at hprim
  refine ⟨by rw [hprim]; linarith, ?_⟩
  rw [abs_le] at hΩ ⊢
  rcases hReg with h | h <;> constructor <;> linarith [hgB.1, hgB.2, hΩ.1, hΩ.2]

end ZInQ.Manuscript.RC.Central
