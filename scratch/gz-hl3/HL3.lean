import ZInQKernel.Contrib.GZDecomp.Decomp
import ZInQKernel.Contrib.GZStatements.Hensel
import ZInQKernel.Contrib.TYZGenus.CM
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.CanonicalHeight.Basic
import Mathlib.NumberTheory.Height.NumberField

/-!
# gz-hl3: `GZDecomp.GrossZagierHeegner` from the Gross–Zagier formula, Gross's conjugation
relation and the Heegner point over genuine definitions

Draft (scratch). See `docs/research/gz-hl3.md`.
-/

noncomputable section

open UpperHalfPlane HeckeRing.GL2 WeierstrassCurve ZInQ.GZDecomp
open ZInQ.Contrib.TYZGenus.CM (HeegnerForm)
open scoped WeierstrassCurve.Affine

namespace ZInQ.GZHL3

/-! ## §1. Objects -/

/-- **The Eichler integral** `φ_f(τ) = 2πi ∫_{i∞}^{τ} f(z) dz = Σ_{n ≥ 1} aₙ(f)/n · e^{2πinτ}` of a
weight-2 newform. -/
def eichler {N : ℕ} [NeZero N] (f : Newform N 2) (τ : ℍ) : ℂ :=
  ∑' n : ℕ, coeff f (n + 1) / ((n : ℂ) + 1) *
    Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * (τ : ℂ))

/-- **`c · Λ_f ⊆ L`**, where `Λ_f = {φ_f(γτ) − φ_f(τ) : γ ∈ Γ₀(N)}` is the period lattice of
`2πi f(τ) dτ` (independent of `τ`): `z ↦ c z` induces `Γ₀(N)\ℍ → ℂ/L`, `τ ↦ c φ_f(τ)`. -/
def PeriodsIn {N : ℕ} [NeZero N] (f : Newform N 2) (c : ℂ) (L : PeriodPair) : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ : ℍ, c * (eichler f (γ • τ) - eichler f τ) ∈ L.lattice

/-- **`L` is the period lattice of `E` over `ℂ`** (for the invariant differential
`dx/(2y + a₁x + a₃)` of the given model): `g₂(L) = c₄/12`, `g₃(L) = c₆/216`, i.e.
`(x, y) = (℘_L(z) − b₂/12, (℘'_L(z) − a₁x − a₃)/2)` maps `ℂ/L` onto `E(ℂ)`. -/
def IsPeriodLattice (E : WeierstrassCurve ℚ) (L : PeriodPair) : Prop :=
  L.g₂ = (E⁄ℂ).c₄ / 12 ∧ L.g₃ = (E⁄ℂ).c₆ / 216

open Classical in
/-- **The point of `E(ℂ)` with parameter `z ∈ ℂ/L`**: `(℘_L(z) − b₂/12, (℘'_L(z) − a₁x − a₃)/2)`,
and `O` for `z ∈ L` (for `IsPeriodLattice E L` the `else` branch is only taken at `z ∈ L`:
`weierPt_some`). -/
def weierPt (E : WeierstrassCurve ℚ) (L : PeriodPair) (z : ℂ) : (E⁄ℂ).Point :=
  if h : z ∉ L.lattice ∧ (E⁄ℂ).Nonsingular (L.weierstrassP z - (E⁄ℂ).b₂ / 12)
      ((L.derivWeierstrassP z - (E⁄ℂ).a₁ * (L.weierstrassP z - (E⁄ℂ).b₂ / 12) - (E⁄ℂ).a₃) / 2)
  then .some _ _ h.2 else 0

/-- `Q = [A, B, C]` has **residue `β`**: `B ≡ β (mod 2N)`. -/
def HasResidue {N : ℕ} {D : ℤ} (β : ℤ) (Q : HeegnerForm N D) : Prop := (2 * N : ℤ) ∣ Q.B - β

/-- `τ_Q` and `τ_{Q'}` are **`Γ₀(N)`-equivalent**. -/
def Gamma0Equiv {N : ℕ} {D : ℤ} (Q Q' : HeegnerForm N D) : Prop :=
  ∃ γ ∈ CongruenceSubgroup.Gamma0 N, γ • Q.tauH = Q'.tauH

/-- **A complete set of representatives of the Heegner points of discriminant `D` and residue
`β`**: forms `[A, B, C]`, `N ∣ A`, `B ≡ β (mod 2N)`, `B² − 4AC = D`, one in each
`Γ₀(N)`-class. -/
def IsHeegnerReps (N : ℕ) (D β : ℤ) (S : Finset (HeegnerForm N D)) : Prop :=
  (∀ Q ∈ S, HasResidue β Q) ∧
    ∀ Q : HeegnerForm N D, HasResidue β Q → ∃! Q', Q' ∈ S ∧ Gamma0Equiv Q Q'

/-- **The Heegner point `y_K = Σ_{σ ∈ Gal(H/K)} φ(x₁)^σ` in `E(ℂ)`**, for the parametrization
`φ(τ) = weierPt E L (c φ_f(τ))`: `Σ_{Q ∈ S} φ(τ_Q)`. -/
def heegnerC (E : WeierstrassCurve ℚ) (L : PeriodPair) {N : ℕ} [NeZero N] (f : Newform N 2)
    (c : ℂ) {D : ℤ} (S : Finset (HeegnerForm N D)) : (E⁄ℂ).Point :=
  ∑ Q ∈ S, weierPt E L (c * eichler f Q.tauH)

/-! ## §2. The leaves -/

/-- **Uniformization.** For `a, b ∈ ℂ` with `a³ − 27b² ≠ 0` there is a lattice `L` with
`g₂(L) = a`, `g₃(L) = b`. Silverman, *The Arithmetic of Elliptic Curves* (GTM 106, 2nd ed.),
Thm VI.5.1 (UNVERIFIED number); Serre, *A Course in Arithmetic*, VII Prop. 5 / §3 (UNVERIFIED). -/
def WeierstrassUniformization : Prop :=
  ∀ a b : ℂ, a ^ 3 - 27 * b ^ 2 ≠ 0 → ∃ L : PeriodPair, L.g₂ = a ∧ L.g₃ = b

/-- **Modular parametrization (Eichler–Shimura, with Faltings' isogeny theorem), in analytic form.**
If `E/ℚ` has the L-series of a weight-2 newform `f` of level `N` and trivial character, and `L` is
the period lattice of `E`, there is a real `c ≠ 0` with `c Λ_f ⊆ L`.

Content: `Λ_f` is a lattice and `ℂ/Λ_f ≅ E_f(ℂ)` for the strong Weil curve `E_f/ℚ`, a quotient of
`J₀(N)` with `L(E_f) = L(f)` (Shimura, *Introduction to the arithmetic theory of automorphic
functions*, 1971, Thm 7.14–7.15, UNVERIFIED); `E` is `ℚ`-isogenous to `E_f` (Faltings, Invent. Math.
73 (1983), Korollar 2, UNVERIFIED; for CM curves Shimura, Nagoya Math. J. 43 (1971)); a
`ℚ`-isogeny `ℂ/Λ_f → ℂ/L` is `z ↦ c z` with `c` real (it commutes with complex conjugation). -/
def EichlerShimuraParam : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
    ∀ L : PeriodPair, IsPeriodLattice E L → ∃ c : ℝ, c ≠ 0 ∧ PeriodsIn f c L

/-- **Rationality of the Heegner point (Shimura's reciprocity law for CM points; Gross).**
In the Heegner setting (`E`, `f`, `D`, `β` with `β² ≡ D (mod 4N)`, a complete set `S` of
representatives of the Heegner points of discriminant `D` and residue `β`, a `ℚ`-rational
parametrization `τ ↦ weierPt E L (c φ_f(τ))`, `c` real), the point
`Σ_{Q ∈ S} φ(τ_Q) ∈ E(ℂ)` is the image of a point of `E(K)`, `K = ℚ(√D)` embedded by
`√D ↦ i√|D|`: it is the trace `y_K = Tr_{H/K} φ(x₁)` of the Heegner point `x₁ = (𝒪_K, 𝔫, [𝒪_K])`,
`𝔫 = (N, (β + √D)/2)`, since `Gal(H/K) ≅ Cl(K)` permutes the `h(D)` Heegner points of residue `β`
simply transitively.

Sources: B. Gross, *Heegner points on X₀(N)*, in *Modular forms* (Durham 1983), Ellis Horwood
1984, §1–§3 (UNVERIFIED); Gross–Zagier, Invent. Math. 84 (1986), Ch. II §1 and Ch. V §1
(UNVERIFIED); Shimura 1971, Thm 5.4 and §6.8 (UNVERIFIED). -/
def HeegnerPointRational : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
    ∀ D β : ℤ, IsOddImagFundDisc D → D < -4 → HeegnerHyp N D → (4 * N : ℤ) ∣ D - β ^ 2 →
    ∀ S : Finset (HeegnerForm N D), IsHeegnerReps N D β S →
    ∀ (L : PeriodPair) (c : ℝ), IsPeriodLattice E L → c ≠ 0 → PeriodsIn f c L →
    ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K], Module.finrank ℚ K = 2 →
    ∀ δ : K, δ ^ 2 = (D : K) →
    ∀ ι : K →ₐ[ℚ] ℂ, ι δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) →
      ∃ y : (E⁄K).Point, Affine.Point.map ι y = heegnerC E L f c S

/-- **The Gross–Zagier formula (Ch. V form, constant forgotten).** In the Heegner setting, let
`y ∈ E(K)` be the Heegner point (`ι(y) = Σ_{Q ∈ S} φ(τ_Q)`), and let `F`, `G` be the entire
continuations of `L(f, s) = L(E, s)` and of `L(f ⊗ χ_D, s)`, so that `F G` is
`L(E/K, s) = L(E, s) L(E^D, s)`. Then `L'(E/K, 1) = κ · ĥ(y)` for some real `κ > 0`.

Source: B. Gross, D. Zagier, *Heegner points and derivatives of L-series*, Invent. Math. 84 (1986),
225–320, Thm I.6.3 (for the `f`-component `c_f` of the Heegner divisor in `J₀(N)`) and Ch. V,
Thm 2.1 (for `E`): `L'(E/K, 1) = ‖ω‖² ĥ(y_K) / (c² u² √|D|)`-type formula with an explicit
positive constant (UNVERIFIED numbers and constant). The printed constant is replaced by `∃ κ > 0`
(the normalization of the height here, Tau Ceti's `canonicalHeight` over `K`, is a positive
multiple of the one in the print), so this is a consequence of the printed theorem; the identity
`L(E/K, s) = L(f, s) L(f ⊗ χ_D, s)` (GZ I.(6.?) UNVERIFIED) is folded in. -/
def GrossZagierFormula : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
    ∀ D β : ℤ, IsOddImagFundDisc D → D < -4 → HeegnerHyp N D → (4 * N : ℤ) ∣ D - β ^ 2 →
    ∀ S : Finset (HeegnerForm N D), IsHeegnerReps N D β S →
    ∀ (L : PeriodPair) (c : ℝ), IsPeriodLattice E L → c ≠ 0 → PeriodsIn f c L →
    ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K], Module.finrank ℚ K = 2 →
    ∀ δ : K, δ ^ 2 = (D : K) →
    ∀ ι : K →ₐ[ℚ] ℂ, ι δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) →
    ∀ y : (E⁄K).Point, Affine.Point.map ι y = heegnerC E L f c S →
    ∀ F G : ℂ → ℂ, IsEntireCont (coeff f) 2 F → IsEntireCont (twistCoeff f D) 2 G →
      ∃ κ : ℝ, 0 < κ ∧ deriv (fun s => F s * G s) 1 = κ * y.canonicalHeight

/-- **Gross's conjugation relation** `ȳ_K = −ε y_K` modulo torsion, `ε` the sign of the functional
equation of `L(E, s)` (`rootNumber f hχ`, the sign in `Λ_N(2 − s) = ε Λ_N(s)`). In the Heegner
setting, with `y ∈ E(K)` the Heegner point and `σ` the nontrivial automorphism of `K`
(`σ(√D) = −√D`): `σ y + y` is torsion if `ε = +1` and `σ y − y` is torsion if `ε = −1`.

Source: B. Gross, *Heegner points on X₀(N)* (1984), §5 (UNVERIFIED): complex conjugation and
`w_N` act on Heegner points by `(𝒪, 𝔫, [𝔞]) ↦ (𝒪, 𝔫̄, [𝔞⁻¹])` resp. `(𝒪, 𝔫̄, [𝔞 𝔫⁻¹])`, and
`φ ∘ w_N = −ε φ + (torsion)`; restated in Gross–Zagier 1986, Ch. V §2 (UNVERIFIED). -/
def GrossConjugation : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2) (hχ : f.χ = 1),
    (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
    ∀ D β : ℤ, IsOddImagFundDisc D → D < -4 → HeegnerHyp N D → (4 * N : ℤ) ∣ D - β ^ 2 →
    ∀ S : Finset (HeegnerForm N D), IsHeegnerReps N D β S →
    ∀ (L : PeriodPair) (c : ℝ), IsPeriodLattice E L → c ≠ 0 → PeriodsIn f c L →
    ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K], Module.finrank ℚ K = 2 →
    ∀ δ : K, δ ^ 2 = (D : K) →
    ∀ ι : K →ₐ[ℚ] ℂ, ι δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) →
    ∀ y : (E⁄K).Point, Affine.Point.map ι y = heegnerC E L f c S →
    ∀ σ : K ≃ₐ[ℚ] K, σ δ = -δ →
      (rootNumber f hχ = 1 → IsOfFinAddOrder (Affine.Point.map σ.toAlgHom y + y)) ∧
      (rootNumber f hχ = -1 → IsOfFinAddOrder (Affine.Point.map σ.toAlgHom y - y))

/-- **(GLUE) Heegner representatives exist**: the Heegner points of discriminant `D` and residue
`β` fall into finitely many `Γ₀(N)`-classes (`h(D)` of them). Gross 1984 §1, GZ II §1
(UNVERIFIED); provable from reduction theory (`SL₂(ℤ)`-classes of forms of discriminant `D` are
finite, `[SL₂(ℤ) : Γ₀(N)] < ∞`). -/
def HeegnerRepsExist : Prop :=
  ∀ (N : ℕ) [NeZero N] (D β : ℤ), IsOddImagFundDisc D → (4 * N : ℤ) ∣ D - β ^ 2 →
    ∃ S : Finset (HeegnerForm N D), IsHeegnerReps N D β S

/-! ## §3. Glue lemmas -/

/-- The discriminant condition of `WeierstrassUniformization` for `(c₄/12, c₆/216)`. -/
theorem disc_ne_zero (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ((E⁄ℂ).c₄ / 12) ^ 3 - 27 * ((E⁄ℂ).c₆ / 216) ^ 2 ≠ 0 := by
  have h := WeierstrassCurve.c_relation (E⁄ℂ)
  have hΔ : (E⁄ℂ).Δ ≠ 0 := (E⁄ℂ).isUnit_Δ.ne_zero
  intro h0
  apply hΔ
  linear_combination (1 / 1728 : ℂ) * h + h0

/-- The period lattice exists (uniformization). -/
theorem exists_isPeriodLattice (hU : WeierstrassUniformization) (E : WeierstrassCurve ℚ)
    [E.IsElliptic] : ∃ L : PeriodPair, IsPeriodLattice E L :=
  hU _ _ (disc_ne_zero E)

/-- `weierPt` is not junk: off the lattice it is the point `(℘ − b₂/12, (℘' − a₁x − a₃)/2)`. -/
theorem weierPt_some (E : WeierstrassCurve ℚ) [E.IsElliptic] {L : PeriodPair}
    (hL : IsPeriodLattice E L) {z : ℂ} (hz : z ∉ L.lattice) :
    (E⁄ℂ).Nonsingular (L.weierstrassP z - (E⁄ℂ).b₂ / 12)
      ((L.derivWeierstrassP z - (E⁄ℂ).a₁ * (L.weierstrassP z - (E⁄ℂ).b₂ / 12) - (E⁄ℂ).a₃) / 2) := by
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular, WeierstrassCurve.Affine.equation_iff]
  have h := L.derivWeierstrassP_sq z hz
  rw [hL.1, hL.2] at h
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆] at h ⊢
  linear_combination (1 / 4 : ℂ) * h

/-- An embedding `ℚ(√D) → ℂ` with `√D ↦ i √|D|`. -/
theorem exists_embedding {K : Type} [Field K] [NumberField K] {D : ℤ} (hD : D < 0) (δ : K)
    (hδ : δ ^ 2 = (D : K)) :
    ∃ ι : K →ₐ[ℚ] ℂ, ι δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) := by
  set w : ℂ := Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) with hw
  have hw2 : w ^ 2 = (D : ℂ) := by
    have h0 : (0 : ℝ) ≤ -(D : ℝ) := by
      have : (D : ℝ) < 0 := by exact_mod_cast hD
      linarith
    rw [hw, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt h0]
    push_cast; ring
  let ι₀ : K →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hz : ι₀ δ ^ 2 = (D : ℂ) := by rw [← map_pow, hδ, map_intCast]
  have hprod : (ι₀ δ - w) * (ι₀ δ + w) = 0 := by linear_combination hz - hw2
  rcases mul_eq_zero.mp hprod with h | h
  · exact ⟨ι₀, sub_eq_zero.mp h⟩
  · refine ⟨ZInQ.Contrib.TYZGenus.CM.conjQ.comp ι₀, ?_⟩
    have : ι₀ δ = -w := eq_neg_of_add_eq_zero_left h
    simp only [AlgHom.comp_apply, this, ZInQ.Contrib.TYZGenus.CM.conjQ, hw]
    simp [Complex.conj_ofReal]

/-- In a quadratic field `ℚ(δ)`, `δ ∉ ℚ`, an automorphism fixing `δ` is the identity. -/
theorem algEquiv_eq_one_of_fix {K : Type} [Field K] [Algebra ℚ K] (hK : Module.finrank ℚ K = 2)
    {δ : K} (hδ : δ ∉ Set.range (algebraMap ℚ K)) (σ : K ≃ₐ[ℚ] K) (hσ : σ δ = δ) : σ = 1 := by
  have hli : LinearIndependent ℚ ![(1 : K), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply hδ
      refine ⟨-s / t, ?_⟩
      have : t • δ = -(s • (1 : K)) := eq_neg_of_add_eq_zero_right hst
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at this
      have ht' : algebraMap ℚ K t ≠ 0 := (map_ne_zero (algebraMap ℚ K)).mpr ht
      rw [map_div₀, map_neg, div_eq_iff ht', ← this]
      ring
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hK])
  have hlin : σ.toLinearMap = LinearMap.id := by
    refine b.ext fun i => ?_
    fin_cases i
    · simp [b, map_one]
    · simp [b, hσ]
  ext x
  have := congrArg (fun g : K →ₗ[ℚ] K => g x) hlin
  simpa using this

/-- A simple zero at `1` has nonzero derivative. -/
theorem deriv_ne_zero_of_order_one {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h1 : analyticOrderAt F 1 = 1) : deriv F 1 ≠ 0 := by
  have hFa : AnalyticAt ℂ F 1 := (Complex.analyticOnNhd_univ_iff_differentiable.mpr hF) 1
    (Set.mem_univ _)
  obtain ⟨g, hga, hg1, hgF⟩ := (hFa.analyticOrderAt_eq_natCast (n := 1)).mp (by exact_mod_cast h1)
  have hd : deriv F 1 = deriv (fun s => (s - 1) * g s) 1 := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hgF] with s hs
    simpa using hs
  rw [hd]
  have : HasDerivAt (fun s => (s - 1) * g s) (1 * g 1 + (1 - 1) * deriv g 1) 1 :=
    ((hasDerivAt_id 1).sub_const 1).mul hga.differentiableAt.hasDerivAt
  rw [this.deriv]
  simpa using hg1

theorem zero_of_order_one {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h1 : analyticOrderAt F 1 = 1) : F 1 = 0 := by
  have hFa : AnalyticAt ℂ F 1 := (Complex.analyticOnNhd_univ_iff_differentiable.mpr hF) 1
    (Set.mem_univ _)
  obtain ⟨g, hga, hg1, hgF⟩ := (hFa.analyticOrderAt_eq_natCast (n := 1)).mp (by exact_mod_cast h1)
  simpa using hgF.self_of_nhds

/-- `L'(E/K, 1) = F'(1) G(1) ≠ 0` when `F` has a simple zero at `1` and `G(1) ≠ 0`. -/
theorem deriv_mul_ne_zero {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (h1 : analyticOrderAt F 1 = 1) (hG1 : G 1 ≠ 0) : deriv (fun s => F s * G s) 1 ≠ 0 := by
  have h : HasDerivAt (fun s => F s * G s) (deriv F 1 * G 1 + F 1 * deriv G 1) 1 :=
    (hF 1).hasDerivAt.mul (hG 1).hasDerivAt
  rw [h.deriv, zero_of_order_one hF h1, zero_mul, add_zero]
  exact mul_ne_zero (deriv_ne_zero_of_order_one hF h1) hG1

/-! ## §4. `GrossZagierHeegner` from the leaves -/

/-- **`GZDecomp.GrossZagierHeegner` from uniformization, the Eichler–Shimura parametrization,
the existence of Heegner representatives, the rationality of the Heegner point, the Gross–Zagier
formula and Gross's conjugation relation** (with the proved glue: `β` by Hensel
(`GZStatements.exists_sq_mod_four_mul_of_heegnerHyp`), the sign of a simple zero
(`GZDecomp.signOfSimpleZero`), `L'(E/K, 1) ≠ 0`, nondegeneracy of `ĥ` on torsion). -/
theorem grossZagierHeegner_of_leaves (hU : WeierstrassUniformization)
    (hES : EichlerShimuraParam) (hR : HeegnerRepsExist) (hHP : HeegnerPointRational)
    (hGZ : GrossZagierFormula) (hGC : GrossConjugation) : GrossZagierHeegner := by
  intro E _ N _ f hχ hf D hDisc hD4 hHeeg F G hF hG h1 hG1 K _ _ instAlg hK2 ⟨δ, hδ⟩
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  obtain rfl : instAlg = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have : FiniteDimensional ℚ K := Module.finite_of_finrank_eq_succ hK2
  have : NumberField K := ⟨⟩
  have hδ' : δ ^ 2 = (D : K) := by rw [hδ]; simp
  obtain ⟨β, hβ⟩ := ZInQ.GZStatements.exists_sq_mod_four_mul_of_heegnerHyp (NeZero.ne N) hDisc hHeeg
  obtain ⟨S, hS⟩ := hR N D β hDisc hβ
  obtain ⟨L, hL⟩ := exists_isPeriodLattice hU E
  obtain ⟨c, hc, hcL⟩ := hES E N f hχ hf L hL
  obtain ⟨ι, hι⟩ := exists_embedding hDisc.1 δ hδ'
  obtain ⟨y, hy⟩ := hHP E N f hχ hf D β hDisc hD4 hHeeg hβ S hS L c hL hc hcL K hK2 δ hδ' ι hι
  refine ⟨y, ?_, ?_⟩
  · -- infinite order: `ĥ(y) ≠ 0` since `L'(E/K, 1) = κ ĥ(y) ≠ 0`
    obtain ⟨κ, -, hκ⟩ := hGZ E N f hχ hf D β hDisc hD4 hHeeg hβ S hS L c hL hc hcL K hK2 δ hδ' ι
      hι y hy F G hF hG
    intro htors
    rw [WeierstrassCurve.Affine.Point.canonicalHeight_eq_zero_of_isOfFinAddOrder htors,
      Complex.ofReal_zero, mul_zero] at hκ
    exact deriv_mul_ne_zero hF.1 hG.1 h1 hG1 hκ
  · intro σ
    have hσ2 : (σ δ - δ) * (σ δ + δ) = 0 := by
      have : σ δ ^ 2 = δ ^ 2 := by rw [← map_pow, hδ', map_intCast]
      linear_combination this
    rcases mul_eq_zero.mp hσ2 with h | h
    · -- `σ = 1`
      have hnr : δ ∉ Set.range (algebraMap ℚ K) := by
        rintro ⟨q, rfl⟩
        have hq : q ^ 2 = (D : ℚ) := by
          apply (algebraMap ℚ K).injective
          rw [map_pow, hδ', map_intCast]
        have : (D : ℚ) < 0 := by exact_mod_cast hDisc.1
        nlinarith [sq_nonneg q]
      have := algEquiv_eq_one_of_fix hK2 hnr σ (sub_eq_zero.mp h)
      subst this
      rw [map_one_apply, sub_self]
      exact IsOfFinAddOrder.zero
    · have hw : rootNumber f hχ = -1 := signOfSimpleZero N f hχ F hF h1
      exact (hGC E N f hχ hf D β hDisc hD4 hHeeg hβ S hS L c hL hc hcL K hK2 δ hδ' ι hι y hy σ
        (eq_neg_of_add_eq_zero_left h)).2 hw

end ZInQ.GZHL3

#print axioms ZInQ.GZHL3.grossZagierHeegner_of_leaves
