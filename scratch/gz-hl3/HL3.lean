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

end ZInQ.GZHL3
