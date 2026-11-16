import ZInQKernel.OneProof.TYZSplit
import ZInQKernel.Contrib.OneProof.ThetaWeierstrass8

/-! h33-dict, part A (scratch test): TYZ Prop. 3.2(4) in its used form, proved from `hCM`, and the
uniformization of `ε` over the representatives `Φ`. -/

noncomputable section

set_option maxRecDepth 8000

namespace ZInQ.Contrib.TYZGenus.H33Dict

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Package
  ZInQ.Contrib.TYZGenus.RingClass ZInQ.PropN NumberField TauCeti.ClassFieldTheory
  TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder ZInQ.RouteK.Rank5b
  ZInQ.Contrib.TYZGenus.CMBridge ZInQ.Contrib.TYZGenus.TYZ35 ZInQ.Contrib.TYZDecomp
  ZInQ.RouteK.Redei ZInQ.Literature ZInQ.Contrib.TYZGenus.TYZSplit

/-! ## §A1. The CM inputs from `hCM` -/

/-- The CM inputs of the TYZ chain (algebraicity, field of definition, Shimura reciprocity on `Pic`) from
the printed main theorem of CM `hCM` and the proved theta identity (theta-wp8, hx-used). -/
theorem cmInputs (hCM : T5Glue.ShimuraMainCM) : X0ModuliUsed.CMInputs :=
  X0ModuliUsed.cmInputs_of (X0EtaRoute.srAt_x ThetaWP8.xEtaWeierstrass hCM)
    (X0EtaRoute.srAt_y ThetaWP8.xEtaWeierstrass hCM)

/-- `Gal(H_{n,4}/H_n)` moves `z_n` only by `ℤτ(1)` (glue KER of the kernel), from the CM inputs. -/
theorem kerFix (h : X0ModuliUsed.CMInputs) : T321.KerFixesZnMod :=
  T321.kerFixesZnMod
    (ZInQ.Contrib.TYZGenus.Shimura.tyzSigmaFixesZn_of h.pic ZInQ.Contrib.TYZGenus.Shimura.etaModelFricke)
    (T321.tyzThm36OneFive_of h.pic h.alg T321.wNegatesI) (X0ModuliUsed.znOverH4_of_field h.field)

/-! ## §A2. Restrictions to `H_n` -/

section General

variable {K : Type} [Field K] [NumberField K]

/-- If the Artin symbol of `c ∈ Pic O` fixes the Hilbert class field, then `c ↦ 1` in `Cl(K)` (stated for a
general `K`: at `K = ℚ(√−n)` the rewrite by `restrict_ringClassArtinEquiv` times out in the kernel). -/
theorem picToMax_eq_one_of_fix (O : NumberFieldOrder K) (c : Pic O)
    (h : ∀ x : ringClassField (maximalNumberFieldOrder K),
      ringClassArtinEquiv O c (IntermediateField.inclusion (ringClassField_maximal_le O) x) =
        IntermediateField.inclusion (ringClassField_maximal_le O) x) :
    picToMax O c = 1 := by
  apply (ringClassArtinEquiv (maximalNumberFieldOrder K)).injective
  rw [map_one]
  ext x
  have e := h x
  rw [← restrictNormalHom_inclusion_apply, restrict_ringClassArtinEquiv] at e
  have e' := (IntermediateField.inclusion (ringClassField_maximal_le O)).injective e
  rw [e']
  rfl

end General

section Restr

variable {n : ℕ} [NeZero n]

theorem restricts_inv_mul {ρ ρ' : GalQ} {t : ClG n} (h : Restricts n ρ t) (h' : Restricts n ρ' t) :
    Restricts n (ρ'⁻¹ * ρ) 1 := by
  intro x
  rw [AlgEquiv.mul_apply, h x, ← h' x]
  simp

theorem restricts_agree {ρ ρ' : GalQ} {t : ClG n} (h : Restricts n ρ t) (h' : Restricts n ρ' t) :
    ∀ x ∈ hilbertBar n, ρ x = ρ' x := by
  intro x hx
  rw [hilbertBar_eq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 := h ⟨y, hy⟩
  have h2 := h' ⟨y, hy⟩
  change ρ (embed n y) = ρ' (embed n y)
  exact h1.trans h2.symm

/-- **An automorphism acting trivially on `H_n` and as `a ∈ Pic(𝒪_{n,4})` on `H_{n,4}` has `a ↦ 1` in
`Cl(K_n)`** (compatibility of the Artin maps, ring-class's `restrict_ringClassArtinEquiv`). -/
theorem picToMax_eq_one {σ : GalQ} (h1 : Restricts n σ 1) {a : Pic (O4 n)} (ha : ActsAsArtin4 σ n a) :
    picToMax (O4 n) a = 1 := by
  have hle := ringClassField_maximal_le (O4 n)
  refine picToMax_eq_one_of_fix (O4 n) a fun x => ?_
  have hc : ((IntermediateField.inclusion hle x : H4 n) : SeparableClosure (QNeg n)) =
      ((x : hilbertField n) : SeparableClosure (QNeg n)) := IntermediateField.coe_inclusion hle x
  have e1 := ha (IntermediateField.inclusion hle x)
  have e2 : σ (embed n ((x : hilbertField n) : SeparableClosure (QNeg n))) =
      embed n ((x : hilbertField n) : SeparableClosure (QNeg n)) := by
    rw [h1 x, AlgEquiv.one_apply]
  rw [hc] at e1
  apply Subtype.ext
  rw [hc]
  exact (embed n).injective (e1.symm.trans e2)

end Restr

/-! ## §A3. TYZ Proposition 3.2(4), used form -/

theorem tauG_two_eq : tauG 2 = pt00 := by
  rw [← one_add_one_eq_two, map_add, tauG_apply, one_smul, ptT_add_self]

theorem tauG_two_tors : IsOfFinAddOrder (tauG 2) :=
  isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2, by norm_num, by rw [two_nsmul, tauG_two_eq, pt00_add_self]⟩

/-- **TYZ Proposition 3.2(4), the form the uniformization of `ε` uses**: for squarefree `n ≡ 5, 7 (mod 8)`
two lifts `ρ, ρ' ∈ Gal(ℚ̄/ℚ)` of the same `t ∈ Cl_n = Gal(H_n/K_n)` move `z_n` (`TYZ35.basePt n`) to
points that differ by a torsion point. TYZ Prop. 3.2(4) (`CM point1`, arXiv:1411.4728v1 about L1261, as
quoted in tyz-split.md and in the docstring of `TYZSplit.IsPhi`: `2z_n ∈ A(H_n)`) gives it at once; here it
is proved from the CM inputs: `Gal(H_{n,4}/H_n)` moves `z_n` by `ℤτ(1)` for `n ≡ 5` (kernel glue KER, from
Shimura reciprocity, TYZ Thm 3.6(1) in Lean and `z_n ∈ A(H_{n,4})`), and `z_n ∈ A(H_n)` for `n ≡ 7`. -/
def TYZProp324Used : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, Squarefree n → (n % 8 = 5 ∨ n % 8 = 7) → ∀ (t : ClG n) (ρ ρ' : GalQ),
    Restricts n ρ t → Restricts n ρ' t → IsOfFinAddOrder (galPt ρ (basePt n) - galPt ρ' (basePt n))

theorem tyzProp324Used_of (h : X0ModuliUsed.CMInputs) : TYZProp324Used := by
  intro n hn0 hsq hn8 t ρ ρ' hρ hρ'
  rcases hn8 with h5 | h7
  · have hb : basePt n = tyzZn n := by simp [basePt, h5]
    rw [hb]
    have hσ := restricts_inv_mul hρ hρ'
    have hω : (ρ'⁻¹ * ρ) (T321.omegaBar n) = T321.omegaBar n :=
      restricts_fix_sqrt_negn hσ T321.omegaBar_sq
    obtain ⟨a, ha⟩ := T321.exists_acts4_of_fix hω
    have hpa := picToMax_eq_one hσ ha
    obtain ⟨j, hj⟩ := kerFix h n hn0 h5 hsq a hpa _ ha
    have hρe : ρ = ρ' * (ρ'⁻¹ * ρ) := by group
    have : galPt ρ (tyzZn n) - galPt ρ' (tyzZn n) = j • tauG 2 := by
      conv_lhs => rw [hρe, galPt_mul, hj, map_add, map_zsmul, T321.galPt_tauG_two]
      abel
    rw [this]
    exact tauG_two_tors.zsmul
  · have hb : basePt n = tyzZ7 n := by
      have : n % 8 ≠ 5 := by omega
      simp [basePt, this]
    rw [hb]
    have hz := cmFieldOfDefinition7_of h.field n h7 hsq
    rw [galPt_congr (restricts_agree hρ hρ') hz, sub_self]
    exact IsOfFinAddOrder.zero


/-! ## §C. The eta model at the cusps (temporary) -/

/-- Pole bounds of x0-32's `x`: at most a double pole at `∞`, bounded at every other cusp. -/
def EtaCuspBounds : Prop :=
  ((fun τ : UpperHalfPlane => X0.xC τ) =O[UpperHalfPlane.atImInfty]
      fun τ => Real.exp (4 * Real.pi * τ.im)) ∧
    ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ¬ (32 : ℤ) ∣ γ 1 0 →
      UpperHalfPlane.IsBoundedAtImInfty (fun τ : UpperHalfPlane => X0.xC (γ • τ : UpperHalfPlane))

theorem etaCuspBounds : EtaCuspBounds := sorry

/-- `x` is unbounded at `∞` (`|x(it)| → ∞`, x0-32's `tendsto_norm_xC_atTop`). -/
theorem not_bounded_xC : ¬ UpperHalfPlane.IsBoundedAtImInfty (fun τ : UpperHalfPlane => X0.xC τ) := by
  intro hb
  obtain ⟨M, A, hMA⟩ := UpperHalfPlane.isBoundedAtImInfty_iff.1 hb
  obtain ⟨t, ht⟩ := ((X0.tendsto_norm_xC_atTop.eventually_gt_atTop M).and
    (Filter.eventually_ge_atTop (max A 1))).exists
  have htpos : 0 < t := lt_of_lt_of_le one_pos ((le_max_right A 1).trans ht.2)
  have hτ : 0 < ((t : ℂ) * Complex.I).im := by simpa using htpos
  have := hMA ⟨(t : ℂ) * Complex.I, hτ⟩ (by
    show A ≤ ((t : ℂ) * Complex.I).im
    simpa using (le_max_left A 1).trans ht.2)
  exact absurd this (not_le.2 ht.1)

/-! ## §B1. Theorem 3.3 with `ε` chosen after `Φ` and `χ` (the printed quantifier order) -/

/-- `P_χ = Σ_{t ∈ Φ} χ(t) z_n^t` for an arbitrary family `z` of CM points (`PchiG` is `PchiGWith basePt`). -/
def PchiGWith (z : ℕ → PtA) (n : ℕ) [NeZero n] (φ : ClG n → GalQ) (χ : ClG n →* ℤˣ) : PtA :=
  ∑ t : ClG n, ((χ t : ℤˣ) : ℤ) • galPt (φ t) (z n)

theorem pchiGWith_basePt {n : ℕ} [NeZero n] (φ : ClG n → GalQ) (χ : ClG n →* ℤˣ) :
    PchiGWith basePt n φ χ = PchiG n φ χ := rfl

/-- **TYZ's class of `ε(d₀, d₁)`** (L1308–1309): `±i` on `(d₀, d₁) ≡ (5, 3) (mod 8)`, `±1` otherwise. -/
def EpsClass (d₀ d₁ : ℕ) (e : GaussianInt) : Prop :=
  (d₀ % 8 = 5 ∧ d₁ % 8 = 3 → e = gi ∨ e = -gi) ∧ (¬ (d₀ % 8 = 5 ∧ d₁ % 8 = 3) → e = 1 ∨ e = -1)

/-- **TYZ Theorem 3.3 for a family `z` of CM points, in the printed quantifier order**: as
`TYZSplit.TYZThm33` (with `basePt` replaced by `z`), except that `ε(d₀, d₁)` is chosen after the set of
representatives `Φ` and the character `χ` (TYZ fix `Φ` at L1279 before stating the theorem, so their
`ε(d₀, d₁)` may a priori depend on `Φ`). -/
def TYZThm33EpsAfter (z : ℕ → PtA) : Prop :=
  ∀ ℓ : ℕ → ℤ, (∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ℓ m : ℂ)) ^ 2 = lcalSq m) →
  ∃ (Q : ℕ → PtA) (m : ℕ → ℕ),
    (∀ d, 0 < m d) ∧ (∀ d, InMinus d (Q d)) ∧
    (∀ d : ℕ, Squarefree d → (d % 8 = 5 ∨ d % 8 = 6 ∨ d % 8 = 7) →
      (¬ ∃ F : ℂ → ℂ, IsLContinuation (ZInQ.Contrib.TYZDecomp.curveC d) F ∧ analyticOrderAt F 1 ≤ 1) →
        IsOfFinAddOrder (Q d)) ∧
    ∀ n : ℕ, ∀ _ : NeZero n, Squarefree n → (n % 8 = 5 ∨ n % 8 = 7) →
      ∀ φ : ClG n → GalQ, IsPhi n φ → ∀ χ : ClG n →* ℤˣ,
        (¬ IsOfFinAddOrder (PchiGWith z n φ χ) →
          ∃ d₀ d₁ : ℕ, d₀ * d₁ = n ∧ (d₀ % 8 = 5 ∨ d₀ % 8 = 6 ∨ d₀ % 8 = 7) ∧
            (d₁ % 8 = 1 ∨ d₁ % 8 = 2 ∨ d₁ % 8 = 3) ∧ IsChiPair n d₁ χ) ∧
        ∀ d₀ d₁ : ℕ, d₀ * d₁ = n → (d₀ % 8 = 5 ∨ d₀ % 8 = 6 ∨ d₀ % 8 = 7) →
          (d₁ % 8 = 1 ∨ d₁ % 8 = 2 ∨ d₁ % 8 = 3) → IsChiPair n d₁ χ →
          ∃ ε : GaussianInt, EpsClass d₀ d₁ ε ∧
            IsOfFinAddOrder ((m d₀ : GaussianInt) • PchiGWith z n φ χ -
              (ε * 2 ^ h2G n * (ℓ d₁ : GaussianInt)) • Q d₀)

/-- Modulo torsion `P_χ` does not depend on `Φ` (from TYZ Prop. 3.2(4), used form). -/
theorem pchi_sub_tors (h324 : TYZProp324Used) {n : ℕ} [NeZero n] (hsq : Squarefree n)
    (hn8 : n % 8 = 5 ∨ n % 8 = 7) {φ φ' : ClG n → GalQ} (hφ : IsPhi n φ) (hφ' : IsPhi n φ')
    (χ : ClG n →* ℤˣ) : IsOfFinAddOrder (PchiGWith basePt n φ χ - PchiGWith basePt n φ' χ) := by
  unfold PchiGWith
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_induction _ IsOfFinAddOrder (fun a b ha hb => ha.add hb) IsOfFinAddOrder.zero
    (fun t _ => ?_)
  rw [← zsmul_sub]
  exact (h324 n inferInstance hsq hn8 t _ _ (hφ t) (hφ' t)).zsmul

theorem gsmul_sub (c : GaussianInt) (P R : PtA) : c • (P - R) = c • P - c • R := smul_sub c P R

theorem natCast_gsmul_tors (k : ℕ) {P : PtA} (h : IsOfFinAddOrder P) :
    IsOfFinAddOrder ((k : GaussianInt) • P) := by
  rw [Nat.cast_smul_eq_nsmul GaussianInt k P]
  exact h.nsmul

theorem radTYZ_ne_zero {n d₁ : ℕ} (h : d₁ ≠ 0) : radTYZ n d₁ ≠ 0 := by
  unfold radTYZ
  split_ifs <;> omega

/-- **`ε` can be chosen before `Φ`**: TYZ Theorem 3.3 in the printed quantifier order for the kernel's
`z_n`, with TYZ Prop. 3.2(4) (used form), gives the kernel's `TYZSplit.TYZThm33`. -/
theorem tyzThm33_of_epsAfter (h324 : TYZProp324Used) (h : TYZThm33EpsAfter basePt) : TYZThm33 := by
  classical
  intro ℓ hℓ
  obtain ⟨Q, m, hm, hQ, htors, hmain⟩ := h ℓ hℓ
  have key : ∀ d₀ d₁ : ℕ, ∃ e : GaussianInt, EpsClass d₀ d₁ e ∧
      ∀ (n : ℕ) (_ : NeZero n), d₀ * d₁ = n → Squarefree n → (n % 8 = 5 ∨ n % 8 = 7) →
        (d₀ % 8 = 5 ∨ d₀ % 8 = 6 ∨ d₀ % 8 = 7) → (d₁ % 8 = 1 ∨ d₁ % 8 = 2 ∨ d₁ % 8 = 3) →
        ∀ φ : ClG n → GalQ, IsPhi n φ → ∀ χ : ClG n →* ℤˣ, IsChiPair n d₁ χ →
          IsOfFinAddOrder ((m d₀ : GaussianInt) • PchiG n φ χ -
            (e * 2 ^ h2G n * (ℓ d₁ : GaussianInt)) • Q d₀) := by
    intro d₀ d₁
    by_cases H : ∃ (_ : NeZero (d₀ * d₁)) (χ : ClG (d₀ * d₁) →* ℤˣ), Squarefree (d₀ * d₁) ∧
        ((d₀ * d₁) % 8 = 5 ∨ (d₀ * d₁) % 8 = 7) ∧ (d₀ % 8 = 5 ∨ d₀ % 8 = 6 ∨ d₀ % 8 = 7) ∧
        (d₁ % 8 = 1 ∨ d₁ % 8 = 2 ∨ d₁ % 8 = 3) ∧ IsChiPair (d₀ * d₁) d₁ χ
    · obtain ⟨hnz, χ₀, hsq, hn8, h0, h1, hχ₀⟩ := H
      choose φ₀ hφ₀ using fun t : ClG (d₀ * d₁) => exists_restricts t
      obtain ⟨e, he, het⟩ := (hmain (d₀ * d₁) hnz hsq hn8 φ₀ hφ₀ χ₀).2 d₀ d₁ rfl h0 h1 hχ₀
      refine ⟨e, he, ?_⟩
      rintro n hnz' rfl - - - - φ hφ χ hχ
      have hd₁ : d₁ ≠ 0 := right_ne_zero_of_mul hnz.out
      have hχe : χ = χ₀ := isExtChar_unique (radTYZ_ne_zero hd₁) hχ hχ₀
      subst hχe
      have hdiff := natCast_gsmul_tors (m d₀) (pchi_sub_tors h324 hsq hn8 hφ hφ₀ χ)
      have e1 : (m d₀ : GaussianInt) • PchiG (d₀ * d₁) φ χ -
          (e * 2 ^ h2G (d₀ * d₁) * (ℓ d₁ : GaussianInt)) • Q d₀ =
          (m d₀ : GaussianInt) • (PchiGWith basePt (d₀ * d₁) φ χ - PchiGWith basePt (d₀ * d₁) φ₀ χ) +
          ((m d₀ : GaussianInt) • PchiGWith basePt (d₀ * d₁) φ₀ χ -
            (e * 2 ^ h2G (d₀ * d₁) * (ℓ d₁ : GaussianInt)) • Q d₀) := by
        rw [gsmul_sub, pchiGWith_basePt]
        abel
      rw [e1]
      exact hdiff.add het
    · refine ⟨if d₀ % 8 = 5 ∧ d₁ % 8 = 3 then gi else 1, ?_, ?_⟩
      · constructor <;> intro hc <;> simp [hc]
      · rintro n hnz rfl hsq hn8 h0 h1 φ hφ χ hχ
        exact absurd ⟨hnz, χ, hsq, hn8, h0, h1, hχ⟩ H
  choose ε hε hεt using key
  refine ⟨Q, m, ε, hm, hQ, fun d₀ d₁ _ _ => hε d₀ d₁, htors, ?_⟩
  intro n hnz hsq hn8 φ hφ χ
  exact ⟨(hmain n hnz hsq hn8 φ hφ χ).1,
    fun d₀ d₁ hd h0 h1 hχ => hεt d₀ d₁ n hnz hd hsq hn8 h0 h1 φ hφ χ hχ⟩

/-! ## §B2. TYZ's identification `i₀ : (X₀(32), ∞) ≅ (A, O)`, over Mathlib's upper half plane -/

open WeierstrassCurve.Affine in
open Classical in
/-- The point `(X(τ), Y(τ)) ∈ A(ℂ)` (`0` if it is not on `A`; never the case under the curve equation). -/
def ptOf (X Y : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) : X0.PtAC :=
  if h : X0.curveAC.toAffine.Nonsingular (X τ) (Y τ) then .some (X τ) (Y τ) h else 0

theorem ptOf_eta (τ : UpperHalfPlane) :
    ptOf (fun τ => X0.xC τ) (fun τ => X0.yC τ) τ = X0.phiC τ := rfl

/-- **`(X, Y) = (x ∘ i₀, y ∘ i₀)` for an isomorphism `i₀ : (X₀(32), ∞) ≅ (A, O)` over `ℚ`** (TYZ L1173–1174),
`A : y² = x³ + 4x` (`ℚ`-isomorphic to TYZ's `2y² = x³ + x` by `(x, y) ↦ (2x, 4y)`). Over `ℂ`,
`X₀(32)(ℂ) = Γ₀(32)\ℍ ∪ {cusps}` and a morphism `i₀` is given by the pullbacks `X = x∘i₀`, `Y = y∘i₀` of the
coordinate functions, which are elements of `ℚ(X₀(32))`; the conditions say:
* `X, Y ∈ ℚ(X₀(32))`, regular on `ℍ` (`IsRatModFn 32`: `Γ₀(32)`-invariant, meromorphic at the cusps, rational
  `q`-expansion at `∞`): `i₀` is a morphism over `ℚ` with `i₀⁻¹(O) ⊆ {cusps}`;
* `Y² = X³ + 4X`: `i₀` lands on `A`;
* `X` is unbounded at `∞`: `i₀(∞) = O`;
* `X = O(e^{4π Im τ})` at `∞` (a pole of order at most `2` in `q`) and `X` is bounded at every other cusp
  `γ∞` (`γ ∈ SL₂(ℤ)`, `32 ∤ c`; the cusps `γ∞` with `32 ∣ c` are `Γ₀(32)`-equivalent to `∞`): `X` has degree
  `2` on `X₀(32)`, so `i₀` has degree `1` (`deg X = deg i₀ · deg x`, `deg x = 2`), i.e. `i₀` is an
  isomorphism.
Conversely every isomorphism `i₀ : (X₀(32), ∞) ≅ (A, O)` over `ℚ` has these pullbacks (`x` has a single
double pole at `O`, `q` is a local parameter at `∞`). So the predicate is exactly TYZ's normalization. -/
def IsX0Identification (X Y : UpperHalfPlane → ℂ) : Prop :=
  Shimura.IsRatModFn 32 X ∧ Shimura.IsRatModFn 32 Y ∧ (∀ τ, Y τ ^ 2 = X τ ^ 3 + 4 * X τ) ∧
    ¬ UpperHalfPlane.IsBoundedAtImInfty X ∧
    (X =O[UpperHalfPlane.atImInfty] fun τ => Real.exp (4 * Real.pi * τ.im)) ∧
    ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ¬ (32 : ℤ) ∣ γ 1 0 →
      UpperHalfPlane.IsBoundedAtImInfty (fun τ => X (γ • τ))

/-- TYZ's `z_n = f_n(P_n)` from the points `w n = i₀(P_n) ∈ A(ℚ̄)`: `f_n = f₀ − f₀∘[i]`, i.e.
`z_n = (1 − [i]) i₀(P_n)`, for `n ≡ 5 (mod 8)`; `f_n = i₀`, `z_n = i₀(P_n)`, otherwise (TYZ L1195–1198). -/
def zOfLift (w : ℕ → PtA) (n : ℕ) : PtA := if n % 8 = 5 then w n - iPt (w n) else w n

/-- **Leaf TYZ-3.3 (printed form): Tian–Yuan–Zhang Theorem 3.3, for TYZ's identification `i₀`.** -/
def TYZThm33Printed : Prop :=
  ∀ X Y : UpperHalfPlane → ℂ, IsX0Identification X Y → ∀ w : ℕ → PtA,
    (∀ n : ℕ, ∀ hn : n % 8 = 5, Squarefree n → toC (w n) = ptOf X Y (tyzForm n hn).tauH) →
    (∀ n : ℕ, ∀ hn : n % 8 = 7, Squarefree n → toC (w n) = ptOf X Y (tyzForm7 n hn).tauH) →
    TYZThm33EpsAfter (zOfLift w)

/-! ## §B3. The eta model is such an identification -/

/-- **The eta-quotient model `phiC = (x, y)` of x0-32 is an identification `(X₀(32), ∞) ≅ (A, O)` in the
sense of `IsX0Identification`.** -/
theorem isX0Identification_eta (hc : EtaCuspBounds) :
    IsX0Identification (fun τ => X0.xC τ) (fun τ => X0.yC τ) := by
  refine ⟨X0ModuliUsed.isRatModFn_x, X0ModuliUsed.isRatModFn_y, fun τ => Shimura.etaModelEquation τ,
    not_bounded_xC, hc.1, hc.2⟩

/-! ## §B4. The main theorem -/

/-- **`TYZSplit.TYZThm33` from TYZ Theorem 3.3 in its printed form** (and the printed main theorem of CM
`hCM`, already a hypothesis of `frozenTarget`). -/
theorem tyzThm33_of_printed (hCM : T5Glue.ShimuraMainCM) (h : TYZThm33Printed) : TYZThm33 := by
  have hI := cmInputs hCM
  apply tyzThm33_of_epsAfter (tyzProp324Used_of hI)
  let w : ℕ → PtA := fun n => if n % 8 = 5 then tyzHeegnerPt n else tyzZ7 n
  have hz : zOfLift w = basePt := by
    funext n
    by_cases h5 : n % 8 = 5 <;> simp [zOfLift, w, basePt, h5, tyzZn]
  rw [← hz]
  refine h _ _ (isX0Identification_eta etaCuspBounds) w ?_ ?_
  · intro n hn _
    have e : w n = heegnerPt (tyzForm n hn) := by simp [w, hn, tyzHeegnerPt]
    rw [e]
    exact toC_heegnerPt _ (hI.alg _ _)
  · intro n hn _
    have h5 : n % 8 ≠ 5 := by omega
    have e : w n = heegnerPt (tyzForm7 n hn) := by simp [w, h5, tyzZ7, hn]
    rw [e]
    exact toC_heegnerPt _ (hI.alg _ _)

end ZInQ.Contrib.TYZGenus.H33Dict

#print axioms ZInQ.Contrib.TYZGenus.H33Dict.tyzProp324Used_of
#print axioms ZInQ.Contrib.TYZGenus.H33Dict.tyzThm33_of_epsAfter
#print axioms ZInQ.Contrib.TYZGenus.H33Dict.tyzThm33_of_printed
