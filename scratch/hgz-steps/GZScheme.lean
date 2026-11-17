import ZInQKernel.Contrib.OneProof.GrossZagierScheme.Core
import ZInQKernel.Contrib.OneProof.GrossZagierScheme.EpsD
import ZInQKernel.Contrib.OneProof.GrossZagierPlane.Extension
import ZInQKernel.Contrib.CloudW07JacobiansCurves.NormalModel

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory UpperHalfPlane Filter Topology HeckeRing.GL2
open scoped WeierstrassCurve.Affine

namespace ZInQ.GZSch

open ZInQ.GZAlg ZInQ.GZDict2

/-! ## §1. Equations over `ℚ`-algebras -/

/-- The Weierstrass equation of `E` over a `ℚ`-algebra. -/
def WEqA (E : WeierstrassCurve ℚ) {K : Type*} [CommRing K] [Algebra ℚ K] (x y : K) : Prop :=
  y ^ 2 + algebraMap ℚ K E.a₁ * x * y + algebraMap ℚ K E.a₃ * y =
    x ^ 3 + algebraMap ℚ K E.a₂ * x ^ 2 + algebraMap ℚ K E.a₄ * x + algebraMap ℚ K E.a₆

theorem affEq_of_wEqA {E : WeierstrassCurve ℚ} {K : Type*} [CommRing K] [Algebra ℚ K] {x y : K}
    (h : WEqA E x y) : (E.map (algebraMap ℚ K)).toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  unfold WEqA at h
  linear_combination h

theorem wEqA_of_wEqR {E : WeierstrassCurve ℚ} {K : Type*} [Field K] [Algebra ℚ K] {x y : K}
    (h : WEqR E x y) : WEqA E x y := by
  unfold WEqA; unfold WEqR at h
  simp only [eq_ratCast]
  exact h

theorem WEqA.map {E : WeierstrassCurve ℚ} {K L : Type*} [CommRing K] [Algebra ℚ K] [CommRing L]
    [Algebra ℚ L] {x y : K} (h : WEqA E x y) (f : K →+* L) : WEqA E (f x) (f y) := by
  have := congrArg f h
  simp only [map_add, map_mul, map_pow, RingHom.map_rat_algebraMap] at this
  exact this

theorem WEqA.of_map {E : WeierstrassCurve ℚ} {K L : Type*} [CommRing K] [Algebra ℚ K] [CommRing L]
    [Algebra ℚ L] {x y : K} (f : K →+* L) (hf : Function.Injective f) (h : WEqA E (f x) (f y)) :
    WEqA E x y := by
  apply hf
  unfold WEqA at h
  simp only [map_add, map_mul, map_pow, RingHom.map_rat_algebraMap]
  exact h

theorem chartHom_congr (E : WeierstrassCurve ℚ) {K : Type} [CommRing K] [Algebra ℚ K] {a b a' b' : K}
    (h h') (ha : a = a') (hb : b = b') : chartHom E a b h = chartHom E a' b' h' := by
  subst ha hb; rfl

/-- `(φ^*x, φ^*y)` is on `E`. -/
theorem wEqA_phi {E : WeierstrassCurve ℚ} {N : ℕ} [NeZero N]
    (φ : E.toAffine.FunctionField →ₐ[ℚ] X0Field N) : WEqA E (φ (genX E)) (φ (genY E)) :=
  wEqA_of_wEqR ((wEqR_gen E).map (φ : E.toAffine.FunctionField →+* X0Field N))

/-- **The `ℚ(X₀(N))`-point `(φ^*x, φ^*y)` of the chart `D₊(Z)`**, transported to `K(X)`. -/
def uOf {E : WeierstrassCurve ℚ} {N : ℕ} [NeZero N] (φ : E.toAffine.FunctionField →ₐ[ℚ] X0Field N)
    {X : Scheme.{0}} [IsIntegral X] (e : X.functionField ≃+* X0Field N) : AZ E →+* X.functionField :=
  (e.symm : X0Field N →+* X.functionField).comp
    (chartHom E (φ (genX E)) (φ (genY E)) (affEq_of_wEqA (wEqA_phi φ)))

theorem uOf_xz {E : WeierstrassCurve ℚ} {N : ℕ} [NeZero N] (φ : E.toAffine.FunctionField →ₐ[ℚ] X0Field N)
    {X : Scheme.{0}} [IsIntegral X] (e : X.functionField ≃+* X0Field N) :
    uOf φ e (xz E) = e.symm (φ (genX E)) := by
  simp [uOf, chartHom_xz]

theorem uOf_yz {E : WeierstrassCurve ℚ} {N : ℕ} [NeZero N] (φ : E.toAffine.FunctionField →ₐ[ℚ] X0Field N)
    {X : Scheme.{0}} [IsIntegral X] (e : X.functionField ≃+* X0Field N) :
    uOf φ e (yz E) = e.symm (φ (genY E)) := by
  simp [uOf, chartHom_yz]

/-! ## §2. The points `τ` and `∞` of `X₀(N)`, and the leaf -/

/-- **`x : Spec ℂ ⟶ X` is the point `τ ∈ ℍ` of `X₀(N)(ℂ)`**, for a model `X` of `X₀(N)` with
`ι : K(X) ≃ ℚ(X₀(N)) = ℚ(j, j_N)`: every function `g` regular at `x` takes at `x` the value at `τ` of
the modular function with `q`-expansion `ι(g)`, i.e. of `P(j, j_N)/Q(j, j_N)` for any
representation `ι(g) = P(jq, jq(q^N))/Q(jq, jq(q^N))` (a limit at the finitely many points where
`Q(j, j_N)` vanishes). This is the uniformization `ℍ → X₀(N)(ℂ)` of the canonical model
(Shimura 1971, §6.7). -/
def IsPointAt (N : ℕ) [NeZero N] {X : Scheme.{0}} [IsIntegral X] (ι : X.functionField ≃+* X0Field N)
    (τ : ℍ) (x : Spec (CommRingCat.of ℂ) ⟶ X) : Prop :=
  ∀ (s : X.presheaf.stalk (x (IsLocalRing.closedPoint (CommRingCat.of ℂ))))
    (P Q : MvPolynomial (Fin 2) ℚ),
    IsRatRep N ((ι (algebraMap _ X.functionField s) : X0Field N) : LaurentSeries ℚ) P Q →
    Tendsto (ratFn N P Q ∘ ofComplex) (𝓝[≠] (τ : ℂ)) (𝓝 ((Scheme.stalkClosedPointTo x).hom s))

/-- **`p` is the cusp `∞` of `X₀(N)`**: the functions regular at `p` have `q`-expansions without
pole (`q` is the local parameter at `∞`, of width `1`). -/
def IsCuspInfty (N : ℕ) [NeZero N] {X : Scheme.{0}} [IsIntegral X]
    (ι : X.functionField ≃+* X0Field N) (p : X) : Prop :=
  ∀ s : X.presheaf.stalk p,
    0 ≤ HahnSeries.addVal ℤ ℚ ((ι (algebraMap _ X.functionField s) : X0Field N) : LaurentSeries ℚ)

/-- **The Gross–Zagier formula for a modular parametrization `π : X₀(N) → E`, a morphism of
curves over `ℚ` (Gross–Zagier 1986, Thm I.6.3 and Ch. V Thm 2.1; positive constant forgotten).**

* `E/ℚ` has the L-series of the newform `f` of level `N`, trivial character.
* `X₀(N)` is the canonical model over `ℚ`: an integral normal scheme `X`, proper of dimension `1`
  over `ℚ`, with function field `ι : K(X) ≃ ℚ(X₀(N)) = ℚ(j, j_N) ⊂ ℚ((q))` (every such `X` is the
  canonical model, up to unique isomorphism: Hartshorne I.6.7–6.9, II.6.7; Shimura 1971, §6.7).
* `E` is the projective scheme `ESch E = Proj ℚ[X, Y, Z]/(F_E)`.
* `π : X ⟶ ESch E` is a nonconstant morphism over `ℚ` with `π(∞) = O`: the cusp `∞` maps outside
  the chart `D₊(Z)` (whose complement in `E` is `O = [0 : 1 : 0]`).
* `D < −4` an odd fundamental discriminant, every `p ∣ N` split in `K = ℚ(√D)` (`ε_D(p) = 1`,
  `ε_D` the quadratic character of `K`, the Kronecker symbol `(D/·)`), `β² ≡ D (mod 4N)`.
* `x_r : Spec ℂ ⟶ X` are the Heegner points of discriminant `D` and residue `β`, `x_r` the point
  `τ_r ∈ ℍ` (`IsPointAt`) for a complete set of representatives `τ_r`.
* `y ∈ E(K)` with `ι(y) = n · Σ_r π(x_r)` in `E(ℂ)`, `n ≠ 0` (`y_K = Tr_{H/K} π(x)`).
* `F`, `G` the entire continuations of `L(f, s)` and `L(f ⊗ ε_D, s)`.

Then `L'(E/K, 1) = (F G)'(1) = κ · ĥ(y)` for some real `κ > 0`.

Source: B. Gross, D. Zagier, *Heegner points and derivatives of L-series*, Invent. Math. 84
(1986), 225–320, Thm I.6.3 and Ch. V §2 (Thm 2.1) for any modular parametrization
`π : X₀(N) → E` with `π(∞) = 0` (fixed in V §2, p. 310). Weaker than the print: the constant is
replaced by `∃ κ > 0`, and `y` may be any nonzero multiple of `y_K` (`ĥ(n y_K) = n² ĥ(y_K)`). -/
def GrossZagierCurveAt (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → ZInQ.GZDecomp.coeff f n = (E.LFunction n : ℂ)) →
    ∀ (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Spec (CommRingCat.of ℚ)), IsProper sX →
    ZInQ.Contrib.CurvesG.IsNormalScheme X → topologicalKrullDim X = 1 →
    ∀ ι : X.functionField ≃+* X0Field N,
    ∀ π : X ⟶ ESch E, π ≫ toSpecQ E = sX →
    (∃ p₁ p₂ : X, π p₁ ≠ π p₂) →
    (∀ p : X, IsCuspInfty N ι p → π p ∉ (chartZ E).opensRange) →
    ∀ D β : ℤ, ZInQ.GZDecomp.IsOddImagFundDisc D → D < -4 →
    (∀ p : ℕ, p.Prime → p ∣ N → ZInQ.HGZSteps.epsD D p = 1) →
    (4 * N : ℤ) ∣ D - β ^ 2 →
    ∀ (R : Type) [Fintype R] (τ : R → ℍ), ZInQ.GZModuli.IsHeegnerPointReps N D β τ →
    ∀ x : R → (Spec (CommRingCat.of ℂ) ⟶ X), (∀ r, IsPointAt N ι (τ r) (x r)) →
    ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K], Module.finrank ℚ K = 2 →
    ∀ δ : K, δ ^ 2 = (D : K) →
    ∀ ιK : K →ₐ[ℚ] ℂ, ιK δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) →
    ∀ n : ℤ, n ≠ 0 →
    ∀ y : (E⁄K).Point, WeierstrassCurve.Affine.Point.map ιK y = n • ∑ r, ptOf E (x r ≫ π) →
    ∀ F G : ℂ → ℂ, ZInQ.GZDecomp.IsEntireCont (ZInQ.GZDecomp.coeff f) 2 F →
      ZInQ.GZDecomp.IsEntireCont (fun m => ZInQ.GZDecomp.coeff f m * (ZInQ.HGZSteps.epsD D m : ℂ)) 2 G →
      ∃ κ : ℝ, 0 < κ ∧ deriv (fun s => F s * G s) 1 = κ * y.canonicalHeight

/-- **The leaf of the `C_d` route, curve form**: `GrossZagierCurveAt E'` for every short model `E'` in
the isogeny class of `C_d : y² = x³ − d²x`, `d ≡ 5 (mod 8)` squarefree. -/
def GrossZagierCurveCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d →
    ∀ (E' : WeierstrassCurve ℚ) [E'.IsElliptic], ZInQ.GZOptimal.IsShortModel E' →
      (∀ n : ℕ, n ≠ 0 → E'.LFunction n = (ZInQ.shortCurve (-(d : ℚ) ^ 2)).LFunction n) →
      GrossZagierCurveAt E'

/-! ## §3. Normal curves have valuation rings as local rings -/

theorem valuationRing_stalk_of_normal (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (hN : ZInQ.Contrib.CurvesG.IsNormalScheme X) (hd : topologicalKrullDim X = 1) (p : X) :
    ValuationRing (X.presheaf.stalk p) := by
  have hle : ringKrullDim (X.presheaf.stalk p) ≤ 1 := by
    rw [ringKrullDim_stalk_eq_coheight, ← hd, topologicalKrullDim,
      Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints]
    exact Order.coheight_le_krullDim p
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk p) := Ring.krullDimLE_iff.mpr (by exact_mod_cast hle)
  haveI := hN p
  have htfae := tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (R := X.presheaf.stalk p)
  have hiff : ValuationRing (X.presheaf.stalk p) ↔ (IsIntegrallyClosed (X.presheaf.stalk p) ∧
      ∀ P : Ideal (X.presheaf.stalk p), P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal _) :=
    htfae.out 2 4
  refine hiff.mpr ⟨inferInstance, fun P hP hPp => ?_⟩
  rcases Ring.krullDimLE_one_iff.mp ‹_› P hPp with hmin | hmax
  · have hmin' : Minimal (fun q : Ideal (X.presheaf.stalk p) => q.IsPrime ∧ ⊥ ≤ q) P := hmin
    exact absurd (hmin'.eq_of_ge ⟨Ideal.isPrime_bot, le_rfl⟩ bot_le) hP
  · exact IsLocalRing.eq_maximalIdeal hmax

/-! ## §4. The center of a valuation ring on a proper scheme -/

theorem exists_center (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Spec (CommRingCat.of ℚ))
    [UniversallyClosed sX] (O : ValuationSubring X.functionField) (c : ℚ →+* O) :
    ∃ (p : X) (θ : X.presheaf.stalk p →+* O), IsLocalHom θ ∧
      ∀ s, (θ s : X.functionField) = algebraMap _ X.functionField s := by
  have hex : ValuativeCriterion.Existence sX :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed sX)).1
  let S : ValuativeCommSq sX :=
    { R := O, K := X.functionField, i₁ := X.fromSpecFunctionField,
      i₂ := Spec.map (CommRingCat.ofHom c), commSq := ⟨specQ_ext _ _⟩ }
  obtain ⟨⟨ℓ, hl, -⟩⟩ := hex S
  refine ⟨ℓ (IsLocalRing.closedPoint (CommRingCat.of O)), (Scheme.stalkClosedPointTo ℓ).hom,
    inferInstance, fun s => ?_⟩
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ℓ
  have h2 : Spec.map (CommRingCat.ofHom (algebraMap O X.functionField)) ≫ ℓ =
      X.fromSpecFunctionField := hl
  have h3 : Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes
      (ℓ (IsLocalRing.closedPoint (CommRingCat.of O))))) ≫
      X.fromSpecStalk (ℓ (IsLocalRing.closedPoint (CommRingCat.of O))) = X.fromSpecFunctionField :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
  rw [← h1, ← Category.assoc, ← Spec.map_comp, ← h3, cancel_mono] at h2
  have h4 := Spec.map_injective h2
  have := congrArg (fun f => f.hom s) h4
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at this
  exact this


/-- `ℚ → 𝒪_{X,p}` for a scheme over `ℚ`. -/
def ratToStalk {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of ℚ)) (p : X) :
    ℚ →+* X.presheaf.stalk p :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ s.appTop ≫ X.presheaf.germ ⊤ p trivial).hom

/-! ## §5. D2: the value of `π` at the point `τ` is `modPt` of the plane model -/

theorem eventually_polyFn_ne_zero {N : ℕ} [NeZero N] {P : MvPolynomial (Fin 2) ℚ}
    (hP : polyQ N P ≠ 0) (τ : ℍ) : ∀ᶠ z in 𝓝[≠] (τ : ℂ), polyFn N P (ofComplex z) ≠ 0 := by
  obtain ⟨T, hT⟩ := HasQExp.exists_ne_zero (hasQExp_polyFn N P) hP
  exact eventually_ne_zero_of_im_gt (fun τ => (holoH_polyFn N P τ).meromorphicAt) hT τ

theorem polyQ_ne_zero_of_rep {N : ℕ} [NeZero N] {g : LaurentSeries ℚ} {P Q : MvPolynomial (Fin 2) ℚ}
    (h : IsRatRep N g P Q) (hg : g ≠ 0) : polyQ N P ≠ 0 := by
  intro h0; apply hg; rw [h.2, h0, zero_div]

theorem isRatRep_inv {N : ℕ} [NeZero N] {g : LaurentSeries ℚ} {P Q : MvPolynomial (Fin 2) ℚ}
    (h : IsRatRep N g P Q) (hg : g ≠ 0) : IsRatRep N g⁻¹ Q P :=
  ⟨polyQ_ne_zero_of_rep h hg, by rw [h.2, inv_div]⟩

/-- A function with a finite limit at `τ` is regular at a point `x` above `τ` (the local ring at
`x` is a valuation ring, and `ev_x` kills its maximal ideal). -/
theorem mem_range_of_tendsto {N : ℕ} [NeZero N] {X : Scheme.{0}} [IsIntegral X]
    (hv : ∀ p : X, ValuationRing (X.presheaf.stalk p)) (ι : X.functionField ≃+* X0Field N) {τ : ℍ}
    {x : Spec (CommRingCat.of ℂ) ⟶ X} (hx : IsPointAt N ι τ x) (g : X.functionField)
    {P Q : MvPolynomial (Fin 2) ℚ} (hr : IsRatRep N ((ι g : X0Field N) : LaurentSeries ℚ) P Q)
    {c : ℂ} (hc : Tendsto (ratFn N P Q ∘ ofComplex) (𝓝[≠] (τ : ℂ)) (𝓝 c)) :
    g ∈ Set.range (algebraMap (X.presheaf.stalk (x (IsLocalRing.closedPoint (CommRingCat.of ℂ))))
      X.functionField) := by
  set O := X.presheaf.stalk (x (IsLocalRing.closedPoint (CommRingCat.of ℂ)))
  haveI := hv (x (IsLocalRing.closedPoint (CommRingCat.of ℂ)))
  by_cases hg0 : g = 0
  · exact ⟨0, by rw [hg0, map_zero]⟩
  rcases ValuationRing.isInteger_or_isInteger O g with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact ⟨t, ht⟩
  by_cases hu : IsUnit t
  · refine ⟨(hu.unit⁻¹ : Oˣ), ?_⟩
    have h1 : algebraMap O X.functionField (hu.unit⁻¹ : Oˣ) * algebraMap O X.functionField t = 1 := by
      rw [← map_mul]; simp
    rw [ht] at h1
    exact (eq_inv_of_mul_eq_one_left h1).trans (inv_inv g)
  · exfalso
    have hev : (Scheme.stalkClosedPointTo x).hom t = 0 := by
      by_contra hne
      exact hu ((isUnit_map_iff (Scheme.stalkClosedPointTo x).hom t).mp (Ne.isUnit hne))
    have hιg : ((ι g : X0Field N) : LaurentSeries ℚ) ≠ 0 := by
      simpa using hg0
    have hr' : IsRatRep N ((ι (algebraMap O X.functionField t) : X0Field N) : LaurentSeries ℚ) Q P := by
      rw [ht, map_inv₀, IntermediateField.coe_inv]
      exact isRatRep_inv hr hιg
    have h0 := hx t Q P hr'
    rw [hev] at h0
    have hprod := hc.mul h0
    rw [mul_zero] at hprod
    have hone : (fun z => (ratFn N P Q ∘ ofComplex) z * (ratFn N Q P ∘ ofComplex) z) =ᶠ[𝓝[≠] (τ : ℂ)]
        fun _ => (1 : ℂ) := by
      filter_upwards [eventually_polyFn_ne_zero hr.1 τ,
        eventually_polyFn_ne_zero (polyQ_ne_zero_of_rep hr hιg) τ] with z h1 h2
      simp only [Function.comp_apply, ratFn]
      field_simp
    have := tendsto_nhds_unique (hprod.congr' hone) tendsto_const_nhds
    exact zero_ne_one this

variable {E : WeierstrassCurve ℚ} {N : ℕ} [NeZero N] (φ : E.toAffine.FunctionField →ₐ[ℚ] X0Field N)
  {X : Scheme.{0}} [IsIntegral X] (hv : ∀ p : X, ValuationRing (X.presheaf.stalk p))
  (e : X.functionField ≃+* X0Field N) (π : X ⟶ ESch E)
  (hπ : X.fromSpecFunctionField ≫ π = Spec.map (CommRingCat.ofHom (uOf φ e)) ≫ chartZ E)

include hπ in
/-- **`π(∞) = O`.** -/
theorem cusp_not_mem_chart (hord : ((φ (genX E) : X0Field N) : LaurentSeries ℚ).order < 0)
    (p : X) (hp : IsCuspInfty N e p) : π p ∉ (chartZ E).opensRange := by
  intro hmem
  obtain ⟨s, hs⟩ := mem_range_of_mem_chart π (uOf φ e) hπ p hmem (xz E)
  rw [uOf_xz] at hs
  have h := hp s
  rw [hs, RingEquiv.apply_symm_apply] at h
  have hne : ((φ (genX E) : X0Field N) : LaurentSeries ℚ) ≠ 0 := by
    intro h0; rw [h0] at hord; simp at hord
  rw [HahnSeries.addVal_apply_of_ne hne] at h
  have : (0 : ℤ) ≤ ((φ (genX E) : X0Field N) : LaurentSeries ℚ).order := by exact_mod_cast h
  omega

include hπ in
/-- **The generic point maps into the chart.** -/
theorem generic_mem_chart : π (genericPoint X) ∈ (chartZ E).opensRange := by
  have h := congrArg (fun f => f (IsLocalRing.closedPoint (CommRingCat.of X.functionField))) hπ
  simp only [Scheme.Hom.comp_apply] at h
  have h0 : X.fromSpecFunctionField (IsLocalRing.closedPoint (CommRingCat.of X.functionField)) =
      genericPoint X := Scheme.fromSpecStalk_closedPoint
  rw [h0] at h
  rw [h]
  exact ⟨_, rfl⟩

set_option backward.isDefEq.respectTransparency true in
include hπ hv in
/-- **D2 in the scheme model: the value of `π` at the point `τ` is gz-dict2's `modPt` of the
plane-model functions.** -/
theorem ptOf_eq_modPt [E.IsElliptic] {Px Qx Py Qy : MvPolynomial (Fin 2) ℚ}
    (hrx : IsRatRep N (φ (genX E) : LaurentSeries ℚ) Px Qx)
    (hry : IsRatRep N (φ (genY E) : LaurentSeries ℚ) Py Qy) (τ : ℍ)
    (x : Spec (CommRingCat.of ℂ) ⟶ X) (hx : IsPointAt N e τ x) :
    ptOf E (x ≫ π) = ZInQ.GZModuli.modPt E (ratFn N Px Qx) (ratFn N Py Qy) τ := by
  have hrx' : IsRatRep N ((e (e.symm (φ (genX E))) : X0Field N) : LaurentSeries ℚ) Px Qx := by
    rw [RingEquiv.apply_symm_apply]; exact hrx
  have hry' : IsRatRep N ((e (e.symm (φ (genY E))) : X0Field N) : LaurentSeries ℚ) Py Qy := by
    rw [RingEquiv.apply_symm_apply]; exact hry
  rcases modPt_plane_cases E φ hrx hry τ with ⟨x₀, y₀, hns, hlx, hly, hmod⟩ | ⟨hpole, hmod⟩
  · rw [hmod]
    letI : Algebra ℚ (X.presheaf.stalk (x (IsLocalRing.closedPoint (CommRingCat.of ℂ)))) :=
      (ratToStalk (π ≫ toSpecQ E) _).toAlgebra
    letI : Algebra ℚ X.functionField :=
      ((e.symm : X0Field N →+* X.functionField).comp (algebraMap ℚ (X0Field N))).toAlgebra
    obtain ⟨sx, hsx⟩ := mem_range_of_tendsto hv e hx _ hrx' hlx
    obtain ⟨sy, hsy⟩ := mem_range_of_tendsto hv e hx _ hry' hly
    have hinj : Function.Injective (algebraMap (X.presheaf.stalk (x (IsLocalRing.closedPoint (CommRingCat.of ℂ)))) X.functionField) :=
      IsFractionRing.injective _ X.functionField
    have hW : WEqA E sx sy := by
      refine WEqA.of_map (algebraMap (X.presheaf.stalk (x (IsLocalRing.closedPoint (CommRingCat.of ℂ)))) X.functionField) hinj ?_
      rw [hsx, hsy]
      exact (wEqA_phi φ).map (e.symm : X0Field N →+* X.functionField)
    have hθ : (algebraMap (X.presheaf.stalk (x (IsLocalRing.closedPoint (CommRingCat.of ℂ)))) X.functionField).comp (chartHom E sx sy (affEq_of_wEqA hW)) = uOf φ e := by
      have h2 := comp_chartHom E (e.symm : X0Field N →+* X.functionField) (φ (genX E))
        (φ (genY E)) (affEq_of_wEqA (wEqA_phi φ))
        (affEq_of_wEqA ((wEqA_phi φ).map (e.symm : X0Field N →+* X.functionField)))
      rw [comp_chartHom E _ sx sy _ (affEq_of_wEqA (hW.map _))]
      unfold uOf
      rw [h2]
      exact chartHom_congr E _ _ hsx hsy
    have hcomp := comp_eq_of_factor π (uOf φ e) hπ hv x (chartHom E sx sy (affEq_of_wEqA hW)) hθ
    have hex : (Scheme.stalkClosedPointTo x).hom sx = x₀ := by
      have := hx sx Px Qx (by rw [hsx]; exact hrx')
      exact tendsto_nhds_unique this hlx
    have hey : (Scheme.stalkClosedPointTo x).hom sy = y₀ := by
      have := hx sy Py Qy (by rw [hsy]; exact hry')
      exact tendsto_nhds_unique this hly
    have hc2 : (Scheme.stalkClosedPointTo x).hom.comp (chartHom E sx sy (affEq_of_wEqA hW)) = chartHom E x₀ y₀ hns.1 := by
      rw [comp_chartHom E _ sx sy _ (affEq_of_wEqA (hW.map _))]
      exact chartHom_congr E _ _ hex hey
    rw [hcomp, hc2, ptOf_chart]
  · rw [hmod]
    apply ptOf_eq_zero
    intro hmem
    have hmem' : π (x (IsLocalRing.closedPoint (CommRingCat.of ℂ))) ∈ (chartZ E).opensRange := hmem
    obtain ⟨s, hs⟩ := mem_range_of_mem_chart π (uOf φ e) hπ _ hmem' (xz E)
    rw [uOf_xz] at hs
    have := hx s Px Qx (by rw [hs]; exact hrx')
    exact not_tendsto_atTop_of_tendsto_nhds this.norm hpole


/-! ## §6. The cusp `∞` exists on every model -/

/-- The valuation ring of `ord_q` (the place `∞`) in `ℚ(X₀(N))`. -/
def qVal (N : ℕ) [NeZero N] : ValuationSubring (X0Field N) where
  carrier := {g | 0 ≤ HahnSeries.addVal ℤ ℚ (g : LaurentSeries ℚ)}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, IntermediateField.coe_mul, AddValuation.map_mul] at *
    exact add_nonneg ha hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, IntermediateField.coe_add] at *
    exact le_trans (le_min ha hb) (AddValuation.map_add _ _ _)
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_setOf_eq, IntermediateField.coe_neg, AddValuation.map_neg] at *
    exact ha
  mem_or_inv_mem' a := by
    by_cases ha : a = 0
    · left; simp [ha]
    have ha' : (a : LaurentSeries ℚ) ≠ 0 := by simpa using ha
    have hia : ((a⁻¹ : X0Field N) : LaurentSeries ℚ) ≠ 0 := by simpa using ha
    have h1 : HahnSeries.addVal ℤ ℚ (a : LaurentSeries ℚ) +
        HahnSeries.addVal ℤ ℚ ((a⁻¹ : X0Field N) : LaurentSeries ℚ) = 0 := by
      rw [← AddValuation.map_mul, ← IntermediateField.coe_mul, mul_inv_cancel₀ ha,
        IntermediateField.coe_one, AddValuation.map_one]
    simp only [Set.mem_setOf_eq]
    rw [HahnSeries.addVal_apply_of_ne ha', HahnSeries.addVal_apply_of_ne hia] at h1 ⊢
    have h2 : (a : LaurentSeries ℚ).order + ((a⁻¹ : X0Field N) : LaurentSeries ℚ).order = 0 := by
      exact_mod_cast h1
    rcases le_total 0 (a : LaurentSeries ℚ).order with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast (show (0 : ℤ) ≤ ((a⁻¹ : X0Field N) : LaurentSeries ℚ).order by omega)

theorem rat_mem_qVal (N : ℕ) [NeZero N] (c : ℚ) : algebraMap ℚ (X0Field N) c ∈ qVal N := by
  show 0 ≤ HahnSeries.addVal ℤ ℚ ((algebraMap ℚ (X0Field N) c : X0Field N) : LaurentSeries ℚ)
  by_cases hc : c = 0
  · simp [hc]
  have hcst : ((algebraMap ℚ (X0Field N) c : X0Field N) : LaurentSeries ℚ) = HahnSeries.single 0 c :=
    (RingHom.congr_fun (Subsingleton.elim (((X0Field N).val : X0Field N →+* LaurentSeries ℚ).comp
      (algebraMap ℚ (X0Field N))) HahnSeries.C) c).trans rfl
  rw [hcst, HahnSeries.addVal_apply_of_ne (by simpa using hc), HahnSeries.order_single hc]
  rfl

/-- `ℚ` inside the comap of a valuation subring of `ℚ(X₀(N))` containing `ℚ`. -/
def ratToComap {N : ℕ} [NeZero N] {X : Scheme.{0}} [IsIntegral X] (e : X.functionField ≃+* X0Field N)
    (O : ValuationSubring (X0Field N)) (hO : ∀ c : ℚ, algebraMap ℚ (X0Field N) c ∈ O) :
    ℚ →+* O.comap (e : X.functionField →+* X0Field N) :=
  ((e.symm : X0Field N →+* X.functionField).comp (algebraMap ℚ (X0Field N))).codRestrict _
    (fun c => by
      rw [ValuationSubring.mem_comap]
      simpa using hO c)

theorem exists_cusp {N : ℕ} [NeZero N] (X : Scheme.{0}) [IsIntegral X]
    (sX : X ⟶ Spec (CommRingCat.of ℚ)) [IsProper sX] (e : X.functionField ≃+* X0Field N) :
    ∃ p : X, IsCuspInfty N e p := by
  obtain ⟨p, θ, -, hθ⟩ := exists_center X sX ((qVal N).comap (e : X.functionField →+* X0Field N))
    (ratToComap e (qVal N) (rat_mem_qVal N))
  refine ⟨p, fun s => ?_⟩
  rw [← hθ s]
  exact (θ s).2

end ZInQ.GZSch
