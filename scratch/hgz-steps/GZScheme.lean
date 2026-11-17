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

end ZInQ.GZSch
