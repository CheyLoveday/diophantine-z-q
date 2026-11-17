import ZInQKernel.Contrib.OneProof.TYZThm33Alg
import ZInQKernel.Contrib.OneProof.TYZThm33Curve.Charts

/-!
# h33-d1: TYZ Theorem 3.3 for TYZ's isomorphism of curves `i₀ : (X₀(32), ∞) ≅ (A, O)` over `ℚ`

Task h33-d1 (2026-11-17). Report: `docs/research/h33-d1.md`; scratch and log: `scratch/h33-d1/`.

The leaf `TYZThm33Curve` states Tian–Yuan–Zhang Theorem 3.3 with `i₀` a genuine isomorphism of
`ℚ`-schemes: `X₀(32)` is an integral proper `ℚ`-scheme `X` with function field
`ι : K(X) ≅ ℚ(X₀(32)) = ℚ(j, j₃₂) ⊂ ℚ((q))`, `A` is the projective scheme
`ESch curveA = Proj ℚ[X, Y, Z]/(Y²Z − X³ − 4XZ²)`, `i₀ : X ⟶ ESch curveA` is an isomorphism over `ℚ`
sending the cusp `∞` to `O` (outside the chart `D₊(Z)`), and the CM points `P_n` are the
`ℂ`-points of `X` at `τ_n` (`GZSch.IsPointAt`), with `i₀(P_n)` read in `A(ℂ)` by `GZSch.ptOf`.

`tyzThm33Alg_of_curve : TYZThm33Curve → H33Fix.TYZThm33Alg` proves the step D1 (curves vs. function
fields) in Lean: for `φ = i₀^*` bijective with `ord_q φ(x) < 0`, the curve `A = ESch curveA` itself,
with `ι = φ ∘ (K(ESch curveA) ≅ ℚ(A))` and `i₀ = 𝟙`, is such a model (`TYZThm33Curve/Charts.lean`:
`ESch` integral, `K(ESch E) ≅ ℚ(E)` through the chart `D₊(Z)`, values at `ℂ`-points through the charts
`D₊(Z)` and `D₊(Y)`), and the value of `i₀` at the point `τ` is `(X(τ), Y(τ))` for the holomorphic
`X, Y` with `q`-expansions `φ(x), φ(y)`.

No `sorry`, no `axiom`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory UpperHalfPlane Filter Topology
open scoped WeierstrassCurve.Affine Manifold

namespace ZInQ.H33D1

open ZInQ.GZSch ZInQ.GZAlg ZInQ.GZDict2
open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.TYZSplit
  ZInQ.Contrib.TYZGenus.H33Dict

/-! ## §1. The identification `ι` of `K(ESch E)` with `ℚ(X₀(N))` given by `φ` -/

/-- `ι = φ ∘ (K(ESch E) ≅ ℚ(E))` for a bijective `φ : ℚ(E) → ℚ(X₀(N))`. -/
def iotaOf (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N]
    (φ : E.toAffine.FunctionField →ₐ[ℚ] X0Field N) (hφ : Function.Bijective φ) :
    (ESch E).functionField ≃+* X0Field N :=
  (ffEquiv E).trans (RingEquiv.ofBijective (φ : E.toAffine.FunctionField →+* X0Field N) hφ)

variable {E : WeierstrassCurve ℚ} {N : ℕ} [NeZero N]
  (φ : E.toAffine.FunctionField →ₐ[ℚ] X0Field N) (hφ : Function.Bijective φ)

theorem iotaOf_xz : iotaOf E φ hφ (kappaZ E (xz E)) = φ (genX E) := by
  simp [iotaOf, ffEquiv_xz]

theorem iotaOf_yz : iotaOf E φ hφ (kappaZ E (yz E)) = φ (genY E) := by
  simp [iotaOf, ffEquiv_yz]

/-! ## §2. The value at a point `τ`, from the charts `D₊(Z)` and `D₊(Y)` -/

/-- **The value of `ESch E` at the point `τ`**: if the plane-model functions of `φ(x)`, `φ(y)` tend
to `(a, b)` at `τ`, the `ℂ`-point at `τ` is `(a, b)`. -/
theorem ptOf_eq_of_tendsto [E.IsElliptic] (τ : ℍ) (x : Spec (CommRingCat.of ℂ) ⟶ ESch E)
    (hx : IsPointAt N (iotaOf E φ hφ) τ x) {Px Qx Py Qy : MvPolynomial (Fin 2) ℚ}
    (hrx : IsRatRep N (φ (genX E) : LaurentSeries ℚ) Px Qx)
    (hry : IsRatRep N (φ (genY E) : LaurentSeries ℚ) Py Qy) {a b : ℂ} (hns : (E⁄ℂ).Nonsingular a b)
    (hla : Tendsto (ratFn N Px Qx ∘ ofComplex) (𝓝[≠] (τ : ℂ)) (𝓝 a))
    (hlb : Tendsto (ratFn N Py Qy ∘ ofComplex) (𝓝[≠] (τ : ℂ)) (𝓝 b)) :
    ptOf E x = .some a b hns := by
  by_cases hp : x (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈ (chartZ E).opensRange
  · obtain ⟨θ, hθ, hfac⟩ := exists_stalk_lift (chartZ E) (kappaZ_spec E) _ hp
    set χ : AZ E →+* ℂ := (Scheme.stalkClosedPointTo x).hom.comp θ with hχ
    have hxe : x = Spec.map (CommRingCat.ofHom χ) ≫ chartZ E := by
      conv_lhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk x]
      rw [hfac, ← Category.assoc, ← Spec.map_comp]
      rfl
    have hθx : algebraMap _ (ESch E).functionField (θ (xz E)) = kappaZ E (xz E) :=
      RingHom.congr_fun hθ _
    have hθy : algebraMap _ (ESch E).functionField (θ (yz E)) = kappaZ E (yz E) :=
      RingHom.congr_fun hθ _
    have ha : χ (xz E) = a := by
      have := hx (θ (xz E)) Px Qx (by rw [hθx, iotaOf_xz]; exact hrx)
      exact tendsto_nhds_unique this hla
    have hb : χ (yz E) = b := by
      have := hx (θ (yz E)) Py Qy (by rw [hθy, iotaOf_yz]; exact hry)
      exact tendsto_nhds_unique this hlb
    have hχe : χ = chartHom E a b hns.1 :=
      (eq_chartHom E χ (equation_of_hom E χ)).trans (chartHom_congr E _ _ ha hb)
    rw [hxe, hχe]
    exact ptOf_chart E hns
  · exfalso
    have hY := mem_basicOpen_Y_of_not_mem_Z E _ (by rwa [chartZ, Proj.opensRange_awayι] at hp)
    have hpY : x (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈ (chartY E).opensRange := by
      rw [chartY, Proj.opensRange_awayι]; exact hY
    obtain ⟨θ, hθ, hfac⟩ := exists_stalk_lift (chartY E) (kappaY_spec E) _ hpY
    set χ : AY E →+* ℂ := (Scheme.stalkClosedPointTo x).hom.comp θ with hχ
    have hxe : x = Spec.map (CommRingCat.ofHom χ) ≫ chartY E := by
      conv_lhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk x]
      rw [hfac, ← Category.assoc, ← Spec.map_comp]
      rfl
    have hv0 : χ (vY E) = 0 := chiY_vY_eq_zero E χ (hxe ▸ hp)
    have hθv : algebraMap _ (ESch E).functionField (θ (vY E)) = kappaY E (vY E) :=
      RingHom.congr_fun hθ _
    have hinv : kappaY E (vY E) = (kappaZ E (yz E))⁻¹ :=
      eq_inv_of_mul_eq_one_left (kappaY_vY_mul E)
    have hyz0 : kappaZ E (yz E) ≠ 0 := right_ne_zero_of_mul_eq_one (kappaY_vY_mul E)
    have hgy : (φ (genY E) : LaurentSeries ℚ) ≠ 0 := by
      rw [← iotaOf_yz φ hφ]
      simpa using hyz0
    have hrep : IsRatRep N ((iotaOf E φ hφ (algebraMap _ (ESch E).functionField (θ (vY E))) :
        X0Field N) : LaurentSeries ℚ) Qy Py := by
      rw [hθv, hinv, map_inv₀, iotaOf_yz, IntermediateField.coe_inv]
      exact isRatRep_inv hry hgy
    have h0 := hx (θ (vY E)) Qy Py hrep
    have hev : (Scheme.stalkClosedPointTo x).hom (θ (vY E)) = 0 := hv0
    rw [hev] at h0
    have hprod := hlb.mul h0
    rw [mul_zero] at hprod
    have hone : (fun z => (ratFn N Py Qy ∘ ofComplex) z * (ratFn N Qy Py ∘ ofComplex) z)
        =ᶠ[𝓝[≠] (τ : ℂ)] fun _ => (1 : ℂ) := by
      filter_upwards [eventually_polyFn_ne_zero hry.1 τ,
        eventually_polyFn_ne_zero (polyQ_ne_zero_of_rep hry hgy) τ] with z h1 h2
      simp only [Function.comp_apply, ratFn]
      field_simp
    exact zero_ne_one (tendsto_nhds_unique (hprod.congr' hone) tendsto_const_nhds)

/-! ## §3. The cusp `∞` maps to `O` -/

theorem not_mem_chartZ_of_cusp (hord : ((φ (genX E) : X0Field N) : LaurentSeries ℚ).order < 0)
    (p : ESch E) (hp : IsCuspInfty N (iotaOf E φ hφ) p) : p ∉ (chartZ E).opensRange := by
  intro hmem
  obtain ⟨θ, hθ, -⟩ := exists_stalk_lift (chartZ E) (kappaZ_spec E) p hmem
  have h := hp (θ (xz E))
  rw [show algebraMap _ (ESch E).functionField (θ (xz E)) = kappaZ E (xz E) from
    RingHom.congr_fun hθ _, iotaOf_xz] at h
  have hne : ((φ (genX E) : X0Field N) : LaurentSeries ℚ) ≠ 0 := by
    intro h0; rw [h0] at hord; simp at hord
  rw [HahnSeries.addVal_apply_of_ne hne] at h
  have : (0 : ℤ) ≤ ((φ (genX E) : X0Field N) : LaurentSeries ℚ).order := by exact_mod_cast h
  omega

/-! ## §4. The leaf -/

instance curveA_isElliptic : curveA.IsElliptic := by
  unfold curveA
  exact ZInQ.shortCurve_isElliptic (by norm_num)

/-- **Leaf TYZ-3.3 (curve form): Tian–Yuan–Zhang Theorem 3.3 for TYZ's isomorphism of curves
`i₀ : (X₀(32), ∞) ≅ (A, O)` over `ℚ`, for `n ≡ 5, 7 (mod 8)`.**

Source: Tian–Yuan–Zhang, *Genus periods, genus points and congruent number problem*,
arXiv:1411.4728v1, Theorem 3.3 (Period7.tex L1296–1311), with §3.1: `A` "is isomorphic to
`(X₀(32), ∞)`. Fix an identification `i₀`" (L1173–1174), `f_n = f₀ − f₀∘[i]` for `n ≡ 5` and
`f_n = i₀` for `n ≡ 7` (L1195–1198), the CM points `P_n` (L1203–1295). Journal version: Asian J.
Math. 21 (2017), NOT checked.

The objects:
* `X₀(32)` is an integral `ℚ`-scheme `X`, proper over `ℚ`, with function field
  `ι : K(X) ≅ ℚ(X₀(32)) = ℚ(j, j₃₂) ⊂ ℚ((q))` (FLT's `modularFunctionField 32`, the function field of
  the canonical model embedded by `q`-expansion at `∞`; Shimura 1971 §6.7, UNVERIFIED locator). Any
  such `X` admitting an isomorphism to `A` is a smooth projective curve with function field
  `ℚ(X₀(32))`, hence the canonical model, compatibly with `ι`.
* `A` is the projective scheme `ESch curveA = Proj ℚ[X, Y, Z]/(Y²Z − X³ − 4XZ²)` (`y² = x³ + 4x`,
  `ℚ`-isomorphic to TYZ's `2y² = x³ + x` by `(x, y) ↦ (2x, 4y)`).
* `i₀ : X ⟶ ESch curveA` is an isomorphism of `ℚ`-schemes with `i₀(∞) = O`: the cusp `∞`
  (`IsCuspInfty`, the center of `ord_q`) maps outside the chart `D₊(Z)`, whose complement is `O`.
* `P_n` is the CM point `τ_n` of `tyzForm n` (`n ≡ 5`) resp. `tyzForm7 n` (`n ≡ 7`): the `ℂ`-points
  `x` of `X` at `τ_n` (`IsPointAt`, unique by `GZSch.isPointAt_unique`), and `i₀(P_n) ∈ A(ℂ)` is
  `ptOf curveA (x ≫ i₀)`.
* `w n ∈ A(ℚ̄)` with `w n = i₀(P_n)` in `A(ℂ)`; then `TYZThm33EpsAfter (zOfLift w)` (h33-dict's display:
  `P_χ` torsion unless `χ = χ_{d₀,d₁}`, and then `P_χ = ε(d₀, d₁) 2^{h₂(n)} 𝓛(d₁) 𝒫(d₀)` in
  `A(ℚ̄) ⊗ ℚ`, `ε` chosen after `Φ`, `χ`), with `z_n = w n − [i](w n)` for `n ≡ 5` (`f₀∘[i] = [i]∘f₀`
  on the component of `P_n`, sign of `[i]` fixed by `α = −i`, h33-sign) and `z_n = w n` for `n ≡ 7`.

Readings (not Lean): `X_U ≅ X₀(32)_{ℚ(i)}` with `P_n ↦ τ_n` (L1191–1193) and the sign of `[i]`
(h33-sign), unchanged from h33-fix; the weakenings of h33-dict. -/
def TYZThm33Curve : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Spec (CommRingCat.of ℚ)), IsProper sX →
  ∀ ι : X.functionField ≃+* X0Field 32,
  ∀ i₀ : X ⟶ ESch curveA, IsIso i₀ → i₀ ≫ toSpecQ curveA = sX →
  (∀ p : X, IsCuspInfty 32 ι p → i₀ p ∉ (chartZ curveA).opensRange) →
  ∀ w : ℕ → PtA,
    (∀ n : ℕ, ∀ hn : n % 8 = 5, Squarefree n → ∀ x : Spec (CommRingCat.of ℂ) ⟶ X,
      IsPointAt 32 ι (tyzForm n hn).tauH x → toC (w n) = ZInQ.GZSch.ptOf curveA (x ≫ i₀)) →
    (∀ n : ℕ, ∀ hn : n % 8 = 7, Squarefree n → ∀ x : Spec (CommRingCat.of ℂ) ⟶ X,
      IsPointAt 32 ι (tyzForm7 n hn).tauH x → toC (w n) = ZInQ.GZSch.ptOf curveA (x ≫ i₀)) →
    TYZThm33EpsAfter (zOfLift w)

/-! ## §5. The value of `i₀` at `τ` is `(X(τ), Y(τ))` -/

theorem tendsto_of_mdiff {Xf : ℍ → ℂ} (hXf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Xf) (τ : ℍ) :
    Tendsto (Xf ∘ ofComplex) (𝓝[≠] (τ : ℂ)) (𝓝 (Xf τ)) := by
  have h := ((ZInQ.H33Fix.analyticOnNhd_of_mdiff hXf) τ τ.im_pos).continuousAt.tendsto
  have e : (Xf ∘ ofComplex) (τ : ℂ) = Xf τ := by simp [Function.comp_apply, ofComplex_apply]
  rw [e] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **D2 for the curve leaf**: at the point `τ` of the model `(ESch curveA, ι_φ)`, `ptOf` is
h33-dict's `ptOf X Y τ` of the holomorphic `X, Y` with `q`-expansions `φ(x), φ(y)`. -/
theorem ptOf_eq_h33 (φ : curveA.toAffine.FunctionField →ₐ[ℚ] X0Field 32) (hφ : ZInQ.H33Fix.IsX0IsoAlg φ)
    {Xf Yf : ℍ → ℂ} (hXf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Xf) (hYf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Yf)
    (hqX : HasQExp Xf (φ (genX curveA))) (hqY : HasQExp Yf (φ (genY curveA))) (τ : ℍ)
    (x : Spec (CommRingCat.of ℂ) ⟶ ESch curveA) (hx : IsPointAt 32 (iotaOf curveA φ hφ.1) τ x) :
    ZInQ.GZSch.ptOf curveA x = ZInQ.Contrib.TYZGenus.H33Dict.ptOf Xf Yf τ := by
  have hrx := repOf_spec (φ (genX curveA))
  have hry := repOf_spec (φ (genY curveA))
  have hmX : ∀ τ : ℍ, MeromorphicAt (Xf ∘ ofComplex) (τ : ℂ) := fun τ =>
    ((ZInQ.H33Fix.analyticOnNhd_of_mdiff hXf) τ τ.im_pos).meromorphicAt
  have hmY : ∀ τ : ℍ, MeromorphicAt (Yf ∘ ofComplex) (τ : ℂ) := fun τ =>
    ((ZInQ.H33Fix.analyticOnNhd_of_mdiff hYf) τ τ.im_pos).meromorphicAt
  have hlx := (tendsto_of_mdiff hXf τ).congr' (eventuallyEq_ratFn hmX hqX hrx τ)
  have hly := (tendsto_of_mdiff hYf τ).congr' (eventuallyEq_ratFn hmY hqY hry τ)
  rcases modPt_plane_cases curveA φ hrx hry τ with ⟨x₀, y₀, hns, hl1, hl2, -⟩ | ⟨hpole, -⟩
  · have e1 : Xf τ = x₀ := tendsto_nhds_unique hlx hl1
    have e2 : Yf τ = y₀ := tendsto_nhds_unique hly hl2
    rw [ptOf_eq_of_tendsto φ hφ.1 τ x hx hrx hry hns hl1 hl2]
    have hns' : ZInQ.Contrib.TYZGenus.X0.curveAC.toAffine.Nonsingular (Xf τ) (Yf τ) := by
      rw [e1, e2]; exact hns
    unfold ZInQ.Contrib.TYZGenus.H33Dict.ptOf
    rw [dif_pos hns']
    exact point_some_congr curveA _ _ e1.symm e2.symm
  · exact absurd hpole (not_tendsto_atTop_of_tendsto_nhds hlx.norm)

/-! ## §6. The bridge -/

/-- **D1 in Lean: the function-field leaf from the curve leaf.** For `φ = i₀^*` bijective with
`ord_q φ(x) < 0`, the curve `ESch curveA` with `ι = φ ∘ (K(ESch curveA) ≅ ℚ(A))` is a model of
`X₀(32)`, and `i₀ = 𝟙` is an isomorphism with `i₀(∞) = O`; its value at `P_n` is `(X(τ_n), Y(τ_n))`. -/
theorem tyzThm33Alg_of_curve (h : TYZThm33Curve) : ZInQ.H33Fix.TYZThm33Alg := by
  intro φ hφ Xf Yf hXf hYf hqX hqY w h5 h7
  refine h (ESch curveA) (toSpecQ curveA) inferInstance (iotaOf curveA φ hφ.1) (𝟙 _)
    inferInstance (Category.id_comp _) (fun p hp => not_mem_chartZ_of_cusp φ hφ.1 hφ.2 p hp) w
    ?_ ?_
  · intro n hn hsq x hx
    rw [Category.comp_id, h5 n hn hsq]
    exact (ptOf_eq_h33 φ hφ hXf hYf hqX hqY _ x hx).symm
  · intro n hn hsq x hx
    rw [Category.comp_id, h7 n hn hsq]
    exact (ptOf_eq_h33 φ hφ hXf hYf hqX hqY _ x hx).symm

/-- **`TYZSplit.TYZThm33` (the binder `h33` of `frozenTarget`) from the curve leaf** and the printed
main theorem of CM `hCM`. -/
theorem tyzThm33_of_curve (hCM : ZInQ.Contrib.TYZGenus.T5Glue.ShimuraMainCM) (h : TYZThm33Curve) :
    TYZThm33 :=
  ZInQ.H33Fix.tyzThm33_of_alg hCM (tyzThm33Alg_of_curve h)

end ZInQ.H33D1
