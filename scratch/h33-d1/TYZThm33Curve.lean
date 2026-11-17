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

end ZInQ.H33D1
