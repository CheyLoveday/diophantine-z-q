import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Projective.CoordinateRing
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Birational.ValuativeExtension
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# hgz-steps: the elliptic curve as a projective `ℚ`-scheme, its affine chart, and D1

* `ESch E = Proj ℚ[X, Y, Z]/(F_E)`, proper over `Spec ℚ`.
* `chartZ E : Spec (A_(Z)) ⟶ ESch E`, the chart `D₊(Z)`.
* `chartHom E a b h : A_(Z) →+* K` for a point `(a, b)` of `E` over a `ℚ`-algebra `K`.
* `exists_extension`: a `K(X)`-point of the chart extends to a morphism `X ⟶ ESch E` for every
  integral scheme `X` whose stalks are valuation rings (D1, Hartshorne I.6.8 / II.4.7).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

namespace ZInQ.GZSch

/-! ## `Spec ℚ` is subterminal -/

theorem specQ_ext {Y : Scheme.{0}} (f g : Y ⟶ Spec (CommRingCat.of ℚ)) : f = g := by
  have h1 := Scheme.toSpecΓ_naturality f
  have h2 := Scheme.toSpecΓ_naturality g
  have hA : f.appTop = g.appTop := by
    have : (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ f.appTop =
        (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ g.appTop := by
      ext1; exact Subsingleton.elim _ _
    simpa using this
  rw [← cancel_mono (Spec (CommRingCat.of ℚ)).toSpecΓ, h1, h2, hA]

variable (E : WeierstrassCurve ℚ)

/-! ## The scheme -/

/-- The grading of `ℚ[X, Y, Z]/(F_E)` by degree. -/
abbrev gr : ℕ → Submodule ℚ E.toProjective.CoordinateRing := E.toProjective.grading

/-- **`E` as a projective `ℚ`-scheme**: `Proj ℚ[X, Y, Z]/(Y²Z + a₁XYZ + a₃YZ² − X³ − a₂X²Z − a₄XZ² − a₆Z³)`
(Tau Ceti's graded homogeneous coordinate ring, Mathlib's `Proj`). -/
abbrev ESch : Scheme.{0} := Proj (gr E)

/-- The class of `Z`. -/
abbrev zC : E.toProjective.CoordinateRing := E.toProjective.coord 2

theorem zC_mem : zC E ∈ gr E 1 := E.toProjective.coord_mem_grading 2

/-- `A_(Z)`, the degree-zero part of the localization at `Z`: the coordinate ring of `D₊(Z)`. -/
abbrev AZ : Type := Away (gr E) (zC E)

/-- **The affine chart `D₊(Z) = Spec A_(Z) ⟶ ESch E`** (an open immersion). -/
def chartZ : Spec (CommRingCat.of (AZ E)) ⟶ ESch E :=
  Proj.awayι (gr E) (zC E) (zC_mem E) one_pos

instance : IsOpenImmersion (chartZ E) := by unfold chartZ; infer_instance

/-- `ℚ ≅ (A)₀`. -/
def grZeroIso : CommRingCat.of ℚ ≅ CommRingCat.of (gr E 0) :=
  (RingEquiv.ofBijective (algebraMap ℚ (gr E 0))
    E.toProjective.bijective_algebraMap_grading_zero).toCommRingCatIso

/-- The structure morphism `ESch E ⟶ Spec ℚ`. -/
def toSpecQ : ESch E ⟶ Spec (CommRingCat.of ℚ) :=
  Proj.toSpecZero (gr E) ≫ Spec.map (grZeroIso E).hom

instance : IsProper (toSpecQ E) := by
  unfold toSpecQ
  infer_instance

/-! ## Points of the chart -/

section Chart

variable {K : Type} [CommRing K] [Algebra ℚ K]

theorem eqn_proj {a b : K} (h : (E.map (algebraMap ℚ K)).toAffine.Equation a b) :
    (E.toProjective.map (algebraMap ℚ K)).Equation ![a, b, 1] :=
  (WeierstrassCurve.Projective.equation_some (W' := (E.map (algebraMap ℚ K)).toProjective) a b).2 h

/-- Evaluation of the homogeneous coordinate ring at `[a : b : 1]`. -/
def evAB (a b : K) (h : (E.map (algebraMap ℚ K)).toAffine.Equation a b) :
    E.toProjective.CoordinateRing →+* K :=
  E.toProjective.evalHom (algebraMap ℚ K) (eqn_proj E h)

theorem evAB_coord (a b : K) (h) (i : Fin 3) :
    evAB E a b h (E.toProjective.coord i) = ![a, b, 1] i :=
  congrFun (E.toProjective.evalHom_comp_coord (algebraMap ℚ K) (eqn_proj E h)) i

theorem evAB_zC (a b : K) (h) : evAB E a b h (zC E) = 1 := evAB_coord E a b h 2

theorem isUnit_evAB_zC (a b : K) (h) : IsUnit (evAB E a b h (zC E)) := by
  rw [evAB_zC]; exact isUnit_one

/-- **The `K`-point `(a, b)` of the chart**: `A_(Z) →+* K`, `F/Z^n ↦ F(a, b, 1)`. -/
def chartHom (a b : K) (h : (E.map (algebraMap ℚ K)).toAffine.Equation a b) : AZ E →+* K where
  toFun u := Localization.awayLift (evAB E a b h) (zC E) (isUnit_evAB_zC E a b h) u.val
  map_one' := by simp
  map_mul' u v := by simp
  map_zero' := by simp
  map_add' u v := by simp

theorem chartHom_mk (a b : K) (h) (n : ℕ) (F : E.toProjective.CoordinateRing)
    (hF : F ∈ gr E (n • 1)) :
    chartHom E a b h (Away.mk (gr E) (zC_mem E) n F hF) = evAB E a b h F := by
  change Localization.awayLift (evAB E a b h) (zC E) (isUnit_evAB_zC E a b h) (Localization.mk F ⟨zC E ^ n, n, rfl⟩) = _
  rw [Localization.awayLift_mk (evAB E a b h) (zC E) F 1 (by rw [evAB_zC, one_mul])]
  simp

/-- `x = X/Z ∈ A_(Z)`. -/
def xz : AZ E := Away.mk (gr E) (zC_mem E) 1 (E.toProjective.coord 0)
  (by simpa using E.toProjective.coord_mem_grading 0)

/-- `y = Y/Z ∈ A_(Z)`. -/
def yz : AZ E := Away.mk (gr E) (zC_mem E) 1 (E.toProjective.coord 1)
  (by simpa using E.toProjective.coord_mem_grading 1)

theorem chartHom_xz (a b : K) (h) : chartHom E a b h (xz E) = a := by
  rw [xz, chartHom_mk, evAB_coord]; rfl

theorem chartHom_yz (a b : K) (h) : chartHom E a b h (yz E) = b := by
  rw [yz, chartHom_mk, evAB_coord]; rfl

/-- Naturality: `f ∘ (a, b) = (f a, f b)`. -/
theorem comp_chartHom {L : Type} [CommRing L] [Algebra ℚ L] (f : K →+* L) (a b : K) (h)
    (h' : (E.map (algebraMap ℚ L)).toAffine.Equation (f a) (f b)) :
    f.comp (chartHom E a b h) = chartHom E (f a) (f b) h' := by
  have hev : f.comp (evAB E a b h) = evAB E (f a) (f b) h' := by
    refine E.toProjective.ringHom_ext ?_ ?_
    · ext r; simp [evAB, RingHom.map_rat_algebraMap]
    · funext i
      simp only [Function.comp_apply, RingHom.coe_comp, evAB_coord]
      fin_cases i <;> simp
  ext u
  obtain ⟨n, F, hF, rfl⟩ := Away.mk_surjective (gr E) (zC_mem E) u
  simp only [RingHom.coe_comp, Function.comp_apply, chartHom_mk]
  exact congrArg (fun g : E.toProjective.CoordinateRing →+* L => g F) hev

end Chart

/-! ## D1: extension of a generic point of the chart -/

instance : (ESch E).Over (Spec (CommRingCat.of ℚ)) := ⟨toSpecQ E⟩

instance : IsProper (ESch E ↘ Spec (CommRingCat.of ℚ)) := (inferInstance : IsProper (toSpecQ E))

/-- **D1 (Hartshorne I.6.8, II.4.7; Silverman AEC II.2.1).** Let `X` be an integral scheme over
`ℚ` whose local rings are valuation rings (a normal curve), and `u : A_(Z) →+* K(X)` a `K(X)`-point
of the chart `D₊(Z)` of `E`. Then the rational map `X ⇢ E` it defines extends to a morphism
`π : X ⟶ E`: `Spec K(X) → X → E` is `Spec K(X) → D₊(Z) → E`. Proof: Jacobian-Challenge's
`exists_hom_of_valuationRing_stalk` (valuative criterion for the proper `E → Spec ℚ`). -/
theorem exists_extension (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Spec (CommRingCat.of ℚ))
    (hv : ∀ p : X, ValuationRing (X.presheaf.stalk p))
    (u : AZ E →+* X.functionField) :
    ∃ π : X ⟶ ESch E,
      X.fromSpecFunctionField ≫ π = Spec.map (CommRingCat.ofHom u) ≫ chartZ E := by
  let _ : X.Over (Spec (CommRingCat.of ℚ)) := ⟨sX⟩
  obtain ⟨π, -, hπ⟩ := Scheme.exists_hom_of_valuationRing_stalk (base := Spec (CommRingCat.of ℚ))
    (target := ESch E) hv (Spec.map (CommRingCat.ofHom u) ≫ chartZ E) (specQ_ext _ _)
  exact ⟨π, hπ⟩

end ZInQ.GZSch
