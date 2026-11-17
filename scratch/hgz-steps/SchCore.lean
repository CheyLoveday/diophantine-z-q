import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Projective.CoordinateRing
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Birational.ValuativeExtension
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Analysis.Complex.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

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


/-! ## The morphism near a point: the two directions of the key lemma -/

section Points

variable {E}
variable {X : Scheme.{0}} [IsIntegral X] (π : X ⟶ ESch E) (u : AZ E →+* X.functionField)
  (hπ : X.fromSpecFunctionField ≫ π = Spec.map (CommRingCat.ofHom u) ≫ chartZ E)
include hπ

/-- **If `π(p) ∈ D₊(Z)`, the coordinates `u(a)` are regular at `p`.** -/
theorem mem_range_of_mem_chart (p : X) (hp : π p ∈ (chartZ E).opensRange) (a : AZ E) :
    u a ∈ Set.range (algebraMap (X.presheaf.stalk p) X.functionField) := by
  have hr : Set.range (X.fromSpecStalk p ≫ π) ⊆ Set.range (chartZ E) := by
    rintro _ ⟨z, rfl⟩
    have hz : X.fromSpecStalk p z ⤳ p := by
      have h0 : X.fromSpecStalk p z ∈ Set.range (X.fromSpecStalk p) := Set.mem_range_self z
      rw [Scheme.range_fromSpecStalk] at h0
      exact h0
    have := (hz.map π.continuous).mem_open (chartZ E).opensRange.isOpen hp
    simpa using this
  set ℓ := IsOpenImmersion.lift (chartZ E) (X.fromSpecStalk p ≫ π) hr
  have hℓ : ℓ ≫ chartZ E = X.fromSpecStalk p ≫ π := IsOpenImmersion.lift_fac _ _ _
  set θ := Spec.preimage ℓ
  have h1 : Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes p)) ≫
      X.fromSpecStalk p = X.fromSpecFunctionField := Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
  have h2 : Spec.map (θ ≫ X.presheaf.stalkSpecializes (genericPoint_specializes p)) =
      Spec.map (CommRingCat.ofHom u) := by
    rw [← cancel_mono (chartZ E), Spec.map_comp, Category.assoc, Spec.map_preimage, hℓ,
      ← Category.assoc, h1, hπ]
  have h3 := Spec.map_injective h2
  refine ⟨θ a, ?_⟩
  have := congrArg (fun f => f.hom a) h3
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at this
  exact this

variable (hv : ∀ p : X, ValuationRing (X.presheaf.stalk p))
include hv

/-- **If the coordinates are regular at `p` (through `θ`), then `π` near `p` is the chart map**
(uniqueness in the valuative criterion: `E` is separated). -/
theorem fromSpecStalk_comp_eq (p : X) (θ : AZ E →+* X.presheaf.stalk p)
    (hθ : (algebraMap (X.presheaf.stalk p) X.functionField).comp θ = u) :
    X.fromSpecStalk p ≫ π = Spec.map (CommRingCat.ofHom θ) ≫ chartZ E := by
  haveI := hv p
  have hsep : ValuativeCriterion.Uniqueness (toSpecQ E) := IsSeparated.valuativeCriterion _
  let S : ValuativeCommSq (toSpecQ E) :=
    { R := X.presheaf.stalk p, K := X.functionField, i₁ := X.fromSpecFunctionField ≫ π,
      i₂ := X.fromSpecStalk p ≫ π ≫ toSpecQ E, commSq := ⟨specQ_ext _ _⟩ }
  have hs := hsep S
  have hA : Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk p) X.functionField)) =
      Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes p)) := rfl
  let l₁ : S.commSq.LiftStruct :=
    { l := X.fromSpecStalk p ≫ π
      fac_left := by
        change Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk p) X.functionField)) ≫
          X.fromSpecStalk p ≫ π = X.fromSpecFunctionField ≫ π
        rw [hA, ← Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      fac_right := specQ_ext _ _ }
  let l₂ : S.commSq.LiftStruct :=
    { l := Spec.map (CommRingCat.ofHom θ) ≫ chartZ E
      fac_left := by
        change Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk p) X.functionField)) ≫
          Spec.map (CommRingCat.ofHom θ) ≫ chartZ E = X.fromSpecFunctionField ≫ π
        rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hθ, hπ]
      fac_right := specQ_ext _ _ }
  exact congrArg CommSq.LiftStruct.l (Subsingleton.elim l₁ l₂)

theorem mem_chart_of_factor (p : X) (θ : AZ E →+* X.presheaf.stalk p)
    (hθ : (algebraMap (X.presheaf.stalk p) X.functionField).comp θ = u) :
    π p ∈ (chartZ E).opensRange := by
  have h := congrArg (fun f => f (IsLocalRing.closedPoint (X.presheaf.stalk p)))
    (fromSpecStalk_comp_eq π u hπ hv p θ hθ)
  simp only [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint] at h
  rw [h]
  exact ⟨_, rfl⟩

/-- **The value at a `ℂ`-point, when the coordinates are regular there.** -/
theorem comp_eq_of_factor (x : Spec (CommRingCat.of ℂ) ⟶ X)
    (θ : AZ E →+* X.presheaf.stalk (x (IsLocalRing.closedPoint (CommRingCat.of ℂ))))
    (hθ : (algebraMap _ X.functionField).comp θ = u) :
    x ≫ π = Spec.map (CommRingCat.ofHom ((Scheme.stalkClosedPointTo x).hom.comp θ)) ≫
      chartZ E := by
  conv_lhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk x]
  rw [Category.assoc, fromSpecStalk_comp_eq π u hπ hv _ θ hθ, ← Category.assoc, ← Spec.map_comp]
  rfl

end Points

/-! ## Points of `E(ℂ)` from `ℂ`-points of the scheme -/

open scoped WeierstrassCurve.Affine

open Classical in
/-- **The point of `E(ℂ)` of a `ℂ`-point `s : Spec ℂ ⟶ ESch E`**: `(a, b)` if `s` is the point
`(a, b)` of the chart `D₊(Z)`, and `O` otherwise (the complement of `D₊(Z)` in `E` is
`V₊(Z, X³) = {[0 : 1 : 0]}`). -/
def ptOf (s : Spec (CommRingCat.of ℂ) ⟶ ESch E) : (E⁄ℂ).Point :=
  if h : ∃ q : ℂ × ℂ, ∃ hq : (E⁄ℂ).Nonsingular q.1 q.2,
      s = Spec.map (CommRingCat.ofHom (chartHom E q.1 q.2 hq.1)) ≫ chartZ E
  then .some _ _ h.choose_spec.choose else 0

theorem point_some_congr {x y x' y' : ℂ} (h : (E⁄ℂ).Nonsingular x y)
    (h' : (E⁄ℂ).Nonsingular x' y') (hx : x = x') (hy : y = y') :
    (WeierstrassCurve.Affine.Point.some x y h : (E⁄ℂ).Point) = .some x' y' h' := by
  subst hx hy; rfl

theorem chartHom_inj {a b a' b' : ℂ} (h h')
    (he : Spec.map (CommRingCat.ofHom (chartHom E a b h)) ≫ chartZ E =
      Spec.map (CommRingCat.ofHom (chartHom E a' b' h')) ≫ chartZ E) : a = a' ∧ b = b' := by
  rw [cancel_mono] at he
  have := Spec.map_injective he
  have h2 : chartHom E a b h = chartHom E a' b' h' := congrArg CommRingCat.Hom.hom this
  refine ⟨?_, ?_⟩
  · have := congrArg (fun g => g (xz E)) h2; simpa [chartHom_xz] using this
  · have := congrArg (fun g => g (yz E)) h2; simpa [chartHom_yz] using this

theorem ptOf_chart {a b : ℂ} (hns : (E⁄ℂ).Nonsingular a b) :
    ptOf E (Spec.map (CommRingCat.ofHom (chartHom E a b hns.1)) ≫ chartZ E) = .some a b hns := by
  have hex : ∃ q : ℂ × ℂ, ∃ hq : (E⁄ℂ).Nonsingular q.1 q.2,
      Spec.map (CommRingCat.ofHom (chartHom E a b hns.1)) ≫ chartZ E =
        Spec.map (CommRingCat.ofHom (chartHom E q.1 q.2 hq.1)) ≫ chartZ E := ⟨(a, b), hns, rfl⟩
  rw [ptOf, dif_pos hex]
  obtain ⟨h1, h2⟩ := chartHom_inj E _ _ hex.choose_spec.choose_spec.symm
  exact point_some_congr E _ _ h1 h2

theorem ptOf_eq_zero (s : Spec (CommRingCat.of ℂ) ⟶ ESch E)
    (hs : s (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∉ (chartZ E).opensRange) : ptOf E s = 0 := by
  rw [ptOf, dif_neg]
  rintro ⟨q, hq, rfl⟩
  exact hs ⟨_, rfl⟩

end ZInQ.GZSch
