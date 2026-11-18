import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.PointMap
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Place

/-!
# A separable isogeny intertwines translations

Let `φ : W₁ → W₂` be a separable isogeny of elliptic curves over a separably closed field `F`, and
`P` a point of `W₁`. Then `φ ∘ τ_P = τ_{φ P} ∘ φ`. On the level of the tautological point `θ_φ` of
`φ` (the point of `W₂` over `F(W₁)` cut out by the pulled-back coordinates) this reads

    τ_P^* θ_φ = θ_φ + φ(P)        (`map_translation_tautologicalPoint`).

The proof is by rigidity, without the general theorem that isogenies are homomorphisms over every
field: the difference `D = τ_P^* θ_φ − θ_φ − φ(P)` reduces at the place of each point `Q` of `W₁`
to `φ(Q + P) − φ(Q) − φ(P)`, since `τ_P^*` moves the place of `Q + P` to the place of `Q`
(`translation_smul_pointEquivDegreeOnePlace`). That is `O` because `φ` acts additively on the
points over `F` (`pointMap_ofIsogeny_eq_toPointHom`). A point reducing to `O` at infinitely many
places is `O` (`eq_zero_of_forall_mem_polePoints`: its `x`-coordinate would have infinitely many
poles).

This is the first step towards the compatibility of the Weil pairing with separable isogenies,
`e_N(φ S, φ T) = e_N(S, T)^{deg φ}` (Silverman III.8.2).

Classification: PROVED.
-/

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine TauCeti

namespace ZInQ.Contrib.CloudB3RC53.WeilIsogeny

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve.Affine F}

omit [DecidableEq F] in
/-- **A point over `F(W₁)` that reduces to `O` at the place of every point of `W₁` is `O`**, when
`W₁` has infinitely many points. PROVED. -/
theorem eq_zero_of_forall_mem_polePoints [W₁.IsElliptic] [W₂.IsElliptic] [Infinite W₁.Point]
    (D : (W₂⁄W₁.FunctionField).toAffine.Point)
    (h : ∀ Q : W₁.Point, D ∈ polePoints W₂ (W₁.pointEquivDegreeOnePlace Q).1) : D = 0 := by
  by_contra hD
  rcases D with _ | ⟨x, y, hxy⟩
  · exact hD rfl
  have hv : ∀ Q : W₁.Point, 1 < (W₁.pointEquivDegreeOnePlace Q).1.valuation x := fun Q =>
    ((mem_polePoints_iff _ _ _).mp (h Q)).resolve_left (fun h0 => by cases h0)
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := hv 0
    rw [map_zero] at this
    exact absurd this (not_lt.mpr zero_le)
  set u : W₁.FunctionFieldˣ := Units.mk0 x hx0
  have hmem : ∀ Q : W₁.Point, (W₁.pointEquivDegreeOnePlace Q).1 ∈
      (Divisor.principal W₁.isFunctionField u).support := by
    intro Q
    rw [Divisor.mem_support_principal_iff]
    intro hord
    have := hv Q
    rw [Place.valuation_eq_exp_neg_ord _ hx0] at this
    simp only [Units.val_mk0, u] at hord
    rw [hord, neg_zero, WithZero.exp_zero] at this
    exact lt_irrefl _ this
  have : Finite W₁.Point := Finite.of_injective
    (fun Q => (⟨(W₁.pointEquivDegreeOnePlace Q).1, hmem Q⟩ :
      (Divisor.principal W₁.isFunctionField u).support))
    (fun Q Q' e => W₁.pointEquivDegreeOnePlace.injective
      (Subtype.ext (congrArg Subtype.val e :)))
  exact not_finite W₁.Point

/-- The reduction at a place of degree one depends only on the place. -/
theorem reductionOfDegreeEqOne_congr [W₂.IsElliptic] {K : Type*} [Field K] [Algebra F K]
    [DecidableEq K] {w w' : Place F K}
    (e : w = w') (hw : w.degree = 1) (hw' : w'.degree = 1) :
    reductionOfDegreeEqOne W₂ hw = reductionOfDegreeEqOne W₂ hw' := by
  subst e; rfl

variable [IsSepClosed F] [W₁.IsElliptic] [W₂.IsElliptic]

/-- **A separable isogeny intertwines translations**: `τ_P^* θ_φ = θ_φ + φ(P)`. PROVED. -/
theorem map_translation_tautologicalPoint (φ : Isogeny W₁ W₂)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField] (P : W₁.Point) :
    Point.map (translation W₁ (Point.equivBaseChangeSelf W₁ P) : W₁.FunctionField →ₐ[F]
        W₁.FunctionField) (Isogeny.Hom.ofIsogeny φ).tautologicalPoint =
      (Isogeny.Hom.ofIsogeny φ).tautologicalPoint + Point.baseChange (W' := W₂) F
        W₁.FunctionField (Point.equivBaseChangeSelf W₂ ((Isogeny.Hom.ofIsogeny φ).pointMap P)) := by
  have := W₂.isIntegrallyClosed_coordinateRing
  have hadd : ∀ Q R : W₁.Point, (Isogeny.Hom.ofIsogeny φ).pointMap (Q + R) =
      (Isogeny.Hom.ofIsogeny φ).pointMap Q + (Isogeny.Hom.ofIsogeny φ).pointMap R := by
    intro Q R
    rw [Isogeny.Hom.pointMap_ofIsogeny_eq_toPointHom, Isogeny.Hom.pointMap_ofIsogeny_eq_toPointHom,
      Isogeny.Hom.pointMap_ofIsogeny_eq_toPointHom, map_add]
  have hred : ∀ R : W₁.Point, reductionOfDegreeEqOne W₂ (W₁.pointEquivDegreeOnePlace R).2
      (Isogeny.Hom.ofIsogeny φ).tautologicalPoint =
        Point.equivBaseChangeSelf W₂ ((Isogeny.Hom.ofIsogeny φ).pointMap R) := by
    intro R
    rw [Isogeny.Hom.pointMap, AddEquiv.apply_symm_apply]
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_mem_polePoints
  intro Q
  rw [← ker_reductionOfDegreeEqOne W₂ (W₁.pointEquivDegreeOnePlace Q).2, AddMonoidHom.mem_ker,
    map_sub, map_add, reductionOfDegreeEqOne_baseChange]
  have e : translation W₁ (Point.equivBaseChangeSelf W₁ P) •
      (W₁.pointEquivDegreeOnePlace (Q + P)).1 = (W₁.pointEquivDegreeOnePlace Q).1 := by
    rw [translation_smul_pointEquivDegreeOnePlace, add_sub_cancel_right]
  have h1 : reductionOfDegreeEqOne W₂ (W₁.pointEquivDegreeOnePlace Q).2
      (Point.map (translation W₁ (Point.equivBaseChangeSelf W₁ P) : W₁.FunctionField →ₐ[F]
        W₁.FunctionField) (Isogeny.Hom.ofIsogeny φ).tautologicalPoint) =
        Point.equivBaseChangeSelf W₂ ((Isogeny.Hom.ofIsogeny φ).pointMap (Q + P)) := by
    rw [reductionOfDegreeEqOne_congr e.symm (W₁.pointEquivDegreeOnePlace Q).2
      ((Place.degree_smul _ _).trans (W₁.pointEquivDegreeOnePlace (Q + P)).2),
      reductionOfDegreeEqOne_smul_map (W := W₂) (hw := (W₁.pointEquivDegreeOnePlace (Q + P)).2), hred]
  rw [h1, hred, hadd, map_add, sub_self]

/-- **A separable isogeny intertwines translations on function fields**:
`φ^* ∘ τ_{φ P}^* = τ_P^* ∘ φ^*`. PROVED. -/
theorem fieldPullback_comp_translation (φ : Isogeny W₁ W₂)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField] (P : W₁.Point) :
    φ.fieldPullback.comp (translation W₂ (Point.equivBaseChangeSelf W₂
        ((Isogeny.Hom.ofIsogeny φ).pointMap P)) : W₂.FunctionField →ₐ[F] W₂.FunctionField) =
      (translation W₁ (Point.equivBaseChangeSelf W₁ P) : W₁.FunctionField →ₐ[F]
        W₁.FunctionField).comp φ.fieldPullback := by
  apply map_genericPoint_injective W₂ (Ω := W₁.FunctionField)
  simp only
  rw [← Point.map_map, ← Point.map_map, map_translation_genericPoint,
    translatedGenericPoint_def, map_add, ← Isogeny.tautologicalPoint_eq_map_genericPoint,
    ← Isogeny.Hom.tautologicalPoint_ofIsogeny,
    map_translation_tautologicalPoint, Point.map_baseChange]

end ZInQ.Contrib.CloudB3RC53.WeilIsogeny
