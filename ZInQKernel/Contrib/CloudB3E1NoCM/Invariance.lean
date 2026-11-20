import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.PointMap
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Add
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.GenericPoint
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.IsSepClosed
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula.VariableChange
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Eval

/-!
# Having no complex multiplication is invariant under a change of variables

Manuscript `diophantine_zq.tex`, tex 1765–1767 (the non-CM step for `E_ℓ`).

Let `D` be an admissible change of variables with `D • W = V`. The change of variables
`(x, y) ↦ (u²x + r, u³y + u²sx + t)` is then an isogeny `V → W` (`vcIsogeny`). Its coordinate
pullback is evaluation at the transformed generic point. It maps infinity to infinity because the
pulled back `x` has a pole there. On points it acts by Tau Ceti's `equivVariableChange`
(`pointMap_vc`, `pointMap_vc_eq`), which is additive.

**`noCM_variableChange`** (PROVED): over a separably closed field, if every endomorphism of `W` is
an integer multiple of the identity, then so is every endomorphism of `C • W`. The proof transports
`f` to `Φ ∘ f ∘ Ψ` on `W`, where `Φ, Ψ` are the change of variables and its inverse, and compares
actions on points. Points are infinite over a separably closed field, so rigidity
(`Isogeny.Hom.ext_pointMap`) applies.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1NoCM

open WeierstrassCurve WeierstrassCurve.Affine TauCeti

variable {F : Type} [Field F] {V W : WeierstrassCurve F} (D : VariableChange F) (hVW : D • W = V)

/-- The pulled back `x`: `u² x + r` on `V`. Kind: definition. -/
def vcX : V.toAffine.FunctionField :=
  algebraMap F _ ((D.u : F) ^ 2) * genericX V.toAffine + algebraMap F _ D.r

/-- The pulled back `y`: `u³ y + u² s x + t` on `V`. Kind: definition. -/
def vcY : V.toAffine.FunctionField :=
  algebraMap F _ ((D.u : F) ^ 3) * genericY V.toAffine +
    algebraMap F _ ((D.u : F) ^ 2 * D.s) * genericX V.toAffine + algebraMap F _ D.t

include hVW in
/-- The transformed generic point lies on `W`. Kind: PROVED. -/
theorem equation_vc : (W⁄(V.toAffine.FunctionField)).toAffine.Equation (vcX D) (vcY D) := by
  subst hVW
  set K := (D • W).toAffine.FunctionField
  have h := equation_genericX_genericY (D • W).toAffine
  have hmap : (D • W)⁄K = D.map (algebraMap F K) • (W⁄K) := (map_variableChange W D _).symm
  change ((D • W)⁄K).toAffine.Equation _ _ at h
  rw [hmap, ← variableChange_equation] at h
  convert h using 2 <;> simp [VariableChange.map, K, vcX, vcY]

/-- The coordinate pullback of the change of variables. Kind: definition. -/
def vcPullback : CoordinatePullback V.toAffine W.toAffine :=
  Affine.CoordinateRing.evalAlgHom (W := W.toAffine) (equation_vc D hVW)

/-- Kind: PROVED. -/
theorem vcPullback_X :
    vcPullback D hVW (AdjoinRoot.of W.toAffine.polynomial Polynomial.X) = vcX D :=
  Affine.CoordinateRing.evalAlgHom_of_X _

/-- Kind: PROVED. -/
theorem vcPullback_Y : vcPullback D hVW (AdjoinRoot.root W.toAffine.polynomial) = vcY D :=
  Affine.CoordinateRing.evalAlgHom_root _

/-- A nonzero constant has valuation one at every place. Kind: PROVED. -/
theorem val_const_eq_one (P : Place F V.toAffine.FunctionField) {c : F} (hc : c ≠ 0) :
    P.valuation (algebraMap F _ c) = 1 := by
  have h1 := (P.mem_integers_iff).mp (P.algebraMap_mem_integers c)
  have h2 := (P.mem_integers_iff).mp (P.algebraMap_mem_integers c⁻¹)
  rw [map_inv₀, map_inv₀] at h2
  have h0 : P.valuation (algebraMap F _ c) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]; exact (map_ne_zero _).mpr hc
  exact le_antisymm h1 (by rwa [inv_le_one₀ (zero_lt_iff.mpr h0)] at h2)

/-- **The change of variables as an isogeny** `V → W`. Kind: definition. -/
def vcIsogeny : Isogeny V.toAffine W.toAffine where
  pullback := vcPullback D hVW
  mapsInfinity := by
    refine CoordinatePullback.mapsInfinity_of_one_lt_infinityPlace _
      (AdjoinRoot.of W.toAffine.polynomial Polynomial.X) ?_
    rw [vcPullback_X, vcX, ← Place.valuation_infinity]
    have hx : 1 < (Place.infinity V.toAffine).valuation (genericX V.toAffine) := by
      rw [Place.valuation_infinity, genericX_eq_algebraMap]
      exact one_lt_infinityPlace_X V.toAffine
    have hu : (D.u : F) ^ 2 ≠ 0 := pow_ne_zero _ D.u.ne_zero
    have h1 : (Place.infinity V.toAffine).valuation
        (algebraMap F _ ((D.u : F) ^ 2) * genericX V.toAffine) =
        (Place.infinity V.toAffine).valuation (genericX V.toAffine) := by
      rw [map_mul, val_const_eq_one _ hu, one_mul]
    have h2 : (Place.infinity V.toAffine).valuation (algebraMap F _ D.r) <
        (Place.infinity V.toAffine).valuation
          (algebraMap F _ ((D.u : F) ^ 2) * genericX V.toAffine) := by
      rw [h1]
      exact lt_of_le_of_lt (((Place.infinity V.toAffine).mem_integers_iff).mp
        ((Place.infinity V.toAffine).algebraMap_mem_integers _)) hx
    rw [Valuation.map_add_eq_of_lt_left _ h2, h1]
    exact hx

/-- Kind: PROVED. -/
theorem fieldPullback_genericX :
    (vcIsogeny D hVW).fieldPullback (genericX W.toAffine) = vcX D := by
  rw [genericX_def, Isogeny.fieldPullback_algebraMap, AdjoinRoot.mk_C]
  exact vcPullback_X D hVW

/-- Kind: PROVED. -/
theorem fieldPullback_genericY :
    (vcIsogeny D hVW).fieldPullback (genericY W.toAffine) = vcY D := by
  rw [genericY_def, Isogeny.fieldPullback_algebraMap, AdjoinRoot.mk_X]
  exact vcPullback_Y D hVW

/-- The transformed coordinates reduce to the transformed point. Kind: PROVED. -/
theorem vc_val_lt (P : Place F V.toAffine.FunctionField) {x y : F}
    (hx : P.valuation (genericX V.toAffine - algebraMap F _ x) < 1)
    (hy : P.valuation (genericY V.toAffine - algebraMap F _ y) < 1) :
    P.valuation (vcX D - algebraMap F _ ((D.u : F) ^ 2 * x + D.r)) < 1 ∧
      P.valuation (vcY D - algebraMap F _
        ((D.u : F) ^ 3 * y + (D.u : F) ^ 2 * D.s * x + D.t)) < 1 := by
  have hle : ∀ c : F, P.valuation (algebraMap F _ c) ≤ 1 := fun c =>
    (P.mem_integers_iff).mp (P.algebraMap_mem_integers c)
  have hmul : ∀ (c : F) (z : V.toAffine.FunctionField), P.valuation z < 1 →
      P.valuation (algebraMap F _ c * z) < 1 := fun c z hz => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle c)) hz
  constructor
  · have : vcX D - algebraMap F V.toAffine.FunctionField ((D.u : F) ^ 2 * x + D.r) =
        algebraMap F _ ((D.u : F) ^ 2) * (genericX V.toAffine - algebraMap F _ x) := by
      simp only [vcX, map_add, map_mul]; ring
    rw [this]; exact hmul _ _ hx
  · have : vcY D - algebraMap F V.toAffine.FunctionField
          ((D.u : F) ^ 3 * y + (D.u : F) ^ 2 * D.s * x + D.t) =
        algebraMap F _ ((D.u : F) ^ 3) * (genericY V.toAffine - algebraMap F _ y) +
          algebraMap F _ ((D.u : F) ^ 2 * D.s) * (genericX V.toAffine - algebraMap F _ x) := by
      simp only [vcY, map_add, map_mul]; ring
    rw [this]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (hmul _ _ hy) (hmul _ _ hx))

/-- **The change of variables acts on points by the coordinate formula.** Kind: PROVED. -/
theorem pointMap_vc [DecidableEq F] [V.IsElliptic] [W.IsElliptic] {x y : F}
    (h : V.toAffine.Nonsingular x y)
    (hQ : W.toAffine.Nonsingular ((D.u : F) ^ 2 * x + D.r)
      ((D.u : F) ^ 3 * y + (D.u : F) ^ 2 * D.s * x + D.t)) :
    (Isogeny.Hom.ofIsogeny (vcIsogeny D hVW)).pointMap (.some x y h) = .some _ _ hQ := by
  rw [Isogeny.Hom.pointMap_eq_iff, Isogeny.Hom.tautologicalPoint_ofIsogeny,
    Isogeny.tautologicalPoint_eq_map_genericPoint, genericPoint_eq_some, Point.map_some,
    Point.equivBaseChangeSelf_some, some_sub_baseChange_mem_polePoints_iff,
    coe_pointEquivDegreeOnePlace_some, fieldPullback_genericX, fieldPullback_genericY]
  exact vc_val_lt D _ (valuation_pointPlace_genericX_sub_lt_one V.toAffine h.left)
    (valuation_pointPlace_genericY_sub_lt_one V.toAffine h.left)

section Main
variable [DecidableEq F]

/-- The action on points is Tau Ceti's `equivVariableChange`. Kind: PROVED. -/
theorem pointMap_vc_eq (W : WeierstrassCurve F) (C : VariableChange F) [W.IsElliptic]
    (P : (C • W).toAffine.Point) :
    (Isogeny.Hom.ofIsogeny (vcIsogeny C (rfl : C • W = C • W))).pointMap P =
      Point.equivVariableChange W C P := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, Isogeny.Hom.pointMap_zero, Point.equivVariableChange_zero]
  · rw [pointMap_vc C rfl h ((variableChange_nonsingular W C x y).mpr h),
      Point.equivVariableChange_some]

/-- The inverse change of variables acts by `equivVariableChange.symm`. Kind: PROVED. -/
theorem pointMap_vc_inv_eq (W : WeierstrassCurve F) (C : VariableChange F) [W.IsElliptic]
    (P : W.toAffine.Point) :
    (Isogeny.Hom.ofIsogeny (vcIsogeny C⁻¹ (inv_smul_smul C W))).pointMap P =
      (Point.equivVariableChange W C).symm P := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, Isogeny.Hom.pointMap_zero, Point.equivVariableChange_symm_zero]
  · rw [Point.equivVariableChange_symm_some]
    exact pointMap_vc C⁻¹ (inv_smul_smul C W) h _

/-- **Having no CM is invariant under a change of variables** over a separably closed field
(tex 1765–1767). Kind: PROVED. -/
theorem noCM_variableChange [IsSepClosed F] (W : WeierstrassCurve F) (C : VariableChange F)
    [W.IsElliptic]
    (hW : ∀ f : Isogeny.Hom W.toAffine W.toAffine, ∃ n : ℤ, f = n • Isogeny.Hom.id W.toAffine) :
    ∀ f : Isogeny.Hom (C • W).toAffine (C • W).toAffine,
      ∃ n : ℤ, f = n • Isogeny.Hom.id (C • W).toAffine := by
  intro f
  let Φ := Isogeny.Hom.ofIsogeny (vcIsogeny C (rfl : C • W = C • W))
  let Ψ := Isogeny.Hom.ofIsogeny (vcIsogeny C⁻¹ (inv_smul_smul C W))
  obtain ⟨n, hn⟩ := hW (Φ.comp (f.comp Ψ))
  refine ⟨n, Isogeny.Hom.ext_pointMap fun P => ?_⟩
  let e := Point.addEquivVariableChange W C
  have he : ∀ Q, e Q = Point.equivVariableChange W C Q := fun _ => rfl
  have hes : ∀ Q, e.symm Q = (Point.equivVariableChange W C).symm Q := fun _ => rfl
  have hg := congrArg (fun g : Isogeny.Hom W.toAffine W.toAffine => g.pointMap (e P)) hn
  simp only [Isogeny.Hom.comp_pointMap, Isogeny.Hom.zsmul_pointMap, Isogeny.Hom.id_pointMap] at hg
  rw [Isogeny.Hom.zsmul_pointMap, Isogeny.Hom.id_pointMap]
  have hΨ : Ψ.pointMap (e P) = P := by
    rw [pointMap_vc_inv_eq, he, Equiv.symm_apply_apply]
  rw [hΨ, pointMap_vc_eq, ← he] at hg
  have := congrArg e.symm hg
  rwa [map_zsmul, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply] at this
end Main

end ZInQ.Contrib.CloudB3E1NoCM
