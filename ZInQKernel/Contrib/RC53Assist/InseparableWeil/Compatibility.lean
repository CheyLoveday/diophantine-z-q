import ZInQKernel.Contrib.RC53Assist.DetDegree.Reduction
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Divisor.Automorphism

/-!
# Weil-pairing compatibility with inseparable endomorphisms

The pullback of a point divisor is its geometric fibre with ramification
multiplicities. Retaining these multiplicities in the divisor proof of
Weil-pairing compatibility avoids a separability assumption. The sum of
the multiplicities is the degree of the isogeny.

References: Silverman, The Arithmetic of Elliptic Curves, II.3, III.3.5,
III.4.8, III.8.2, and III.8.6; Stichtenoth, Algebraic Function Fields and
Codes, Definition 3.1.8 and Corollary 3.1.14.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.InseparableWeil

open WeierstrassCurve WeierstrassCurve.Affine TauCeti TauCeti.Isogeny AlgebraicGeometry
open scoped Classical

section Intertwining

variable {K : Type*} [Field K] [DecidableEq K] [IsSepClosed K]
  {W₁ W₂ : WeierstrassCurve.Affine K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁ W₂) (α : W₁.Point →+ W₂.Point)
  (hα : ∀ P, (Hom.ofIsogeny φ).pointMap P = α P)

include hα

/-- **PROVED theorem** (Silverman III.4.8): an isogeny with its additive
point map intertwines translation on the tautological point, without a
separability assumption. -/
theorem map_translation_tautologicalPoint (P : W₁.Point) :
    Point.map (translation W₁ (Point.equivBaseChangeSelf W₁ P) : W₁.FunctionField →ₐ[K]
        W₁.FunctionField) (Hom.ofIsogeny φ).tautologicalPoint =
      (Hom.ofIsogeny φ).tautologicalPoint + Point.baseChange (W' := W₂) K
        W₁.FunctionField (Point.equivBaseChangeSelf W₂ (α P)) := by
  have hred : ∀ R : W₁.Point, reductionOfDegreeEqOne W₂ (W₁.pointEquivDegreeOnePlace R).2
      (Hom.ofIsogeny φ).tautologicalPoint = Point.equivBaseChangeSelf W₂ (α R) := by
    intro R
    rw [← hα R, Hom.pointMap, AddEquiv.apply_symm_apply]
  rw [← sub_eq_zero]
  apply ZInQ.Contrib.CloudB3RC53.WeilIsogeny.eq_zero_of_forall_mem_polePoints
  intro Q
  rw [← ker_reductionOfDegreeEqOne W₂ (W₁.pointEquivDegreeOnePlace Q).2,
    AddMonoidHom.mem_ker, map_sub, map_add, reductionOfDegreeEqOne_baseChange]
  have e : translation W₁ (Point.equivBaseChangeSelf W₁ P) •
      (W₁.pointEquivDegreeOnePlace (Q + P)).1 = (W₁.pointEquivDegreeOnePlace Q).1 := by
    rw [translation_smul_pointEquivDegreeOnePlace, add_sub_cancel_right]
  have h1 : reductionOfDegreeEqOne W₂ (W₁.pointEquivDegreeOnePlace Q).2
      (Point.map (translation W₁ (Point.equivBaseChangeSelf W₁ P) : W₁.FunctionField →ₐ[K]
        W₁.FunctionField) (Hom.ofIsogeny φ).tautologicalPoint) =
      Point.equivBaseChangeSelf W₂ (α (Q + P)) := by
    rw [ZInQ.Contrib.CloudB3RC53.WeilIsogeny.reductionOfDegreeEqOne_congr e.symm
        (W₁.pointEquivDegreeOnePlace Q).2
        ((Place.degree_smul _ _).trans (W₁.pointEquivDegreeOnePlace (Q + P)).2),
      reductionOfDegreeEqOne_smul_map (W := W₂) (hw := (W₁.pointEquivDegreeOnePlace (Q + P)).2),
      hred]
  rw [h1, hred, map_add, map_add, sub_self]

/-- **PROVED theorem** (Silverman III.4.8): pullback along an isogeny
intertwines the translation automorphisms of the function fields. -/
theorem fieldPullback_comp_translation (P : W₁.Point) :
    φ.fieldPullback.comp (translation W₂ (Point.equivBaseChangeSelf W₂ (α P)) :
        W₂.FunctionField →ₐ[K] W₂.FunctionField) =
      (translation W₁ (Point.equivBaseChangeSelf W₁ P) : W₁.FunctionField →ₐ[K]
        W₁.FunctionField).comp φ.fieldPullback := by
  apply map_genericPoint_injective W₂ (Ω := W₁.FunctionField)
  simp only
  rw [← Point.map_map, ← Point.map_map, map_translation_genericPoint,
    translatedGenericPoint_def, map_add, ← Isogeny.tautologicalPoint_eq_map_genericPoint,
    ← Hom.tautologicalPoint_ofIsogeny, map_translation_tautologicalPoint φ α hα,
    Point.map_baseChange]

/-- **PROVED theorem** (Silverman III.4.8): every isogeny with its additive
point map commutes with multiplication by an integer. -/
theorem comp_mulByInt {n : ℤ} (h₁ : psiFunctionField W₁ n ≠ 0)
    (h₂ : psiFunctionField W₂ n ≠ 0) :
    φ.comp (mulByIntIsogeny W₁ h₁) = (mulByIntIsogeny W₂ h₂).comp φ := by
  apply Hom.ofIsogeny_injective
  rw [← Hom.ofIsogeny_comp_ofIsogeny, ← Hom.ofIsogeny_comp_ofIsogeny,
    ofIsogeny_mulByIntIsogeny, ofIsogeny_mulByIntIsogeny, Hom.zsmul_comp, Hom.id_comp]
  refine Hom.ext_pointMap fun P => ?_
  rw [Hom.comp_pointMap, Hom.zsmul_pointMap, Hom.zsmul_pointMap,
    Hom.id_pointMap, hα, hα, map_zsmul]

/-- **PROVED theorem** (Silverman III.4.8): the function-field pullbacks
of an isogeny and multiplication by an integer commute. -/
theorem fieldPullback_mulByInt_comm {n : ℤ} (h₁ : psiFunctionField W₁ n ≠ 0)
    (h₂ : psiFunctionField W₂ n ≠ 0) (z : W₂.FunctionField) :
    (mulByIntIsogeny W₁ h₁).fieldPullback (φ.fieldPullback z) =
      φ.fieldPullback ((mulByIntIsogeny W₂ h₂).fieldPullback z) := by
  have h := congrArg (fun ψ : Isogeny W₁ W₂ => ψ.fieldPullback z)
    (comp_mulByInt φ α hα h₁ h₂)
  simpa only [Isogeny.comp_fieldPullback, AlgHom.comp_apply] using h

end Intertwining

section WeightedFibres

variable {K : Type*} [Field K] [DecidableEq K]
  {W₁ W₂ : WeierstrassCurve.Affine K} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **DEFINITION** (Silverman II.3; Stichtenoth Definition 3.1.5): the
ramification multiplicity of an isogeny at a geometric point. -/
def ramificationMultiplicity (φ : Isogeny W₁ W₂) (R : W₁.Point) : ℕ :=
  letI := φ.fieldPullback.toRingHom.toAlgebra
  Place.ramificationIdx W₂.FunctionField (W₁.pointEquivDegreeOnePlace R).1

/-- **DEFINITION** (Silverman II.2 and III.4.8): the finite geometric
fibre of a nonzero isogeny, using its existing point map. -/
def fibreFinset (φ : Isogeny W₁ W₂) (Q : W₂.Point) : Finset W₁.Point :=
  (Hom.finite_setOf_pointMap_eq (Hom.ofIsogeny_ne_zero φ) Q).toFinset

/-- **PROVED theorem** (Silverman II.2): membership in a geometric
fibre is precisely equality of the image point. -/
theorem mem_fibreFinset (φ : Isogeny W₁ W₂) (Q : W₂.Point) (R : W₁.Point) :
    R ∈ fibreFinset φ Q ↔ (Hom.ofIsogeny φ).pointMap R = Q :=
  Set.Finite.mem_toFinset _

variable [IsAlgClosed K]

/-- **PROVED theorem** (Silverman II.3; Stichtenoth Remark 1.1.17): every
place above a geometric point is the place of a point in its fibre,
including for inseparable isogenies. -/
theorem restrict_eq_pointEquivDegreeOnePlace_iff (φ : Isogeny W₁ W₂)
    (Q : W₂.Point) (P : Place K W₁.FunctionField) :
    letI := φ.fieldPullback.toRingHom.toAlgebra
    haveI := φ.finiteDimensional_functionField (fun _ => rfl)
    P.restrict K W₂.FunctionField = (W₂.pointEquivDegreeOnePlace Q).1 ↔
      ∃ R, (Hom.ofIsogeny φ).pointMap R = Q ∧ (W₁.pointEquivDegreeOnePlace R).1 = P := by
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  have := φ.finiteDimensional_functionField (fun _ => rfl)
  have hover (R : W₁.Point) :
      (W₁.pointEquivDegreeOnePlace R).1.restrict K W₂.FunctionField =
        (W₂.pointEquivDegreeOnePlace Q).1 ↔ (Hom.ofIsogeny φ).pointMap R = Q :=
    (Hom.pointMap_ofIsogeny_eq_iff_restrict φ).symm
  refine ⟨fun hP => ?_, fun ⟨R, hR, hRP⟩ => by rw [← hRP]; exact (hover R).mpr hR⟩
  have hdeg : P.degree = 1 := P.degree_eq_one_of_isAlgClosed_of_isFunctionField W₁.isFunctionField
  obtain ⟨R, hR⟩ : ∃ R, (W₁.pointEquivDegreeOnePlace R).1 = P :=
    ⟨(W₁.pointEquivDegreeOnePlace).symm ⟨P, hdeg⟩, by simp⟩
  exact ⟨R, (hover R).mp (by rw [hR]; exact hP), hR⟩

/-- **PROVED theorem** (Silverman II.3; Stichtenoth Definition 3.1.8):
the pullback of a geometric point divisor is its fibre, weighted by the
ramification multiplicities, without a separability assumption. -/
theorem divisorPullback_ofPoint_weighted (φ : Isogeny W₁ W₂) (Q : W₂.Point) :
    ZInQ.Contrib.CloudB3RC53.WeilIsogeny.pb φ
        (WeilDivisor.ofPoint (W₂.pointEquivDegreeOnePlace Q).1) =
      ∑ R ∈ fibreFinset φ Q, ramificationMultiplicity φ R •
        WeilDivisor.ofPoint (W₁.pointEquivDegreeOnePlace R).1 := by
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  have := φ.finiteDimensional_functionField (fun _ => rfl)
  let s := (fibreFinset φ Q).map ⟨fun R => (W₁.pointEquivDegreeOnePlace R).1,
    Subtype.val_injective.comp (W₁.pointEquivDegreeOnePlace).injective⟩
  have hsum : ∑ R ∈ fibreFinset φ Q, ramificationMultiplicity φ R •
        WeilDivisor.ofPoint (W₁.pointEquivDegreeOnePlace R).1 =
      WeilDivisor.ofFinsetWithMultiplicity s (Place.ramificationIdx W₂.FunctionField) := by
    rw [WeilDivisor.ofFinsetWithMultiplicity_eq_sum, Finset.sum_map, Function.Embedding.coeFn_mk]
    simp only [ramificationMultiplicity, natCast_zsmul]
  rw [hsum]
  ext P
  change (φ.divisorPullback (fun _ => rfl)
    (WeilDivisor.ofPoint (W₂.pointEquivDegreeOnePlace Q).1)).coeff P = _
  rw [Isogeny.coeff_divisorPullback, WeilDivisor.coeff_ofFinsetWithMultiplicity]
  split_ifs with hmem
  · obtain ⟨R, hR, hRP⟩ := Finset.mem_map.mp hmem
    rw [(restrict_eq_pointEquivDegreeOnePlace_iff φ Q P).mpr
      ⟨R, (mem_fibreFinset φ Q R).mp hR, hRP⟩, WeilDivisor.coeff_ofPoint_self, mul_one]
  · rw [WeilDivisor.coeff_ofPoint_of_ne (by
        intro hP
        obtain ⟨R, hR, hRP⟩ := (restrict_eq_pointEquivDegreeOnePlace_iff φ Q P).mp hP
        exact hmem (Finset.mem_map.mpr ⟨R, (mem_fibreFinset φ Q R).mpr hR, hRP⟩)),
      mul_zero, Nat.cast_zero]

/-- **PROVED theorem** (Silverman II.3 and III.4.8): ramification
multiplicity is unchanged by translation, because an isogeny intertwines
the corresponding function-field automorphisms. -/
theorem ramificationMultiplicity_add (φ : Isogeny W₁ W₂) (α : W₁.Point →+ W₂.Point)
    (hα : ∀ P, (Hom.ofIsogeny φ).pointMap P = α P) (T R : W₁.Point) :
    ramificationMultiplicity φ (T + R) = ramificationMultiplicity φ R := by
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  let σ₁ := translation W₁ (Point.equivBaseChangeSelf W₁ T)
  let σ₂ := translation W₂ (Point.equivBaseChangeSelf W₂ (α T))
  have hp : translation W₁ (Point.equivBaseChangeSelf W₁ (-T)) •
      (W₁.pointEquivDegreeOnePlace R).1 = (W₁.pointEquivDegreeOnePlace (T + R)).1 := by
    rw [translation_smul_pointEquivDegreeOnePlace]
    congr 2
    abel
  have hv : (W₁.pointEquivDegreeOnePlace (T + R)).1.valuation =
      (W₁.pointEquivDegreeOnePlace R).1.valuation.comap σ₁.toRingHom := by
    ext z
    rw [← hp, Place.valuation_smul, map_neg, translation_neg,
      AlgEquiv.aut_inv, AlgEquiv.symm_symm]
    rfl
  have hc : σ₁.toRingHom.comp φ.fieldPullback.toRingHom =
      φ.fieldPullback.toRingHom.comp σ₂.toRingHom := by
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      RingEquiv.toRingHom_eq_coe, AlgEquiv.toAlgHom_toRingHom,
      AlgEquiv.toRingEquiv_toRingHom] using
      congrArg AlgHom.toRingHom (fieldPullback_comp_translation φ α hα T).symm
  change Place.ramificationIdx W₂.FunctionField (W₁.pointEquivDegreeOnePlace (T + R)).1 =
    Place.ramificationIdx W₂.FunctionField (W₁.pointEquivDegreeOnePlace R).1
  rw [Place.ramificationIdx_def, Place.ramificationIdx_def]
  change ((W₁.pointEquivDegreeOnePlace (T + R)).1.valuation.comap φ.fieldPullback.toRingHom).ordIndex =
    ((W₁.pointEquivDegreeOnePlace R).1.valuation.comap φ.fieldPullback.toRingHom).ordIndex
  rw [hv, ← Valuation.comap_comp, hc, Valuation.comap_comp]
  exact Valuation.ordIndex_comap_of_surjective _ (f := σ₂.toRingHom) σ₂.toRingEquiv.surjective

/-- **PROVED theorem** (Silverman II.3; Stichtenoth Corollary 3.1.14):
the sum of the ramification multiplicities in every geometric fibre is
the degree of the isogeny. No separability assumption is required. -/
theorem sum_ramificationMultiplicity (φ : Isogeny W₁ W₂) (Q : W₂.Point) :
    ∑ R ∈ fibreFinset φ Q, ramificationMultiplicity φ R = φ.degree := by
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  have := φ.finiteDimensional_functionField (fun _ => rfl)
  let s := (fibreFinset φ Q).map ⟨fun R => (W₁.pointEquivDegreeOnePlace R).1,
    Subtype.val_injective.comp (W₁.pointEquivDegreeOnePlace).injective⟩
  have hs (P : Place K W₁.FunctionField) :
      P ∈ s ↔ P.restrict K W₂.FunctionField = (W₂.pointEquivDegreeOnePlace Q).1 := by
    rw [restrict_eq_pointEquivDegreeOnePlace_iff φ Q P]
    constructor
    · rintro hP
      obtain ⟨R, hR, hRP⟩ := Finset.mem_map.mp hP
      exact ⟨R, (mem_fibreFinset φ Q R).mp hR, hRP⟩
    · rintro ⟨R, hR, hRP⟩
      exact Finset.mem_map.mpr ⟨R, (mem_fibreFinset φ Q R).mpr hR, hRP⟩
  have hrel (P : Place K W₁.FunctionField) : Place.relativeDegree K W₂.FunctionField P = 1 := by
    have hdeg := P.degree_eq_one_of_isAlgClosed_of_isFunctionField W₁.isFunctionField
    have hres := (P.restrict K W₂.FunctionField).degree_eq_one_of_isAlgClosed_of_isFunctionField
      W₂.isFunctionField
    have h := Place.degree_eq_degree_restrict_mul_relativeDegree K W₂.FunctionField P
    rw [hdeg, hres, one_mul] at h
    exact h.symm
  have hfund := Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isFunctionField
    K W₂.FunctionField W₂.isFunctionField (W₂.pointEquivDegreeOnePlace Q).1 hs
  simp only [hrel, mul_one] at hfund
  rw [Finset.sum_map, Function.Embedding.coeFn_mk] at hfund
  rw [Isogeny.degree_eq_finrank φ (fun _ => rfl)]
  exact hfund

end WeightedFibres

section WeilDivisors

open ZInQ.Contrib.CloudB3RC53.WeilIsogeny

variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]
  {E₁ E₂ : WeierstrassCurve K} [E₁.IsElliptic] [E₂.IsElliptic]

/-- **PROVED theorem** (Silverman III.8.2; Stichtenoth Definition 3.1.8):
the Weil divisor pulls back to the multiplication pullback of the
translated kernel divisor, with all ramification multiplicities retained.
This includes inseparable isogenies. -/
theorem pb_weilPairingDivisor_weighted (φ : Isogeny E₁.toAffine E₂.toAffine)
    (α : E₁.toAffine.Point →+ E₂.toAffine.Point)
    (hα : ∀ P, (Hom.ofIsogeny φ).pointMap P = α P) {n : ℤ}
    (h₁ : psiFunctionField E₁.toAffine n ≠ 0) (h₂ : psiFunctionField E₂.toAffine n ≠ 0)
    (T : E₁.toAffine.Point) :
    pb φ (weilPairingDivisor E₂ h₂ (α T)) =
      pb (mulByIntIsogeny E₁.toAffine h₁)
        (∑ R ∈ fibreFinset φ 0, ramificationMultiplicity φ R •
          (WeilDivisor.ofPoint (E₁.toAffine.pointEquivDegreeOnePlace (T + R)).1 -
            WeilDivisor.ofPoint (E₁.toAffine.pointEquivDegreeOnePlace R).1)) := by
  have hpb : ∀ D, pb φ (pb (mulByIntIsogeny E₂.toAffine h₂) D) =
      pb (mulByIntIsogeny E₁.toAffine h₁) (pb φ D) := by
    intro D
    rw [← pb_comp, ← pb_comp, comp_mulByInt φ α hα h₁ h₂]
  have hW : ∀ Q : E₂.toAffine.Point, weilPairingDivisor E₂ h₂ Q =
      pb (mulByIntIsogeny E₂.toAffine h₂)
          (WeilDivisor.ofPoint (E₂.toAffine.pointEquivDegreeOnePlace Q).1) -
        pb (mulByIntIsogeny E₂.toAffine h₂)
          (WeilDivisor.ofPoint (E₂.toAffine.pointEquivDegreeOnePlace 0).1) := by
    intro Q
    rw [weilPairingDivisor_def, ← coe_pointEquivDegreeOnePlace_zero]
    rfl
  have hfib0 : pb φ (WeilDivisor.ofPoint (E₂.toAffine.pointEquivDegreeOnePlace 0).1) =
      ∑ R ∈ fibreFinset φ 0, ramificationMultiplicity φ R •
        WeilDivisor.ofPoint (E₁.toAffine.pointEquivDegreeOnePlace R).1 :=
    divisorPullback_ofPoint_weighted φ 0
  have hfibT : pb φ (WeilDivisor.ofPoint (E₂.toAffine.pointEquivDegreeOnePlace (α T)).1) =
      ∑ R ∈ fibreFinset φ 0, ramificationMultiplicity φ R •
        WeilDivisor.ofPoint (E₁.toAffine.pointEquivDegreeOnePlace (T + R)).1 := by
    refine (divisorPullback_ofPoint_weighted φ (α T)).trans ?_
    refine Finset.sum_bij' (fun R _ => R - T) (fun R _ => T + R) ?_ ?_ ?_ ?_ ?_
    · intro R hR
      rw [mem_fibreFinset, hα] at hR ⊢
      rw [map_sub, hR, sub_self]
    · intro R hR
      rw [mem_fibreFinset, hα] at hR ⊢
      rw [map_add, hR, add_zero]
    · intro R _
      abel
    · intro R _
      abel
    · intro R _
      have hr : T + (R - T) = R := by abel
      have he := ramificationMultiplicity_add φ α hα T (R - T)
      rw [hr] at he
      rw [hr, he]
  rw [hW, map_sub, hpb, hpb, hfibT, hfib0, ← map_sub]
  simp only [smul_sub, Finset.sum_sub_distrib]

end WeilDivisors

/-- **DEFINITION** (Silverman III.4.8): the restriction of an additive
point map to the subgroup killed by a positive integer. -/
def torsionMap {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (α : A →+ B) (N : ℕ) (S : Submodule.torsionBy ℤ A (N : ℤ)) :
    Submodule.torsionBy ℤ B (N : ℤ) :=
  ⟨α S, by
    rw [Submodule.mem_torsionBy_iff, ← map_zsmul,
      (Submodule.mem_torsionBy_iff _ _).mp S.2, map_zero]⟩

section Pairing

open ZInQ.Contrib.CloudB3RC53.WeilIsogeny

variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]
  {E₁ E₂ : WeierstrassCurve K} [E₁.IsElliptic] [E₂.IsElliptic]

/-- **PROVED theorem** (Silverman III.8.2 and III.8.6): an arbitrary
isogeny over an algebraically closed field scales the Weil pairing by
its degree. The given additive point map is used on torsion, and no
separability hypothesis or Frobenius factorization is assumed. -/
theorem weilPairing_torsionMap (φ : Isogeny E₁.toAffine E₂.toAffine)
    (α : E₁.toAffine.Point →+ E₂.toAffine.Point)
    (hα : ∀ P, (Hom.ofIsogeny φ).pointMap P = α P)
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (S T : Submodule.torsionBy ℤ E₁.toAffine.Point (N : ℤ)) :
    weilPairing E₂ N hN (torsionMap α N S) (torsionMap α N T) =
      φ.degree • weilPairing E₁ N hN S T := by
  have := E₁.toAffine.isIntegrallyClosed_coordinateRing
  have := E₁.toAffine.isDedekindDomain_coordinateRing_of_isIntegrallyClosed
  have hc : ((N : ℤ) : K) ≠ 0 := by rwa [Int.cast_natCast]
  have h₁ := psiFunctionField_ne_zero E₁.toAffine hc
  have h₂ := psiFunctionField_ne_zero E₂.toAffine hc
  have hT₁ : (N : ℤ) • (T : E₁.toAffine.Point) = 0 :=
    (Submodule.mem_torsionBy_iff _ _).mp T.2
  have hT₂ : (N : ℤ) • ((torsionMap α N T : Submodule.torsionBy ℤ E₂.toAffine.Point
      (N : ℤ)) : E₂.toAffine.Point) = 0 :=
    (Submodule.mem_torsionBy_iff _ _).mp (torsionMap α N T).2
  obtain ⟨g₂, hg₂⟩ := exists_principal_eq_weilPairingDivisor E₂ hc hT₂
  obtain ⟨g₁, hg₁⟩ := exists_principal_eq_weilPairingDivisor E₁ hc hT₁
  set ψ := mulByIntIsogeny E₁.toAffine h₁
  have hex := fun R : E₁.toAffine.Point =>
    E₁.toAffine.exists_principal_eq_ofPoint_add_sub (T : E₁.toAffine.Point) R
  set H : E₁.toAffine.FunctionFieldˣ :=
    ∏ R ∈ fibreFinset φ 0, (hex R).choose ^ ramificationMultiplicity φ R
  have hH : Divisor.principal E₁.toAffine.isFunctionField H =
      ∑ R ∈ fibreFinset φ 0, ramificationMultiplicity φ R •
        (WeilDivisor.ofPoint (E₁.toAffine.pointEquivDegreeOnePlace (T + R)).1 -
          WeilDivisor.ofPoint (E₁.toAffine.pointEquivDegreeOnePlace T).1 -
          (WeilDivisor.ofPoint (E₁.toAffine.pointEquivDegreeOnePlace R).1 -
            WeilDivisor.ofPoint (Place.infinity E₁.toAffine))) := by
    rw [principal_prod]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [principal_pow, (hex R).choose_spec]
  set G : E₁.toAffine.FunctionFieldˣ :=
    Units.map (φ.fieldPullback : E₂.toAffine.FunctionField →* E₁.toAffine.FunctionField) g₂
  set g' : E₁.toAffine.FunctionFieldˣ := g₁ ^ φ.degree *
    Units.map (ψ.fieldPullback : E₁.toAffine.FunctionField →* E₁.toAffine.FunctionField) H
  have hpbP : ∀ {A B : WeierstrassCurve.Affine K} (χ : Isogeny A B) (z : B.FunctionFieldˣ),
      pb χ (Divisor.principal B.isFunctionField z) = Divisor.principal A.isFunctionField
        (Units.map (χ.fieldPullback : B.FunctionField →* A.FunctionField) z) :=
    fun χ z => @Isogeny.divisorPullback_principal K _ _ _ χ χ.fieldPullback.toRingHom.toAlgebra
      (fun _ => rfl) z
  have hdivG : Divisor.principal E₁.toAffine.isFunctionField G =
      pb ψ (∑ R ∈ fibreFinset φ 0, ramificationMultiplicity φ R •
        (WeilDivisor.ofPoint (E₁.toAffine.pointEquivDegreeOnePlace (T + R)).1 -
          WeilDivisor.ofPoint (E₁.toAffine.pointEquivDegreeOnePlace R).1)) := by
    rw [← hpbP, hg₂]
    exact pb_weilPairingDivisor_weighted φ α hα h₁ h₂ T
  have hdivg' : Divisor.principal E₁.toAffine.isFunctionField g' =
      pb ψ (∑ R ∈ fibreFinset φ 0, ramificationMultiplicity φ R •
        (WeilDivisor.ofPoint (E₁.toAffine.pointEquivDegreeOnePlace (T + R)).1 -
          WeilDivisor.ofPoint (E₁.toAffine.pointEquivDegreeOnePlace R).1)) := by
    have hW : weilPairingDivisor E₁ h₁ T =
        pb ψ (WeilDivisor.ofPoint (E₁.toAffine.pointEquivDegreeOnePlace T).1 -
          WeilDivisor.ofPoint (Place.infinity E₁.toAffine)) := by
      rw [weilPairingDivisor_def, map_sub]
      rfl
    rw [Divisor.principal_mul, principal_pow, hg₁, ← hpbP, hH, hW,
      ← map_nsmul, ← map_add, ← sum_ramificationMultiplicity φ 0,
      Finset.sum_smul, ← Finset.sum_add_distrib]
    refine congrArg (pb ψ) (Finset.sum_congr rfl fun R _ => ?_)
    simp only [smul_sub]
    abel
  have hg₁N : (g₁ : E₁.toAffine.FunctionField) ^ N ∈ ψ.fieldPullback.fieldRange := by
    have := zpow_mem_fieldRange_mulByIntIsogeny E₁ h₁ hT₁ hg₁
    rwa [zpow_natCast] at this
  have hGN : (G : E₁.toAffine.FunctionField) ^ N ∈ ψ.fieldPullback.fieldRange := by
    have h2 := zpow_mem_fieldRange_mulByIntIsogeny E₂ h₂ hT₂ hg₂
    rw [zpow_natCast] at h2
    obtain ⟨k, hk⟩ := h2
    refine ⟨φ.fieldPullback k, ?_⟩
    change ψ.fieldPullback (φ.fieldPullback k) = (φ.fieldPullback (g₂ : _)) ^ N
    rw [fieldPullback_mulByInt_comm φ α hα h₁ h₂ k, ← map_pow]
    exact congrArg φ.fieldPullback hk
  have hHm : ((Units.map (ψ.fieldPullback : E₁.toAffine.FunctionField →* E₁.toAffine.FunctionField)
      H : E₁.toAffine.FunctionFieldˣ) : E₁.toAffine.FunctionField) ∈ ψ.fieldPullback.fieldRange :=
    ⟨H, rfl⟩
  have hg₁d : ((g₁ ^ φ.degree : E₁.toAffine.FunctionFieldˣ) : E₁.toAffine.FunctionField) ^ N ∈
      ψ.fieldPullback.fieldRange := by
    rw [Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul]
    exact pow_mem hg₁N _
  have hg'N : (g' : E₁.toAffine.FunctionField) ^ N ∈ ψ.fieldPullback.fieldRange := by
    rw [Units.val_mul, mul_pow]
    exact mul_mem hg₁d (pow_mem hHm N)
  have hκ : ψ.kummerCharacter N G hGN = ψ.kummerCharacter N g₁ hg₁N ^ φ.degree := by
    rw [kummerCharacter_eq_of_principal_eq hGN (hdivG.trans hdivg'.symm),
      kummerCharacter_congr N ψ rfl _ hg'N, kummerCharacter_mul hg₁d (pow_mem hHm N),
      kummerCharacter_eq_one_of_mem_fieldRange hHm, mul_one, kummerCharacter_pow N ψ hg₁N]
  have hS : (N : ℤ) • (S : E₁.toAffine.Point) = 0 := (Submodule.mem_torsionBy_iff _ _).mp S.2
  let S' : Multiplicative ψ.ker := Multiplicative.ofAdd
    ⟨Point.equivBaseChangeSelf E₁.toAffine S,
      (mem_ker_mulByIntIsogeny_iff _ _).mpr (by rw [← map_zsmul, hS, map_zero])⟩
  have key1 : algebraMap K E₁.toAffine.FunctionField (ψ.kummerCharacter N G hGN S' : Kˣ) =
      translation E₁.toAffine (Point.equivBaseChangeSelf E₁.toAffine S)
        (G : E₁.toAffine.FunctionField) / G := algebraMap_kummerCharacter hGN S'
  have key2 : algebraMap K E₁.toAffine.FunctionField (ψ.kummerCharacter N g₁ hg₁N S' : Kˣ) =
      algebraMap K E₁.toAffine.FunctionField ((weilPairing E₁ N hN S T).toMul : Kˣ) :=
    (algebraMap_kummerCharacter hg₁N S').trans (algebraMap_weilPairing E₁ N hN hg₁).symm
  have key3 : translation E₁.toAffine (Point.equivBaseChangeSelf E₁.toAffine S)
      (G : E₁.toAffine.FunctionField) / G = algebraMap K E₁.toAffine.FunctionField
        ((weilPairing E₂ N hN (torsionMap α N S) (torsionMap α N T)).toMul : Kˣ) := by
    have ht : φ.fieldPullback (translation E₂.toAffine
        (Point.equivBaseChangeSelf E₂.toAffine (α S)) (g₂ : E₂.toAffine.FunctionField)) =
        translation E₁.toAffine (Point.equivBaseChangeSelf E₁.toAffine S)
          (φ.fieldPullback (g₂ : E₂.toAffine.FunctionField)) := by
      simpa only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply] using
        congrArg (fun χ : E₂.toAffine.FunctionField →ₐ[K] E₁.toAffine.FunctionField =>
          χ (g₂ : E₂.toAffine.FunctionField)) (fieldPullback_comp_translation φ α hα S)
    change translation E₁.toAffine (Point.equivBaseChangeSelf E₁.toAffine S)
      (φ.fieldPullback g₂) / φ.fieldPullback g₂ = _
    have hw2 : algebraMap K E₂.toAffine.FunctionField
        ((weilPairing E₂ N hN (torsionMap α N S) (torsionMap α N T)).toMul : Kˣ) =
        translation E₂.toAffine (Point.equivBaseChangeSelf E₂.toAffine (α S))
          (g₂ : E₂.toAffine.FunctionField) / g₂ :=
      algebraMap_weilPairing E₂ N hN (S := torsionMap α N S) hg₂
    rw [← ht, ← map_div₀, ← hw2, AlgHom.commutes]
  have hfin : algebraMap K E₁.toAffine.FunctionField
      ((weilPairing E₂ N hN (torsionMap α N S) (torsionMap α N T)).toMul : Kˣ) =
      algebraMap K E₁.toAffine.FunctionField
        ((((weilPairing E₁ N hN S T).toMul : Kˣ) : K) ^ φ.degree) := by
    rw [← key3, ← key1, hκ, MonoidHom.pow_apply, SubmonoidClass.coe_pow,
      Units.val_pow_eq_pow_val, map_pow, key2, ← map_pow]
  have hinj := (algebraMap K E₁.toAffine.FunctionField).injective hfin
  apply Additive.toMul.injective
  rw [toMul_nsmul]
  ext
  simpa using hinj

end Pairing

/-- **PROVED theorem** (Silverman III.8.2, III.8.6, and V.2.3): the
prime-power Weil-pairing compatibility for every nonzero inseparable
endomorphism of a reduced elliptic curve follows from the
ramification-weighted divisor argument. -/
theorem inseparableWeilPairingCompatibility_proved :
    ZInQ.Contrib.RC53Assist.DetDegree.InseparableWeilPairingCompatibility := by
  intro p _ Et _ ℓ _ _ f hf _ α hα n hN S T
  let : NeZero (ℓ ^ n) := ⟨pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero⟩
  have hφ : ∀ P, (Hom.ofIsogeny (Hom.toIsogeny hf)).pointMap P = α P := by
    simpa only [Hom.ofIsogeny_toIsogeny] using hα
  have hm (U : TateModuleLevel ℓ
      (Et.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point n) :
      TateModule.levelMap (p := ℓ) α n U = torsionMap α (ℓ ^ n) U :=
    Subtype.ext rfl
  rw [hm S, hm T]
  have h := weilPairing_torsionMap (Hom.toIsogeny hf) α hφ (ℓ ^ n) hN S T
  rw [← Hom.degree_ofIsogeny, Hom.ofIsogeny_toIsogeny] at h
  exact h

/-- **PROVED theorem** (Silverman III.8.6 and V.2.3): every endomorphism
of a reduced elliptic curve has Tate-module determinant equal to its
degree, including zero, separable, and inseparable endomorphisms. -/
theorem detEqDegree_proved : ZInQ.Contrib.CloudB3RC53.ModularWeil.DetEqDegree :=
  ZInQ.Contrib.RC53Assist.DetDegree.detEqDegree_of_inseparableWeilPairingCompatibility
    inseparableWeilPairingCompatibility_proved

end ZInQ.Contrib.RC53Assist.InseparableWeil
