import ZInQKernel.Contrib.OneProof.RC.X0Model.Rational
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.PowerSeries.Inverse

/-! The specialization step for the rational model. The Laurent-series
embedding gives the rational point at the formal q-cusp. The same
valuative argument works on any local analytic branch once its field
embedding is constructed. Tex 1785–1787 and 2837–2838; on the spot
(provenance (c)). -/

noncomputable section

open AlgebraicGeometry CategoryTheory ModularCurve TopologicalSpace

namespace ZInQ.Manuscript.RC.X0Model

private theorem eq_over_rat {K : Type} [CommRing K]
    (f g : Spec (.of K) ⟶ Spec (.of ℚ)) : f = g := by
  apply Spec.homEquiv.injective
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

/-- The generic map indexed by a field realization of the modular functions. -/
def genericMap (N : ℕ) [NeZero N] {K : Type} [Field K]
    (e : modularFunctionField N →+* K) : Spec (.of K) ⟶ curve N :=
  Spec.map (CommRingCat.ofHom (e.comp (functionField N).toRingHom)) ≫
    (curve N).fromSpecStalk (genericPoint (curve N))

private def specializationSquare (N : ℕ) [NeZero N]
    {R K : Type} [CommRing R] [IsDomain R] [ValuationRing R] [Algebra ℚ R]
    [Field K] [Algebra R K] [IsFractionRing R K] (e : modularFunctionField N →+* K) :
    ValuativeCommSq (overQ N) where
  R := R
  K := K
  i₁ := genericMap N e
  i₂ := Spec.map (CommRingCat.ofHom (algebraMap ℚ R))
  commSq := ⟨eq_over_rat _ _⟩

/-- A realization of the modular function field in a fraction field has a
unique extension over the valuation ring. This includes parameters over
singular points of the plane modular equation. -/
theorem existsUnique_specialization (N : ℕ) [NeZero N]
    {R K : Type} [CommRing R] [IsDomain R] [ValuationRing R] [Algebra ℚ R]
    [Field K] [Algebra R K] [IsFractionRing R K] (e : modularFunctionField N →+* K) :
    ∃! f : Spec (.of R) ⟶ curve N,
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ f = genericMap N e ∧
      f ≫ overQ N = Spec.map (CommRingCat.ofHom (algebraMap ℚ R)) := by
  let s := specializationSquare (R := R) N e
  have h := proper N
  rw [IsProper.eq_valuativeCriterion] at h
  have hvc : ValuativeCriterion (overQ N) := h.1.1.1
  obtain ⟨u⟩ := hvc s
  let l := u.default
  refine ⟨l.l, ⟨l.fac_left, l.fac_right⟩, ?_⟩
  intro g hg
  exact congrArg CommSq.LiftStruct.l (u.uniq ⟨g, hg.1, hg.2⟩)

/-- Pull back a section when the whole affine source is in its domain. -/
def sectionMap {X : Scheme.{0}} {A : Type} [CommRing A] (u : Spec (.of A) ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ u ⁻¹ᵁ U) : Γ(X, U) ⟶ CommRingCat.of A :=
  u.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (.of A)).hom

set_option backward.isDefEq.respectTransparency.types false in
theorem sectionMap_comp {X : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B]
    (u : Spec (.of A) ⟶ X) (e : A →+* B) (U : X.Opens) (hu : ⊤ ≤ u ⁻¹ᵁ U)
    (he : ⊤ ≤ (Spec.map (CommRingCat.ofHom e) ≫ u) ⁻¹ᵁ U) :
    sectionMap (Spec.map (CommRingCat.ofHom e) ≫ u) U he =
      sectionMap u U hu ≫ CommRingCat.ofHom e := by
  unfold sectionMap
  have htop : ⊤ ≤ Spec.map (CommRingCat.ofHom e) ⁻¹ᵁ ⊤ := by rw [Opens.map_top]
  have hApp : (Spec.map (CommRingCat.ofHom e)).appLE ⊤ ⊤ htop =
      (Spec.map (CommRingCat.ofHom e)).appTop :=
    (Spec.map (CommRingCat.ofHom e)).appLE_eq_app
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom e)) u U ⊤ ⊤ hu htop,
    Category.assoc, hApp,
    Scheme.ΓSpecIso_naturality, ← Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionMap_stalk {X : Scheme.{0}} {A : Type} [CommRing A] [IsLocalRing A]
    (u : Spec (.of A) ⟶ X) (U : X.Opens) (hu : ⊤ ≤ u ⁻¹ᵁ U) :
    sectionMap u U hu =
      X.presheaf.germ U _ (hu (show IsLocalRing.closedPoint A ∈ ⊤ from trivial)) ≫
        Scheme.stalkClosedPointTo u := by
  symm
  rw [Scheme.germ_stalkClosedPointTo]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, sectionMap,
    Scheme.Hom.appLE, Category.assoc]
  rfl

theorem sectionMap_generic (N : ℕ) [NeZero N] {K : Type} [Field K]
    (e : modularFunctionField N →+* K) (U : (curve N).Opens) [Nonempty U]
    (hu : ⊤ ≤ (genericMap N e) ⁻¹ᵁ U) :
    sectionMap (genericMap N e) U hu =
      (curve N).germToFunctionField U ≫ CommRingCat.ofHom (e.comp (functionField N).toRingHom) := by
  rw [sectionMap_stalk]
  exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk _ U _

/-- The formal q-arc selected by the specified Laurent expansion. -/
def formalQArc (N : ℕ) [NeZero N] : Spec (.of (PowerSeries ℚ)) ⟶ curve N :=
  (existsUnique_specialization (R := PowerSeries ℚ) N
    (modularFunctionField N).subtype).exists.choose

theorem formalQArc_generic (N : ℕ) [NeZero N] :
    Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries ℚ) (LaurentSeries ℚ))) ≫
      formalQArc N = genericMap N (modularFunctionField N).subtype :=
  (existsUnique_specialization (R := PowerSeries ℚ) N
    (modularFunctionField N).subtype).exists.choose_spec.1

/-- The special point q = 0 of the formal q-arc. -/
def cusp (N : ℕ) [NeZero N] : Spec (.of ℚ) ⟶ curve N :=
  Spec.map (CommRingCat.ofHom PowerSeries.constantCoeff) ≫ formalQArc N

theorem cusp_overQ (N : ℕ) [NeZero N] : cusp N ≫ overQ N = 𝟙 _ :=
  eq_over_rat _ _


end ZInQ.Manuscript.RC.X0Model
