import ZInQKernel.Contrib.OneProof.Y3FullThreeZ30
import ZInQKernel.Contrib.CloudR2Poincare.L1.Normalization
import ZInQKernel.HDecomp.QM.Polar
import ZInQKernel.OneProof.H.TailZ24

/-!
# The polarized full-three problem and the relative Lemma P

In the absence of a constructed relative dual abelian scheme, use the normalized
line bundle class on `A ×ₛ A` that corresponds to `A → Aᵛ` via the Poincaré bundle.
Principality is tested on each geometric fibre against an ample line bundle, with
trivial kernel on all test schemes. The global adjointness condition fixes the
involution of the manuscript, not just stability of the quaternionic order.

`RelativeLemmaP` identifies the unproved geometry. The comparison of universal
properties is conditional on that proposition.
-/

noncomputable section

namespace Y3LemmaP

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV Y3Fix SGRSplit Y3RouteA
open ZInQ.Contrib.CloudR2Poincare.L1
open scoped CategoryTheory.Obj MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The fixed Rosati involution of the manuscript, restricted to the actual maximal order. -/
def canonicalAdjoint (a : O) : O :=
  ⟨RvQMPolar.dag a.val, RvQMPolar.dag_mem a.property⟩

@[simp]
theorem canonicalAdjoint_involutive (a : O) :
    canonicalAdjoint (canonicalAdjoint a) = a :=
  Subtype.ext (RvQMPolar.dag_dag _)

theorem canonicalAdjoint_mul (a b : O) :
    canonicalAdjoint (a * b) = canonicalAdjoint b * canonicalAdjoint a :=
  Subtype.ext (RvQMPolar.dag_mul _ _)

/-- The adjoint used below is the adjoint of the manuscript's form
`E₀(x, y) = trd(μ⁻¹ x ȳ)`, before the sign is chosen on a complex fibre. -/
theorem canonicalAdjoint_riemann (a : O) (x y : B) :
    RvQMPolar.E0 (a.val * x) y = RvQMPolar.E0 x ((canonicalAdjoint a).val * y) :=
  RvQMPolar.E0_rosati _ _ _

/-- The map on the twofold fibre products induced by a map over a change of base. -/
def pairMap {S T : Scheme.{0}} {A : Over S} {B : Over T} {g : S ⟶ T}
    (h : A.left ⟶ B.left) (w : h ≫ B.hom = A.hom ≫ g) :
    (A ⊗ A).left ⟶ (B ⊗ B).left :=
  pullback.lift ((fst A A).left ≫ h) ((snd A A).left ≫ h)
    (by
      calc
        ((fst A A).left ≫ h) ≫ B.hom = (A ⊗ A).hom ≫ g := by
          rw [Category.assoc, w, ← Category.assoc, Over.w]
        _ = _ := by rw [Category.assoc, w, ← Category.assoc, Over.w])

@[simp]
theorem pairMap_id {S : Scheme.{0}} (A : Over S)
    (w : 𝟙 A.left ≫ A.hom = A.hom ≫ 𝟙 S) :
    pairMap (A := A) (B := A) (g := 𝟙 S) (𝟙 A.left) w = 𝟙 _ := by
  apply pullback.hom_ext
  · change pairMap (A := A) (B := A) (𝟙 A.left) w ≫ (fst A A).left = _
    simp [pairMap]
  · change pairMap (A := A) (B := A) (𝟙 A.left) w ≫ (snd A A).left = _
    simp [pairMap]

/-- Evaluation of a bundle on a pair of generalized points of an abelian scheme. -/
def evalClass {S : Scheme.{0}} {A U : Over S} (P : (A ⊗ A).left.Pic)
    (x y : U ⟶ A) : U.left.Pic :=
  Scheme.Pic.map (lift x y).left P

/-- Biadditivity as classes of line bundles, tested also on nonreduced schemes.
In particular the class is trivial along each zero section. -/
def IsBilinear {S : Scheme.{0}} {A : Over S} [MonObj A] (P : (A ⊗ A).left.Pic) : Prop :=
  ∀ (U : Over S) (x x' y y' : U ⟶ A),
    evalClass P (x * x') y = evalClass P x y * evalClass P x' y ∧
    evalClass P x (y * y') = evalClass P x y * evalClass P x y'

/-- Biadditivity normalizes the bundle in its first variable on all tests. -/
theorem IsBilinear.eval_one_left {S : Scheme.{0}} {A U : Over S} [MonObj A]
    {P : (A ⊗ A).left.Pic} (h : IsBilinear P) (y : U ⟶ A) :
    evalClass P 1 y = 1 := by
  have e : evalClass P 1 y = evalClass P 1 y * evalClass P 1 y := by
    simpa only [_root_.one_mul] using (h U 1 1 y 1).1
  exact mul_left_cancel (show evalClass P 1 y * evalClass P 1 y = evalClass P 1 y * 1 by
    rw [_root_.mul_one, ← e])

/-- Biadditivity normalizes the bundle in its second variable on all tests. -/
theorem IsBilinear.eval_one_right {S : Scheme.{0}} {A U : Over S} [MonObj A]
    {P : (A ⊗ A).left.Pic} (h : IsBilinear P) (x : U ⟶ A) :
    evalClass P x 1 = 1 := by
  have e : evalClass P x 1 = evalClass P x 1 * evalClass P x 1 := by
    simpa only [_root_.one_mul] using (h U x 1 1 1).2
  exact mul_left_cancel (show evalClass P x 1 * evalClass P x 1 = evalClass P x 1 * 1 by
    rw [_root_.mul_one, ← e])

/-- A normalized Mumford class from an ample line bundle on a geometric fibre,
with trivial scheme-theoretic kernel. Testing against all schemes is needed to
detect infinitesimal kernels in positive characteristic. -/
def IsPrincipalFibreClass {S : Scheme.{0}} (A : Over S) [MonObj A]
    (P : (A ⊗ A).left.Pic) : Prop :=
  ∃ L : A.left.Pic, T09Pic.IsAmple A.left L ∧
    P = normalizedPolarizationFamily A L (𝟙 A) ∧
    ∀ (U : Over S) (x : U ⟶ A), normalizedPolarizationFamily A L x = 1 → x = 1

/-- The pullback of the relative class to every geometric fibre is principal. -/
def IsGeometricallyPrincipal {S : Scheme.{0}} (A : QMAbSchemeP S)
    (P : (A.F ⊗ A.F).left.Pic) : Prop :=
  letI := A.grp
  ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S),
    IsPrincipalFibreClass ((Over.pullback s).obj A.F)
      (Scheme.Pic.map (pairMap (A := (Over.pullback s).obj A.F) (B := A.F) (g := s)
        (pullback.fst A.F.hom s) pullback.condition) P)

/-- The action of the maximal order, as endomorphisms over the base. -/
def iotaOver {S : Scheme.{0}} (A : QMAbSchemeP S) (a : O) : A.F ⟶ A.F :=
  Over.homMk (A.iota a) (A.iota_over a)

/-- The equality expresses `ι(a)ᵛ ∘ λ = λ ∘ ι(a†)`; the first factor is the
line-bundle variable and the second is the varying Picard parameter. -/
def HasCanonicalRosati {S : Scheme.{0}} (A : QMAbSchemeP S)
    (P : (A.F ⊗ A.F).left.Pic) : Prop :=
  ∀ a : O,
    Scheme.Pic.map (iotaOver A a ⊗ₘ 𝟙 A.F).left P =
      Scheme.Pic.map (𝟙 A.F ⊗ₘ iotaOver A (canonicalAdjoint a)).left P

/-- A principal polarization of the manuscript's fixed type, in the
normalized Picard class formulation. Neither an ample bundle on the whole
family nor choices of inducing ample bundles on the fibres are part of the data. -/
structure CanonicalPrincipalPolarization {S : Scheme.{0}} (A : QMAbSchemeP S) where
  pairing : (A.F ⊗ A.F).left.Pic
  bilinear : letI := A.grp; IsBilinear pairing
  symmetric : Scheme.Pic.map (β_ A.F A.F).hom.left pairing = pairing
  principal : IsGeometricallyPrincipal A pairing
  rosati : HasCanonicalRosati A pairing

theorem CanonicalPrincipalPolarization.ext {S : Scheme.{0}} {A : QMAbSchemeP S}
    {P Q : CanonicalPrincipalPolarization A} (h : P.pairing = Q.pairing) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- Full level three with the canonical type of principal polarization. -/
structure QMAbSchemePPol (S : Scheme.{0}) extends QMAbSchemeP S where
  polarization : CanonicalPrincipalPolarization toQMAbSchemeP

/-- One and the same pullback identification carries the QM action, level
sections and normalized polarization class. At the identity of the base this
is the relation of being isomorphic as polarized objects. -/
def QMFamFibrePol {S T : Scheme.{0}} (A : QMAbSchemePPol T) (g : S ⟶ T)
    (B : QMAbSchemePPol S) : Prop :=
  ∃ (h : B.F.left ⟶ A.F.left) (hp : IsPullback h B.F.hom A.F.hom g),
    (∀ a : O, B.iota a ≫ h = h ≫ A.iota a) ∧
    (∀ a : O, B.eta a ≫ h = g ≫ A.eta a) ∧
    Scheme.Pic.map (pairMap (A := B.F) (B := A.F) h hp.w) A.polarization.pairing =
      B.polarization.pairing

/-- Existence of the type-`μ` principal polarization on every test object. -/
def CanonicalPolarizationExists : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of Z30))), IsLocallyNoetherian S.left →
    ∀ A : QMAbSchemeP S.left, Nonempty (CanonicalPrincipalPolarization A)

/-- Rigidity and functoriality of the canonical class, stated on the exact
cartesian identifications used by the original universal property. In
particular, the identity square tests uniqueness on an individual object. -/
def CanonicalPolarizationPullback : Prop :=
  ∀ {S T : Over (Spec (CommRingCat.of Z30))},
    IsLocallyNoetherian S.left → IsLocallyNoetherian T.left →
    ∀ {g : S ⟶ T} {A : QMAbSchemeP T.left} {B : QMAbSchemeP S.left}
      (P : CanonicalPrincipalPolarization A) (Q : CanonicalPrincipalPolarization B)
      (h : B.F.left ⟶ A.F.left) (hp : IsPullback h B.F.hom A.F.hom g.left),
      (∀ a : O, B.iota a ≫ h = h ≫ A.iota a) →
      (∀ a : O, B.eta a ≫ h = g.left ≫ A.eta a) →
      Scheme.Pic.map (pairMap (A := B.F) (B := A.F) h hp.w) P.pairing = Q.pairing

/-- **Open glue**, recording precisely the polarization input for the comparison.
It is not a leaf or a provider. -/
def RelativeLemmaP : Prop := CanonicalPolarizationExists ∧ CanonicalPolarizationPullback

/-- In particular, the missing pullback statement gives uniqueness on every test object. -/
theorem canonicalPolarization_eq (hP : CanonicalPolarizationPullback)
    (S : Over (Spec (CommRingCat.of Z30))) (hS : IsLocallyNoetherian S.left)
    (A : QMAbSchemeP S.left) (P Q : CanonicalPrincipalPolarization A) : P = Q := by
  have hpb : IsPullback (𝟙 A.F.left) A.F.hom A.F.hom (𝟙 S.left) := by
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  apply CanonicalPrincipalPolarization.ext
  simpa using hP hS hS (g := 𝟙 S) P Q (𝟙 _) hpb (fun _ => by simp) (fun _ => by simp)

/-- Relative Lemma P implies exactly one polarized structure for each test object. -/
theorem existsUnique_canonicalPolarization (hP : RelativeLemmaP)
    (S : Over (Spec (CommRingCat.of Z30))) (hS : IsLocallyNoetherian S.left)
    (A : QMAbSchemeP S.left) : ∃! _P : CanonicalPrincipalPolarization A, True := by
  obtain ⟨P⟩ := hP.1 S hS A
  exact ⟨P, trivial, fun Q _ => canonicalPolarization_eq hP.2 S hS A Q P⟩

/-- Forgetting the polarization gives the same pullback condition once the
canonical class is known to be preserved. -/
theorem qmFamFibrePol_iff (hP : CanonicalPolarizationPullback)
    {S T : Over (Spec (CommRingCat.of Z30))} (hS : IsLocallyNoetherian S.left)
    (hT : IsLocallyNoetherian T.left) (g : S ⟶ T) (A : QMAbSchemePPol T.left) (B : QMAbSchemePPol S.left) :
    QMFamFibrePol A g.left B ↔ QMFamFibre A.toQMFamily g.left B.toQMFamily := by
  constructor
  · rintro ⟨h, hp, hi, he, _⟩
    exact ⟨h, hp, hi, he⟩
  · rintro ⟨h, hp, hi, he⟩
    exact ⟨h, hp, hi, he, hP hS hT (g := g) A.polarization B.polarization h hp hi he⟩

/-- The polarized version of the same universal property, on the same bases,
and with properness and smoothness as in the unpolarized statement. -/
def Y3FullThreeRepZ30Pol : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of Z30))) (A : QMAbSchemePPol Y.left),
    IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧
    ∀ (S : Over (Spec (CommRingCat.of Z30))), IsLocallyNoetherian S.left →
      ∀ B : QMAbSchemePPol S.left, ∃! g : S ⟶ Y, QMFamFibrePol A g.left B

/-- The representability statements are equivalent conditional on the one
remaining geometric input, relative Lemma P. -/
theorem y3FullThreeRepZ30Pol_iff (hP : RelativeLemmaP) :
    Y3FullThreeRepZ30Pol ↔ Y3FullThreeRepZ30 := by
  constructor
  · rintro ⟨Y, A, hp, hs, hu⟩
    have : SmoothOfRelativeDimension 1 Y.hom := hs
    have : Smooth Y.hom := SmoothOfRelativeDimension.smooth (n := 1) (f := Y.hom)
    have hY : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    refine ⟨Y, A.toQMAbSchemeP, hp, hs, fun S hS B => ?_⟩
    obtain ⟨pB⟩ := hP.1 S hS B
    let B' : QMAbSchemePPol S.left := ⟨B, pB⟩
    obtain ⟨g, hg, hunique⟩ := hu S hS B'
    exact ⟨g, (qmFamFibrePol_iff hP.2 hS hY g A B').mp hg,
      fun f hf => hunique f ((qmFamFibrePol_iff hP.2 hS hY f A B').mpr hf)⟩
  · rintro ⟨Y, A, hp, hs, hu⟩
    have : SmoothOfRelativeDimension 1 Y.hom := hs
    have : Smooth Y.hom := SmoothOfRelativeDimension.smooth (n := 1) (f := Y.hom)
    have hY : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    obtain ⟨pA⟩ := hP.1 Y hY A
    let A' : QMAbSchemePPol Y.left := ⟨A, pA⟩
    refine ⟨Y, A', hp, hs, fun S hS B => ?_⟩
    obtain ⟨g, hg, hunique⟩ := hu S hS B.toQMAbSchemeP
    exact ⟨g, (qmFamFibrePol_iff hP.2 hS hY g A' B).mpr hg,
      fun f hf => hunique f ((qmFamFibrePol_iff hP.2 hS hY f A' B).mp hf)⟩

end Y3LemmaP

#print axioms Y3LemmaP.canonicalAdjoint_involutive
#print axioms Y3LemmaP.canonicalAdjoint_mul
#print axioms Y3LemmaP.canonicalAdjoint_riemann
#print axioms Y3LemmaP.pairMap_id
#print axioms Y3LemmaP.IsBilinear.eval_one_left
#print axioms Y3LemmaP.IsBilinear.eval_one_right
#print axioms Y3LemmaP.CanonicalPrincipalPolarization.ext
#print axioms Y3LemmaP.canonicalPolarization_eq
#print axioms Y3LemmaP.existsUnique_canonicalPolarization
#print axioms Y3LemmaP.qmFamFibrePol_iff
#print axioms Y3LemmaP.y3FullThreeRepZ30Pol_iff
