import ZInQKernel.Contrib.OneProof.Y3LemmaP

/-!
# Native pullback identities for the relative Lemma P

The lemmas below concern actual classes in the Picard group of the twofold
fibre product. They do not require a representing Picard scheme.
-/

noncomputable section

namespace Y3LemmaP

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM Y3Fix
open ZInQ.Contrib.CloudR2Poincare.L1
open scoped CategoryTheory.Obj MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- The group instances must unfold to the fields in the frozen propositions.
set_option linter.style.haveILetI false

@[reassoc (attr := simp)]
theorem pairMap_fst {S T : Scheme.{0}} {A : Over S} {B : Over T} {g : S ⟶ T}
    (h : A.left ⟶ B.left) (w : h ≫ B.hom = A.hom ≫ g) :
    pairMap (A := A) (B := B) h w ≫ pullback.fst B.hom B.hom = pullback.fst A.hom A.hom ≫ h :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pairMap_snd {S T : Scheme.{0}} {A : Over S} {B : Over T} {g : S ⟶ T}
    (h : A.left ⟶ B.left) (w : h ≫ B.hom = A.hom ≫ g) :
    pairMap (A := A) (B := B) h w ≫ pullback.snd B.hom B.hom = pullback.snd A.hom A.hom ≫ h :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem pairMap_comp {S T U : Scheme.{0}} {A : Over S} {B : Over T} {C : Over U}
    {g : S ⟶ T} {f : T ⟶ U}
    (h : A.left ⟶ B.left) (w : h ≫ B.hom = A.hom ≫ g)
    (j : B.left ⟶ C.left) (v : j ≫ C.hom = B.hom ≫ f) :
    pairMap (A := A) (B := B) h w ≫ pairMap (A := B) (B := C) j v =
      pairMap (A := A) (B := C) (g := g ≫ f) (h ≫ j) (by
        rw [Category.assoc, v, ← Category.assoc, w, Category.assoc]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pairMap_fst, pairMap_fst_assoc]
  · simp only [Category.assoc, pairMap_snd, pairMap_snd_assoc]

/-- Restriction along the double zero section excludes any ambiguity from a
class on the base, including over nonreduced schemes. -/
theorem baseTwist_eq_one_of_isBilinear {S : Scheme.{0}} {A : Over S} [MonObj A]
    {P : (A ⊗ A).left.Pic} {N : S.Pic} (hP : IsBilinear P)
    (hPN : IsBilinear (P * Scheme.Pic.map (A ⊗ A).hom N)) : N = 1 := by
  let U := 𝟙_ (Over S)
  let z : U ⟶ A := 1
  have h : (lift z z).left ≫ (A ⊗ A).hom = 𝟙 S := Over.w (lift z z)
  have h1 := hP.eval_one_left z
  have h2 := hPN.eval_one_left z
  change evalClass (P * Scheme.Pic.map (A ⊗ A).hom N) z z = 1 at h2
  unfold evalClass at h1 h2
  rw [Scheme.Pic.map_mul, h1, _root_.one_mul, ← Scheme.Pic.map_comp, h] at h2
  exact (Scheme.Pic.map_id N).symm.trans h2

/-- The difference of two biadditive classes is biadditive. -/
theorem IsBilinear.div {S : Scheme.{0}} {A : Over S} [MonObj A]
    {P Q : (A ⊗ A).left.Pic} (hP : IsBilinear P) (hQ : IsBilinear Q) :
    IsBilinear (P / Q) := by
  intro U x x' y y'
  have aux (a b : U ⟶ A) : evalClass (P / Q) a b = evalClass P a b / evalClass Q a b :=
    map_div (Scheme.Pic.mapHom (lift a b).left) P Q
  constructor
  · simp only [aux, (hP U x x' y y').1, (hQ U x x' y y').1]
    exact mul_div_mul_comm _ _ _ _
  · simp only [aux, (hP U x x' y y').2, (hQ U x x' y y').2]
    exact mul_div_mul_comm _ _ _ _

@[reassoc]
private theorem tensor_fst_left {S : Scheme.{0}} {A B C D : Over S} (f : A ⟶ B) (g : C ⟶ D) :
    (f ⊗ₘ g).left ≫ pullback.fst B.hom D.hom = pullback.fst A.hom C.hom ≫ f.left :=
  congrArg Over.Hom.left (tensorHom_fst f g)

@[reassoc]
private theorem tensor_snd_left {S : Scheme.{0}} {A B C D : Over S} (f : A ⟶ B) (g : C ⟶ D) :
    (f ⊗ₘ g).left ≫ pullback.snd B.hom D.hom = pullback.snd A.hom C.hom ≫ g.left :=
  congrArg Over.Hom.left (tensorHom_snd f g)

/-- Pullback of the adjoint identity along a map intertwining both actions. -/
theorem HasCanonicalRosati.map_pairMap {S T : Scheme.{0}} {A : QMAbSchemeP T}
    {B : QMAbSchemeP S} {g : S ⟶ T} (h : B.F.left ⟶ A.F.left)
    (w : h ≫ A.F.hom = B.F.hom ≫ g) (hi : ∀ a : O, B.iota a ≫ h = h ≫ A.iota a)
    {P : (A.F ⊗ A.F).left.Pic} (hP : HasCanonicalRosati A P) :
    HasCanonicalRosati B (Scheme.Pic.map (pairMap (A := B.F) (B := A.F) h w) P) := by
  intro a
  have commute (b : O) :
      (iotaOver B b ⊗ₘ 𝟙 B.F).left ≫ pairMap (A := B.F) (B := A.F) h w =
        pairMap (A := B.F) (B := A.F) h w ≫ (iotaOver A b ⊗ₘ 𝟙 A.F).left := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pairMap_fst, pairMap_fst_assoc, tensor_fst_left,
        tensor_fst_left_assoc, iotaOver, Over.homMk_left, hi b]
    · simp only [Category.assoc, pairMap_snd, tensor_snd_left,
        tensor_snd_left_assoc, Over.id_left, Category.comp_id, Category.id_comp]
  have commute' (b : O) :
      (𝟙 B.F ⊗ₘ iotaOver B b).left ≫ pairMap (A := B.F) (B := A.F) h w =
        pairMap (A := B.F) (B := A.F) h w ≫ (𝟙 A.F ⊗ₘ iotaOver A b).left := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pairMap_fst, tensor_fst_left,
        tensor_fst_left_assoc, Over.id_left, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, pairMap_snd, pairMap_snd_assoc, tensor_snd_left,
        tensor_snd_left_assoc, iotaOver, Over.homMk_left, hi b]
  rw [← Scheme.Pic.map_comp, ← Scheme.Pic.map_comp, commute, commute', Scheme.Pic.map_comp,
    Scheme.Pic.map_comp, hP a]

/-- Each geometric restriction is taken on the actual pullback scheme and
then on its twofold fibre product. -/
def geometricPairClass {S : Scheme.{0}} (A : Over S) {k : Type} [Field k]
    (s : Spec (CommRingCat.of k) ⟶ S) (P : (A ⊗ A).left.Pic) :
    (((Over.pullback s).obj A) ⊗ ((Over.pullback s).obj A)).left.Pic :=
  Scheme.Pic.map (pairMap (A := (Over.pullback s).obj A) (B := A)
    (g := s) (pullback.fst A.hom s) pullback.condition) P

/-- This is the equality-on-geometric-fibres portion of preservation across
a cartesian identification. It deliberately omits the global equality. -/
def CanonicalPolarizationFibreComparison : Prop :=
  ∀ {S T : Over (Spec (CommRingCat.of Y3RouteA.Z30))},
    IsLocallyNoetherian S.left → IsLocallyNoetherian T.left →
    ∀ {g : S ⟶ T} {A : QMAbSchemeP T.left} {B : QMAbSchemeP S.left}
      (P : CanonicalPrincipalPolarization A) (Q : CanonicalPrincipalPolarization B)
      (h : B.F.left ⟶ A.F.left) (hp : IsPullback h B.F.hom A.F.hom g.left),
      (∀ a : O, B.iota a ≫ h = h ≫ A.iota a) →
      (∀ a : O, B.eta a ≫ h = g.left ≫ A.eta a) →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S.left),
        geometricPairClass B.F s (Scheme.Pic.map (pairMap (A := B.F) (B := A.F) h hp.w) P.pairing) =
          geometricPairClass B.F s Q.pairing

/-- Regard a generalized point of the source as a generalized point of the
target, using the composite structure map on its parameter scheme. -/
def pointAlong {S T : Scheme.{0}} {A U : Over S} {B : Over T} {g : S ⟶ T}
    (h : A.left ⟶ B.left) (w : h ≫ B.hom = A.hom ≫ g) (x : U ⟶ A) :
    Over.mk (U.hom ≫ g) ⟶ B :=
  Over.homMk (x.left ≫ h) (by
    change (x.left ≫ h) ≫ B.hom = U.hom ≫ g
    rw [Category.assoc, w, ← Category.assoc, Over.w])

@[reassoc]
private theorem lift_fst_left {S : Scheme.{0}} {A U : Over S} (x y : U ⟶ A) :
    (lift x y).left ≫ pullback.fst A.hom A.hom = x.left :=
  congrArg Over.Hom.left (lift_fst x y)

@[reassoc]
private theorem lift_snd_left {S : Scheme.{0}} {A U : Over S} (x y : U ⟶ A) :
    (lift x y).left ≫ pullback.snd A.hom A.hom = y.left :=
  congrArg Over.Hom.left (lift_snd x y)

private theorem lift_comp_pairMap {S T : Scheme.{0}} {A U : Over S} {B : Over T} {g : S ⟶ T}
    (h : A.left ⟶ B.left) (w : h ≫ B.hom = A.hom ≫ g) (x y : U ⟶ A) :
    (lift x y).left ≫ pairMap (A := A) (B := B) h w =
      (lift (pointAlong h w x) (pointAlong h w y)).left := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pairMap_fst, lift_fst_left_assoc, lift_fst_left]
    rfl
  · simp only [Category.assoc, pairMap_snd, lift_snd_left_assoc, lift_snd_left]
    rfl

/-- Evaluation commutes with pulling back a pairing. -/
theorem evalClass_map_pairMap {S T : Scheme.{0}} {A U : Over S} {B : Over T} {g : S ⟶ T}
    (h : A.left ⟶ B.left) (w : h ≫ B.hom = A.hom ≫ g)
    (P : (B ⊗ B).left.Pic) (x y : U ⟶ A) :
    evalClass (Scheme.Pic.map (pairMap (A := A) (B := B) h w) P) x y =
      evalClass P (pointAlong h w x) (pointAlong h w y) := by
  unfold evalClass
  rw [← Scheme.Pic.map_comp, lift_comp_pairMap]

/-- A multiplication-compatible base-change morphism pulls biadditive
classes back to biadditive classes, on all test schemes. -/
theorem IsBilinear.map_pairMap {S T : Scheme.{0}} {A : Over S} {B : Over T}
    [MonObj A] [MonObj B] {g : S ⟶ T}
    (h : A.left ⟶ B.left) (w : h ≫ B.hom = A.hom ≫ g)
    (hmul : μ[A].left ≫ h = pairMap (A := A) (B := B) h w ≫ μ[B].left)
    {P : (B ⊗ B).left.Pic} (hP : IsBilinear P) :
    IsBilinear (Scheme.Pic.map (pairMap (A := A) (B := B) h w) P) := by
  intro U x x' y y'
  have mulEq (u v : U ⟶ A) :
      pointAlong h w (u * v) = pointAlong h w u * pointAlong h w v := by
    apply Over.OverMorphism.ext
    change (lift u v).left ≫ μ[A].left ≫ h =
      (lift (pointAlong h w u) (pointAlong h w v)).left ≫ μ[B].left
    rw [hmul, ← Category.assoc, lift_comp_pairMap]
  simp only [evalClass_map_pairMap, mulEq]
  exact hP _ _ _ _ _

/-- The two zero-axis identities as equalities of actual Picard classes on
all generalized points. -/
def IsZeroAxisNormalized {S : Scheme.{0}} {A : Over S} [MonObj A]
    (P : (A ⊗ A).left.Pic) : Prop :=
  ∀ (U : Over S) (x : U ⟶ A), evalClass P 1 x = 1 ∧ evalClass P x 1 = 1

theorem IsBilinear.isZeroAxisNormalized {S : Scheme.{0}} {A : Over S} [MonObj A]
    {P : (A ⊗ A).left.Pic} (hP : IsBilinear P) : IsZeroAxisNormalized P :=
  fun _ x => ⟨hP.eval_one_left x, hP.eval_one_right x⟩

theorem IsZeroAxisNormalized.div {S : Scheme.{0}} {A : Over S} [MonObj A]
    {P Q : (A ⊗ A).left.Pic} (hP : IsZeroAxisNormalized P) (hQ : IsZeroAxisNormalized Q) :
    IsZeroAxisNormalized (P / Q) := by
  intro U x
  have aux (a b : U ⟶ A) : evalClass (P / Q) a b = evalClass P a b / evalClass Q a b :=
    map_div (Scheme.Pic.mapHom (lift a b).left) P Q
  simp only [aux, (hP U x).1, (hP U x).2, (hQ U x).1, (hQ U x).2, div_self', and_self]

/-- Pullback of normalization needs only the identity section, not the
multiplication law. -/
theorem IsZeroAxisNormalized.map_pairMap {S T : Scheme.{0}} {A : Over S} {B : Over T}
    [MonObj A] [MonObj B] {g : S ⟶ T}
    (h : A.left ⟶ B.left) (w : h ≫ B.hom = A.hom ≫ g)
    (hzero : η[A].left ≫ h = g ≫ η[B].left)
    {P : (B ⊗ B).left.Pic} (hP : IsZeroAxisNormalized P) :
    IsZeroAxisNormalized (Scheme.Pic.map (pairMap (A := A) (B := B) h w) P) := by
  intro U x
  have hz : pointAlong h w (1 : U ⟶ A) = 1 := by
    apply Over.OverMorphism.ext
    change (U.hom ≫ η[A].left) ≫ h = (U.hom ≫ g) ≫ η[B].left
    simp only [Category.assoc, hzero]
  simpa only [evalClass_map_pairMap, hz] using hP _ (pointAlong h w x)

/-- A two-axis seesaw for the twofold fibre product. This version needs no
separate theorem on transport of the group law. -/
def NormalizedPairFibreRigidity : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of Y3RouteA.Z30))), IsLocallyNoetherian S.left →
    ∀ (A : QMAbSchemeP S.left) (P : (A.F ⊗ A.F).left.Pic),
      (letI := A.grp; IsZeroAxisNormalized P) →
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S.left),
        geometricPairClass A.F s P = 1) → P = 1

/-- Zero detection suffices to compare any two normalized classes from
equality of their geometric restrictions. -/
theorem eq_of_geometricPairClass_eq (hRig : NormalizedPairFibreRigidity)
    (S : Over (Spec (CommRingCat.of Y3RouteA.Z30))) (hS : IsLocallyNoetherian S.left)
    (A : QMAbSchemeP S.left) {P Q : (A.F ⊗ A.F).left.Pic}
    (hP : letI := A.grp; IsZeroAxisNormalized P)
    (hQ : letI := A.grp; IsZeroAxisNormalized Q)
    (hFib : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S.left),
      geometricPairClass A.F s P = geometricPairClass A.F s Q) : P = Q := by
  letI := A.grp
  apply div_eq_one.mp
  apply hRig S hS A (P / Q) (IsZeroAxisNormalized.div hP hQ)
  intro k _ _ s
  change Scheme.Pic.mapHom _ (P / Q) = 1
  rw [map_div]
  exact div_eq_one.mpr (hFib k s)

/-- The axis-normalized seesaw and the comparison on geometric fibres suffice
for the frozen pullback half. The marking gives preservation of the two
axes by using its value at zero. -/
theorem canonicalPolarizationPullback_of_normalizedSeesaw
    (hRig : NormalizedPairFibreRigidity) (hFib : CanonicalPolarizationFibreComparison) :
    CanonicalPolarizationPullback := by
  intro S T hS hT g A B P Q h hp hi he
  letI := A.grp
  letI := B.grp
  have hz : η[B.F].left ≫ h = g.left ≫ η[A.F].left := by
    rw [B.one_eq, A.one_eq]
    exact he 0
  apply eq_of_geometricPairClass_eq hRig S hS B
    (IsZeroAxisNormalized.map_pairMap h hp.w hz (IsBilinear.isZeroAxisNormalized P.bilinear))
    (IsBilinear.isZeroAxisNormalized Q.bilinear)
  exact hFib hS hT P Q h hp hi he

/-- Under normalized seesaw the pullback half is exactly the fixed-type
comparison on geometric fibres. -/
theorem canonicalPolarizationPullback_iff_fibreComparison (hRig : NormalizedPairFibreRigidity) :
    CanonicalPolarizationPullback ↔ CanonicalPolarizationFibreComparison := by
  refine ⟨?_, canonicalPolarizationPullback_of_normalizedSeesaw hRig⟩
  intro h S T hS hT g A B P Q f hp hi he k _ _ s
  exact congrArg (geometricPairClass B.F s) (h hS hT P Q f hp hi he)

/-- Existence and the two pieces of fibre comparison give the frozen
representability equivalence. -/
theorem y3FullThreeRepZ30Pol_iff_of_relativePieces
    (hRig : NormalizedPairFibreRigidity)
    (hFib : CanonicalPolarizationFibreComparison) (hExists : CanonicalPolarizationExists) :
    Y3FullThreeRepZ30Pol ↔ Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30Pol_iff
    ⟨hExists, canonicalPolarizationPullback_of_normalizedSeesaw hRig hFib⟩

#print axioms tensor_fst_left
#print axioms tensor_snd_left
#print axioms lift_fst_left
#print axioms lift_snd_left
#print axioms lift_comp_pairMap

end Y3LemmaP

#print axioms Y3LemmaP.pairMap_fst
#print axioms Y3LemmaP.pairMap_snd
#print axioms Y3LemmaP.pairMap_comp
#print axioms Y3LemmaP.baseTwist_eq_one_of_isBilinear
#print axioms Y3LemmaP.IsBilinear.div
#print axioms Y3LemmaP.HasCanonicalRosati.map_pairMap
#print axioms Y3LemmaP.eq_of_geometricPairClass_eq
#print axioms Y3LemmaP.evalClass_map_pairMap
#print axioms Y3LemmaP.IsBilinear.map_pairMap
#print axioms Y3LemmaP.y3FullThreeRepZ30Pol_iff_of_relativePieces
#print axioms Y3LemmaP.IsBilinear.isZeroAxisNormalized
#print axioms Y3LemmaP.IsZeroAxisNormalized.div
#print axioms Y3LemmaP.IsZeroAxisNormalized.map_pairMap
#print axioms Y3LemmaP.canonicalPolarizationPullback_of_normalizedSeesaw
#print axioms Y3LemmaP.canonicalPolarizationPullback_iff_fibreComparison
