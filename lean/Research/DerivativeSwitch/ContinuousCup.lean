import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.Abel

/-!
# The degree-(1,1) continuous homogeneous cup

The Alexander–Whitney formula on representatives uses the overlapping
vertex. The construction uses Mathlib's actual continuous cochains and
the diagonal action. Only the coefficient pairing and its equivariance
and continuity are supplied.
-/

namespace Research.DerivativeSwitch.ContinuousCup

open CategoryTheory

universe u
variable {R G : Type u} [CommRing R] [TopologicalSpace R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

variable {X Y Z : TopRep.{u} R G}

abbrev Cochain (X : TopRep.{u} R G) (n : ℕ) := (TopRep.homogeneousCochains X).X n

variable (pairing : X →ₗ[R] Y →ₗ[R] Z)
  (cont : Continuous fun xy : X × Y => pairing xy.1 xy.2)
  (equiv : ∀ g x y, pairing (X.ρ g x) (Y.ρ g y) = Z.ρ g (pairing x y))

private def rawCup (f : Cochain X 1) (g : Cochain Y 1) :
    ContinuousMap G (ContinuousMap G (ContinuousMap G Z)) :=
  let left : ContinuousMap (G × G) X := (f.1 : ContinuousMap G (ContinuousMap G X)).uncurry
  let right : ContinuousMap (G × G) Y := (g.1 : ContinuousMap G (ContinuousMap G Y)).uncurry
  let raw : ContinuousMap (G × G × G) Z := {
    toFun := fun xyz => pairing (left (xyz.1, xyz.2.1)) (right xyz.2)
    continuous_toFun := cont.comp <|
      (left.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
        (right.continuous.comp continuous_snd) }
  let curry := (Homeomorph.curry (X := G) (Y := G) (Z := Z))
  (ContinuousMap.mk curry curry.continuous_toFun).comp raw.curry

omit [LocallyCompactSpace G] in
private theorem invariant_one {A : TopRep.{u} R G} (f : Cochain A 1) (g a b : G) :
    A.ρ g (f.1 (g⁻¹ * a) (g⁻¹ * b)) = f.1 a b :=
  congrArg (fun p : ContinuousMap G (ContinuousMap G A) => p a b) (f.2 g)

include equiv in
private def cupValue (f : Cochain X 1) (g : Cochain Y 1) : Cochain Z 2 := by
  refine ⟨rawCup pairing cont f g, ?_⟩
  intro k
  apply ContinuousMap.ext
  intro a
  apply ContinuousMap.ext
  intro b
  apply ContinuousMap.ext
  intro c
  change Z.ρ k (pairing (f.1 (k⁻¹ * a) (k⁻¹ * b)) (g.1 (k⁻¹ * b) (k⁻¹ * c))) =
    pairing (f.1 a b) (g.1 b c)
  rw [← equiv, invariant_one, invariant_one]

/-- The continuous cup on cochains of degree one. -/
def cup11 : Cochain X 1 →ₗ[R] Cochain Y 1 →ₗ[R] Cochain Z 2 where
  toFun f := {
    toFun := cupValue pairing cont equiv f
    map_add' g h := by
      apply Subtype.ext
      ext a b c
      exact (pairing (f.1 a b)).map_add (g.1 b c) (h.1 b c)
    map_smul' r g := by
      apply Subtype.ext
      ext a b c
      exact (pairing (f.1 a b)).map_smul r (g.1 b c) }
  map_add' f h := by
    apply LinearMap.ext
    intro g
    apply Subtype.ext
    ext a b c
    exact congrArg (fun l : Y →ₗ[R] Z => l (g.1 b c)) (pairing.map_add (f.1 a b) (h.1 a b))
  map_smul' r f := by
    apply LinearMap.ext
    intro g
    apply Subtype.ext
    ext a b c
    exact congrArg (fun l : Y →ₗ[R] Z => l (g.1 b c)) (pairing.map_smul r (f.1 a b))

theorem cup11_eval (f : Cochain X 1) (g : Cochain Y 1) (a b c : G) :
    (cup11 pairing cont equiv f g).1 a b c = pairing (f.1 a b) (g.1 b c) := rfl

/-- Localization is pullback on each vertex and commutes with the continuous cup. -/
theorem cup11_restrict {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] (r : H →ₜ* G) (f : Cochain X 1) (g : Cochain Y 1) :
    ((ContinuousCohomology.cochainsMap r (𝟙 (TopRep.res (r : H →* G) Z))).f 2).hom
        (cup11 pairing cont equiv f g) =
      cup11 (G := H) (X := TopRep.res (r : H →* G) X) (Y := TopRep.res (r : H →* G) Y)
        (Z := TopRep.res (r : H →* G) Z) pairing cont (fun h => equiv (r h))
        (((ContinuousCohomology.cochainsMap r (𝟙 (TopRep.res (r : H →* G) X))).f 1).hom f)
        (((ContinuousCohomology.cochainsMap r (𝟙 (TopRep.res (r : H →* G) Y))).f 1).hom g) := by
  apply Subtype.ext
  ext a b c
  rfl

omit [LocallyCompactSpace G] in
theorem d1_eval (f : Cochain X 1) (a b c : G) :
    (((TopRep.homogeneousCochains X).d 1 2).hom f).1 a b c =
      f.1 b c - (f.1 a c - f.1 a b) := by
  have h := congrArg (fun p : ContinuousMap G (ContinuousMap G (ContinuousMap G X)) => p a b c)
    (TopRep.homogeneousCochains.d_apply X 1 f)
  exact h

omit [LocallyCompactSpace G] in
theorem d2_eval (f : Cochain X 2) (a b c d : G) :
    (((TopRep.homogeneousCochains X).d 2 3).hom f).1 a b c d =
      f.1 b c d - (f.1 a c d - (f.1 a b d - f.1 a b c)) := by
  have h := congrArg (fun p : ContinuousMap G (ContinuousMap G
      (ContinuousMap G (ContinuousMap G X))) => p a b c d)
    (TopRep.homogeneousCochains.d_apply X 2 f)
  exact h

omit [LocallyCompactSpace G] in
private theorem cocycle_add (f : Cochain X 1) (hf : ((TopRep.homogeneousCochains X).d 1 2).hom f = 0)
    (a b c : G) : f.1 a c = f.1 b c + f.1 a b := by
  have h := d1_eval f a b c
  rw [hf] at h
  change 0 = f.1 b c - (f.1 a c - f.1 a b) at h
  exact sub_eq_iff_eq_add.mp (sub_eq_zero.mp h.symm).symm

/-- Cups of continuous degree-one cocycles give closed local degree-two representatives. -/
theorem cup11_closed (f : Cochain X 1) (g : Cochain Y 1)
    (hf : ((TopRep.homogeneousCochains X).d 1 2).hom f = 0)
    (hg : ((TopRep.homogeneousCochains Y).d 1 2).hom g = 0) :
    ((TopRep.homogeneousCochains Z).d 2 3).hom (cup11 pairing cont equiv f g) = 0 := by
  apply Subtype.ext
  ext a b c d
  change (((TopRep.homogeneousCochains Z).d 2 3).hom (cup11 pairing cont equiv f g)).1 a b c d = 0
  rw [d2_eval, cup11_eval, cup11_eval, cup11_eval, cup11_eval, cocycle_add f hf a b c,
    cocycle_add g hg b c d]
  simp only [map_add, LinearMap.add_apply]
  abel

end Research.DerivativeSwitch.ContinuousCup
