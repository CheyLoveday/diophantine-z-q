import Research.DerivativeSwitch.NativeSelmerCone
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Selmer and compact-support complexes of continuous cochains

The global and local objects use Mathlib's continuous homogeneous cochains.
Extension to integer degrees retains the cochains in nonnegative degrees.
Only the topology on the modules of cochains is forgotten for the cone.
-/

namespace Research.DerivativeSwitch.ContinuousSelmer

open CategoryTheory NativeSelmerCone

universe u
variable {R : Type u} [CommRing R] [TopologicalSpace R]

noncomputable section

/-- Forget the topology of already continuous cochains and extend by zero. -/
def moduleCochains (R : Type u) [CommRing R] [TopologicalSpace R] :
    CochainComplex (TopModuleCat.{u} R) ℕ ⥤ Complex (R := R) :=
  (forget₂ (TopModuleCat R) (ModuleCat R)).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    ComplexShape.embeddingUpNat.extendFunctor (ModuleCat R)

variable {G H K : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

def cochains (X : TopRep.{u} R G) : Complex (R := R) :=
  (moduleCochains R).obj (TopRep.homogeneousCochains X)

/-- The cochain map using a continuous group homomorphism and an intertwiner. -/
def cochainsMap {X : TopRep.{u} R G} {Y : TopRep.{u} R H}
    (f : H →ₜ* G) (e : TopRep.res (f : H →* G) X ⟶ Y) : cochains X ⟶ cochains Y :=
  (moduleCochains R).map (ContinuousCohomology.cochainsMap f e)

theorem cochainsMap_comp {X : TopRep.{u} R G} {Y : TopRep.{u} R H}
    {Z : TopRep.{u} R K} (f : H →ₜ* G) (g : K →ₜ* H)
    (e : TopRep.res (f : H →* G) X ⟶ Y) (e' : TopRep.res (g : K →* H) Y ⟶ Z) :
    cochainsMap (f.comp g) ((TopRep.resFunctor (g : K →* H)).map e ≫ e') =
      cochainsMap f e ≫ cochainsMap g e' := by
  rw [cochainsMap, ContinuousCohomology.cochainsMap_comp, Functor.map_comp]
  rfl

@[simp] theorem cochainsMap_id (X : TopRep.{u} R G) :
    cochainsMap (ContinuousMonoidHom.id G) (𝟙 X) = 𝟙 (cochains X) := by
  change (moduleCochains R).map (ContinuousCohomology.cochainsMap
    (ContinuousMonoidHom.id G) (𝟙 X)) = 𝟙 _
  rw [ContinuousCohomology.cochainsMap_id]
  exact (moduleCochains R).map_id _

def restrict (X : TopRep.{u} R G) (f : H →ₜ* G) :
    cochains X ⟶ cochains (TopRep.res (f : H →* G) X) := cochainsMap f (𝟙 _)

section LocalTerms

variable {ι : Type u}

/-- On a finite set of places the product is the finite direct sum. -/
abbrev product (L : ι → Complex (R := R)) : Complex (R := R) :=
  CochainComplex.of (fun n => ModuleCat.of R (∀ v, (L v).X n))
    (fun n => ModuleCat.ofHom (LinearMap.pi fun v =>
      ((L v).d n (n + 1)).hom.comp (LinearMap.proj v))) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext v
    exact congrArg (fun f : (L v).X n ⟶ (L v).X (n + 1 + 1) => f (x v))
      ((L v).d_comp_d n (n + 1) (n + 1 + 1)))

omit [TopologicalSpace R] in
@[simp] theorem product_d (L : ι → Complex (R := R)) (n : ℤ)
    (x : (product L).X n) (v : ι) :
    (product L).d n (n + 1) x v = (L v).d n (n + 1) (x v) := by
  change (CochainComplex.of.d (fun n => ModuleCat.of R (∀ v, (L v).X n)) _ n (n + 1)).hom x v = _
  rw [CochainComplex.of_d]
  rfl

def toProduct {A : Complex (R := R)} {L : ι → Complex (R := R)}
    (f : ∀ v, A ⟶ L v) : A ⟶ product L :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (LinearMap.pi fun v => ((f v).f n).hom)) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext v
    change (product L).d n (n + 1) (fun v => (f v).f n x) v = (f v).f (n + 1) (A.d n (n + 1) x)
    rw [product_d]
    exact congrArg (fun h : A.X n ⟶ (L v).X (n + 1) => h x) ((f v).comm n (n + 1)))

def productMap {L M : ι → Complex (R := R)} (f : ∀ v, L v ⟶ M v) : product L ⟶ product M :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (LinearMap.pi fun v =>
    ((f v).f n).hom.comp (LinearMap.proj v))) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext v
    change (product M).d n (n + 1) (fun v => (f v).f n (x v)) v =
      (f v).f (n + 1) ((product L).d n (n + 1) x v)
    rw [product_d, product_d]
    exact congrArg (fun h : (L v).X n ⟶ (M v).X (n + 1) => h (x v)) ((f v).comm n (n + 1)))

variable {localGroup : ι → Type u} [∀ v, Group (localGroup v)]
  [∀ v, TopologicalSpace (localGroup v)] [∀ v, IsTopologicalGroup (localGroup v)]

abbrev localCochains (X : TopRep.{u} R G) (r : ∀ v, localGroup v →ₜ* G) (v : ι) :
    Complex (R := R) := cochains (TopRep.res (r v : localGroup v →* G) X)

/-- The direct sum of the actual restriction maps at the chosen places. -/
def localization (X : TopRep.{u} R G) (r : ∀ v, localGroup v →ₜ* G) :
    cochains X ⟶ product (localCochains X r) := toProduct fun v => restrict X (r v)

theorem localization_component (X : TopRep.{u} R G) (r : ∀ v, localGroup v →ₜ* G)
    (n : ℤ) (x : (cochains X).X n) (v : ι) :
    (localization X r).f n x v = (restrict X (r v)).f n x := rfl

structure LocalCondition (L : Complex (R := R)) where
  complex : Complex (R := R)
  inclusion : complex ⟶ L

def LocalCondition.full (L : Complex (R := R)) : LocalCondition L := ⟨L, 𝟙 L⟩

/-- Inflation from an unramified quotient with its descended coefficient action. -/
def LocalCondition.unramified (f : H →ₜ* G) (X : TopRep.{u} R G) :
    LocalCondition (cochains (TopRep.res (f : H →* G) X)) := ⟨cochains X, restrict X f⟩

variable (X : TopRep.{u} R G) (r : ∀ v, localGroup v →ₜ* G)

abbrev compactSupport : Complex (R := R) := fibre (-(localization X r))

variable (U : ∀ v, LocalCondition (localCochains X r v))

abbrev conditionInclusion : product (fun v => (U v).complex) ⟶ product (localCochains X r) :=
  productMap fun v => (U v).inclusion

abbrev selmerComplex : Complex (R := R) := selmer (localization X r) (conditionInclusion X r U)

/-- A Selmer degree-one cycle recovers each actual local witness equation.
The cone coordinate is the negative of the H22 coordinate. -/
theorem selmer_cycle_at_place (z : (selmerComplex X r U).X 0)
    (hz : (selmerComplex X r U).d 0 1 z = 0) (v : ι) :
    ((U v).inclusion.f 1 (z.1.2 v)) =
      (restrict X (r v)).f 1 z.1.1 + (localCochains X r v).d 0 1 (z.2 v) := by
  have h := congrFun (selmer_cycle_equation (localization X r) (conditionInclusion X r U) z hz) v
  change ((U v).inclusion.f 1 (z.1.2 v)) =
    (localization X r).f 1 z.1.1 v + (product (localCochains X r)).d 0 1 z.2 v at h
  have hd := product_d (localCochains X r) 0 z.2 v
  change (product (localCochains X r)).d 0 1 z.2 v = _ at hd
  rwa [localization_component, hd] at h

/-- Closed global and condition cochains with H22 boundary witnesses give a
cycle in the continuous Selmer cone. -/
theorem selmer_cycle_of_witnesses (p : (cochains X).X 1)
    (u : ∀ v, (U v).complex.X 1) (q : ∀ v, (localCochains X r v).X 0)
    (hp : (cochains X).d 1 2 p = 0) (hu : ∀ v, (U v).complex.d 1 2 (u v) = 0)
    (witness : ∀ v, (restrict X (r v)).f 1 p - (U v).inclusion.f 1 (u v) =
      (localCochains X r v).d 0 1 (q v)) :
    (selmerComplex X r U).d 0 1 ((p, u), -q) = 0 := by
  apply Prod.ext
  · apply Prod.ext
    · exact hp
    · funext v
      change (product (fun v => (U v).complex)).d 1 2 u v = 0
      exact (product_d (fun v => (U v).complex) 1 u v).trans (hu v)
  · funext v
    change -(restrict X (r v)).f 1 p + (U v).inclusion.f 1 (u v) -
      (product (localCochains X r)).d 0 1 (-q) v = 0
    have hd := product_d (localCochains X r) 0 (-q) v
    change (product (localCochains X r)).d 0 1 (-q) v = _ at hd
    rw [hd]
    change -(restrict X (r v)).f 1 p + (U v).inclusion.f 1 (u v) -
      ((localCochains X r v).d 0 1).hom (-(q v)) = 0
    rw [map_neg, ← witness v]
    abel

end LocalTerms

end

end Research.DerivativeSwitch.ContinuousSelmer
