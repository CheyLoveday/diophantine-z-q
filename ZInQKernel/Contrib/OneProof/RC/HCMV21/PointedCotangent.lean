import ZInQKernel.Contrib.AbVarBC.Mul
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra

/-! Pullback on the cotangent spaces at rational sections. For a group
endomorphism its underlying map is the cotangent map already in the tree. -/

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory AlgebraicGeometry IsLocalRing MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section

variable {k : Type} [Field k]

/-- A scheme over a field equipped with a rational section. -/
structure PointedScheme (k : Type) [Field k] where
  X : Over (Spec (.of k))
  sectionMap : 𝟙_ (Over (Spec (.of k))) ⟶ X

namespace PointedScheme

instance (P : PointedScheme k) : P.X.left.Over (Spec (.of k)) :=
  ⟨P.X.hom⟩

abbrev point (P : PointedScheme k) : P.X.left :=
  P.sectionMap.left (closedPoint k)

/-- The local ring at the section's image. -/
abbrev localRing (P : PointedScheme k) : CommRingCat := P.X.left.presheaf.stalk P.point

abbrev cotangent (P : PointedScheme k) := CotangentSpace P.localRing

/-- Evaluation at the rational section. -/
abbrev evaluation (P : PointedScheme k) : P.localRing ⟶ CommRingCat.of k :=
  Scheme.stalkClosedPointTo P.sectionMap.left

private theorem over_of_section (P : PointedScheme k) :
    P.sectionMap.left ≫ P.X.hom = 𝟙 (Spec (.of k)) := P.sectionMap.w

theorem evaluation_constant (P : PointedScheme k) (c : k) :
    P.evaluation (algebraMap k P.localRing c) = c := by
  let u := (Scheme.ΓSpecIso (.of k)).inv c
  have hw : P.sectionMap.left ≫ P.X.hom = Spec.map (𝟙 (CommRingCat.of k)) :=
    (over_of_section P).trans (Spec.map_id _).symm
  change Scheme.stalkClosedPointTo P.sectionMap.left
    (P.X.left.presheaf.germ ⊤ P.point trivial (P.X.hom.appTop u)) = c
  have hg := Scheme.Hom.germ_stalkMap_apply P.X.hom ⊤ P.point
    (show P.X.hom P.point ∈ (⊤ : (Spec (.of k)).Opens) from trivial) u
  erw [← hg]
  change (P.X.hom.stalkMap P.point ≫ Scheme.stalkClosedPointTo P.sectionMap.left)
    ((Spec (.of k)).presheaf.germ ⊤ (P.X.hom P.point) trivial u) = c
  rw [← Scheme.stalkClosedPointTo_comp]
  have he (f : Spec (.of k) ⟶ Spec (.of k))
      (h : f = Spec.map (𝟙 (CommRingCat.of k))) :
      (Spec (.of k)).presheaf.germ ⊤ (f (closedPoint k)) trivial ≫
        Scheme.stalkClosedPointTo f = (Scheme.ΓSpecIso (.of k)).hom := by
    subst f
    rw [Scheme.germ_stalkClosedPointTo_Spec, Category.comp_id]
  exact (ConcreteCategory.congr_hom (he _ hw) u).trans
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of k)).inv_hom_id c)

variable {P Q T : PointedScheme k}

/-- Correct the target point of the stalk map by the indicated equality. -/
private def stalkMapAt {X Y : Scheme} (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y) :
    Y.presheaf.stalk y ⟶ X.presheaf.stalk x := by
  subst y
  exact f.stalkMap x

@[simp] private theorem stalkMapAt_canonical {X Y : Scheme} (f : X ⟶ Y) (x : X) :
    stalkMapAt f x (f x) rfl = f.stalkMap x := rfl

private theorem stalkMapAt_eq {X Y : Scheme} (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y) :
    stalkMapAt f x y h = (Y.presheaf.stalkCongr (Inseparable.of_eq h.symm)).hom ≫ f.stalkMap x := by
  subst y
  rw [stalkMapAt_canonical]
  change f.stalkMap x = Y.presheaf.stalkSpecializes (specializes_refl (f x)) ≫ f.stalkMap x
  rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

private theorem stalkMapAt_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) (y : Y) (z : Z) (hf : f x = y) (hg : g y = z) :
    stalkMapAt (f ≫ g) x z (by rw [Scheme.Hom.comp_apply, hf, hg]) =
      stalkMapAt g y z hg ≫ stalkMapAt f x y hf := by
  subst y
  subst z
  exact Scheme.Hom.stalkMap_comp f g x

private theorem stalkMapAt_id (X : Scheme) (x : X) :
    stalkMapAt (𝟙 X) x x (by simp) = 𝟙 _ := by
  exact Scheme.Hom.stalkMap_id X x

private theorem stalkMapAt_germ_top {X Y : Scheme} (f : X ⟶ Y) (x : X) (y : Y)
    (h : f x = y) :
    Y.presheaf.germ ⊤ y trivial ≫ stalkMapAt f x y h =
      f.appTop ≫ X.presheaf.germ ⊤ x trivial := by
  subst y
  exact Scheme.Hom.germ_stalkMap f ⊤ x trivial

private theorem map_point (f : P.X ⟶ Q.X) (hf : P.sectionMap ≫ f = Q.sectionMap) :
    f.left P.point = Q.point :=
  (Scheme.Hom.comp_apply P.sectionMap.left f.left (closedPoint k)).symm.trans
    (congrArg (fun g : 𝟙_ (Over (Spec (.of k))) ⟶ Q.X => g.left (closedPoint k)) hf)

/-- The stalk map of a morphism carrying one rational section to another. -/
def pullStalk (f : P.X ⟶ Q.X) (hf : P.sectionMap ≫ f = Q.sectionMap) :
    Q.localRing →ₐ[k] P.localRing where
  toRingHom := (stalkMapAt f.left P.point Q.point (map_point f hf)).hom
  commutes' c := by
    have htop := stalkMapAt_germ_top f.left P.point Q.point (map_point f hf)
    have hw : f.left ≫ Q.X.hom = P.X.hom := f.w
    have happ : Q.X.hom.appTop ≫ f.left.appTop = P.X.hom.appTop :=
      (Scheme.Hom.comp_appTop f.left Q.X.hom).symm.trans (congrArg Scheme.Hom.appTop hw)
    let u := (Scheme.ΓSpecIso (.of k)).inv c
    change (Q.X.left.presheaf.germ ⊤ Q.point trivial ≫
      stalkMapAt f.left P.point Q.point (map_point f hf)) (Q.X.hom.appTop u) =
        (P.X.hom.appTop ≫ P.X.left.presheaf.germ ⊤ P.point trivial) u
    rw [htop]
    exact ConcreteCategory.congr_hom (congrArg
      (fun d => d ≫ P.X.left.presheaf.germ ⊤ P.point trivial) happ) u

instance (f : P.X ⟶ Q.X) (hf : P.sectionMap ≫ f = Q.sectionMap) :
    IsLocalHom (pullStalk f hf).toRingHom := by
  change IsLocalHom (stalkMapAt f.left P.point Q.point (map_point f hf)).hom
  rw [stalkMapAt_eq, CommRingCat.hom_comp]
  infer_instance

private theorem pullStalk_id (P : PointedScheme k) :
    pullStalk (𝟙 P.X) (by simp) = AlgHom.id k P.localRing := by
  ext x
  change (stalkMapAt (𝟙 P.X.left) P.point P.point (by simp)) x = x
  rw [stalkMapAt_id]
  rfl

private theorem pullStalk_comp (f : P.X ⟶ Q.X) (g : Q.X ⟶ T.X)
    (hf : P.sectionMap ≫ f = Q.sectionMap) (hg : Q.sectionMap ≫ g = T.sectionMap) :
    pullStalk (f ≫ g) (by rw [← Category.assoc, hf, hg]) =
      (pullStalk f hf).comp (pullStalk g hg) := by
  ext x
  exact ConcreteCategory.congr_hom
    (stalkMapAt_comp f.left g.left P.point Q.point T.point (map_point f hf) (map_point g hg)) x

private theorem mem_maximalIdeal_pullStalk (f : P.X ⟶ Q.X) (hf : P.sectionMap ≫ f = Q.sectionMap)
    {x : Q.localRing} (hx : x ∈ maximalIdeal Q.localRing) :
    pullStalk f hf x ∈ maximalIdeal P.localRing := by
  change ¬ IsUnit (pullStalk f hf x)
  exact fun h => hx (isUnit_of_map_unit (pullStalk f hf).toRingHom x h)

theorem evaluation_pullStalk (f : P.X ⟶ Q.X) (hf : P.sectionMap ≫ f = Q.sectionMap)
    (x : Q.localRing) : P.evaluation (pullStalk f hf x) = Q.evaluation x := by
  have h : P.sectionMap.left ≫ f.left = Q.sectionMap.left :=
    congrArg (fun z : 𝟙_ (Over (Spec (.of k))) ⟶ Q.X => z.left) hf
  change (stalkMapAt f.left P.point Q.point (map_point f hf) ≫ P.evaluation) x = _
  have e (s : Spec (.of k) ⟶ P.X.left) (t : Spec (.of k) ⟶ Q.X.left)
      (ht : s ≫ f.left = t) :
      stalkMapAt f.left (s (closedPoint k)) (t (closedPoint k))
        ((Scheme.Hom.comp_apply s f.left (closedPoint k)).symm.trans
          (congrArg (fun u : Spec (.of k) ⟶ Q.X.left => u (closedPoint k)) ht)) ≫
        Scheme.stalkClosedPointTo s = Scheme.stalkClosedPointTo t := by
    subst t
    exact (Scheme.stalkClosedPointTo_comp s f.left).symm
  exact ConcreteCategory.congr_hom (e _ _ h) x

theorem specMap_pullStalk (f : P.X ⟶ Q.X) (hf : P.sectionMap ≫ f = Q.sectionMap) :
    Spec.map (CommRingCat.ofHom (pullStalk f hf).toRingHom) ≫ Q.X.left.fromSpecStalk Q.point =
      P.X.left.fromSpecStalk P.point ≫ f.left := by
  have e {X Y : Scheme} (g : X ⟶ Y) (x : X) (y : Y) (h : g x = y) :
      Spec.map (stalkMapAt g x y h) ≫ Y.fromSpecStalk y =
        X.fromSpecStalk x ≫ g := by
    subst y
    rw [stalkMapAt_canonical, Scheme.SpecMap_stalkMap_fromSpecStalk]
  exact e f.left P.point Q.point (map_point f hf)

/-- Pull back the genuine origin cotangent classes, now linearly over
the field of the rational section. -/
def pullCotangent (f : P.X ⟶ Q.X) (hf : P.sectionMap ≫ f = Q.sectionMap) :
    Q.cotangent →ₗ[k] P.cotangent :=
  Ideal.mapCotangent _ _ (pullStalk f hf) fun _ hx => mem_maximalIdeal_pullStalk f hf hx

@[simp] theorem pullCotangent_mk (f : P.X ⟶ Q.X) (hf : P.sectionMap ≫ f = Q.sectionMap)
    (x : maximalIdeal Q.localRing) :
    pullCotangent f hf ((maximalIdeal Q.localRing).toCotangent x) =
      (maximalIdeal P.localRing).toCotangent ⟨pullStalk f hf x, mem_maximalIdeal_pullStalk f hf x.2⟩ :=
  rfl

@[simp] theorem pullCotangent_id (P : PointedScheme k) :
    pullCotangent (𝟙 P.X) (by simp) = LinearMap.id := by
  ext x
  obtain ⟨y, rfl⟩ := (maximalIdeal P.localRing).toCotangent_surjective x
  rw [pullCotangent_mk, LinearMap.id_apply]
  congr 1
  apply Subtype.ext
  change pullStalk (𝟙 P.X) (by simp) (y : P.localRing) = y
  exact DFunLike.congr_fun (pullStalk_id P) (y : P.localRing)

theorem pullCotangent_comp (f : P.X ⟶ Q.X) (g : Q.X ⟶ T.X)
    (hf : P.sectionMap ≫ f = Q.sectionMap) (hg : Q.sectionMap ≫ g = T.sectionMap) :
    pullCotangent (f ≫ g) (by rw [← Category.assoc, hf, hg]) =
      (pullCotangent f hf).comp (pullCotangent g hg) := by
  ext x
  obtain ⟨y, rfl⟩ := (maximalIdeal T.localRing).toCotangent_surjective x
  simp only [pullCotangent_mk, LinearMap.comp_apply]
  congr 1
  apply Subtype.ext
  change pullStalk (f ≫ g) (by rw [← Category.assoc, hf, hg]) (y : T.localRing) =
    pullStalk f hf (pullStalk g hg y)
  exact DFunLike.congr_fun (pullStalk_comp f g hf hg) (y : T.localRing)

/-- Use the identity section of the actual abelian variety. -/
abbrev ofAbVar (A : PkgI3.AbVar k) : PointedScheme k := ⟨A.X, η[A.X]⟩

theorem pullCotangent_eq_geometric (A : PkgI3.AbVar k) (f : A.End)
    (v : (ofAbVar A).cotangent) :
    pullCotangent (P := ofAbVar A) (Q := ofAbVar A) f.hom (IsMonHom.one_hom f.hom) v =
      ZInQ.Contrib.AbVarBC.MulRigidity.cotangentMap A f.hom v := by
  obtain ⟨x, rfl⟩ := (maximalIdeal (ofAbVar A).localRing).toCotangent_surjective v
  erw [pullCotangent_mk (P := ofAbVar A) (Q := ofAbVar A)]
  unfold ZInQ.Contrib.AbVarBC.MulRigidity.cotangentMap
  erw [Ideal.mapCotangent_toCotangent]
  congr 1
  apply Subtype.ext
  change (stalkMapAt f.hom.left (ofAbVar A).point (ofAbVar A).point
    (map_point (P := ofAbVar A) (Q := ofAbVar A) f.hom (IsMonHom.one_hom f.hom))) (x : (ofAbVar A).localRing) =
      ZInQ.Contrib.AbVarBC.MulRigidity.stalkEndo A f.hom (x : (ofAbVar A).localRing)
  rw [stalkMapAt_eq]
  rfl

end PointedScheme
end

end ZInQ.Manuscript.RC.HCMV21
