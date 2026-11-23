import ZInQKernel.Contrib.OneProof.RC.HCMV21.CotangentProduct
import ZInQKernel.Contrib.Dim.HodgeLattice

/-! The scalar character of the level-one endomorphism ring on the
cotangent line. Tex 9146–9148 and 9245–9263. -/

namespace ZInQ.Manuscript.RC.HCMV21

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open IsLocalRing PointedScheme
open scoped CategoryTheory.MonObj

noncomputable section

variable {k : Type} [Field k]

namespace PointedScheme

private abbrev basePoint (k : Type) [Field k] : PointedScheme k :=
  ⟨𝟙_ (Over (Spec (.of k))), 𝟙 _⟩

private theorem baseCotangent_subsingleton : Subsingleton (basePoint k).cotangent := by
  let e := (stalkClosedPointIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  have h : maximalIdeal (basePoint k).localRing = ⊥ := by
    ext x
    change (¬ IsUnit x) ↔ x = 0
    have he : IsUnit (e x) ↔ IsUnit x :=
      MulEquiv.isUnit_map (f := e.toMulEquiv)
    calc
      (¬ IsUnit x) ↔ ¬ IsUnit (e x) := not_congr he.symm
      _ ↔ e x = 0 := by rw [isUnit_iff_ne_zero, not_ne_iff]
      _ ↔ x = 0 := map_eq_zero_iff e e.injective
  exact (Ideal.cotangent_subsingleton_iff _).mpr (by rw [h]; simp [IsIdempotentElem])

private theorem pullCotangent_const (P Q : PointedScheme k) :
    pullCotangent (P := P) (Q := Q) (toUnit P.X ≫ Q.sectionMap)
      (by
        rw [← Category.assoc, toUnit_unique (P.sectionMap ≫ toUnit P.X)
          (𝟙 (𝟙_ (Over (Spec (.of k))))), Category.id_comp]) =
      0 := by
  have h1 : P.sectionMap ≫ toUnit P.X = (basePoint k).sectionMap := toUnit_unique _ _
  have h2 : (basePoint k).sectionMap ≫ Q.sectionMap = Q.sectionMap := Category.id_comp _
  rw [pullCotangent_comp (Q := basePoint k) _ _ h1 h2]
  have := baseCotangent_subsingleton (k := k)
  apply LinearMap.ext
  intro v
  change pullCotangent (P := P) (Q := basePoint k) _ h1
    (pullCotangent (P := basePoint k) (Q := Q) _ h2 v) = 0
  rw [Subsingleton.elim (pullCotangent _ h2 v) 0, map_zero]

private abbrev squarePoint (P : PointedScheme k) : PointedScheme k :=
  ⟨P.X ⊗ P.X, CartesianMonoidalCategory.lift P.sectionMap P.sectionMap⟩

private theorem square_fst (P : PointedScheme k) :
    (squarePoint P).sectionMap ≫ CartesianMonoidalCategory.fst P.X P.X = P.sectionMap :=
  lift_fst _ _

private theorem square_snd (P : PointedScheme k) :
    (squarePoint P).sectionMap ≫ CartesianMonoidalCategory.snd P.X P.X = P.sectionMap :=
  lift_snd _ _

set_option maxHeartbeats 600000 in
private theorem square_cotangent_span (P : PointedScheme k) :
    LinearMap.range (pullCotangent (P := squarePoint P) (Q := P) _ (square_fst P)) ⊔
      LinearMap.range (pullCotangent (P := squarePoint P) (Q := P) _ (square_snd P)) = ⊤ := by
  classical
  let f : Bool → ((squarePoint P).X ⟶ P.X) := fun i =>
    if i then CartesianMonoidalCategory.fst _ _ else CartesianMonoidalCategory.snd _ _
  have hf (i : Bool) : (squarePoint P).sectionMap ≫ f i = P.sectionMap := by
    cases i
    · exact square_snd P
    · exact square_fst P
  have h := cotangent_ranges_sup_eq_top (squarePoint P) (fun _ : Bool => P) f hf (by
    intro S u v huv
    exact CartesianMonoidalCategory.hom_ext u v (huv true) (huv false))
  apply top_unique
  rw [← h]
  apply iSup_le
  intro i
  cases i
  · exact le_sup_right
  · exact le_sup_left

end PointedScheme

set_option maxHeartbeats 1000000 in
private theorem pullCotangent_add (A : PkgI3.AbVar k) (f g : A.End) :
    pullCotangent (P := ofAbVar A) (Q := ofAbVar A) (f + g).hom (IsMonHom.one_hom _) =
      pullCotangent (P := ofAbVar A) (Q := ofAbVar A) f.hom (IsMonHom.one_hom _) +
      pullCotangent (P := ofAbVar A) (Q := ofAbVar A) g.hom (IsMonHom.one_hom _) := by
  let P := ofAbVar A
  let J := squarePoint P
  let u₁ : A.X ⟶ A.X ⊗ A.X := CartesianMonoidalCategory.lift (𝟙 _) 1
  let u₂ : A.X ⟶ A.X ⊗ A.X := CartesianMonoidalCategory.lift 1 (𝟙 _)
  have hη : η[A.X] ≫ (1 : A.X ⟶ A.X) = η[A.X] := by
    rw [MonObj.comp_one]
    rfl
  have hu₁ : P.sectionMap ≫ u₁ = J.sectionMap := by
    change η[A.X] ≫ CartesianMonoidalCategory.lift (𝟙 _) 1 = _
    rw [comp_lift, Category.comp_id, hη]
  have hu₂ : P.sectionMap ≫ u₂ = J.sectionMap := by
    change η[A.X] ≫ CartesianMonoidalCategory.lift 1 (𝟙 _) = _
    rw [comp_lift, Category.comp_id, hη]
  have hμ : J.sectionMap ≫ μ[A.X] = P.sectionMap :=
    one_mul (1 : 𝟙_ _ ⟶ A.X)
  let d₁ := pullCotangent (P := J) (Q := P) _ (square_fst P)
  let d₂ := pullCotangent (P := J) (Q := P) _ (square_snd P)
  let i₁ := pullCotangent (P := P) (Q := J) u₁ hu₁
  let i₂ := pullCotangent (P := P) (Q := J) u₂ hu₂
  have compose (u : P.X ⟶ J.X) (v : J.X ⟶ P.X) (w : P.X ⟶ P.X)
      (hu : P.sectionMap ≫ u = J.sectionMap) (hv : J.sectionMap ≫ v = P.sectionMap)
      (hw : P.sectionMap ≫ w = P.sectionMap) (e : u ≫ v = w) :
      (pullCotangent u hu).comp (pullCotangent v hv) = pullCotangent w hw :=
    (pullCotangent_comp u v hu hv).symm.trans
      (pullCotangent_congr e (by rw [← Category.assoc, hu, hv]) hw)
  have hId : P.sectionMap ≫ 𝟙 P.X = P.sectionMap := Category.comp_id _
  have hd₁₁ : i₁.comp d₁ = LinearMap.id :=
    (compose _ _ _ hu₁ (square_fst P) hId (lift_fst _ _)).trans (pullCotangent_id P)
  have hd₂₂ : i₂.comp d₂ = LinearMap.id :=
    (compose _ _ _ hu₂ (square_snd P) hId (lift_snd _ _)).trans (pullCotangent_id P)
  have hd₁₂ : i₁.comp d₂ = 0 :=
    (compose _ _ _ hu₁ (square_snd P) hη (lift_snd _ _)).trans (pullCotangent_const P P)
  have hd₂₁ : i₂.comp d₁ = 0 :=
    (compose _ _ _ hu₂ (square_fst P) hη (lift_fst _ _)).trans (pullCotangent_const P P)
  have hleft : u₁ ≫ μ[A.X] = 𝟙 _ := mul_one _
  have hright : u₂ ≫ μ[A.X] = 𝟙 _ := one_mul _
  let dμ := pullCotangent (P := J) (Q := P) μ[A.X] hμ
  have hm₁ : i₁.comp dμ = LinearMap.id :=
    (compose _ _ _ hu₁ hμ hId hleft).trans (pullCotangent_id P)
  have hm₂ : i₂.comp dμ = LinearMap.id :=
    (compose _ _ _ hu₂ hμ hId hright).trans (pullCotangent_id P)
  have hmul : dμ = d₁ + d₂ := by
    apply LinearMap.ext
    intro v
    let w := dμ v
    have hw : w ∈ LinearMap.range d₁ ⊔ LinearMap.range d₂ :=
      (square_cotangent_span P).symm ▸ Submodule.mem_top
    obtain ⟨_, ⟨v₁, rfl⟩, _, ⟨v₂, rfl⟩, he⟩ := Submodule.mem_sup.mp hw
    have he₁ : i₁ w = v₁ := by
      rw [← he, map_add, ← LinearMap.comp_apply, hd₁₁, ← LinearMap.comp_apply, hd₁₂]
      simp
    have he₂ : i₂ w = v₂ := by
      rw [← he, map_add, ← LinearMap.comp_apply, hd₂₁, ← LinearMap.comp_apply, hd₂₂]
      simp
    have hv₁ : i₁ w = v := DFunLike.congr_fun hm₁ v
    have hv₂ : i₂ w = v := DFunLike.congr_fun hm₂ v
    change w = d₁ v + d₂ v
    rw [he₁.symm.trans hv₁, he₂.symm.trans hv₂] at he
    exact he.symm
  let u := CartesianMonoidalCategory.lift f.hom g.hom
  have hu : P.sectionMap ≫ u = J.sectionMap := by
    change η[A.X] ≫ CartesianMonoidalCategory.lift f.hom g.hom = _
    rw [comp_lift, IsMonHom.one_hom, IsMonHom.one_hom]
  have hd₁ : (pullCotangent (P := P) (Q := J) u hu).comp d₁ =
      pullCotangent (P := P) (Q := P) f.hom (IsMonHom.one_hom _) :=
    compose _ _ _ hu (square_fst P) _ (lift_fst _ _)
  have hd₂ : (pullCotangent (P := P) (Q := J) u hu).comp d₂ =
      pullCotangent (P := P) (Q := P) g.hom (IsMonHom.one_hom _) :=
    compose _ _ _ hu (square_snd P) _ (lift_snd _ _)
  have h := pullCotangent_comp (P := P) (Q := J) (T := P) u μ[A.X] hu hμ
  calc
    _ = (pullCotangent (P := P) (Q := J) u hu).comp dμ := h
    _ = _ := by rw [hmul, LinearMap.comp_add, hd₁, hd₂]

/-- The additive representation on the actual cotangent space.
Composition acts in reverse order. -/
def cotangentEndMap (A : PkgI3.AbVar k) :
    A.End →+ Module.End k (ofAbVar A).cotangent where
  toFun f := pullCotangent (P := ofAbVar A) (Q := ofAbVar A) f.hom (IsMonHom.one_hom _)
  map_zero' := pullCotangent_const _ _
  map_add' := pullCotangent_add A

@[simp] theorem cotangentEndMap_one (A : PkgI3.AbVar k) :
    cotangentEndMap A 1 = 1 := by
  change pullCotangent (P := ofAbVar A) (Q := ofAbVar A) (𝟙 A.X) _ = LinearMap.id
  exact pullCotangent_id (ofAbVar A)

set_option maxHeartbeats 550000 in
theorem cotangentEndMap_mul (A : PkgI3.AbVar k) (f g : A.End) :
    cotangentEndMap A (f * g) = cotangentEndMap A g * cotangentEndMap A f := by
  change pullCotangent (P := ofAbVar A) (Q := ofAbVar A) (g.hom ≫ f.hom) _ =
    (pullCotangent (P := ofAbVar A) (Q := ofAbVar A) g.hom (IsMonHom.one_hom g.hom)).comp
      (pullCotangent (P := ofAbVar A) (Q := ofAbVar A) f.hom (IsMonHom.one_hom f.hom))
  exact pullCotangent_comp (P := ofAbVar A) (Q := ofAbVar A) (T := ofAbVar A)
    g.hom f.hom (IsMonHom.one_hom _) (IsMonHom.one_hom _)

private theorem onLine_eq_smul {V : Type} [AddCommGroup V] [Module k V]
    (e : V ≃ₗ[k] k) (f : V →ₗ[k] V) (v : V) :
    f v = e (f (e.symm 1)) • v := by
  have hv : e v • e.symm 1 = v := e.injective (by simp)
  calc
    f v = f (e v • e.symm 1) := congrArg f hv.symm
    _ = e v • f (e.symm 1) := f.map_smul _ _
    _ = e (f (e.symm 1)) • v := e.injective (by simp [mul_comm])

/-- The cotangent scalar in a chosen trivialization of the line.
The scalars commute, giving a ring homomorphism. -/
def cotangentCharacter (A : PkgI3.AbVar k) (e : (ofAbVar A).cotangent ≃ₗ[k] k) :
    A.End →+* k where
  toFun f := e (cotangentEndMap A f (e.symm 1))
  map_zero' := by simp
  map_one' := by simp
  map_add' f g := by simp
  map_mul' f g := by
    rw [cotangentEndMap_mul, Module.End.mul_apply,
      onLine_eq_smul e (cotangentEndMap A g) (cotangentEndMap A f (e.symm 1)),
      map_smul, smul_eq_mul, mul_comm]

/-- The scalar acts on every cotangent vector through the actual scheme map. -/
theorem cotangentMap_eq_character_smul (A : PkgI3.AbVar k)
    (e : (ofAbVar A).cotangent ≃ₗ[k] k) (f : A.End) (v : (ofAbVar A).cotangent) :
    ZInQ.Contrib.AbVarBC.MulRigidity.cotangentMap A f.hom v = cotangentCharacter A e f • v := by
  calc
    _ = cotangentEndMap A f v := (pullCotangent_eq_geometric A f v).symm
    _ = _ := onLine_eq_smul e (cotangentEndMap A f) v

/-- The dual tangent map has the same scalar. -/
theorem tangentMap_eq_character_smul (A : PkgI3.AbVar k)
    (e : (ofAbVar A).cotangent ≃ₗ[k] k) (f : A.End)
    (v : Module.Dual k (ofAbVar A).cotangent) :
    v.comp (cotangentEndMap A f) = cotangentCharacter A e f • v := by
  ext w
  change v (cotangentEndMap A f w) = cotangentCharacter A e f • v w
  rw [onLine_eq_smul e (cotangentEndMap A f) w, map_smul]
  rfl

/-- The rational section identifies the actual residue field at its
image with the ground field. -/
def residueAtSection (P : PointedScheme k) : ResidueField P.localRing ≃+* k := by
  have : IsLocalHom P.evaluation.hom := Scheme.isLocalHom_stalkClosedPointTo' P.sectionMap.left
  let f := ResidueField.lift P.evaluation.hom
  exact RingEquiv.ofBijective f ⟨f.injective, fun c => ⟨residue _ (algebraMap k P.localRing c),
    evaluation_constant P c⟩⟩

/-- The origin cotangent space of a curve has a basis with one element over
the ground field of its rational identity section. -/
theorem cotangent_finrank_one (A : PkgI3.AbVar k) (hdim : A.dim = 1) :
    Module.finrank k (ofAbVar A).cotangent = 1 := by
  let P := ofAbVar A
  have hK : Module.finrank k (ResidueField P.localRing) = 1 := by
    let e : k ≃ₐ[k] ResidueField P.localRing :=
      AlgEquiv.ofBijective (Algebra.ofId k _) ⟨
        (algebraMap k (ResidueField P.localRing)).injective, fun c => ⟨residueAtSection P c, by
          apply (residueAtSection P).injective
          change P.evaluation (algebraMap k P.localRing (residueAtSection P c)) = _
          exact evaluation_constant P (residueAtSection P c)⟩⟩
    rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
  have hC : Module.finrank (ResidueField P.localRing) P.cotangent = 1 := by
    have hpoint : P.point = ZInQ.DefFaltings.HodgeLattice.originPt A :=
      congrArg (fun x : Spec (.of k) => P.sectionMap.left x) (Subsingleton.elim _ _)
    change Module.finrank (ResidueField (A.X.left.presheaf.stalk P.point))
      (CotangentSpace (A.X.left.presheaf.stalk P.point)) = 1
    rw [hpoint]
    exact ZInQ.Contrib.Dim.tangentDimAtOrigin k A 1 hdim
  have : IsScalarTower k (ResidueField P.localRing) P.cotangent := ⟨fun c d v => by
    change (algebraMap k P.localRing c • d) • v = algebraMap k P.localRing c • (d • v)
    exact smul_assoc _ _ _⟩
  change Module.finrank k P.cotangent = 1
  rw [← Module.finrank_mul_finrank k (ResidueField P.localRing) P.cotangent, hK, hC, Nat.one_mul]

/-- Choose a generator of the genuine cotangent line. -/
def cotangentLine (A : PkgI3.AbVar k) (hdim : A.dim = 1) :
    (ofAbVar A).cotangent ≃ₗ[k] k :=
  (Module.basisUnique (Fin 1) (cotangent_finrank_one A hdim)).equivFun.trans
    (LinearEquiv.funUnique (Fin 1) k k)

end

end ZInQ.Manuscript.RC.HCMV21
