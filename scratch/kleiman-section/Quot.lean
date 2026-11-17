import ZInQKernel.Contrib.OneProof.PicZeroAbVarCharZero
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.NormalizedSheaf
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.RepresentableGroup

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory

namespace KleimanSection

open Scheme

variable {X S : Scheme.{u}}

/-- The image of `Pic(T)` in `Pic(X ×_S T)` under pullback along the projection. -/
abbrev picBase (f : X ⟶ S) (T : Over S) : Subgroup (pullback f T.hom).Pic :=
  (Pic.mapHom (pullback.snd f T.hom)).range

lemma map_baseChangeMap_map_snd (f : X ⟶ S) {T T' : Over S} (φ : T' ⟶ T) (M : T.left.Pic) :
    Pic.map (JacobianChallenge.baseChangeMap f φ) (Pic.map (pullback.snd f T.hom) M) =
      Pic.map (pullback.snd f T'.hom) (Pic.map φ.left M) := by
  rw [← Pic.map_comp, ← Pic.map_comp, pullback.lift_snd]

/-- **Kleiman's relative Picard functor** (Kleiman, *The Picard scheme*, Def. 9.2.2; UNVERIFIED numbering) as a
presheaf of groups: `T ↦ Pic(X ×_S T) / Pic(T)`. -/
def kleimanPicardPresheafGrp (f : X ⟶ S) : (Over S)ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj T := GrpCat.of ((pullback f T.unop.hom).Pic ⧸ picBase f T.unop)
  map φ := GrpCat.ofHom (QuotientGroup.map _ _ (Pic.mapHom (JacobianChallenge.baseChangeMap f φ.unop)) (by
    rintro _ ⟨M, rfl⟩
    exact ⟨Pic.map φ.unop.left M, (map_baseChangeMap_map_snd f φ.unop M).symm⟩))
  map_id T := by
    refine GrpCat.hom_ext (QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun x ↦ ?_))
    change (QuotientGroup.mk (Pic.map (JacobianChallenge.baseChangeMap f (𝟙 T).unop) x) :
      (pullback f T.unop.hom).Pic ⧸ picBase f T.unop) = QuotientGroup.mk x
    rw [unop_id, JacobianChallenge.baseChangeMap_id, Pic.map_id]
  map_comp φ ψ := by
    refine GrpCat.hom_ext (QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun x ↦ ?_))
    change (QuotientGroup.mk (Pic.map (JacobianChallenge.baseChangeMap f (φ ≫ ψ).unop) x) : _ ⧸ _) =
      QuotientGroup.mk (Pic.map (JacobianChallenge.baseChangeMap f ψ.unop)
        (Pic.map (JacobianChallenge.baseChangeMap f φ.unop) x))
    rw [unop_comp, JacobianChallenge.baseChangeMap_comp, Pic.map_comp]

/-- Kleiman's relative Picard functor `T ↦ Pic(X_T)/Pic(T)` as a presheaf of sets. -/
abbrev kleimanPicardPresheaf (f : X ⟶ S) : (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  kleimanPicardPresheafGrp f ⋙ forget GrpCat

/-- **Kleiman's `Pic_{(X/S)(fppf)}`**: the fppf sheafification of `T ↦ Pic(X_T)/Pic(T)` (Kleiman, *The Picard
scheme*, Def. 9.2.2; UNVERIFIED numbering). -/
def kleimanPicardSheaf (f : X ⟶ S) : Sheaf (fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (fppfTopology.over S) (Type (u + 1))).obj (kleimanPicardPresheaf f)

/-- The quotient map `Pic(X_T) → Pic(X_T)/Pic(T)`, as a morphism of presheaves of groups. -/
def quotGrp (f : X ⟶ S) : picardPresheafGrp f ⟶ kleimanPicardPresheafGrp f where
  app T := GrpCat.ofHom (QuotientGroup.mk' (picBase f T.unop))
  naturality T T' φ := by
    refine GrpCat.hom_ext (MonoidHom.ext fun x ↦ ?_)
    rfl

/-- The quotient map as a morphism of presheaves of sets, out of `picardPresheaf`. -/
def quot (f : X ⟶ S) : picardPresheaf f ⟶ kleimanPicardPresheaf f :=
  Functor.whiskerRight (quotGrp f) (forget GrpCat)

instance isLocallySurjective_quot (f : X ⟶ S) :
    Presheaf.IsLocallySurjective (fppfTopology.over S) (quot f) :=
  Presheaf.isLocallySurjective_of_surjective _ _ fun T y ↦ by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective (s := picBase f T.unop) y
    exact ⟨x, rfl⟩

instance isLocallyInjective_quot (f : X ⟶ S) :
    Presheaf.IsLocallyInjective (fppfTopology.over S) (quot f) where
  equalizerSieve_mem {T} x y h := by
    change (pullback f T.unop.hom).Pic at x y
    have h' : (QuotientGroup.mk x : (pullback f T.unop.hom).Pic ⧸ picBase f T.unop) = QuotientGroup.mk y := h
    obtain ⟨M, hM⟩ := QuotientGroup.eq.mp h'
    have hy : y = x * Pic.map (pullback.snd f T.unop.hom) M := by
      rw [show Pic.map (pullback.snd f T.unop.hom) M = x⁻¹ * y from hM, mul_inv_cancel_left]
    choose cover membership triv using fun point : T.unop.left ↦ Pic.exists_map_iota_eq_one M point
    rw [GrothendieckTopology.mem_over_iff]
    refine fppfTopology.superset_covering ?_ (Precoverage.generate_mem_toGrothendieck
      (R := Presieve.ofArrows (fun point ↦ (cover point).toScheme) (fun point ↦ (cover point).ι)) ?_)
    · rw [Sieve.generate_le_iff]
      rintro _ _ ⟨point⟩
      rw [Sieve.overEquiv_iff]
      let restriction : Over.mk ((cover point).ι ≫ T.unop.hom) ⟶ T.unop := Over.homMk (cover point).ι
      change Pic.map (JacobianChallenge.baseChangeMap f restriction) x =
        Pic.map (JacobianChallenge.baseChangeMap f restriction) y
      rw [hy, Pic.map_mul, map_baseChangeMap_map_snd]
      change _ = _ * Pic.map _ (Pic.map (cover point).ι M)
      rw [triv point, Pic.map_one, mul_one]
    · rw [fppfPrecoverage, ofArrows_mem_precoverage_iff]
      exact ⟨fun point ↦ ⟨point, ⟨point, membership point⟩, rfl⟩,
        fun point ↦ ⟨inferInstance, inferInstance⟩⟩

instance isIso_presheafToSheaf_map_quot (f : X ⟶ S) :
    IsIso ((presheafToSheaf (fppfTopology.over S) (Type (u + 1))).map (quot f)) :=
  ((fppfTopology.over S).W_iff _).mp ((fppfTopology.over S).W_of_isLocallyBijective _)

/-- **Comparison (no section needed).** The tree's `picardFunctor f` (the fppf sheafification of
`T ↦ Pic(X_T)`) is isomorphic to Kleiman's `Pic_{(X/S)(fppf)}` (the fppf sheafification of
`T ↦ Pic(X_T)/Pic(T)`), by the sheafified quotient map. -/
def picardFunctorIsoKleiman (f : X ⟶ S) : picardFunctor f ≅ kleimanPicardSheaf f :=
  asIso ((presheafToSheaf (fppfTopology.over S) (Type (u + 1))).map (quot f))


/-- The group law of a scheme representing Kleiman's `Pic_{(X/S)(fppf)}`, induced from the quotient groups
`Pic(X_T)/Pic(T)` (the same construction as the tree's `picardFunctorCommGrpObj`). -/
@[instance_reducible]
def kleimanPicardGrpObj (f : X ⟶ S) {P : Over S} (rep : (kleimanPicardSheaf f).obj.RepresentableBy P) :
    GrpObj P :=
  GrpObj.ofRepresentableBySheafify (fppfTopology.over S) (kleimanPicardPresheafGrp f) P rep

/-- A representation of the tree's `picardFunctor` is a representation of Kleiman's sheaf. -/
def repKleiman (f : X ⟶ S) {P : Over S} (rep : (picardFunctor f).obj.RepresentableBy P) :
    (kleimanPicardSheaf f).obj.RepresentableBy P :=
  rep.ofIso ((sheafToPresheaf _ _).mapIso (picardFunctorIsoKleiman f))

/-- A representation of Kleiman's sheaf is a representation of the tree's `picardFunctor`. -/
def repTree (f : X ⟶ S) {P : Over S} (rep : (kleimanPicardSheaf f).obj.RepresentableBy P) :
    (picardFunctor f).obj.RepresentableBy P :=
  rep.ofIso ((sheafToPresheaf _ _).mapIso (picardFunctorIsoKleiman f).symm)

open scoped MonObj in
/-- The identity points agree: the class of the trivial bundle maps to the class of the trivial bundle. -/
lemma eta_repKleiman (f : X ⟶ S) {P : Over S} (rep : (picardFunctor f).obj.RepresentableBy P) :
    (letI := kleimanPicardGrpObj f (repKleiman f rep); η[P]) =
      (letI := picardFunctorCommGrpObj f rep; η[P]) := by
  change (repKleiman f rep).homEquiv.symm
      ((toSheafify (fppfTopology.over S) (kleimanPicardPresheaf f)).app _
        (1 : (pullback f (𝟙_ (Over S)).hom).Pic ⧸ picBase f (𝟙_ (Over S)))) =
    rep.homEquiv.symm ((toSheafify (fppfTopology.over S) (picardPresheaf f)).app _
      (1 : (pullback f (𝟙_ (Over S)).hom).Pic))
  rw [Equiv.symm_apply_eq]
  change _ = ((presheafToSheaf (fppfTopology.over S) (Type (u + 1))).map (quot f)).hom.app _
    (rep.homEquiv (rep.homEquiv.symm ((toSheafify (fppfTopology.over S) (picardPresheaf f)).app _
      (1 : (pullback f (𝟙_ (Over S)).hom).Pic))))
  rw [Equiv.apply_symm_apply]
  exact ConcreteCategory.congr_hom (congr_app (toSheafify_naturality (fppfTopology.over S) (quot f))
    (op (𝟙_ (Over S)))) (1 : (pullback f (𝟙_ (Over S)).hom).Pic)


/-! ## The leaves and the derivations -/

open T09Pic PkgI3 PkgI3.AbVar PicDict PicFix

lemma identityComponent_repKleiman {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))}
    {P : Over (Spec (CommRingCat.of K))} (rep : (picardFunctor X.hom).obj.RepresentableBy P) :
    (letI := kleimanPicardGrpObj X.hom (repKleiman X.hom rep); identityComponent P) =
      (letI := picardFunctorCommGrpObj X.hom rep; identityComponent P) := by
  unfold identityComponent
  rw [eta_repKleiman]

/-- **LEAF (Kleiman 9.5.4 over Kleiman's own functor; same hypotheses as `PicFix.KleimanPicZeroProper`).** -/
def KleimanPicZeroProperQ : Prop :=
  ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))), IsProper X.hom →
    geometrically IsNormalScheme X.hom →
    ∀ (P : Over (Spec (CommRingCat.of K))) (rep : (kleimanPicardSheaf X.hom).obj.RepresentableBy P)
      (V : P.left.Opens),
      letI := kleimanPicardGrpObj X.hom rep
      (V : Set P.left) = identityComponent P → IsProper (V.ι ≫ P.hom)

theorem kleimanPicZeroProper_of_Q (h : KleimanPicZeroProperQ) : PicFix.KleimanPicZeroProper := by
  intro K _ X hX hN P rep V hV
  refine h K X hX hN P (repKleiman X.hom rep) V ?_
  rw [identityComponent_repKleiman]
  exact hV

/-- **LEAF (printed form, weakest reading).** -/
def KleimanPicZeroProperPrinted : Prop :=
  ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))), IsProper X.hom →
    GeometricallyIntegral X.hom → geometrically IsNormalScheme X.hom →
    (∃ (N : Type) (_ : Finite N) (i : X.left ⟶ ℙ(N; Spec (CommRingCat.of K))),
      IsImmersion i ∧ i ≫ ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K) = X.hom) →
    (∃ σ : Spec (CommRingCat.of K) ⟶ X.left, σ ≫ X.hom = 𝟙 _) →
    ∀ (P : Over (Spec (CommRingCat.of K))) (rep : (kleimanPicardSheaf X.hom).obj.RepresentableBy P)
      (V : P.left.Opens),
      letI := kleimanPicardGrpObj X.hom rep
      (V : Set P.left) = identityComponent P → IsProper (V.ι ≫ P.hom)

theorem kleimanPicZeroProperPrinted_of_Q (h : KleimanPicZeroProperQ) : KleimanPicZeroProperPrinted :=
  fun K _ X hX _ hN _ _ => h K X hX hN

open scoped MonObj in
theorem picZeroProperAt_of_printed (h : KleimanPicZeroProperPrinted) (K : Type) [Field K] :
    PicZeroChar0.PicZeroProperAt K := by
  intro A P rep V hV
  obtain ⟨L, N, hN, i, hi, hover, -⟩ := exists_isVeryAmple A
  refine h K A.X inferInstance inferInstance (geometricallyNormal_of_smooth A.X.hom) ⟨N, hN, i, hi, hover⟩
    ⟨η[A.X].left, Over.w η[A.X]⟩ P (repKleiman A.X.hom rep) V ?_
  rw [identityComponent_repKleiman]
  exact hV

theorem picZeroAbVar0_of_printed (h1 : PicLocFinType) (h2 : IdentityComponentLFT)
    (h3 : KleimanPicZeroProperPrinted) : PicZeroChar0.PicZeroAbVar0 := fun K _ _ =>
  PicZeroChar0.picZeroAbVarAt_of h1 h2 K
    (PicZeroChar0.picZeroSmoothAt_charZero ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof h1 K)
    (picZeroProperAt_of_printed h3 K)

end KleimanSection
