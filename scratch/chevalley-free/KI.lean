import ZInQKernel.Contrib.OneProof.SemiAbelianDescendsPerfect
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.AbelianVariety.RationalCurves
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Birational.ValuativeExtension
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.Dimension

/-! # chevalley-free, step R: morphisms from `𝔾_m` to an abelian variety are constant -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry.ProjectiveLine AlgebraicGeometry.ProjectiveSpace ZInQ.SemiAbDescend
open DictModels.RaynaudOr ZInQ.HeightSplit

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ZInQ.ChevFree

section Rig

variable (K : Type) [Field K]

/-- `Spec K`. -/
abbrev PK : Scheme := Spec (CommRingCat.of K)

/-- The overlap `𝔾_m ⊆ ℙ¹_K` of the two standard charts. -/
abbrev Ov : Scheme := (relativeOverlap (PK K)).toScheme

/-- An element of `K` as a global section of `Spec K`. -/
abbrev secK (s : K) : Γ(PK K, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv s

theorem mem_overlap (s : Kˣ) (x : PK K) :
    normalized (𝟙 (PK K)) ⟨1⟩ (secK K s) x ∈ relativeOverlap (PK K) := by
  have hc : ∀ c : ULift.{0} (Fin 2),
      normalized (𝟙 (PK K)) ⟨1⟩ (secK K s) x ∈ standardOpen (ULift.{0} (Fin 2)) (PK K) c := by
    intro c
    change x ∈ normalized (𝟙 (PK K)) ⟨1⟩ (secK K s) ⁻¹ᵁ standardOpen (ULift.{0} (Fin 2)) (PK K) c
    rw [normalized, homOfSections_preimage_standardOpen]
    have hu : IsUnit (normalizedSections (source := PK K) ⟨1⟩ (secK K s) c) := by
      unfold normalizedSections
      split_ifs
      · exact isUnit_one
      · exact (s.isUnit.map _)
    rw [Scheme.basicOpen_of_isUnit _ hu]
    trivial
  exact ⟨hc ⟨0⟩, hc ⟨1⟩⟩

/-- The `K`-point `[s : 1]` of the overlap. -/
def ovPt (s : Kˣ) : PK K ⟶ Ov K :=
  IsOpenImmersion.lift (relativeOverlap (PK K)).ι (normalized (𝟙 (PK K)) ⟨1⟩ (secK K s)) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact mem_overlap K s x)

@[reassoc (attr := simp)]
theorem ovPt_ι (s : Kˣ) : ovPt K s ≫ (relativeOverlap (PK K)).ι = normalized (𝟙 (PK K)) ⟨1⟩ (secK K s) :=
  IsOpenImmersion.lift_fac ..

theorem ovPt_over (s : Kˣ) : ovPt K s ≫ overlapToBase K = 𝟙 (PK K) := by
  rw [overlapToBase, ovPt_ι_assoc, normalized_over]

theorem ovPt_coordinate (s : Kˣ) : (ovPt K s).appTop (scalingCoordinate K ⟨1⟩) = secK K s := by
  have chartEquation : ovPt K s ≫ ((relativeLine (PK K))).homOfLE
      (relativeOverlap_le_standardOpen (PK K) ⟨1⟩) =
      relativeChartPoint (𝟙 (PK K)) ⟨1⟩ (secK K s) := by
    apply (cancel_mono (standardOpen (ULift.{0} (Fin 2)) (PK K) ⟨1⟩).ι).mp
    simp
  rw [scalingCoordinate, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    chartEquation, relativeChartPoint_coordinate]

/-- `ℙ¹_K` is smooth of relative dimension one. -/
instance line_smooth : SmoothOfRelativeDimension 1 (relativeLine (PK K) ↘ PK K) := by
  haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{0} 1) (relativeChartCover (PK K))
  intro (c : ULift.{0} (Fin 2))
  change SmoothOfRelativeDimension 1
    ((standardOpen (ULift.{0} (Fin 2)) (PK K) c).ι ≫ relativeLine (PK K) ↘ PK K)
  rw [← standardOpenIso_hom_over]
  have : Nat.card {o : ULift.{0} (Fin 2) // o ≠ c} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨⟨c.down.rev⟩, ?_⟩⟩⟩
    · rcases a with ⟨⟨a⟩, ha⟩; rcases b with ⟨⟨b⟩, hb⟩; rcases c with ⟨c⟩
      ext; simp only [ne_eq, ULift.ext_iff] at ha hb ⊢; omega
    · rcases c with ⟨c⟩; simp only [ne_eq, ULift.ext_iff]; fin_cases c <;> decide
  rw [MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension.{0} 1)]
  exact AffineSpace.smoothOfRelativeDimension_of_card_eq (n := {o : ULift.{0} (Fin 2) // o ≠ c})
    (PK K) this


variable {K}

theorem genericPoint_mem_overlap : genericPoint (relativeLine (PK K)) ∈ relativeOverlap (PK K) := by
  rw [← SetLike.mem_coe,
    (genericPoint_spec (relativeLine (PK K))).mem_open_set_iff (relativeOverlap (PK K)).isOpen]
  simpa using (Scheme.Opens.nonempty_iff _).mp (inferInstance : Nonempty (Ov K))

/-- `Spec K(ℙ¹) → 𝔾_m`. -/
abbrev ξg : Spec (relativeLine (PK K)).functionField ⟶ Ov K :=
  (relativeOverlap (PK K)).fromSpecStalkOfMem _ (genericPoint_mem_overlap (K := K))

theorem ξg_ι : ξg (K := K) ≫ (relativeOverlap (PK K)).ι = (relativeLine (PK K)).fromSpecFunctionField :=
  Scheme.Opens.fromSpecStalkOfMem_ι _ _ _

instance : IsDominant (ξg (K := K)) := by
  constructor
  let p : Spec (relativeLine (PK K)).functionField :=
    IsLocalRing.closedPoint ((relativeLine (PK K)).functionField)
  let z := (ξg (K := K)) p
  have hz : (relativeOverlap (PK K)).ι z = genericPoint (relativeLine (PK K)) := by
    show (relativeOverlap (PK K)).ι ((ξg (K := K)) p) = _
    rw [← Scheme.Hom.comp_apply, ξg_ι]
    exact Scheme.fromSpecStalk_closedPoint
  have hd : Dense ({z} : Set (Ov K)) := by
    rw [dense_iff_closure_eq,
      (relativeOverlap (PK K)).ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      Set.image_singleton, hz, genericPoint_closure]
    rfl
  exact hd.mono (by rintro _ rfl; exact ⟨_, rfl⟩)

/-- Every morphism `ℙ¹_K → B` to an abelian variety takes the same value at all `K`-points
(vendored `RationalCurves.eq_zero_comp`, commutativity from Mathlib). -/
theorem line_const (B : PkgI3.AbVar K) (E : relativeLineOver K ⟶ B.X)
    (a b : 𝟙_ (Over (PK K)) ⟶ relativeLineOver K) : a ≫ E = b ≫ E := by
  letI := B.grp
  haveI := B.proper
  haveI := B.smooth
  haveI := B.geomInt
  haveI : IsCommMonObj B.X := isCommMonObj_of_isProper_of_geometricallyIntegral B.X
  let V : AlgebraicGeometry.AbelianVariety K := ⟨CommGrp.mk B.X⟩
  have hE := AlgebraicGeometry.AbelianVariety.RationalCurves.eq_zero_comp V E
  have ha : a ≫ E = ProjectiveLine.zeroPointOver K ≫ E := by
    conv_lhs => rw [hE]
    rw [← Category.assoc, ← Category.assoc, Subsingleton.elim (a ≫ toUnit _) (𝟙 _), Category.id_comp]
  have hb : b ≫ E = ProjectiveLine.zeroPointOver K ≫ E := by
    conv_lhs => rw [hE]
    rw [← Category.assoc, ← Category.assoc, Subsingleton.elim (b ≫ toUnit _) (𝟙 _), Category.id_comp]
  rw [ha, hb]

/-- **Rigidity for `𝔾_m`**: a morphism from the overlap `𝔾_m ⊆ ℙ¹_K` to an abelian variety over `K` takes
the same value at all the points `[s : 1]`. -/
theorem overlap_const (B : PkgI3.AbVar K) (h : Ov K ⟶ B.X.left) (hh : h ≫ B.X.hom = overlapToBase K)
    (s t : Kˣ) : ovPt K s ≫ h = ovPt K t ≫ h := by
  letI : (B.X.left).Over (PK K) := ⟨B.X.hom⟩
  haveI : IsProper (B.X.left ↘ PK K) := B.proper
  haveI : B.X.left.IsSeparated := ⟨by
    rw [← terminal.comp_from B.X.hom]
    haveI : IsSeparated B.X.hom := inferInstanceAs (IsSeparated (B.X.left ↘ PK K))
    infer_instance⟩
  have hval : ∀ x, ValuationRing ((relativeLine (PK K)).presheaf.stalk x) :=
    Scheme.valuationRing_stalk (relativeLine (PK K) ↘ PK K)
  obtain ⟨E, hEo, hE⟩ := Scheme.exists_hom_of_valuationRing_stalk (base := PK K) hval (ξg ≫ h) (by
    change ξg ≫ h ≫ B.X.hom = _
    rw [hh, overlapToBase, ← Category.assoc, ξg_ι])
  have hEo' : E ≫ B.X.hom = relativeLine (PK K) ↘ PK K := hEo.comp_over
  have hagree : (relativeOverlap (PK K)).ι ≫ E = h := by
    apply ext_of_isDominant_of_isSeparated B.X.hom ?_ (ξg (K := K)) ?_
    · rw [Category.assoc, hEo', hh, overlapToBase]
    · rw [← Category.assoc, ξg_ι, hE]
  let Em : relativeLineOver K ⟶ B.X := Over.homMk E hEo'
  let pt : Kˣ → (𝟙_ (Over (PK K)) ⟶ relativeLineOver K) := fun s =>
    Over.homMk (ovPt K s ≫ (relativeOverlap (PK K)).ι) (by
      change (ovPt K s ≫ (relativeOverlap (PK K)).ι) ≫ relativeLine (PK K) ↘ PK K = 𝟙 _
      rw [Category.assoc, ← overlapToBase, ovPt_over])
  have := congrArg CommaMorphism.left (line_const B Em (pt s) (pt t))
  simp only [Over.comp_left, Over.homMk_left, Em, pt] at this
  rw [← hagree, ← Category.assoc, ← Category.assoc]
  simpa only [Category.assoc] using this

/-- The `K`-algebra structure of `Γ(𝔾_m)`. -/
@[reducible] def ovAlg : Algebra K Γ(Ov K, ⊤) :=
  ((overlapToBase K).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra

/-- The coordinate `u = X₀/X₁` of `𝔾_m`, a unit. -/
def uOv : Γ(Ov K, ⊤)ˣ :=
  ⟨scalingCoordinate K ⟨1⟩, scalingCoordinate K ⟨0⟩, scalingCoordinate_mul K ⟨1⟩ ⟨0⟩ (by decide),
    scalingCoordinate_mul K ⟨0⟩ ⟨1⟩ (by decide)⟩

/-- `𝔾_m ⊆ ℙ¹ → Spec K[x^{±1}]`, `x ↦ u`. -/
def mOv : Ov K ⟶ Spec (CommRingCat.of (TorusRing K 1)) :=
  letI := ovAlg (K := K)
  (Ov K).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (torusLift (K := K) (fun _ => uOv (K := K))).toRingHom)

theorem ovPt_mOv (s : Kˣ) :
    ovPt K s ≫ mOv = Spec.map (CommRingCat.ofHom (torusLift (K := K) (R := K) (fun _ => s)).toRingHom) := by
  letI := ovAlg (K := K)
  rw [mOv, Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext1
  apply IsLocalization.ringHom_ext (Submonoid.powers (∏ i : Fin 1, MvPolynomial.X i :
    MvPolynomial (Fin 1) K))
  apply MvPolynomial.ringHom_ext
  · intro a
    have h1 : (ovPt K s).appTop ((overlapToBase K).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) =
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv a := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ovPt_over]; rfl
    simp only [RingHom.comp_apply, CommRingCat.hom_comp, CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [show (algebraMap (MvPolynomial (Fin 1) K) (TorusRing K 1)) (MvPolynomial.C a) =
      algebraMap K (TorusRing K 1) a from rfl, AlgHom.commutes, AlgHom.commutes]
    change (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((ovPt K s).appTop
      ((overlapToBase K).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))) = a
    rw [h1, ← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl
  · intro i
    have hi : (algebraMap (MvPolynomial (Fin 1) K) (TorusRing K 1)) (MvPolynomial.X i) =
        ((tUniv 1 i : (TorusRing K 1)ˣ) : TorusRing K 1) := by simp [tUniv]
    simp only [RingHom.comp_apply, CommRingCat.hom_comp, CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [hi, torusLift_tUniv, torusLift_tUniv]
    change (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((ovPt K s).appTop (scalingCoordinate K ⟨1⟩)) = s
    rw [ovPt_coordinate, secK, ← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl

theorem mOv_over : mOv (K := K) ≫ (algPt K (TorusRing K 1)).hom = overlapToBase K := by
  letI := ovAlg (K := K)
  change ((Ov K).toSpecΓ ≫ Spec.map _) ≫ Spec.map (CommRingCat.ofHom (algebraMap K (TorusRing K 1))) = _
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [show ((torusLift (K := K) (fun _ => uOv (K := K))).toRingHom.comp (algebraMap K (TorusRing K 1))) =
    algebraMap K Γ(Ov K, ⊤) from (torusLift (K := K) (fun _ => uOv (K := K))).comp_algebraMap]
  change (Ov K).toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (overlapToBase K).appTop) = _
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- **Rigidity for `𝔾_m`, torus form**: a morphism `Spec K[x^{±1}] → B` to an abelian variety over a field `K`
takes the same value at all `K`-points `x ↦ s`. -/
theorem torus1_const (B : PkgI3.AbVar K) (g : algPt K (TorusRing K 1) ⟶ B.X) (s : Kˣ) :
    algPtMap (torusLift (K := K) (R := K) (fun _ => s)) ≫ g =
      algPtMap (torusLift (K := K) (R := K) (fun _ => (1 : Kˣ))) ≫ g := by
  have hh : (mOv (K := K) ≫ g.left) ≫ B.X.hom = overlapToBase K := by
    rw [Category.assoc, Over.w g, mOv_over]
  have := overlap_const B (mOv ≫ g.left) hh s 1
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  rw [← Category.assoc, ovPt_mOv, ← Category.assoc, ovPt_mOv] at this
  exact this

end Rig


section TorusR

set_option maxHeartbeats 300000

variable {K : Type} [Field K]

theorem algPtMap_comp {R S T : Type} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S] [CommRing T]
    [Algebra K T] (f : R →ₐ[K] S) (g : S →ₐ[K] T) :
    algPtMap (k := K) g ≫ algPtMap f = algPtMap (g.comp f) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- One coordinate of a torus point can be moved to `1`. -/
theorem torus_update_const (B : PkgI3.AbVar K) {r : ℕ} (g : algPt K (TorusRing K r) ⟶ B.X)
    (c : Fin r → Kˣ) (j : Fin r) (s : Kˣ) :
    algPtMap (torusLift (K := K) (R := K) (Function.update c j s)) ≫ g =
      algPtMap (torusLift (K := K) (R := K) (Function.update c j 1)) ≫ g := by
  let φ : TorusRing K r →ₐ[K] TorusRing K 1 := torusLift (K := K)
    (fun i => if i = j then tUniv 1 0 else Units.map (algebraMap K (TorusRing K 1) : K →* TorusRing K 1) (c i))
  have key : ∀ s' : Kˣ, (torusLift (K := K) (R := K) (fun _ => s')).comp φ =
      torusLift (K := K) (R := K) (Function.update c j s') := by
    intro s'
    apply algHom_ext_torus
    intro i
    rw [AlgHom.comp_apply, torusLift_tUniv, torusLift_tUniv]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, torusLift_tUniv, Function.update_self]
    · rw [if_neg hij, Function.update_of_ne hij]
      change (torusLift (K := K) (R := K) (fun _ => s')) (algebraMap K (TorusRing K 1) (c i : K)) = (c i : K)
      rw [AlgHom.commutes]; rfl
  have h := torus1_const B (algPtMap φ ≫ g) s
  rw [← Category.assoc, ← Category.assoc, algPtMap_comp, algPtMap_comp, key, key] at h
  exact h

/-- **Rigidity for `𝔾_m^r`**: a morphism `Spec K[x₁^{±1}, …, x_r^{±1}] → B` to an abelian variety takes the same
value at all `K`-points. -/
theorem torusR_const (B : PkgI3.AbVar K) {r : ℕ} (g : algPt K (TorusRing K r) ⟶ B.X) (t : Fin r → Kˣ) :
    algPtMap (torusLift (K := K) (R := K) t) ≫ g =
      algPtMap (torusLift (K := K) (R := K) (fun _ => (1 : Kˣ))) ≫ g := by
  classical
  have hs : ∀ s : Finset (Fin r), algPtMap (torusLift (K := K) (R := K)
      (fun i => if i ∈ s then t i else 1)) ≫ g =
      algPtMap (torusLift (K := K) (R := K) (fun _ => (1 : Kˣ))) ≫ g := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      have e1 : (fun i => if i ∈ insert j s then t i else 1) =
          Function.update (fun i => if i ∈ s then t i else 1) j (t j) := by
        funext i
        by_cases hij : i = j
        · subst hij; simp
        · simp [hij, Function.update_of_ne hij]
      have e2 : (fun i => if i ∈ s then t i else (1 : Kˣ)) =
          Function.update (fun i => if i ∈ s then t i else 1) j 1 := by
        funext i
        by_cases hij : i = j
        · subst hij; simp [hj]
        · simp [Function.update_of_ne hij]
      rw [e1, torus_update_const, ← e2, ih]
  have := hs Finset.univ
  simpa using this

end TorusR

section KbarKI

set_option synthInstance.maxHeartbeats 400000

variable {k : Type} [Field k] {U : Over (Spec (CommRingCat.of k))} [GrpObj U]
  {B' : PkgI3.AbVar (AlgebraicClosure k)}

/-- The base change of an abelian variety along a field extension `ρ : K → L`. -/
def abVarBC {K L : Type} [Field K] [Field L] (ρ : K →+* L) (B : PkgI3.AbVar K) : PkgI3.AbVar L :=
  letI := B.grp
  haveI := B.proper
  haveI := B.smooth
  haveI := B.geomInt
  { X := (Over.pullback (sφ ρ)).obj B.X
    grp := Functor.grpObjObj
    proper := by change IsProper (pullback.snd B.X.hom (sφ ρ)); infer_instance
    smooth := by change Smooth (pullback.snd B.X.hom (sφ ρ)); infer_instance
    geomInt := by change GeometricallyIntegral (pullback.snd B.X.hom (sφ ρ)); infer_instance }

/-- **Rigidity, raw form**: for a field `L` with `ρ : k̄ → L` and a `U`-point `W` of the torus
`Spec L[x^{±1}]` (structure through `ρ`), `π'(W, ρ)` takes the same value at all `L`-points of the torus. -/
theorem rig_raw (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X) (L : Type) [Field L]
    (ρ : AlgebraicClosure k →+* L) (r : ℕ) (W : Spec (CommRingCat.of (TorusRing L r)) ⟶ U.left)
    (hW : W ≫ U.hom = Spec.map (CommRingCat.ofHom ((algebraMap L (TorusRing L r)).comp ρ)) ≫ sφ (φbar k))
    (t : Fin r → Lˣ) :
    Spec.map (CommRingCat.ofHom (torusLift (K := L) (R := L) t).toRingHom) ≫
        (pullback.lift W _ hW ≫ π'.left) =
      Spec.map (CommRingCat.ofHom (torusLift (K := L) (R := L) (fun _ => (1 : Lˣ))).toRingHom) ≫
        (pullback.lift W _ hW ≫ π'.left) := by
  letI := B'.grp
  letI Ib0 : Algebra (AlgebraicClosure k) (TorusRing L r) := algK ρ (TorusRing L r)
  letI : GrpObj ((Over.pullback (sφ ρ)).obj B'.X) := Functor.grpObjObj
  let g : algPt (AlgebraicClosure k) (TorusRing L r) ⟶ B'.X :=
    Over.homMk (pullback.lift W _ hW ≫ π'.left) (by
      change (pullback.lift W _ hW ≫ π'.left) ≫ B'.X.hom = _
      rw [Category.assoc, Over.w π']
      exact pullback.lift_snd _ _ _)
  let g' := (Φ ρ B'.X (TorusRing L r)).symm g
  have hc := torusR_const (abVarBC ρ B') g' t
  have h2 := congrArg (Φ ρ B'.X L) hc
  rw [Φ_natural, Φ_natural, MulEquiv.apply_symm_apply] at h2
  exact congrArg (fun z => Over.Hom.left z) h2


/-- The unit of `U_{k̄}` at a `k̄`-algebra `L`, on `U`. -/
theorem one_left_fst (L : Type) [CommRing L] [Algebra (AlgebraicClosure k) L] :
    letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
    (1 : algPt (AlgebraicClosure k) L ⟶ (Over.pullback (sφ (φbar k))).obj U).left ≫
        pullback.fst U.hom (sφ (φbar k)) =
      (algPt (AlgebraicClosure k) L).hom ≫ sφ (φbar k) ≫ (η[U] : 𝟙_ _ ⟶ U).left := by
  letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
  rw [Hom.one_def, Over.comp_left, Category.assoc, CToPrinted.unit_bc_fst]
  rfl

/-- `η` of `U_{k̄}` composed with a point `ρ`, as a lift. -/
theorem lift_unit (L : Type) [CommRing L] (ρ : CommRingCat.of (AlgebraicClosure k) ⟶ CommRingCat.of L)
    (x : Spec (CommRingCat.of L) ⟶ U.left) (hx : x = Spec.map ρ ≫ sφ (φbar k) ≫ (η[U] : 𝟙_ _ ⟶ U).left)
    (h : x ≫ U.hom = Spec.map ρ ≫ sφ (φbar k)) :
    letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
    pullback.lift x (Spec.map ρ) h =
      Spec.map ρ ≫ (η[(Over.pullback (sφ (φbar k))).obj U] : 𝟙_ _ ⟶ _).left := by
  letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, CToPrinted.unit_bc_fst, hx]
  · rw [pullback.lift_snd, Category.assoc]
    have := Over.w (η[(Over.pullback (sφ (φbar k))).obj U] : 𝟙_ _ ⟶ _)
    change _ ≫ pullback.snd U.hom (sφ (φbar k)) = 𝟙 _ at this
    rw [this, Category.comp_id]

/-- **Torus kernels are transport-stable**: a point of the torus `ker π'` for the `k̄`-structure `ra` on `L` maps to
the unit under `π'` for any other `k̄`-structure `rb` with the same restriction to `k` (rigidity). -/
theorem torus_kernel_transfer (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X)
    (hπ : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      IsMonHom π') (r : ℕ)
    (e : letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U))
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)
    (L : Type) [Field L] (ra rb : AlgebraicClosure k →+* L) (hab : ra.comp (φbar k) = rb.comp (φbar k))
    (t : Fin r → Lˣ) :
    letI := ra.toAlgebra
    ∀ (hcond : ((e L t).left ≫ pullback.fst U.hom (sφ (φbar k))) ≫ U.hom =
        Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k)),
    pullback.lift ((e L t).left ≫ pullback.fst U.hom (sφ (φbar k))) _ hcond ≫ π'.left =
      Spec.map (CommRingCat.ofHom rb) ≫ (η[B'.X] : 𝟙_ _ ⟶ B'.X).left := by
  letI Ia := ra.toAlgebra
  intro hcond
  letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
  letI := B'.grp
  haveI := hπ
  letI Ia0 : Algebra (AlgebraicClosure k) (TorusRing L r) := algK ra (TorusRing L r)
  let fl : (Fin r → Lˣ) → (TorusRing L r →ₐ[AlgebraicClosure k] L) := fun t' =>
    { (torusLift (K := L) (R := L) t').toRingHom with
      commutes' := fun x => (torusLift (K := L) (R := L) t').commutes (ra x) }
  have hnat : ∀ t' : Fin r → Lˣ, e L t' = algPtMap (fl t') ≫ e (TorusRing L r) (tUniv r) := by
    intro t'
    have := he_nat (TorusRing L r) L (fl t') (tUniv r)
    have hmap : (fun i => Units.map ((fl t' : TorusRing L r →ₐ[AlgebraicClosure k] L) :
        TorusRing L r →* L) (tUniv r i)) = t' := by
      funext i; ext; exact torusLift_tUniv t' i
    rwa [hmap] at this
  let W := (e (TorusRing L r) (tUniv r)).left ≫ pullback.fst U.hom (sφ (φbar k))
  have hW : W ≫ U.hom =
      Spec.map (CommRingCat.ofHom ((algebraMap L (TorusRing L r)).comp rb)) ≫ sφ (φbar k) := by
    simp only [W, Category.assoc]
    have hw : (e (TorusRing L r) (tUniv r)).left ≫ pullback.snd U.hom (sφ (φbar k)) =
        (algPt (AlgebraicClosure k) (TorusRing L r)).hom := Over.w (e (TorusRing L r) (tUniv r))
    rw [pullback.condition, ← Category.assoc, hw]
    change Spec.map (CommRingCat.ofHom ((algebraMap L (TorusRing L r)).comp ra)) ≫ sφ (φbar k) = _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      RingHom.comp_assoc, RingHom.comp_assoc, hab]
  have hlift : ∀ (t' : Fin r → Lˣ) (h' : ((e L t').left ≫ pullback.fst U.hom (sφ (φbar k))) ≫ U.hom =
      Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k)),
      pullback.lift ((e L t').left ≫ pullback.fst U.hom (sφ (φbar k))) _ h' =
        Spec.map (CommRingCat.ofHom (torusLift (K := L) (R := L) t').toRingHom) ≫ pullback.lift W _ hW := by
    intro t' h'
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, hnat t']
      rfl
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      congr 2
      ext x
      exact ((torusLift (K := L) (R := L) t').commutes (rb x)).symm
  have h1 : e L (fun _ => (1 : Lˣ)) = 1 := map_one (e L)
  have hc1 : ((e L (fun _ => (1 : Lˣ))).left ≫ pullback.fst U.hom (sφ (φbar k))) ≫ U.hom =
      Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k) := by
    have hw : (e L (fun _ => (1 : Lˣ))).left ≫ pullback.snd U.hom (sφ (φbar k)) =
        Spec.map (CommRingCat.ofHom ra) := Over.w (e L _)
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hab]
  rw [hlift t hcond, Category.assoc, rig_raw π' L rb r W hW t, ← Category.assoc, ← hlift _ hc1]
  have hx : (e L (fun _ => (1 : Lˣ))).left ≫ pullback.fst U.hom (sφ (φbar k)) =
      Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k) ≫ (η[U] : 𝟙_ _ ⟶ U).left := by
    rw [h1, one_left_fst, ← Category.assoc, ← Category.assoc]
    congr 1
    change Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k) = _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hab]
  rw [lift_unit L (CommRingCat.ofHom rb) _ hx hc1, Category.assoc, ← Over.comp_left, IsMonHom.one_hom]

end KbarKI

end ZInQ.ChevFree

#print axioms ZInQ.ChevFree.rig_raw
#print axioms ZInQ.ChevFree.torus_kernel_transfer
