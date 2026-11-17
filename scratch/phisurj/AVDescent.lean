import ZInQKernel.Contrib.OneProof.PhiSurjDescent
import ZInQKernel.Contrib.OneProof.WeilFormulaTheta
import ZInQKernel.Contrib.OneProof.MumfordSquareMulN

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

namespace PhiSurj.AVDesc

open PicDict PkgI3 PkgI3.AbVar PicDict.Transport WeilProof WeilProof.Theta

variable {k : Type} [Field k]

/-- `[n]` is étale, surjective and proper (from weil-proof's `divisibleAC` argument). -/
theorem mul_props [IsAlgClosed k] (X : AbVar k) (n : ℕ) (hnk : (n : k) ≠ 0) :
    Etale (AC.mul X n).left ∧ Surjective (AC.mul X n).left ∧ IsProper (AC.mul X n).left := by
  have : GeometricallyConnected X.X.hom := geomConn_of_geomInt X.X.hom
  have : PkgI2.IsAbelianScheme (ObjBridge.toGrp X) := ⟨X.proper, X.smooth, inferInstance⟩
  have hE : Etale ((𝟙 (ObjBridge.toGrp X).X ^ n : (ObjBridge.toGrp X).X ⟶ (ObjBridge.toGrp X).X).left) :=
    ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof k (ObjBridge.toGrp X) n
      (by exact (IsUnit.mk0 _ hnk))
  have hE' : Etale (AC.mul X n).left := hE
  set f := (AC.mul X n).left with hfdef
  have hopen : IsOpenMap f := isOpenMap_of_generalizingMap f (Flat.generalizingMap f)
  have hw : f ≫ X.X.hom = X.X.hom := Over.w (AC.mul X n)
  have : IsProper (f ≫ X.X.hom) := by rw [hw]; infer_instance
  have hP : IsProper f := IsProper.of_comp f X.X.hom
  have hclosed : IsClosedMap f := f.isClosedMap
  have : IsIntegral X.X.left := GeometricallyIntegral.isIntegral_of_subsingleton X.X.hom
  have hrange : Set.range f = Set.univ := by
    have hne : (Set.range f).Nonempty := by
      obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
      exact ⟨_, ⟨η[X.X].left p, rfl⟩⟩
    exact (IsClopen.eq_univ ⟨hclosed.isClosed_range, hopen.isOpen_range⟩ hne)
  refine ⟨hE', ⟨fun y => ?_⟩, hP⟩
  have : y ∈ Set.range f := by rw [hrange]; trivial
  exact this

/-- `[n]` generates an fpqc covering. -/
theorem mul_cover [IsAlgClosed k] (X : AbVar k) (n : ℕ) (hnk : (n : k) ≠ 0) :
    Sieve.ofArrows (fun _ : PUnit.{1} => X.X.left) (fun _ => (AC.mul X n).left) ∈
      Scheme.fpqcTopology X.X.left := by
  obtain ⟨hE, hS, hP⟩ := mul_props X n hnk
  change Sieve.generate (Presieve.ofArrows _ _) ∈ _
  rw [Presieve.ofArrows_pUnit]
  exact Precoverage.generate_mem_toGrothendieck (Scheme.Hom.singleton_mem_fpqcPrecoverage _)

lemma tr_left_comp_mul {X : AbVar k} {n : ℕ} (x : AC.Kpt X) (hx : x ^ n = 1) :
    (AC.tr x).left ≫ (AC.mul X n).left = (AC.mul X n).left := by
  rw [← Over.comp_left, AC.tr_comp_mul x hx]

/-- The sections `y ↦ (y, y + x)`, `x ∈ X[n]`, are open immersions. -/
theorem sec_isOpenImmersion [IsAlgClosed k] {X : AbVar k} {n : ℕ} [hF : Fact ((n : k) ≠ 0)] (x : AC.Kpt X) (hx : x ^ n = 1) :
    IsOpenImmersion (Desc.sec (AC.mul X n).left (tr_left_comp_mul x hx)) := by
  obtain ⟨hE, -, -⟩ := mul_props X n (Fact.out)
  exact ZInQ.Contrib.AbVarBC.MulRigidity.isOpenImmersion_of_section _
    (pullback.fst (AC.mul X n).left (AC.mul X n).left) (pullback.lift_fst _ _ _)

lemma kpt_comp_tr {X : AbVar k} (y x : AC.Kpt X) : y ≫ AC.tr x = y * x := by
  simp only [AC.tr, ← CategoryTheory.Hom.mul_def]
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    CartesianMonoidalCategory.toUnit_unique (y ≫ CartesianMonoidalCategory.toUnit X.X) (𝟙 _),
    Category.id_comp]

lemma kpt_comp_mul {X : AbVar k} (y : AC.Kpt X) (n : ℕ) : y ≫ AC.mul X n = y ^ n := by
  simp only [AC.mul]
  rw [MonObj.comp_pow, Category.comp_id]

/-- The sections `y ↦ (y, y + x)`, `x ∈ X[n](k)`, cover `X ×_{[n],X,[n]} X` (on points). -/
theorem sec_cover [IsAlgClosed k] (X : AbVar k) (n : ℕ) (hnk : (n : k) ≠ 0)
    (y : (pullback (AC.mul X n).left (AC.mul X n).left : Scheme)) :
    ∃ i : {x : AC.Kpt X // x ^ n = 1},
      y ∈ Set.range (Desc.sec (AC.mul X n).left (tr_left_comp_mul i.1 i.2)).base := by
  obtain ⟨hE, -, -⟩ := mul_props X n hnk
  let m := (AC.mul X n).left
  have hmw : m ≫ X.X.hom = X.X.hom := Over.w (AC.mul X n)
  let str : pullback m m ⟶ Spec (CommRingCat.of k) := pullback.fst m m ≫ X.X.hom
  have : LocallyOfFiniteType str := by dsimp [str]; infer_instance
  have : JacobsonSpace (pullback m m : Scheme) := LocallyOfFiniteType.jacobsonSpace str
  by_contra hy
  push_neg at hy
  let V : Set (pullback m m : Scheme) :=
    ⋃ i : {x : AC.Kpt X // x ^ n = 1}, Set.range (Desc.sec m (tr_left_comp_mul i.1 i.2)).base
  have hVo : IsOpen V := by
    refine isOpen_iUnion fun i => ?_
    have := sec_isOpenImmersion (n := n) (hF := ⟨hnk⟩) i.1 i.2
    exact (Desc.sec m (tr_left_comp_mul i.1 i.2)).isOpenEmbedding.isOpen_range
  have hZ : (Vᶜ).Nonempty := ⟨y, by simpa [V] using hy⟩
  obtain ⟨z, hzZ, hzc⟩ := nonempty_inter_closedPoints hZ hVo.isClosed_compl.isLocallyClosed
  let σ := pointOfClosedPoint str z hzc
  have hσ : σ ≫ str = 𝟙 _ := pointOfClosedPoint_comp str z hzc
  let x1 : AC.Kpt X := Over.homMk (σ ≫ pullback.fst m m) (by
    change (σ ≫ pullback.fst m m) ≫ X.X.hom = 𝟙 _
    rw [Category.assoc]; exact hσ)
  let x2 : AC.Kpt X := Over.homMk (σ ≫ pullback.snd m m) (by
    change (σ ≫ pullback.snd m m) ≫ X.X.hom = 𝟙 _
    rw [Category.assoc, ← hmw, ← Category.assoc (pullback.snd m m), ← pullback.condition, Category.assoc,
      hmw]
    exact hσ)
  have hx12 : x1 ≫ AC.mul X n = x2 ≫ AC.mul X n := by
    apply Over.OverMorphism.ext
    change (σ ≫ pullback.fst m m) ≫ m = (σ ≫ pullback.snd m m) ≫ m
    rw [Category.assoc, Category.assoc, pullback.condition]
  rw [kpt_comp_mul, kpt_comp_mul] at hx12
  let x := x1⁻¹ * x2
  have hx : x ^ n = 1 := by
    simp only [x, mul_pow, inv_pow, hx12, inv_mul_cancel]
  apply hzZ
  refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
  have hsec : x1.left ≫ Desc.sec m (tr_left_comp_mul x hx) = σ := by
    apply pullback.hom_ext
    · simp [x1]
    · have h2 : (x1 ≫ AC.tr x).left = x2.left := by
        rw [kpt_comp_tr]
        congr 1
        simp only [x, mul_inv_cancel_left]
      simp only [Category.assoc, pullback.lift_snd]
      exact h2
  refine ⟨x1.left (IsLocalRing.closedPoint k), ?_⟩
  have e := congrArg (fun f : Spec (CommRingCat.of k) ⟶ (pullback m m : Scheme) =>
    f.base (IsLocalRing.closedPoint k)) hsec
  simp only [Scheme.Hom.comp_base] at e
  have hσz : σ.base (IsLocalRing.closedPoint k) = z := pointOfClosedPoint_apply str z hzc _
  rw [hσz] at e
  exact e

end PhiSurj.AVDesc
