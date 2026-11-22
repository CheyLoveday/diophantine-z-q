import ZInQKernel.Contrib.AbVarBC.Main
import ZInQKernel.OneProof.H.TailZ24
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! The two-torsion chart on the fixed locus of Picard pullback by inversion. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace ZInQ.PazukiFixedQuasiFinite

variable {k : Type} [Field k] [CharZero k]

/-- A fixed chart cut out by the doubling equation on a dual abelian variety
is quasi-finite at every point of the chart. The equation is tested on all
schemes, so the argument also handles nonreduced subschemes. -/
private theorem quasiFiniteAt_of_doubling_chart {P : Over (Spec (.of k))}
    (D : P ⟶ P) (B : PkgI3.AbVar k) (u : B.X ⟶ P) (hu : IsOpenImmersion u.left)
    (h : ∀ {T : Scheme} (b : T ⟶ B.X.left),
      b ≫ u.left ≫ D.left = b ≫ u.left ↔
        b ≫ (((2 : ℤ) : PkgI3.AbVar.End B).hom).left = (b ≫ B.X.hom) ≫ η[B.X].left)
    (x : ↑(equalizer D.left (𝟙 P.left)))
    (hx : equalizer.ι D.left (𝟙 P.left) x ∈ Set.range u.left) :
    (equalizer.ι D.left (𝟙 P.left) ≫ P.hom).QuasiFiniteAt x := by
  let d := (((2 : ℤ) : PkgI3.AbVar.End B).hom).left
  let zero := η[B.X].left
  let m : pullback d zero ⟶ B.X.left := pullback.fst d zero
  let n : pullback d zero ⟶ Spec (.of k) := pullback.snd d zero
  let v := equalizer.ι D.left (𝟙 P.left)
  have hd : d ≫ B.X.hom = B.X.hom := Over.w _
  have hz : zero ≫ B.X.hom = 𝟙 (Spec (.of k)) := Over.w (η[B.X])
  have hm : m ≫ d = n ≫ zero := pullback.condition
  have hbase : m ≫ B.X.hom = n := by
    simpa only [Category.assoc, hd, hz, Category.comp_id] using
      congrArg (fun f => f ≫ B.X.hom) hm
  have hfix : (m ≫ u.left) ≫ D.left = (m ≫ u.left) ≫ 𝟙 _ := by
    rw [Category.comp_id, Category.assoc]
    apply (h m).2
    rw [hbase]
    exact hm
  let q := equalizer.lift (m ≫ u.left) hfix
  have hq : q ≫ v = m ≫ u.left := equalizer.lift_ι _ _
  have hv : v ≫ D.left = v := by
    simpa only [Category.comp_id] using equalizer.condition D.left (𝟙 _)
  have hpb : IsPullback q m v u.left := by
    apply IsPullback.mk' hq
    · intro T a b _ hm'
      apply pullback.hom_ext
      · exact hm'
      · change a ≫ n = b ≫ n
        simpa only [Category.assoc, hbase] using congrArg (· ≫ B.X.hom) hm'
    · intro T a b hab
      have hbf : b ≫ u.left ≫ D.left = b ≫ u.left := by
        rw [← Category.assoc, ← hab, Category.assoc, hv]
      let l := pullback.lift b (b ≫ B.X.hom) ((h b).1 hbf)
      have hl : l ≫ m = b := pullback.lift_fst _ _ _
      refine ⟨l, ?_, hl⟩
      apply (cancel_mono v).1
      rw [Category.assoc, hq, ← Category.assoc, hl, hab]
  haveI : IsOpenImmersion q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) hpb.flip hu
  haveI : IsFinite d := (ZInQ.Contrib.AbVarBC.mulIsogeny k B 2 (by decide)).1
  haveI : IsFinite n := inferInstanceAs (IsFinite (pullback.snd d zero))
  have hqbase : q ≫ (v ≫ P.hom) = n := by
    rw [← Category.assoc, hq, Category.assoc, Over.w u, hbase]
  haveI : LocallyQuasiFinite (q ≫ (v ≫ P.hom)) := by
    rw [hqbase]
    infer_instance
  obtain ⟨b, hb⟩ := hx
  obtain ⟨z, hz', _⟩ := Scheme.exists_preimage_of_isPullback hpb x b hb.symm
  exact hz' ▸ Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion.mp
    ((q ≫ (v ≫ P.hom)).quasiFiniteAt z)

private def translate {P : Over (Spec (.of k))} [GrpObj P]
    (s : 𝟙_ (Over (Spec (.of k))) ⟶ P) : P ⟶ P :=
  (𝟙 P) * (toUnit P ≫ s)

private lemma comp_translate {P T : Over (Spec (.of k))} [GrpObj P]
    (f : T ⟶ P) (s : 𝟙_ (Over (Spec (.of k))) ⟶ P) :
    f ≫ translate s = f * (toUnit T ≫ s) := by
  rw [translate, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    toUnit_unique (f ≫ toUnit P) (toUnit T)]

private instance {P : Over (Spec (.of k))} [GrpObj P]
    (s : 𝟙_ (Over (Spec (.of k))) ⟶ P) : IsIso (translate s) := by
  refine ⟨⟨translate (s⁻¹), ?_, ?_⟩⟩
  · rw [comp_translate, translate, GrpObj.comp_inv, mul_assoc, mul_inv_cancel, mul_one]
  · rw [comp_translate, translate, GrpObj.comp_inv, mul_assoc, inv_mul_cancel, mul_one]

/-- At a fixed rational section of the represented Picard functor, the actual
equalizer of pullback by inversion is quasi-finite over the field, provided
the action is multiplicative and restricts to inversion on the named Pic⁰.
The argument uses the scheme-theoretic kernel of [2] on that abelian variety.
It can be applied after changing the ground field to the complex numbers. -/
theorem picard_fixed_quasiFiniteAt_section
    (A : PkgI3.AbVar k) {P : Over (Spec (.of k))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P)
    (B : PkgI3.AbVar k) (j : B.X ⟶ P) (hj : T09Pic.IsPicZero rep B j)
    (hmon : letI := picardFunctorCommGrpObj A.X.hom rep
            IsMonHom (T09Pic.dualP rep (GrpObj.inv (X := A.X))))
    (hres : j ≫ T09Pic.dualP rep (GrpObj.inv (X := A.X)) =
      GrpObj.inv (X := B.X) ≫ j)
    (s : 𝟙_ (Over (Spec (.of k))) ⟶ P)
    (hs : s ≫ T09Pic.dualP rep (GrpObj.inv (X := A.X)) = s) :
    let D := T09Pic.dualP rep (GrpObj.inv (X := A.X))
    ∀ x : ↑(equalizer D.left (𝟙 P.left)),
      equalizer.ι D.left (𝟙 P.left) x = s.left (IsLocalRing.closedPoint k) →
      (equalizer.ι D.left (𝟙 P.left) ≫ P.hom).QuasiFiniteAt x := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  let D := T09Pic.dualP rep (GrpObj.inv (X := A.X))
  letI : IsMonHom D := hmon
  letI : IsOpenImmersion j.left := hj.1
  letI : IsMonHom j := hj.2.2
  letI : Mono j := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  let u := j ≫ translate s
  haveI : IsIso (translate s).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (translate s)))
  have hu : IsOpenImmersion u.left := by
    change IsOpenImmersion (j.left ≫ (translate s).left)
    infer_instance
  have hucomp {T : Over (Spec (.of k))} (f : T ⟶ B.X) :
      f ≫ u = (f ≫ j) * (toUnit T ≫ s) := by
    change f ≫ (j ≫ translate s) = _
    rw [← Category.assoc, comp_translate]
  have criterion {T : Over (Spec (.of k))} (f : T ⟶ B.X) :
      (f ≫ u) ≫ D = f ≫ u ↔ f ≫ ((2 : ℤ) : PkgI3.AbVar.End B).hom = 1 := by
    have hr : (f ≫ j) ≫ D = f⁻¹ ≫ j := by
      rw [Category.assoc, show j ≫ D = _ from hres, ← Category.assoc, ← Hom.inv_def]
    have ht : (toUnit T ≫ s) ≫ D = toUnit T ≫ s := by
      rw [Category.assoc, show s ≫ D = s from hs]
    rw [hucomp, MonObj.mul_comp, hr, ht, mul_left_inj, cancel_mono j,
      ZInQ.Contrib.AbVarBC.Tangent.comp_intCast_hom B f 2]
    simp [inv_eq_iff_mul_eq_one, pow_two]
  have criterionLeft {T : Scheme} (b : T ⟶ B.X.left) :
      b ≫ u.left ≫ D.left = b ≫ u.left ↔
      b ≫ (((2 : ℤ) : PkgI3.AbVar.End B).hom).left = (b ≫ B.X.hom) ≫ η[B.X].left := by
    let T' := Over.mk (b ≫ B.X.hom)
    let f : T' ⟶ B.X := Over.homMk b rfl
    constructor
    · intro hf
      have he : (f ≫ u) ≫ D = f ≫ u := by
        apply Over.OverMorphism.ext
        change (b ≫ u.left) ≫ D.left = b ≫ u.left
        rwa [Category.assoc]
      exact congrArg (fun (g : T' ⟶ B.X) => g.left) ((criterion f).1 he)
    · intro hf
      have he : f ≫ ((2 : ℤ) : PkgI3.AbVar.End B).hom = 1 := Over.OverMorphism.ext hf
      rw [← Category.assoc]
      exact congrArg (fun (g : T' ⟶ P) => g.left) ((criterion f).2 he)
  change ∀ x : ↑(equalizer D.left (𝟙 P.left)),
    equalizer.ι D.left (𝟙 P.left) x = s.left (IsLocalRing.closedPoint k) →
      (equalizer.ι D.left (𝟙 P.left) ≫ P.hom).QuasiFiniteAt x
  intro x hx
  apply quasiFiniteAt_of_doubling_chart D B u hu (@criterionLeft) x
  have ht : toUnit (𝟙_ (Over (Spec (.of k)))) = 𝟙 _ := toUnit_unique _ _
  have hη : η[P] = (1 : 𝟙_ (Over (Spec (.of k))) ⟶ P) := by
    rw [Hom.one_def, ht, Category.id_comp]
  have hu0 : η[B.X] ≫ u = s := by
    rw [hucomp, IsMonHom.one_hom j, hη, one_mul, ht, Category.id_comp]
  refine ⟨η[B.X].left (IsLocalRing.closedPoint k), ?_⟩
  rw [hx]
  change (η[B.X] ≫ u).left (IsLocalRing.closedPoint k) = _
  exact congrArg (fun (g : 𝟙_ (Over (Spec (.of k))) ⟶ P) =>
    g.left (IsLocalRing.closedPoint k)) hu0

end ZInQ.PazukiFixedQuasiFinite
