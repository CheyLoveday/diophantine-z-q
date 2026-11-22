import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! A fixed subscheme commutes with base change, over the specified new base. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.PazukiFixedEqualizerBaseChange

universe u

variable {S T : Scheme.{u}} {P : Over S}

/-- The base-changed equalizer of an endomorphism with the identity is the
equalizer of the base-changed endomorphism with the identity, as a scheme
over the new base. Both arrows are constructed from the universal properties. -/
def fixedEqualizerBaseChangeIso (D : P ⟶ P) (g : T ⟶ S) :
    Over.mk (pullback.snd (equalizer.ι D.left (𝟙 P.left) ≫ P.hom) g) ≅
      Over.mk (equalizer.ι ((Over.pullback g).map D).left (𝟙 ((Over.pullback g).obj P).left) ≫
        ((Over.pullback g).obj P).hom) := by
  let e := equalizer.ι D.left (𝟙 P.left)
  let D' := ((Over.pullback g).map D).left
  let e' := equalizer.ι D' (𝟙 ((Over.pullback g).obj P).left)
  let px := pullback.fst P.hom g
  let pt := pullback.snd P.hom g
  let wx := pullback.fst (e ≫ P.hom) g
  let wt := pullback.snd (e ≫ P.hom) g
  have hp : px ≫ P.hom = pt ≫ g := pullback.condition
  have hpx : D' ≫ px = px ≫ D.left := by simp [D', px, Over.pullback_map_left]
  have hpt : D' ≫ pt = pt := by simp [D', pt, Over.pullback_map_left]
  have he : e ≫ D.left = e := by simpa only [Category.comp_id] using
    (equalizer.condition D.left (𝟙 P.left))
  have he' : e' ≫ D' = e' := by simpa only [Category.comp_id] using
    (equalizer.condition D' (𝟙 _))

  let a := pullback.lift (wx ≫ e) wt (show (wx ≫ e) ≫ P.hom = wt ≫ g by
    rw [Category.assoc]
    exact pullback.condition)
  have hax : a ≫ px = wx ≫ e := pullback.lift_fst _ _ _
  have hat : a ≫ pt = wt := pullback.lift_snd _ _ _
  have ha : a ≫ D' = a ≫ 𝟙 _ := by
    rw [Category.comp_id]
    apply pullback.hom_ext
    · change (a ≫ D') ≫ px = a ≫ px
      rw [Category.assoc, hpx, ← Category.assoc, hax, Category.assoc, he]
    · change (a ≫ D') ≫ pt = a ≫ pt
      rw [Category.assoc, hpt]
  let forward := equalizer.lift a ha
  have hforward : forward ≫ e' = a := equalizer.lift_ι _ _

  have hb : (e' ≫ px) ≫ D.left = (e' ≫ px) ≫ 𝟙 _ := by
    rw [Category.comp_id, Category.assoc, ← hpx, ← Category.assoc, he']
  let b := equalizer.lift (e' ≫ px) hb
  have hbx : b ≫ e = e' ≫ px := equalizer.lift_ι _ _
  let back := pullback.lift b (e' ≫ pt) (show b ≫ (e ≫ P.hom) = (e' ≫ pt) ≫ g by
    rw [← Category.assoc, hbx, Category.assoc, hp, Category.assoc])
  have hbackx : back ≫ wx = b := pullback.lift_fst _ _ _
  have hbackt : back ≫ wt = e' ≫ pt := pullback.lift_snd _ _ _

  have hfb : forward ≫ back = 𝟙 _ := by
    apply pullback.hom_ext
    · change (forward ≫ back) ≫ wx = 𝟙 _ ≫ wx
      rw [Category.assoc, hbackx, Category.id_comp]
      apply (cancel_mono e).1
      rw [Category.assoc, hbx, ← Category.assoc, hforward, hax]
    · change (forward ≫ back) ≫ wt = 𝟙 _ ≫ wt
      rw [Category.assoc, hbackt, ← Category.assoc, hforward, hat, Category.id_comp]
  have hbf : back ≫ forward = 𝟙 _ := by
    apply (cancel_mono e').1
    rw [Category.assoc, hforward, Category.id_comp]
    apply pullback.hom_ext
    · change (back ≫ a) ≫ px = e' ≫ px
      rw [Category.assoc, hax, ← Category.assoc, hbackx, hbx]
    · change (back ≫ a) ≫ pt = e' ≫ pt
      rw [Category.assoc, hat, hbackt]
  refine Over.isoMk (show _ ≅ _ from ⟨forward, back, hfb, hbf⟩) ?_
  change forward ≫ (e' ≫ pt) = wt
  rw [← Category.assoc, hforward, hat]

/-- Local quasi-finiteness of the fixed locus after transporting the action
is local quasi-finiteness of the pullback of the original fixed locus. -/
theorem locallyQuasiFinite_fixed_pullback (D : P ⟶ P) (g : T ⟶ S)
    (h : LocallyQuasiFinite
      (equalizer.ι ((Over.pullback g).map D).left (𝟙 ((Over.pullback g).obj P).left) ≫
        ((Over.pullback g).obj P).hom)) :
    LocallyQuasiFinite (pullback.snd (equalizer.ι D.left (𝟙 P.left) ≫ P.hom) g) := by
  letI : LocallyQuasiFinite
      (equalizer.ι ((Over.pullback g).map D).left (𝟙 _) ≫ ((Over.pullback g).obj P).hom) := h
  let e := fixedEqualizerBaseChangeIso D g
  haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget T).mapIso e).hom)
  have w := Over.w e.hom
  change e.hom.left ≫ (equalizer.ι ((Over.pullback g).map D).left (𝟙 _) ≫
    ((Over.pullback g).obj P).hom) = pullback.snd (equalizer.ι D.left (𝟙 _) ≫ P.hom) g at w
  rw [← w]
  infer_instance

end ZInQ.PazukiFixedEqualizerBaseChange
