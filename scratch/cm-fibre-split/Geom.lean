import ZInQKernel.Contrib.OneProof.CMFibreSplit
import ZInQKernel.Contrib.OneProof.CartierSmooth
import ZInQKernel.Contrib.Dim.IntegralHom

/-! # cm-fibre-split: the curve `E` and the isogeny `E² → A` from multiples of matrix units
(manuscript L583-585); geometry only -/

set_option maxHeartbeats 1000000

noncomputable section

namespace HDec
namespace CMBranch
namespace FibreSplit

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- `f` are matrix units scaled by `n`. -/
def IsScaledMatrixUnits {R : Type*} [Ring R] (n : ℕ) (f : Fin 2 → Fin 2 → R) : Prop :=
  (∀ i j k l, f i j * f k l = if j = k then (n : R) * f i l else 0) ∧ f 0 0 + f 1 1 = (n : R)

section Hom

variable {K : Type} [Field K]

/-- Composition of homomorphisms (diagram order). -/
def cmp {X Y Z : PkgI3.AbVar K} (g : PkgI3.AbVar.Hom X Y) (f : PkgI3.AbVar.Hom Y Z) :
    PkgI3.AbVar.Hom X Z :=
  PkgI3.AbVar.Hom.mk' (g.hom ≫ f.hom)

@[simp] theorem cmp_hom {X Y Z : PkgI3.AbVar K} (g : PkgI3.AbVar.Hom X Y) (f : PkgI3.AbVar.Hom Y Z) :
    (cmp g f).hom = g.hom ≫ f.hom := rfl

theorem cmp_assoc {X Y Z W : PkgI3.AbVar K} (g : PkgI3.AbVar.Hom X Y) (f : PkgI3.AbVar.Hom Y Z)
    (e : PkgI3.AbVar.Hom Z W) : cmp (cmp g f) e = cmp g (cmp f e) :=
  PkgI3.AbVar.Hom.ext' (Category.assoc _ _ _)

/-- `g ↦ g ∘ f`, additive. -/
def cmpR {X Y Z : PkgI3.AbVar K} (f : PkgI3.AbVar.Hom Y Z) :
    PkgI3.AbVar.Hom X Y →+ PkgI3.AbVar.Hom X Z where
  toFun g := cmp g f
  map_zero' := PkgI3.AbVar.Hom.ext' (by
    change (1 : X.X ⟶ Y.X) ≫ f.hom = 1
    exact MonObj.one_comp _)
  map_add' g g' := PkgI3.AbVar.Hom.ext' (by
    change (g.hom * g'.hom) ≫ f.hom = g.hom ≫ f.hom * g'.hom ≫ f.hom
    exact MonObj.mul_comp _ _ _)

/-- `f ↦ g ∘ f`, additive. -/
def cmpL {X Y Z : PkgI3.AbVar K} (g : PkgI3.AbVar.Hom X Y) :
    PkgI3.AbVar.Hom Y Z →+ PkgI3.AbVar.Hom X Z where
  toFun f := cmp g f
  map_zero' := PkgI3.AbVar.Hom.ext' (by
    change g.hom ≫ (1 : Y.X ⟶ Z.X) = 1
    exact MonObj.comp_one _)
  map_add' f f' := PkgI3.AbVar.Hom.ext' (by
    change g.hom ≫ (f.hom * f'.hom) = g.hom ≫ f.hom * g.hom ≫ f'.hom
    exact MonObj.comp_mul _ _ _)

theorem cmp_add_left {X Y Z : PkgI3.AbVar K} (g g' : PkgI3.AbVar.Hom X Y) (f : PkgI3.AbVar.Hom Y Z) :
    cmp (g + g') f = cmp g f + cmp g' f := (cmpR f).map_add g g'
theorem cmp_add_right {X Y Z : PkgI3.AbVar K} (g : PkgI3.AbVar.Hom X Y) (f f' : PkgI3.AbVar.Hom Y Z) :
    cmp g (f + f') = cmp g f + cmp g f' := (cmpL g).map_add f f'
theorem cmp_zsmul_left {X Y Z : PkgI3.AbVar K} (m : ℤ) (g : PkgI3.AbVar.Hom X Y)
    (f : PkgI3.AbVar.Hom Y Z) : cmp (m • g) f = m • cmp g f := (cmpR f).map_zsmul g m
theorem cmp_zsmul_right {X Y Z : PkgI3.AbVar K} (m : ℤ) (g : PkgI3.AbVar.Hom X Y)
    (f : PkgI3.AbVar.Hom Y Z) : cmp g (m • f) = m • cmp g f := (cmpL g).map_zsmul f m
@[simp] theorem cmp_zero_left {X Y Z : PkgI3.AbVar K} (f : PkgI3.AbVar.Hom Y Z) :
    cmp (0 : PkgI3.AbVar.Hom X Y) f = 0 := (cmpR f).map_zero
@[simp] theorem cmp_zero_right {X Y Z : PkgI3.AbVar K} (g : PkgI3.AbVar.Hom X Y) :
    cmp g (0 : PkgI3.AbVar.Hom Y Z) = 0 := (cmpL g).map_zero
@[simp] theorem cmp_one_left {X Y : PkgI3.AbVar K} (f : PkgI3.AbVar.Hom X Y) :
    cmp (1 : PkgI3.AbVar.End X) f = f := PkgI3.AbVar.Hom.ext' (Category.id_comp _)
@[simp] theorem cmp_one_right {X Y : PkgI3.AbVar K} (g : PkgI3.AbVar.Hom X Y) :
    cmp g (1 : PkgI3.AbVar.End Y) = g := PkgI3.AbVar.Hom.ext' (Category.comp_id _)

/-- In `End`, `f * g = g ≫ f`. -/
theorem mul_eq_cmp {X : PkgI3.AbVar K} (f g : PkgI3.AbVar.End X) : f * g = cmp g f := rfl

theorem intCast_eq_zsmul {X : PkgI3.AbVar K} (m : ℤ) : (m : PkgI3.AbVar.End X) = m • 1 := by
  rw [zsmul_eq_mul, mul_one]

theorem cmp_intCast_left {X Y : PkgI3.AbVar K} (m : ℤ) (f : PkgI3.AbVar.Hom X Y) :
    cmp (m : PkgI3.AbVar.End X) f = m • f := by
  rw [intCast_eq_zsmul, cmp_zsmul_left, cmp_one_left]

theorem cmp_intCast_right {X Y : PkgI3.AbVar K} (m : ℤ) (f : PkgI3.AbVar.Hom X Y) :
    cmp f (m : PkgI3.AbVar.End Y) = m • f := by
  rw [intCast_eq_zsmul, cmp_zsmul_right, cmp_one_right]

theorem cmp_nsmul_left {X Y Z : PkgI3.AbVar K} (m : ℕ) (g : PkgI3.AbVar.Hom X Y)
    (f : PkgI3.AbVar.Hom Y Z) : cmp (m • g) f = m • cmp g f := (cmpR f).map_nsmul g m
theorem cmp_nsmul_right {X Y Z : PkgI3.AbVar K} (m : ℕ) (g : PkgI3.AbVar.Hom X Y)
    (f : PkgI3.AbVar.Hom Y Z) : cmp g (m • f) = m • cmp g f := (cmpL g).map_nsmul f m

theorem natCast_eq_nsmul {X : PkgI3.AbVar K} (m : ℕ) : (m : PkgI3.AbVar.End X) = m • 1 := by
  rw [nsmul_eq_mul, mul_one]

theorem cmp_natCast_left {X Y : PkgI3.AbVar K} (m : ℕ) (f : PkgI3.AbVar.Hom X Y) :
    cmp (m : PkgI3.AbVar.End X) f = m • f := by
  rw [natCast_eq_nsmul, cmp_nsmul_left, cmp_one_left]

theorem cmp_natCast_right {X Y : PkgI3.AbVar K} (m : ℕ) (f : PkgI3.AbVar.Hom X Y) :
    cmp f (m : PkgI3.AbVar.End Y) = m • f := by
  rw [natCast_eq_nsmul, cmp_nsmul_right, cmp_one_right]

/-- A closed immersion is a monomorphism of homomorphisms. -/
theorem cancel_closedImm {X Y Z : PkgI3.AbVar K} (i : PkgI3.AbVar.Hom Y Z)
    (hi : IsClosedImmersion i.hom.left) {g g' : PkgI3.AbVar.Hom X Y} (h : cmp g i = cmp g' i) :
    g = g' := by
  apply PkgI3.AbVar.Hom.ext'
  apply Over.OverMorphism.ext
  have e := congrArg (fun k => k.hom.left) h
  simp only [cmp_hom, Over.comp_left] at e
  exact (cancel_mono i.hom.left).mp e

/-- A surjective homomorphism is an epimorphism (`Y` reduced, targets separated). -/
theorem cancel_surj {X Y Z : PkgI3.AbVar K} (h : PkgI3.AbVar.Hom X Y)
    (hs : Surjective h.hom.left) {g g' : PkgI3.AbVar.Hom Y Z} (e : cmp h g = cmp h g') : g = g' := by
  apply PkgI3.AbVar.Hom.ext'
  apply Over.OverMorphism.ext
  have e' := congrArg (fun k => k.hom.left) e
  simp only [cmp_hom, Over.comp_left] at e'
  exact ext_of_isDominant_of_isSeparated Z.X.hom ((Over.w g.hom).trans (Over.w g'.hom).symm)
    h.hom.left e'

end Hom

theorem withBot_eq_one_of_add_self (x : WithBot ℕ∞) (h : x + x = 2) : x = 1 := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe m =>
      have h' : ((m + m : ℕ) : WithBot ℕ∞) = ((2 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h
      have : m + m = 2 := by exact_mod_cast h'
      have hm : m = 1 := by omega
      subst hm; rfl

end FibreSplit
end CMBranch
end HDec
