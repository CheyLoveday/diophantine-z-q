import Research.DerivativeSwitch.OrthogonalComparison
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Prod

/-!
# Explicit mapping fibres in Mathlib's category of cochain complexes

`fibre phi` uses native index `n` for the usual fibre degree `n+1`.
Its terms are `A^(n+1) × B^n` and its differential is
`(a,l) ↦ (da, phi(a)-dl)`. For `phi(g,u)=-loc(g)+inc(u)` this is the
boundary-cup Selmer-cone convention. The square-zero law and projections are
proved here, rather than posited as equations on arbitrary linear maps.
`raise` is a plain reindexing with unchanged differentials, not the signed
categorical shift functor. All applications state the index translation.

These are native complexes and chain maps. They are not yet the manuscript's
continuous arithmetic cochains or its retained inner models.
-/

namespace Research.DerivativeSwitch.NativeSelmerCone

open CategoryTheory

universe u
variable {R : Type u} [CommRing R]

abbrev Complex := CochainComplex (ModuleCat.{u} R) ℤ

noncomputable section

def pairStep (A B : Complex (R := R)) (n : ℤ) :
    ModuleCat.of R (A.X n × B.X n) ⟶ ModuleCat.of R (A.X (n + 1) × B.X (n + 1)) :=
  ModuleCat.ofHom ((A.d n (n + 1)).hom.prodMap (B.d n (n + 1)).hom)

lemma pairStep_sq (A B : Complex (R := R)) (n : ℤ) :
    pairStep A B n ≫ pairStep A B (n + 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · exact congrArg (fun f : A.X n ⟶ A.X (n + 1 + 1) => f x.1)
      (A.d_comp_d n (n + 1) (n + 1 + 1))
  · exact congrArg (fun f : B.X n ⟶ B.X (n + 1 + 1) => f x.2)
      (B.d_comp_d n (n + 1) (n + 1 + 1))

abbrev pair (A B : Complex (R := R)) : Complex (R := R) :=
  CochainComplex.of (fun n => ModuleCat.of R (A.X n × B.X n))
    (pairStep A B) (pairStep_sq A B)

@[simp] lemma pair_d (A B : Complex (R := R)) (n : ℤ) (x : (pair A B).X n) :
    (pair A B).d n (n + 1) x = (A.d n (n + 1) x.1, B.d n (n + 1) x.2) := by
  change (CochainComplex.of.d (fun n : ℤ => ModuleCat.of R (A.X n × B.X n))
    (pairStep A B) n (n + 1)).hom x = _
  rw [CochainComplex.of_d]
  rfl

def pairFst (A B : Complex (R := R)) : pair A B ⟶ A :=
  CochainComplex.ofHom (fun _ => ModuleCat.ofHom (LinearMap.fst R _ _)) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change A.d n (n + 1) x.1 = ((pair A B).d n (n + 1) x).1
    rw [pair_d])

def pairSnd (A B : Complex (R := R)) : pair A B ⟶ B :=
  CochainComplex.ofHom (fun _ => ModuleCat.ofHom (LinearMap.snd R _ _)) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change B.d n (n + 1) x.2 = ((pair A B).d n (n + 1) x).2
    rw [pair_d])

abbrev raise (A : Complex (R := R)) : Complex (R := R) :=
  CochainComplex.of (fun n => A.X (n + 1)) (fun n => A.d (n + 1) (n + 1 + 1))
    (fun n => A.d_comp_d (n + 1) (n + 1 + 1) (n + 1 + 1 + 1))

@[simp] lemma raise_d (A : Complex (R := R)) (n : ℤ) :
    (raise A).d n (n + 1) = A.d (n + 1) (n + 1 + 1) := by
  exact CochainComplex.of_d (fun n : ℤ => A.X (n + 1))
    (fun n => A.d (n + 1) (n + 1 + 1)) n

def raiseMap {A B : Complex (R := R)} (f : A ⟶ B) : raise A ⟶ raise B :=
  CochainComplex.ofHom (fun n => f.f (n + 1)) (by
    intro n
    rw [raise_d, raise_d]
    exact f.comm (n + 1) (n + 1 + 1))

def fibreStep {A B : Complex (R := R)} (phi : A ⟶ B) (n : ℤ) :
    ModuleCat.of R (A.X (n + 1) × B.X n) ⟶
      ModuleCat.of R (A.X (n + 1 + 1) × B.X (n + 1)) :=
  ModuleCat.ofHom (((A.d (n + 1) (n + 1 + 1)).hom.comp
      (LinearMap.fst R (A.X (n + 1)) (B.X n))).prod
      ((phi.f (n + 1)).hom.comp (LinearMap.fst R (A.X (n + 1)) (B.X n)) -
        (B.d n (n + 1)).hom.comp (LinearMap.snd R (A.X (n + 1)) (B.X n))))

lemma fibreStep_sq {A B : Complex (R := R)} (phi : A ⟶ B) (n : ℤ) :
    fibreStep phi n ≫ fibreStep phi (n + 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · exact congrArg (fun f : A.X (n + 1) ⟶ A.X (n + 1 + 1 + 1) => f x.1)
      (A.d_comp_d (n + 1) (n + 1 + 1) (n + 1 + 1 + 1))
  · have hc := congrArg (fun f : A.X (n + 1) ⟶ B.X (n + 1 + 1) => f x.1)
      (phi.comm (n + 1) (n + 1 + 1))
    have hd := congrArg (fun f : B.X n ⟶ B.X (n + 1 + 1) => f x.2)
      (B.d_comp_d n (n + 1) (n + 1 + 1))
    change phi.f (n + 1 + 1) (A.d (n + 1) (n + 1 + 1) x.1) -
      B.d (n + 1) (n + 1 + 1) (phi.f (n + 1) x.1 - B.d n (n + 1) x.2) = 0
    simp only [ModuleCat.comp_apply] at hc
    change B.d (n + 1) (n + 1 + 1) (B.d n (n + 1) x.2) = 0 at hd
    rw [map_sub, hc, hd, sub_zero, sub_self]

abbrev fibre {A B : Complex (R := R)} (phi : A ⟶ B) : Complex (R := R) :=
  CochainComplex.of (fun n => ModuleCat.of R (A.X (n + 1) × B.X n))
    (fibreStep phi) (fibreStep_sq phi)

@[simp] lemma fibre_d {A B : Complex (R := R)} (phi : A ⟶ B) (n : ℤ)
    (x : (fibre phi).X n) :
    (fibre phi).d n (n + 1) x =
      (A.d (n + 1) (n + 1 + 1) x.1, phi.f (n + 1) x.1 - B.d n (n + 1) x.2) := by
  change (CochainComplex.of.d (fun n : ℤ => ModuleCat.of R (A.X (n + 1) × B.X n))
    (fibreStep phi) n (n + 1)).hom x = _
  rw [CochainComplex.of_d]
  rfl

def projection {A B : Complex (R := R)} (phi : A ⟶ B) : fibre phi ⟶ raise A :=
  CochainComplex.ofHom (fun _ => ModuleCat.ofHom (LinearMap.fst R _ _)) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (raise A).d n (n + 1) x.1 = ((fibre phi).d n (n + 1) x).1
    rw [raise_d, fibre_d])

/-- The canonical pure local cochain, in the boundary-cup sign convention. -/
def pureLocal {A B : Complex (R := R)} (phi : A ⟶ B) (n : ℤ) :
    B.X n →ₗ[R] (fibre phi).X n :=
  (0 : B.X n →ₗ[R] A.X (n + 1)).prod LinearMap.id

@[simp] lemma pureLocal_apply {A B : Complex (R := R)} (phi : A ⟶ B) (n : ℤ)
    (l : B.X n) : pureLocal phi n l = (0, l) := rfl

theorem pureLocal_closed {A B : Complex (R := R)} (phi : A ⟶ B)
    (l : B.X 1) (hl : B.d 1 2 l = 0) :
    (fibre phi).d 1 2 (pureLocal phi 1 l) = 0 := by
  change (A.d 2 3 0, phi.f 2 0 - B.d 1 2 l) = 0
  simp [hl]

def selmerMap {G U L : Complex (R := R)} (loc : G ⟶ L) (inc : U ⟶ L) :
    pair G U ⟶ L := -(pairFst G U ≫ loc) + (pairSnd G U ≫ inc)

abbrev selmer {G U L : Complex (R := R)} (loc : G ⟶ L) (inc : U ⟶ L) :=
  fibre (selmerMap loc inc)

def globalProjection {G U L : Complex (R := R)} (loc : G ⟶ L) (inc : U ⟶ L) :
    selmer loc inc ⟶ raise G := projection (selmerMap loc inc) ≫ raiseMap (pairFst G U)

/-- Extracted from closure under the actual cone differential. -/
theorem selmer_cycle_equation {G U L : Complex (R := R)} (loc : G ⟶ L) (inc : U ⟶ L)
    (y : (selmer loc inc).X 0) (hy : (selmer loc inc).d 0 1 y = 0) :
    inc.f 1 y.1.2 = loc.f 1 y.1.1 + L.d 0 1 y.2 := by
  have h := congrArg Prod.snd hy
  change -loc.f 1 y.1.1 + inc.f 1 y.1.2 - L.d 0 1 y.2 = 0 at h
  have h' : -loc.f 1 y.1.1 + inc.f 1 y.1.2 - L.d 0 1 y.2 = 0 := h
  rw [sub_eq_zero] at h'
  rw [← h']
  abel

/-- A native chain homotopy gives the precise representative-level correction
needed by the local cup calculation, rather than a postulated local equality. -/
theorem homotopy_cycle_boundary {A B : Complex (R := R)} {f g : A ⟶ B}
    (H : Homotopy f g) (z : A.X 0) (hz : A.d 0 1 z = 0) :
    f.f 0 z = g.f 0 z + B.d (-1) 0 (H.hom 0 (-1) z) := by
  have h := H.comm 0
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 from rfl),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)] at h
  have he := congrArg (fun a : A.X 0 ⟶ B.X 0 => a z) h
  simpa [ModuleCat.comp_apply, hz, add_comm] using he

end

end Research.DerivativeSwitch.NativeSelmerCone
