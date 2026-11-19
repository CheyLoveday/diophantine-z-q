import Research.DerivativeSwitch.NativeSelmerCone
import Research.DerivativeSwitch.RetainedCoefficients
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Retaining the differential and maps of based finite Selmer models

The finite models and their bases are supplied stagewise. One common
ultrafilter retains the matrices read directly from their differentials
and chain maps. The resulting objects are cochain complexes over the ring
of compatible scalar residues, even when the original models vary.
-/

namespace Research.DerivativeSwitch.RetainedSelmerModels

open CategoryTheory NativeSelmerCone Filter FiniteSelmerCoefficients RetainedCoefficients

noncomputable section

structure BasedModel (rank : ℤ → ℕ) (i : ℕ) where
  complex : Complex (R := Scalar i)
  basis (n : ℤ) : Module.Basis (Fin (rank n)) (Scalar i) (complex.X n)

private def familyMatrix {a b : Type} (M : ∀ i, Matrix a b (Scalar i)) : Matrix a b StageFamily :=
  Matrix.of fun r c i => M i r c

private theorem familyMatrix_mul {a b c : Type} [Fintype b]
    (M : ∀ i, Matrix a b (Scalar i)) (N : ∀ i, Matrix b c (Scalar i)) :
    familyMatrix (fun i => M i * N i) = familyMatrix M * familyMatrix N := by
  ext r c i
  simp [familyMatrix, Matrix.mul_apply, Finset.sum_apply]

variable (U : Ultrafilter ℕ) (cofinal : ∀ n, ∀ᶠ i in (U : Filter ℕ), n ≤ i)

def retainMatrix {a b : Type} (M : ∀ i, Matrix a b (Scalar i)) : Matrix a b CompatibleScalars :=
  (familyMatrix M).map (retain U cofinal)

@[simp] theorem retainMatrix_mul {a b c : Type} [Fintype b]
    (M : ∀ i, Matrix a b (Scalar i)) (N : ∀ i, Matrix b c (Scalar i)) :
    retainMatrix U cofinal (fun i => M i * N i) = retainMatrix U cofinal M * retainMatrix U cofinal N := by
  rw [retainMatrix, familyMatrix_mul, Matrix.map_mul]
  rfl

@[simp] theorem retainMatrix_zero {a b : Type} :
    retainMatrix U cofinal (fun i => (0 : Matrix a b (Scalar i))) = 0 := by
  apply Matrix.ext
  intro r c
  change retain U cofinal (0 : StageFamily) = 0
  exact map_zero _

@[simp] theorem retainMatrix_add {a b : Type} (M N : ∀ i, Matrix a b (Scalar i)) :
    retainMatrix U cofinal (fun i => M i + N i) = retainMatrix U cofinal M + retainMatrix U cofinal N := by
  apply Matrix.ext
  intro r c
  exact map_add (retain U cofinal) (fun i => M i r c) (fun i => N i r c)

@[simp] theorem retainMatrix_one {a : Type} [DecidableEq a] :
    retainMatrix U cofinal (fun i => (1 : Matrix a a (Scalar i))) = 1 := by
  apply Matrix.ext
  intro r c
  simp only [retainMatrix, Matrix.map_apply, familyMatrix, Matrix.of_apply, Matrix.one_apply]
  split_ifs
  · exact map_one (retain U cofinal)
  · exact map_zero (retain U cofinal)

variable {r s : ℤ → ℕ} (C : ∀ i, BasedModel r i) (D : ∀ i, BasedModel s i)

def differential (i : ℕ) (n : ℤ) : Matrix (Fin (r (n + 1))) (Fin (r n)) (Scalar i) :=
  LinearMap.toMatrix ((C i).basis n) ((C i).basis (n + 1)) ((C i).complex.d n (n + 1)).hom

theorem differential_sq (i : ℕ) (n : ℤ) :
    differential C i (n + 1) * differential C i n = 0 := by
  have h := congrArg (fun f : (C i).complex.X n ⟶ (C i).complex.X (n + 1 + 1) =>
    LinearMap.toMatrix ((C i).basis n) ((C i).basis (n + 1 + 1)) f.hom)
    ((C i).complex.d_comp_d n (n + 1) (n + 1 + 1))
  unfold differential
  rw [← LinearMap.toMatrix_comp ((C i).basis n) ((C i).basis (n + 1)) ((C i).basis (n + 1 + 1))]
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero, map_zero] using h

private def retainedStep (n : ℤ) :
    ModuleCat.of CompatibleScalars (Fin (r n) → CompatibleScalars) ⟶
      ModuleCat.of CompatibleScalars (Fin (r (n + 1)) → CompatibleScalars) :=
  ModuleCat.ofHom (retainMatrix U cofinal (fun i => differential C i n)).mulVecLin

private theorem retainedStep_sq (n : ℤ) :
    retainedStep U cofinal C n ≫ retainedStep U cofinal C (n + 1) = 0 := by
  have h := congrArg (retainMatrix U cofinal)
    (funext fun i => differential_sq C i n)
  rw [retainMatrix_mul, retainMatrix_zero] at h
  apply ModuleCat.hom_ext
  simp only [retainedStep, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero]
  rw [← Matrix.mulVecLin_mul, h, Matrix.mulVecLin_zero]

/-- The cochain complex obtained by retaining the actual finite model
differentials over all precisions. -/
abbrev retainedComplex : Complex (R := CompatibleScalars) :=
  CochainComplex.of (fun n => ModuleCat.of CompatibleScalars (Fin (r n) → CompatibleScalars))
    (retainedStep U cofinal C) (retainedStep_sq U cofinal C)

private theorem retainedComplex_d (n : ℤ) :
    (retainedComplex U cofinal C).d n (n + 1) = retainedStep U cofinal C n := by
  exact CochainComplex.of_d (fun n : ℤ => ModuleCat.of CompatibleScalars (Fin (r n) → CompatibleScalars))
    (retainedStep U cofinal C) n

variable (f : ∀ i, (C i).complex ⟶ (D i).complex)

def mapMatrix (i : ℕ) (n : ℤ) : Matrix (Fin (s n)) (Fin (r n)) (Scalar i) :=
  LinearMap.toMatrix ((C i).basis n) ((D i).basis n) ((f i).f n).hom

theorem mapMatrix_comm (i : ℕ) (n : ℤ) :
    differential D i n * mapMatrix C D f i n =
      mapMatrix C D f i (n + 1) * differential C i n := by
  have h := congrArg (fun g : (C i).complex.X n ⟶ (D i).complex.X (n + 1) =>
    LinearMap.toMatrix ((C i).basis n) ((D i).basis (n + 1)) g.hom) ((f i).comm n (n + 1))
  unfold differential mapMatrix
  rw [← LinearMap.toMatrix_comp ((C i).basis n) ((D i).basis n) ((D i).basis (n + 1)),
    ← LinearMap.toMatrix_comp ((C i).basis n) ((C i).basis (n + 1)) ((D i).basis (n + 1))]
  simpa only [ModuleCat.hom_comp] using h

/-- Retain the actual entries of a family of maps between the finite models. -/
def retainedMap : retainedComplex U cofinal C ⟶ retainedComplex U cofinal D :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom
    (retainMatrix U cofinal (fun i => mapMatrix C D f i n)).mulVecLin) (by
    intro n
    have h := congrArg (retainMatrix U cofinal) (funext fun i => mapMatrix_comm C D f i n)
    rw [retainMatrix_mul, retainMatrix_mul] at h
    rw [retainedComplex_d, retainedComplex_d]
    apply ModuleCat.hom_ext
    simp only [retainedStep, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul, h])

@[simp] theorem retainedMap_id : retainedMap U cofinal C C (fun i => 𝟙 (C i).complex) =
    𝟙 (retainedComplex U cofinal C) := by
  ext n : 1
  apply ModuleCat.hom_ext
  change (retainMatrix U cofinal (fun i => mapMatrix C C (fun j => 𝟙 (C j).complex) i n)).mulVecLin =
    LinearMap.id
  have h : (fun i => mapMatrix C C (fun j => 𝟙 (C j).complex) i n) = fun _ => 1 := by
    funext i
    exact LinearMap.toMatrix_id ((C i).basis n)
  rw [h, retainMatrix_one]
  exact Matrix.mulVecLin_one

theorem retainedMap_comp {q : ℤ → ℕ} (E : ∀ i, BasedModel q i)
    (g : ∀ i, (D i).complex ⟶ (E i).complex) :
    retainedMap U cofinal C E (fun i => f i ≫ g i) =
      retainedMap U cofinal C D f ≫ retainedMap U cofinal D E g := by
  ext n : 1
  apply ModuleCat.hom_ext
  change (retainMatrix U cofinal (fun i => mapMatrix C E (fun j => f j ≫ g j) i n)).mulVecLin =
    (retainMatrix U cofinal (fun i => mapMatrix D E g i n)).mulVecLin.comp
      (retainMatrix U cofinal (fun i => mapMatrix C D f i n)).mulVecLin
  rw [← Matrix.mulVecLin_mul, ← retainMatrix_mul]
  apply congrArg (fun M => (retainMatrix U cofinal M).mulVecLin)
  funext i
  exact LinearMap.toMatrix_comp ((C i).basis n) ((D i).basis n) ((E i).basis n) _ _

variable {f} {g : ∀ i, (C i).complex ⟶ (D i).complex}

private def homotopyMatrix (H : ∀ i, Homotopy (f i) (g i)) (i : ℕ) (n m : ℤ) :
    Matrix (Fin (s m)) (Fin (r n)) (Scalar i) :=
  LinearMap.toMatrix ((C i).basis n) ((D i).basis m) ((H i).hom n m).hom

/-- The actual degree-minus-one maps retain the homotopy equation. -/
def retainedHomotopy (H : ∀ i, Homotopy (f i) (g i)) :
    Homotopy (retainedMap U cofinal C D f) (retainedMap U cofinal C D g) where
  hom n m := ModuleCat.ofHom
    (retainMatrix U cofinal (fun i => homotopyMatrix C D H i n m)).mulVecLin
  zero n m h := by
    have hz : (fun i => homotopyMatrix C D H i n m) = fun _ => 0 := by
      funext i
      simp [homotopyMatrix, (H i).zero n m h]
    rw [hz, retainMatrix_zero, Matrix.mulVecLin_zero]
    rfl
  comm n := by
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, n = p + 1 := ⟨n - 1, by omega⟩
    have hn : (ComplexShape.up ℤ).Rel (p + 1) (p + 1 + 1) := rfl
    have hp : (ComplexShape.up ℤ).Rel p (p + 1) := rfl
    rw [dNext_eq _ hn, prevD_eq _ hp, retainedComplex_d, retainedComplex_d]
    apply ModuleCat.hom_ext
    change (retainMatrix U cofinal (fun i => mapMatrix C D f i (p + 1))).mulVecLin =
      (retainMatrix U cofinal (fun i => homotopyMatrix C D H i (p + 1 + 1) (p + 1))).mulVecLin.comp
        (retainMatrix U cofinal (fun i => differential C i (p + 1))).mulVecLin +
      (retainMatrix U cofinal (fun i => differential D i p)).mulVecLin.comp
        (retainMatrix U cofinal (fun i => homotopyMatrix C D H i (p + 1) p)).mulVecLin +
      (retainMatrix U cofinal (fun i => mapMatrix C D g i (p + 1))).mulVecLin
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_add, ← Matrix.mulVecLin_add,
      ← retainMatrix_mul, ← retainMatrix_mul, ← retainMatrix_add, ← retainMatrix_add]
    apply congrArg (fun M => (retainMatrix U cofinal M).mulVecLin)
    funext i
    have h := (H i).comm (p + 1)
    rw [dNext_eq _ hn, prevD_eq _ hp] at h
    unfold mapMatrix differential homotopyMatrix
    rw [← LinearMap.toMatrix_comp ((C i).basis (p + 1)) ((C i).basis (p + 1 + 1)) ((D i).basis (p + 1)),
      ← LinearMap.toMatrix_comp ((C i).basis (p + 1)) ((D i).basis p) ((D i).basis (p + 1)),
      ← map_add, ← map_add]
    exact congrArg (fun m : (C i).complex.X (p + 1) ⟶ (D i).complex.X (p + 1) =>
      LinearMap.toMatrix ((C i).basis (p + 1)) ((D i).basis (p + 1)) m.hom) h

/-- Stagewise homotopy inverses remain homotopy inverses over the residue limit. -/
def retainedHomotopyEquiv (e : ∀ i, HomotopyEquiv (C i).complex (D i).complex) :
    HomotopyEquiv (retainedComplex U cofinal C) (retainedComplex U cofinal D) where
  hom := retainedMap U cofinal C D fun i => (e i).hom
  inv := retainedMap U cofinal D C fun i => (e i).inv
  homotopyHomInvId := (Homotopy.ofEq (retainedMap_comp U cofinal C D _ C _).symm).trans
    ((retainedHomotopy U cofinal C C (fun i => (e i).homotopyHomInvId)).trans
      (Homotopy.ofEq (retainedMap_id U cofinal C)))
  homotopyInvHomId := (Homotopy.ofEq (retainedMap_comp U cofinal D C _ D _).symm).trans
    ((retainedHomotopy U cofinal D D (fun i => (e i).homotopyInvHomId)).trans
      (Homotopy.ofEq (retainedMap_id U cofinal D)))

end

end Research.DerivativeSwitch.RetainedSelmerModels
