import Research.DerivativeSwitch.NativeSelmerCone
import Mathlib.LinearAlgebra.BilinearMap

/-!
# The adjoint of the traced Selmer cup

The native index `n` represents ordinary degree `n+1`. The complementary
index for total ordinary degree three is `1-n`. The product and its
Leibniz identity are inputs on cochains, and the trace kills boundaries.
The output is a map of actual cochain complexes into the shifted algebraic
dual. Its cohomological perfectness is a separate arithmetic theorem.
-/

namespace Research.DerivativeSwitch.SelmerDualityMap

open CategoryTheory NativeSelmerCone

universe u
variable {R : Type u} [CommRing R]

def sign (R : Type u) [CommRing R] (n : ℤ) : R := if n % 2 = 0 then 1 else -1

private def dualStep (B : Complex (R := R)) (n : ℤ) :
    ModuleCat.of R (B.X (1 - n) →ₗ[R] R) ⟶ ModuleCat.of R (B.X (1 - (n + 1)) →ₗ[R] R) :=
  ModuleCat.ofHom (sign R n • LinearMap.lcomp R R (B.d (1 - (n + 1)) (1 - n)).hom)

private theorem dualStep_sq (B : Complex (R := R)) (n : ℤ) :
    dualStep B n ≫ dualStep B (n + 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro y
  have hh := congrArg (fun d : B.X (1 - (n + 1 + 1)) ⟶ B.X (1 - n) => d y)
    (B.d_comp_d (1 - (n + 1 + 1)) (1 - (n + 1)) (1 - n))
  change B.d (1 - (n + 1)) (1 - n) (B.d (1 - (n + 1 + 1)) (1 - (n + 1)) y) = 0 at hh
  change sign R (n + 1) • (sign R n •
    f (B.d (1 - (n + 1)) (1 - n) (B.d (1 - (n + 1 + 1)) (1 - (n + 1)) y))) = 0
  rw [hh, map_zero, smul_zero, smul_zero]

/-- The shifted dual in native degrees. -/
abbrev shiftedDual (B : Complex (R := R)) : Complex (R := R) :=
  CochainComplex.of (fun n : ℤ => ModuleCat.of R (B.X (1 - n) →ₗ[R] R))
    (dualStep B) (dualStep_sq B)

private theorem dual_d (B : Complex (R := R)) (n : ℤ)
    (f : (shiftedDual B).X n) (y : B.X (1 - (n + 1))) :
    ((shiftedDual B).d n (n + 1) f) y = sign R n • f (B.d (1 - (n + 1)) (1 - n) y) := by
  change ((CochainComplex.of.d (fun n : ℤ => ModuleCat.of R (B.X (1 - n) →ₗ[R] R))
    (dualStep B) n (n + 1)).hom f) y = _
  rw [CochainComplex.of_d]
  rfl

/-- The two total degrees needed for adjunction, with Leibniz **before**
the trace. `T` is the common compact-support cone. -/
structure TraceProduct (A B T : Complex (R := R)) where
  totalThree (n : ℤ) : A.X n →ₗ[R] B.X (1 - n) →ₗ[R] T.X 2
  totalTwo (n : ℤ) : A.X n →ₗ[R] B.X (1 - (n + 1)) →ₗ[R] T.X 1
  leibniz : ∀ (n : ℤ) (x : A.X n) (y : B.X (1 - (n + 1))),
    T.d 1 2 (totalTwo n x y) =
      totalThree (n + 1) (A.d n (n + 1) x) y -
        sign R n • totalThree n x (B.d (1 - (n + 1)) (1 - n) y)

variable {A B T : Complex (R := R)}

/-- Adjunction of the product evaluated by the compact-support trace. -/
def adjoint (P : TraceProduct A B T) (trace : T.X 2 →ₗ[R] R)
    (kills : ∀ b : T.X 1, trace (T.d 1 2 b) = 0) : A ⟶ shiftedDual B :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom
    ((LinearMap.llcomp R _ _ _ trace).comp (P.totalThree n))) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
      dual_d]
    have h := congrArg trace (P.leibniz n x y)
    rw [kills, map_sub, map_smul, eq_comm, sub_eq_zero] at h
    exact h.symm)

theorem adjoint_apply (P : TraceProduct A B T) (trace : T.X 2 →ₗ[R] R)
    (kills : ∀ b : T.X 1, trace (T.d 1 2 b) = 0) (n : ℤ) (x : A.X n) (y : B.X (1 - n)) :
    ((adjoint P trace kills).f n x) y = trace (P.totalThree n x y) := rfl

variable {A' B' : Complex (R := R)}

/-- Pull back both product arguments along their actual chain maps to the
source complexes. For retained models these are the inclusion maps. -/
def TraceProduct.pullback (P : TraceProduct A B T) (i : A' ⟶ A) (j : B' ⟶ B) :
    TraceProduct A' B' T where
  totalThree n := (LinearMap.lcomp R _ (j.f (1 - n)).hom).comp
    ((P.totalThree n).comp (i.f n).hom)
  totalTwo n := (LinearMap.lcomp R _ (j.f (1 - (n + 1))).hom).comp
    ((P.totalTwo n).comp (i.f n).hom)
  leibniz n x y := by
    have hi := congrArg (fun f : A'.X n ⟶ A.X (n + 1) => f x) (i.comm n (n + 1))
    have hj := congrArg (fun f : B'.X (1 - (n + 1)) ⟶ B.X (1 - n) => f y)
      (j.comm (1 - (n + 1)) (1 - n))
    simp only [ModuleCat.comp_apply] at hi hj
    change T.d 1 2 (P.totalTwo n (i.f n x) (j.f (1 - (n + 1)) y)) =
      P.totalThree (n + 1) (i.f (n + 1) (A'.d n (n + 1) x)) (j.f (1 - (n + 1)) y) -
        sign R n • P.totalThree n (i.f n x) (j.f (1 - n) (B'.d (1 - (n + 1)) (1 - n) y))
    rw [← hi, ← hj]
    exact P.leibniz n (i.f n x) (j.f (1 - (n + 1)) y)

/-- The actual paired row evaluates the original product after including
both retained cochains. -/
theorem retained_adjoint_apply (P : TraceProduct A B T) (i : A' ⟶ A) (j : B' ⟶ B)
    (trace : T.X 2 →ₗ[R] R) (kills : ∀ b : T.X 1, trace (T.d 1 2 b) = 0)
    (n : ℤ) (x : A'.X n) (y : B'.X (1 - n)) :
    ((adjoint (P.pullback i j) trace kills).f n x) y =
      trace (P.totalThree n (i.f n x) (j.f (1 - n) y)) := rfl

end Research.DerivativeSwitch.SelmerDualityMap
