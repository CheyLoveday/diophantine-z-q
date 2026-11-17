import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RepresentationTheory.Continuous.TopRep

/-!
# The conjugate Weil pairing on the twisted coefficients

The coefficient ring is fixed by conjugation. The scalar character on the
two arguments cancels and the Tate involution occurs once in the pairing.
-/

namespace Research.DerivativeSwitch.ConjugateWeilPairing

universe u
variable {R G : Type u} [CommRing R] [TopologicalSpace R] [Group G]

variable (T : TopRep.{u} R G) (alpha : G →* Rˣ)

def scalarTwist : TopRep.{u} R G := TopRep.of (X := T) ⟨{
  toFun g := (alpha g : R) • T.ρ g
  map_one' := by simp
  map_mul' g h := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [map_mul, Units.val_mul, smul_apply, mul_apply_eq_comp, map_smul, mul_smul]
    exact smul_comm _ _ _ }⟩

/-- Continuity in the group variable and the vector for the twisted action. -/
theorem scalarTwist_continuous [TopologicalSpace G]
    (hT : Continuous fun z : G × T => T.ρ z.1 z.2)
    (hAlpha : Continuous fun g : G => (alpha g : R)) :
    Continuous fun z : G × T => (scalarTwist T alpha).ρ z.1 z.2 := by
  change Continuous fun z : G × T => (alpha z.1 : R) • T.ρ z.1 z.2
  exact (hAlpha.comp continuous_fst).smul hT

variable (e : T →ₗ[R] T →ₗ[R] R) (J : T ≃ₗ[R] T)

def paired : T →ₗ[R] T →ₗ[R] R := (LinearMap.lcomp R R J.toLinearMap).comp e

/-- The underlying perfect pairing identifies the conjugate carrier with
the linear dual. The equivariance theorem records the cyclotomic twist. -/
noncomputable def conjugateDual [e.IsPerfPair] : T ≃ₗ[R] Module.Dual R T :=
  J.trans e.flip.toPerfPair

@[simp] theorem conjugateDual_apply [e.IsPerfPair] (x y : T) :
    conjugateDual T e J y x = paired T e J x y := rfl

theorem paired_equivariant (tau : G →* G) (chi : G →* Rˣ)
    (hAlpha : ∀ g, (alpha g : R) * (alpha (tau g) : R) = 1)
    (hJ : ∀ g y, J (T.ρ (tau g) y) = T.ρ g (J y))
    (hWeil : ∀ g x y, e (T.ρ g x) (T.ρ g y) = (chi g : R) • e x y)
    (g : G) (x y : T) :
    paired T e J ((scalarTwist T alpha).ρ g x) ((scalarTwist T alpha).ρ (tau g) y) =
      (chi g : R) • paired T e J x y := by
  change e ((alpha g : R) • T.ρ g x) (J ((alpha (tau g) : R) • T.ρ (tau g) y)) =
    (chi g : R) • e x (J y)
  rw [map_smul, map_smul, LinearMap.smul_apply, hJ, map_smul, smul_smul,
    hAlpha, one_smul, hWeil]

end Research.DerivativeSwitch.ConjugateWeilPairing
