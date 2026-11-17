import Research.DerivativeSwitch.CommonStrict
import Research.DerivativeSwitchBoundary
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The common-strict target determinant from the exact boundary kernel

For a two-term strict presentation, use its actual cokernel and the maps
induced by the appended blocks. Injectivity of the strict differential and
the exact axes kernel imply the generic target determinant is nonzero.
-/

namespace Research.DerivativeSwitch.ScalarRatio

open Matrix
open scoped Matrix

variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

/-- The connecting map in the strict cokernel of the two-term presentation. -/
def strictBoundary (D0 : Matrix (Index I) I K) (A : Matrix (Index I) (Fin 2) K) :
    Local K →ₗ[K] ((Index I → K) ⧸ LinearMap.range D0.mulVecLin) :=
  (LinearMap.range D0.mulVecLin).mkQ.comp A.mulVecLin

private lemma smul_eq_axis {v x : Local K} (hx : area v x ≠ 0) {s a : K}
    (heq : s • x = a • v) : s = 0 := by
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  simp only [Pi.smul_apply, smul_eq_mul] at h0 h1
  exact (mul_eq_zero.mp (show s * area v x = 0 by
    unfold area
    linear_combination v 0 * h1 - v 1 * h0)).resolve_right hx

/-- The exact relaxed kernel separates the two complementary boundary
directions modulo the strict columns. Strict injectivity then gives
independence of all the target columns. -/
theorem target_det_ne_zero_of_axes
    (D0 : Matrix (Index I) I K) (AF AS : Matrix (Index I) (Fin 2) K)
    (J : Local K ≃ₗ[K] Local K) (v x : Local K)
    (hD0 : Function.Injective D0.mulVecLin)
    (haxes : AxesKernel (strictBoundary D0 AF) (strictBoundary D0 AS) J v)
    (hx : area v x ≠ 0) :
    (target D0 (AF *ᵥ x) (AS *ᵥ J x)).det ≠ 0 := by
  let a := AF *ᵥ x
  let b := AS *ᵥ J x
  have hmul (w : Index I → K) :
      target D0 a b *ᵥ w =
        D0.mulVecLin (w ∘ Sum.inl) + w (.inr 0) • a + w (.inr 1) • b := by
    ext i
    simp [target, join, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_two, mul_comm, add_assoc]
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  change Function.Injective (target D0 a b).mulVecLin
  apply LinearMap.ker_eq_bot.mp
  apply Matrix.ker_mulVecLin_eq_bot_iff.mpr
  intro w hw
  rw [hmul] at hw
  let p := (LinearMap.range D0.mulVecLin).mkQ
  have hp : p (D0.mulVecLin (w ∘ Sum.inl)) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self _ _
  have hpw := congrArg p hw
  rw [map_add, map_add, hp, zero_add, map_zero] at hpw
  have hboundary :
      strictBoundary D0 AF (w (.inr 0) • x) +
        strictBoundary D0 AS (w (.inr 1) • J x) = 0 := by
    simpa only [map_smul, strictBoundary, LinearMap.comp_apply, Matrix.mulVecLin_apply]
      using hpw
  obtain ⟨s, t, hs, ht⟩ := (haxes _ _).mp hboundary
  have hw0 := smul_eq_axis hx hs
  have hw1 := smul_eq_axis hx (J.injective (by simpa only [map_smul] using ht))
  rw [hw0, hw1, zero_smul, zero_smul, add_zero, add_zero] at hw
  have hstrict : w ∘ Sum.inl = 0 := hD0 (by simpa using hw)
  funext i
  rcases i with i | i
  · exact congrFun hstrict i
  · fin_cases i
    · exact hw0
    · exact hw1

/-- Populate the existing coordinate input with the original matrices, cycles,
and rows. The target nonvanishing field is supplied by the strict cokernel. -/
noncomputable def CommonStrictData.ofAxes
    (D0 : Matrix (Index I) I K)
    (AF AS : Matrix (Index I) (Fin 2) K)
    (hF hS : I → K) (v x : Local K)
    (J : (Matrix (Fin 2) (Fin 2) K)ˣ)
    (lamF lamS : Index I → K)
    (hcycleF : join D0 AF *ᵥ cycle hF v = 0)
    (hcycleS : join D0 AS *ᵥ cycle hS ((J : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = 0)
    (hclosedF : lamF ᵥ* join D0 AF = 0)
    (hclosedS : lamS ᵥ* join D0 AS = 0)
    (hx : area v x ≠ 0)
    (hD0 : Function.Injective D0.mulVecLin)
    (haxes : AxesKernel (strictBoundary D0 AF) (strictBoundary D0 AS)
      (Matrix.GeneralLinearGroup.toLin J).toLinearEquiv v) : CommonStrictData K I where
  D0 := D0
  AF := AF
  AS := AS
  hF := hF
  hS := hS
  v := v
  x := x
  J := J
  lamF := lamF
  lamS := lamS
  cycleF := hcycleF
  cycleS := hcycleS
  closedF := hclosedF
  closedS := hclosedS
  area_ne := hx
  target_ne := by
    have h := target_det_ne_zero_of_axes D0 AF AS
      (Matrix.GeneralLinearGroup.toLin J).toLinearEquiv v x hD0 haxes hx
    exact h

end Research.DerivativeSwitch.ScalarRatio
