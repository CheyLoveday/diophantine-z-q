import Research.DerivativeSwitch.FiniteTateTwist
import Mathlib.Topology.Instances.ZMod

/-! The first coefficient stage and the mod-two Tate action. -/

namespace Research.DerivativeSwitch.FirstSelmerPrecision

open FiniteSelmerCoefficients FiniteTateTwist Polynomial

noncomputable section

private def evaluateConstant : Scalar 1 →+* ZMod 2 :=
  Ideal.Quotient.lift (truncationIdeal 1) (Polynomial.evalRingHom 0) (by
    intro p hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hp
    simp)

/-- At precision one the deformation parameter vanishes, giving `ℤ/2`. -/
def scalarEquiv : Scalar 1 ≃+* ZMod 2 :=
  RingEquiv.ofRingHom evaluateConstant ((quotient 1).comp Polynomial.C) (by
    apply RingHom.ext
    intro a
    change Polynomial.eval 0 (Polynomial.C a) = a
    exact Polynomial.eval_C) (by
    apply RingHom.ext
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change quotient 1 (Polynomial.C (p.eval 0)) = quotient 1 p
    apply Ideal.Quotient.eq.mpr
    simp only [Ideal.mem_span_singleton, pow_one, Polynomial.X_dvd_iff,
      Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_sub, Polynomial.eval_C, sub_self])

theorem scalarEquiv_quotient (p : Polynomial (Base 1)) : scalarEquiv (quotient 1 p) = p.eval 0 := rfl

/-- Every Galois operator on the first Tate line acts as the identity. -/
theorem coefficientLine_action {G : Type} [Group G] (chi : G →* (ZMod 2)ˣ)
    (g : G) (x : ZMod 2) :
    (coefficientLine (i := 0) (RingHom.id (ZMod 2)) chi).ρ g x = x := by
  have h : (chi g : ZMod 2) = 1 := by
    have hn := (chi g).ne_zero
    generalize (↑(chi g) : ZMod 2) = a at hn ⊢
    fin_cases a
    · exact (hn rfl).elim
    · rfl
  change (chi g : ZMod 2) • x = x
  rw [h, one_smul]

end

end Research.DerivativeSwitch.FirstSelmerPrecision
