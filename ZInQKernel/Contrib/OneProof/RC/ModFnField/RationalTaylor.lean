import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.Basic

/-! Closure properties of rational Taylor coefficients (provenance (c)). -/

noncomputable section
open scoped ContDiff

namespace ZInQ.Manuscript.RC.ModFnField

/-- The rational numbers embedded in the complex numbers. -/
abbrev rationalConstants : Subfield ℂ := (Rat.castHom ℂ).fieldRange

/-- The complex derivatives of every order, including order zero, are
rational at the indicated center. -/
def RationalTaylor (f : ℂ → ℂ) (z : ℂ) : Prop :=
  ∀ n : ℕ, iteratedDeriv n f z ∈ rationalConstants

namespace RationalTaylor

theorem const {c : ℂ} (hc : c ∈ rationalConstants) (z : ℂ) :
    RationalTaylor (fun _ => c) z := by
  intro n
  by_cases hn : n = 0
  · simpa [hn] using hc
  · simp [iteratedDeriv_const, hn]

theorem id_zero : RationalTaylor (fun z => z) 0 := by
  intro n
  simp [iteratedDeriv_fun_id_zero, apply_ite]

theorem add {f g : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hF : RationalTaylor f z) (hG : RationalTaylor g z) :
    RationalTaylor (fun w => f w + g w) z := by
  intro n
  rw [iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt]
  exact rationalConstants.add_mem (hF n) (hG n)

theorem sub {f g : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hF : RationalTaylor f z) (hG : RationalTaylor g z) :
    RationalTaylor (fun w => f w - g w) z := by
  intro n
  rw [iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt]
  exact rationalConstants.sub_mem (hF n) (hG n)

theorem mul {f g : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hF : RationalTaylor f z) (hG : RationalTaylor g z) :
    RationalTaylor (fun w => f w * g w) z := by
  intro n
  rw [iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt]
  exact rationalConstants.sum_mem fun i _ =>
    rationalConstants.mul_mem (rationalConstants.mul_mem (natCast_mem _ _) (hF i)) (hG (n - i))

theorem pow {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hF : RationalTaylor f z) (n : ℕ) :
    RationalTaylor (fun w => f w ^ n) z := by
  induction n with
  | zero => simpa using const rationalConstants.one_mem z
  | succ n ih =>
    simpa only [pow_succ, Pi.pow_apply] using mul (hf.pow n) hf ih hF

theorem comp {f g : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f (g z)) (hg : AnalyticAt ℂ g z)
    (hF : RationalTaylor f (g z)) (hG : RationalTaylor g z) :
    RationalTaylor (f ∘ g) z := by
  intro n
  rw [iteratedDeriv_scomp_eq_sum_orderedFinpartition hf.contDiffAt hg.contDiffAt (show (n : ℕ∞ω) ≤ n from le_rfl)]
  exact rationalConstants.sum_mem fun i _ =>
    rationalConstants.mul_mem (rationalConstants.prod_mem fun j _ => hG (i.partSize j))
      (hF i.length)

theorem inv {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hn : f z ≠ 0)
    (hF : RationalTaylor f z) : RationalTaylor (fun w => (f w)⁻¹) z := by
  have hfz : f z ∈ rationalConstants := by simpa using hF 0
  apply comp (analyticAt_id.inv hn) hf _ hF
  intro n
  change iteratedDeriv n Inv.inv (f z) ∈ rationalConstants
  rw [iteratedDeriv_eq_iterate, iter_deriv_inv]
  exact rationalConstants.mul_mem (rationalConstants.mul_mem
    (rationalConstants.pow_mem (rationalConstants.neg_mem rationalConstants.one_mem) n)
    (natCast_mem _ _)) (rationalConstants.zpow_mem hfz _)

theorem deriv {f : ℂ → ℂ} {z : ℂ} (hf : RationalTaylor f z) :
    RationalTaylor (deriv f) z := by
  intro n
  rw [← iteratedDeriv_succ']
  exact hf (n + 1)

open Filter Topology in
/-- Dividing by a simple parameter preserves rational coefficients when the
quotient is analytic. Its value at zero is the first derivative. -/
theorem factor_at_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hF : RationalTaylor f 0)
    (h0 : f 0 = 0) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ RationalTaylor u 0 ∧ u 0 = _root_.deriv f 0 ∧
      f =ᶠ[𝓝 0] fun q => q * u q := by
  obtain ⟨u, hu, hfu⟩ := hf.exists_eventuallyEq_sum_add_pow_mul 1
  have hfu' : f =ᶠ[𝓝 0] fun q => q * u q := by
    change ∀ᶠ q in 𝓝 0, f q = q * u q
    simpa [h0] using hfu
  clear hfu
  have hcoeff (n : ℕ) : iteratedDeriv (n + 1) f 0 = ((n + 1 : ℕ) : ℂ) * iteratedDeriv n u 0 := by
    have hi : AnalyticAt ℂ (fun q : ℂ => q) 0 := analyticAt_id
    rw [hfu'.iteratedDeriv_eq, iteratedDeriv_fun_mul hi.contDiffAt hu.contDiffAt]
    rw [Finset.sum_eq_single 1]
    · rw [iteratedDeriv_fun_id_zero]
      simp [Nat.choose_one_right]
    · intro j _ hj
      rw [iteratedDeriv_fun_id_zero, ite_eq_right hj]
      simp
    · intro h
      exact (h (by simp)).elim
  refine ⟨u, hu, fun n => ?_, ?_, hfu'⟩
  · have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have he : iteratedDeriv n u 0 = iteratedDeriv (n + 1) f 0 / ((n + 1 : ℕ) : ℂ) := by
      rw [hcoeff, mul_comm, mul_div_cancel_right₀ _ hn]
    rw [he]
    exact rationalConstants.div_mem (hF (n + 1)) (natCast_mem _ _)
  · have h := hcoeff 0
    simpa using h.symm

end RationalTaylor


end ZInQ.Manuscript.RC.ModFnField
