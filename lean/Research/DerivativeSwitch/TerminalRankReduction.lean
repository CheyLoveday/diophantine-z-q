import Research.DerivativeSwitch.ConjugateLocalTransport
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.LinearCombination

/-!
# Linear algebra for the terminal derivative switches

Polarization finds one actual element of the additive evaluation image.
At a quadratic characteristic-zero test, self-annihilating subspaces of
each symmetric hyperbolic sign plane are its two coordinate axes.
-/

namespace Research.DerivativeSwitch.TerminalRankReduction

section ExactKernel

open ConjugateLocalTransport

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

/-- Vanishing on the exact kernel forces a coboundary when a central-modulo-
kernel element acts by a nonidentity scalar. -/
theorem coboundary_of_vanishing_on_kernel (rho : G →* Module.End K V)
    (b : G → V) (hb : IsCrossed rho b) (H : Subgroup G)
    (z : G) (c : K) (hscalar : ∀ w : V, rho z w = c • w) (hc : c ≠ 1)
    (hcentral : ∀ g : G, (g * z)⁻¹ * (z * g) ∈ H) (hzero : ∀ h ∈ H, b h = 0)
    (g : G) : b g = rho g ((c - 1)⁻¹ • b z) - (c - 1)⁻¹ • b z := by
  have h : b (z * g) = b (g * z) := by
    calc
      b (z * g) = b ((g * z) * ((g * z)⁻¹ * (z * g))) := by rw [mul_inv_cancel_left]
      _ = b (g * z) := by rw [hb, hzero _ (hcentral g), map_zero, add_zero]
  rw [hb z g, hb g z, hscalar] at h
  have hdiff : (c - 1) • b g = rho g (b z) - b z := by
    rw [sub_smul, one_smul, sub_eq_sub_iff_add_eq_add]
    simpa only [add_comm] using h
  have heq := congrArg (fun w : V => (c - 1)⁻¹ • w) hdiff
  simpa only [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hc), one_smul,
    smul_sub, map_smul] using heq

end ExactKernel

section Detection

variable {K H V W : Type*} [Field K] [AddMonoid H]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

private theorem linearMap_eq_zero_of_evaluation_span (e : H →+ V)
    (hspan : Submodule.span K (Set.range e) = ⊤) (f : V →ₗ[K] W)
    (hzero : ∀ a, f (e a) = 0) : f = 0 := by
  have hle : Submodule.span K (Set.range e) ≤ LinearMap.ker f :=
    Submodule.span_le.mpr fun _ ⟨a, ha⟩ => ha ▸ LinearMap.mem_ker.mpr (hzero a)
  apply LinearMap.ext
  intro x
  exact LinearMap.mem_ker.mp (hle (by rw [hspan]; exact Submodule.mem_top))

/-- A determinant or mixed-coordinate product that is nonzero on the span
of an additive evaluation image is nonzero at one actual evaluation. -/
theorem exists_quadratic_value_ne_zero (e : H →+ V)
    (hspan : Submodule.span K (Set.range e) = ⊤) (B : V →ₗ[K] V →ₗ[K] K)
    (htwo : (2 : K) ≠ 0) {x : V} (hx : B x x ≠ 0) :
    ∃ a, B (e a) (e a) ≠ 0 := by
  by_contra! hzero
  have hpair (a b : H) : B (e a) (e b) + B (e b) (e a) = 0 := by
    simpa only [map_add, LinearMap.add_apply, hzero, zero_add, add_zero] using hzero (b + a)
  let S := B + B.flip
  have hS : S = 0 := linearMap_eq_zero_of_evaluation_span e hspan S (fun a =>
    linearMap_eq_zero_of_evaluation_span e hspan (S (e a)) (fun b => hpair a b))
  have h := congrArg (fun f : V →ₗ[K] V →ₗ[K] K => f x x) hS
  change B x x + B x x = 0 at h
  rw [← two_mul] at h
  exact hx ((mul_eq_zero.mp h).resolve_left htwo)

end Detection

section HyperbolicPlane

variable {K : Type*} [Field K]

def hyperbolicPair (x y : K × K) : K := x.1 * y.2 + x.2 * y.1

/-- Exact annihilation for the symmetric hyperbolic form leaves only the
finite or singular axis over a field of characteristic different from two. -/
theorem hyperbolic_axes (U : Submodule K (K × K)) (htwo : (2 : K) ≠ 0)
    (hU : ∀ x, x ∈ U ↔ ∀ y ∈ U, hyperbolicPair x y = 0) :
    U = LinearMap.ker (LinearMap.snd K K K) ∨ U = LinearMap.ker (LinearMap.fst K K K) := by
  by_cases hF : ((1, 0) : K × K) ∈ U
  · left
    have hz (x : K × K) (hx : x ∈ U) : x.2 = 0 := by
      simpa [hyperbolicPair] using (hU x).mp hx _ hF
    apply Submodule.ext
    intro x
    change x ∈ U ↔ x.2 = 0
    refine ⟨hz x, fun hx => (hU x).mpr ?_⟩
    intro y hy
    simp [hyperbolicPair, hx, hz y hy]
  · right
    have hex : ∃ x ∈ U, (x : K × K).2 ≠ 0 := by
      by_contra! h
      apply hF
      apply (hU _).mpr
      intro y hy
      simp [hyperbolicPair, h y hy]
    obtain ⟨a, ha, hane⟩ := hex
    have hself := (hU a).mp ha a ha
    have hzero : (2 : K) * (a.1 * a.2) = 0 := by
      unfold hyperbolicPair at hself
      linear_combination hself
    have ha1 := (mul_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left htwo)).resolve_right hane
    have hS : ((0, 1) : K × K) ∈ U := by
      have hScaled := U.smul_mem a.2⁻¹ ha
      have heq : a.2⁻¹ • a = ((0, 1) : K × K) := by
        apply Prod.ext
        · simp [ha1]
        · simp [hane]
      rwa [heq] at hScaled
    have hz (x : K × K) (hx : x ∈ U) : x.1 = 0 := by
      simpa [hyperbolicPair] using (hU x).mp hx _ hS
    apply Submodule.ext
    intro x
    change x ∈ U ↔ x.1 = 0
    refine ⟨hz x, fun hx => (hU x).mpr ?_⟩
    intro y hy
    simp [hyperbolicPair, hx, hz y hy]

end HyperbolicPlane

end Research.DerivativeSwitch.TerminalRankReduction
