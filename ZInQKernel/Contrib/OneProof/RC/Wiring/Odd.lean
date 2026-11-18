import ZInQKernel.Contrib.OneProof.RC.Wiring.Data
import ZInQKernel.Contrib.OneProof.RC.Odd.Statements

/-!
# Theorem 5.3, Lane RC0 round 2: visibility (O.8) from lane RC12

`visibilityTarget_of_inputs` (PROVED from lane RC12's `visibility_of_comparison`): the field
`RCSteps.visibility` ((O.8), App F `ex:app-visibility`, tex 9407–9445) from RC12's remaining
inputs, `VisibilityInputs`: the comparison (O.7) (Cornut–Jetchev Thm 3.1, PRINT, with Elliot's
theta construction, ELLIOT), the native-index bound (ELLIOT/GLUE) and the torsion clause (the
height formula, Cai–Shu–Tian Thm 1.1, PRINT).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 Filter Topology

attribute [local instance] Nat.fact_prime_two

variable {ℓ : ℕ} (D : RCData ℓ)

/-- **The inputs of (O.8) left by lane RC12** (`visibility_of_comparison`), over the data:
the Kummer values `λ_θ(D)` (integer lifts of `λ_{M_θ}(\overline{L P_D^{gen}})`, tex 2512–2530), the
number `ω = ω(N)` and a constant `C`, with
* (O.7) (`ThetaComparison`; App F `ex:app-theta-comparison`, tex 9101–9405; PRINT Cornut–Jetchev
  Thm 3.1 with Elliot's theta construction, ELLIOT; owner RC12 / RC9);
* the native-index bound (tex 9425–9431; ELLIOT/GLUE: an integral finite-field Kummer map cannot
  decrease the index valuation; owner RC12 / batch 3 GenusOdd): at a known simple zero,
  `2^k ∣ λ_θ(D)` for `k ≤ min(M_θ, j_gen(D) − C)`;
* the torsion clause (tex 9440–9444; PRINT Cai–Shu–Tian Thm 1.1: an odd-sign `D` that is not a
  simple zero has a torsion genus point, killed by `L`; owner CST application / batch 3 GenusOdd):
  `2^{M_θ} ∣ λ_θ(D)`. -/
def VisibilityInputs : Prop :=
  ∃ (lam : ℕ → ℤ → ℤ) (ω : ℕ) (C : ℤ),
    Odd.ThetaComparison D.Mθ D.aθ lam D.admissible ω ∧
    (∀ θ Dd, D.admissible θ Dd → AnalyticRank (Etw ℓ Dd) 1 → ∀ k : ℕ, k ≤ D.Mθ θ →
      (k : ℤ) ≤ D.jgen Dd - C → (2 : ℤ) ^ k ∣ lam θ Dd) ∧
    (∀ θ Dd, D.admissible θ Dd → ¬ AnalyticRank (Etw ℓ Dd) 1 → (2 : ℤ) ^ D.Mθ θ ∣ lam θ Dd)

/-- Lane RC12's `vZ` is the skeleton's `vZ` (PROVED). -/
theorem odd_vZ_eq (n : ℤ) : Odd.vZ n = vZ n := by
  simp only [Odd.vZ, vZ, v2, Rat.cast_intCast]

/-- **Visibility (O.8)** (PROVED from lane RC12's `visibility_of_comparison`). -/
theorem visibilityTarget_of_inputs (h : VisibilityInputs D) : VisibilityTarget D := by
  obtain ⟨lam, ω, C, hO7, hnat, htor⟩ := h
  obtain ⟨Cdet, hC⟩ := Odd.visibility_of_comparison D.Mθ D.aθ lam D.admissible
    (fun Dd => AnalyticRank (Etw ℓ Dd) 1) D.jgen ω C hO7 hnat htor
  refine ⟨Cdet, fun θ Dd hadm hlt => ?_⟩
  have hlt' : Odd.vZ (D.aθ θ Dd) < (((D.Mθ θ : ℕ) : ℤ) : WithTop ℤ) := by
    rw [odd_vZ_eq]
    simpa using hlt
  obtain ⟨h1, h2⟩ := hC θ Dd hadm hlt'
  refine ⟨h1, ?_⟩
  rw [odd_vZ_eq] at h2
  exact h2

end ZInQ.Manuscript.RC.Wiring
