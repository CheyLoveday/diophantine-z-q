import ZInQKernel.Contrib.OneProof.RC.Wiring.Data
import ZInQKernel.Contrib.OneProof.RC.Odd.Statements

/-!
# Theorem 5.3, Lane RC0 round 2: visibility (O.8) from lane RC12

`visibilityTarget_of_inputs` (PROVED from lane RC12's `visibility_of_comparison`): the field
`RCSteps.visibility` ((O.8), App F `ex:app-visibility`, tex 9407–9445) from RC12's remaining
inputs, `VisibilityInputs`: the comparison (O.7) (Cornut–Jetchev Thm 3.1, PRINT, with Elliot's
theta construction, ELLIOT), the native-index bound (ELLIOT/GLUE) and the torsion clause (the
height formula, Cai–Shu–Tian Thm 1.1, PRINT).

`oddStageSource_of_data` (PROVED, lane RC27): App G's valid odd stages (`Odd.OddStageSource`, the
inputs of (O.9)–(O.11) at an odd stage) over the data `D : RCData ℓ`, from the stage cores, the
phase relation with `D.aθ`, (F.5), the advancing stages and `D.δo` the attained minimum, through
lane RC12's `Odd.oddStageSource_eventually` (batch 3's `f6_of_isLeast`, `stageChoice_proof`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 Filter Topology

attribute [local instance] Nat.fact_prime_two

variable {ℓ : ℕ} (D : RCData ℓ)

/-- **The inputs of (O.8) left by lane RC12** (`visibility_of_comparison`), over the data:
the Kummer values `λ_θ(D)` (integer lifts of `λ_{M_θ}(\overline{L P_D^{gen}})`, tex 2495–2496,
2522–2530), the
number `ω = ω(N)` and a constant `C`, with
* (O.7) (`ThetaComparison`; App F `ex:app-theta-comparison`, tex 9101–9405; PRINT Cornut–Jetchev
  Thm 3.1 with Elliot's theta construction, ELLIOT; owner RC12 / RC9);
* the native-index bound (tex 9411–9413, 9422–9428; ELLIOT/GLUE: an integral finite-field Kummer
  map cannot decrease the index valuation; owner RC12 / batch 3 GenusOdd): at a known simple zero,
  `2^k ∣ λ_θ(D)` for `k ≤ min(M_θ, j_gen(D) − C)`;
* the torsion clause (tex 9417–9419, 9439–9443; PRINT Cai–Shu–Tian Thm 1.1: an odd-sign `D` that is
  not a simple zero has a torsion genus point, killed by `L`; owner CST application / batch 3
  GenusOdd): `2^{M_θ} ∣ λ_θ(D)`. DEPARTURE (harmless): stated for every admissible `D`; every
  admissible `D` has odd sign (tex 2344–2346: `w(E^{(D)}) = w(E) χ_D(−N) = −1` for `D > 0` a square
  at `2N`). -/
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

/-- **PROVED (lane RC27; App G, Proposition `ex:app-odd-minimum`, tex 10190–10227; App F,
tex 9450–9453, 9578–9584): the valid odd stages over the data.** For `D : RCData ℓ` (stages
`D.stages`, precisions `D.Mθ`, phase-removed integer coefficients `D.aθ`, stage support
`D.admissible`, odd minimum `D.δo`), given:
* the stage coefficient functions `a θ` in `𝒪/2^{M_θ}𝒪` with their cores (`Odd.OddStageCore`,
  ELLIOT: the theta form (O.4)–(O.6) and its supports, tex 8409–9100, 9471–9476, 2530–2532);
* the phase relation at the squarefree parameters of the stage support: the actual coefficient is a
  multiple `ζ · a_θ(D)` of the phase-removed integer (tex 2538, (3.8) at 2527–2530; lane RC23's
  `ThetaSide.coeff` in this form);
* the advancing stages (`RCSteps.stages_advance`), (F.5) at every stage (batch 3's `CoarseF5`; the
  wiring's `exists_oddMinimum` derives it from the leaves) and `D.δo` the attained minimum (the body of
  `OddMinimumTarget`);
for every finite operator budget `W_U` and `R ≥ 2`, the stages are valid eventually along the
ultrafilter. -/
theorem oddStageSource_of_data (O : Type*) [CommRing O]
    (η : (θ : ℕ) → ℕ → Odd.StageRing O (D.Mθ θ)) (Good : ℕ → ℕ → Prop) (ap : ℕ → ℤ)
    (a : (θ : ℕ) → ℕ → Odd.StageRing O (D.Mθ θ))
    (hcore : ∀ θ, Odd.OddStageCore O (D.Mθ θ) (η θ) (Good θ) (fun n => D.admissible θ n) ap (a θ))
    (ζ : ℕ → ℕ → O)
    (hphase : ∀ θ (Dn : ℕ), Squarefree Dn → D.admissible θ Dn →
      a θ Dn = Ideal.Quotient.mk (Ideal.span {(2 : O) ^ D.Mθ θ}) (ζ θ Dn * (D.aθ θ Dn : O)))
    (hM : Tendsto D.Mθ (D.stages : Filter ℕ) atTop) (Ccoarse : ℚ)
    (hF5 : ∀ θ Dd, D.admissible θ Dd → AppGEndpoints.QLe
      (min (D.Mθ θ : ℚ) (AppGEndpoints.omega Dd - Ccoarse)) (vZ (D.aθ θ Dd)))
    (hmin : IsLeast (AppGEndpoints.DepthSet D.stages D.Mθ (fun θ Dd => vZ (D.aθ θ Dd))
      D.admissible) D.δo)
    (WU R : ℕ) (hR : 2 ≤ R) :
    ∀ᶠ θ in (D.stages : Filter ℕ), Odd.OddStageSource O WU R (D.Mθ θ) D.δo (η θ) (Good θ)
      (fun n => D.admissible θ n) ap (a θ) :=
  Odd.oddStageSource_eventually D.stages D.Mθ hM (fun θ Dd => vZ (D.aθ θ Dd)) D.admissible η Good
    ap a hcore
    (fun θ Dn k hsq hadm hle => by
      rw [hphase θ Dn hsq hadm]
      exact Odd.two_pow_dvd_stage_of_le_vZ O (D.Mθ θ) (ζ θ Dn) (by rwa [odd_vZ_eq]))
    Ccoarse hF5 hmin WU R hR

end ZInQ.Manuscript.RC.Wiring
