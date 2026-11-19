import ZInQKernel.Contrib.OneProof.RC.AppGCoarse.Intrinsic
import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.Realization
import ZInQKernel.Contrib.OneProof.RC.Stages.PreparedStages

/-! The intrinsic instance uses the prepared squareclasses at the original
coefficient support and the moving Legendre test. Its ultrafilter and
precisions come from the existing detecting sequence. -/

noncomputable section

namespace ZInQ.Manuscript.RC.AppGCoarse

open Filter ZInQ.Contrib.CloudB3RC53 Wiring Visibility Stages O12StageVal

variable {ℓ : ℕ} (W : WData ℓ) (S : Finset ℕ) (hstar : ℤ)
variable {At : ℕ → ℕ → Prop} {c : ℕ} {excluded : Finset ℕ} (q : StageSequence At c excluded)

/-- The prepared filter of the original stages satisfies the arithmetic
preparation test for the rough companion construction. -/
theorem preparedSpec_of_intrinsic (h2 : 2 ∈ S) :
    PreparedSpec (withPreparedStages W S hstar q) := by
  intro n hn
  change positivePrepared S n at hn
  obtain ⟨hpos, hsf, hlocal⟩ := hn
  obtain ⟨h2d, hsq⟩ := hlocal 2 h2
  have hnd : ¬ (2 : ℤ) ∣ n := h2d
  have hodd : Odd n := Int.odd_iff.mpr (by omega)
  have h8 : n % 8 = 1 % 8 := Nonvanishing.modEq_eight_of_isSquareAt_two hodd odd_one
    (by simpa using hsq)
  exact ⟨hpos, hsf, by omega, fun p hp => (hlocal p hp).1⟩

/-- The actual increasing precisions and the full prepared coefficient
domain supply the stage choices for all fixed budgets. The arithmetic inputs
and the two Kummer comparisons concern this data before any address labels
are imposed. -/
theorem depths_of_prepared_stages {A : ℕ} {CE CR Cper Cnative : ℤ}
    (h33 : F3At (withPreparedStages W S hstar q) A CE)
    (h34 : Gz34CompAt (withPreparedStages W S hstar q) Cper)
    (h35 : Eq35At (withPreparedStages W S hstar q) A CR)
    (lam : ℕ → ℤ → ℤ) (ωN : ℕ) {Dw : ℤ} {cw : ℕ} :
    let V := withPreparedStages W S hstar q
    Odd.ThetaComparison V.Mθ V.aθ lam V.admissible ωN →
    (∀ i n, V.admissible i n → AnalyticRank (Etw ℓ n) 1 → ∀ k : ℕ,
      k ≤ V.Mθ i → (k : ℤ) ≤ V.jgen n - Cnative → (2 : ℤ) ^ k ∣ lam i n) →
    (∀ i n, V.admissible i n → ¬ AnalyticRank (Etw ℓ n) 1 → (2 : ℤ) ^ V.Mθ i ∣ lam i n) →
    WitnessValuation V lam Dw cw →
    ∃ C : ℚ, (∀ i n, V.admissible i n → AppGEndpoints.QLe
      (min (V.Mθ i : ℚ) (AppGEndpoints.omega n - C)) (vZ (V.aθ i n))) ∧
      ∃ δ : ℤ, IsLeast (AppGEndpoints.DepthSet V.stages V.Mθ
        (fun i n => vZ (V.aθ i n)) V.admissible) δ ∧
        ∀ B R : ℕ, 2 ≤ R → ∀ᶠ i in (V.stages : Filter ℕ),
          IntegerDepth (V.Mθ i) B R δ (fun n => V.admissible i n) (V.aθ i) := by
  dsimp only
  let V := withPreparedStages W S hstar q
  intro hO7 hnative htorsion hO2
  obtain ⟨Cdet, hvis⟩ := visibilityTarget_of_inputs V.toRCData
    ⟨lam, ωN, Cnative, hO7, hnative, htorsion⟩
  have hM : Tendsto V.Mθ (V.stages : Filter ℕ) atTop :=
    stages_advance_withStages (ℓ := ℓ) { W with S := S, hstar := hstar } q (positivePrepared S)
  exact depths_on_filter V V.admissible h33 h34 h35 hvis (fun _ _ hn => hn.1)
    lam ωN hO7 hO2 hM

#print axioms preparedSpec_of_intrinsic
#print axioms depths_of_prepared_stages

end ZInQ.Manuscript.RC.AppGCoarse
