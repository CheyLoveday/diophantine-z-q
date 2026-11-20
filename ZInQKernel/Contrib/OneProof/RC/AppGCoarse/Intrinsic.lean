import ZInQKernel.Contrib.OneProof.RC.O12StageVal.Apply

/-! Appendix G, tex 10171–10234, on the domain of the original odd source.
The domain is passed independently of the address support in `WData`. -/

noncomputable section

namespace ZInQ.Manuscript.RC.AppGCoarse

open Filter ZInQ.Contrib.CloudB3RC53 Wiring Visibility
open O12StageVal

variable {ℓ : ℕ} (W : WData ℓ) (domain : ℕ → ℤ → Prop)

/-- Read visibility on a specified coefficient filter, with the original stages,
integers and arithmetic data. -/
abbrev onFilter : WData ℓ := { W with admissible := domain }

/-- (F.4) and (O.8) give (F.5) uniformly on the specified domain. Only visible
indices use a rank-one index comparison; coefficients at or above precision
already satisfy the truncated inequality. -/
theorem coarse_on_filter {A : ℕ} {CE CR Cper Cdet : ℤ}
    (h33 : F3At W A CE) (h34 : Gz34CompAt W Cper) (h35 : Eq35At W A CR)
    (hvis : VisAt (onFilter W domain) Cdet) (hprep : ∀ i n, domain i n → W.prepared n) :
    ∃ C : ℚ, ∀ i n, domain i n → AppGEndpoints.QLe
      (min (W.Mθ i : ℚ) (AppGEndpoints.omega n - C)) (vZ (W.aθ i n)) :=
  coarseF5_of_leaves (onFilter W domain) h33 h34 h35 hvis hprep

/-- The same `Dw` works at arbitrarily high precision. The valuation is
`9 + ω(N) + cw` by the exact order calculation for the integer multiplier. -/
theorem fixed_witness_on_filter (lam : ℕ → ℤ → ℤ) (ωN : ℕ) {Dw : ℤ} {cw : ℕ}
    (hO7 : Odd.ThetaComparison W.Mθ W.aθ lam domain ωN)
    (hO2 : WitnessValuation (onFilter W domain) lam Dw cw)
    (hM : Tendsto W.Mθ (W.stages : Filter ℕ) atTop) :
    ∀ᶠ i in (W.stages : Filter ℕ), domain i Dw ∧
      vZ (W.aθ i Dw) = (((9 + ωN + cw : ℕ) : ℤ) : WithTop ℤ) ∧
      (((9 + ωN + cw : ℕ) : ℤ) : WithTop ℤ) < W.Mθ i := by
  have hprec : ∀ᶠ i in (W.stages : Filter ℕ), 9 + ωN + cw < W.Mθ i :=
    hM.eventually (eventually_gt_atTop _)
  change ∀ᶠ i in (W.stages : Filter ℕ), domain i Dw ∧ (2 : ℤ) ^ cw ∣ lam i Dw ∧
    ¬ (2 : ℤ) ^ (cw + 1) ∣ lam i Dw at hO2
  filter_upwards [hO2, hprec] with i hi hMi
  obtain ⟨hD, hdiv, hndiv⟩ := hi
  obtain ⟨ζ, hζ, hcong⟩ := hO7 i Dw hD
  refine ⟨hD, ?_, ?_⟩
  · rw [← odd_vZ_eq]
    exact Odd.witness_vZ ωN (W.Mθ i) cw hζ hdiv hndiv hcong hMi
  · exact_mod_cast hMi

/-- The minimum is attained by a bounded-weight sequence on the very same
domain on which the coarse bound holds. The witness used for nonemptiness
need not itself attain the minimum. -/
theorem minimum_on_filter (C : ℚ)
    (hF5 : ∀ i n, domain i n → AppGEndpoints.QLe
      (min (W.Mθ i : ℚ) (AppGEndpoints.omega n - C)) (vZ (W.aθ i n)))
    (lam : ℕ → ℤ → ℤ) (ωN : ℕ) {Dw : ℤ} {cw : ℕ}
    (hO7 : Odd.ThetaComparison W.Mθ W.aθ lam domain ωN)
    (hO2 : WitnessValuation (onFilter W domain) lam Dw cw)
    (hM : Tendsto W.Mθ (W.stages : Filter ℕ) atTop) :
    ∃ δ : ℤ, IsLeast (AppGEndpoints.DepthSet W.stages W.Mθ
      (fun i n => vZ (W.aθ i n)) domain) δ := by
  obtain ⟨δ, hδ, -⟩ := AppGEndpoints.oddMinimumF6_proof W.stages W.Mθ
    (fun i n => vZ (W.aθ i n)) domain C hF5
    ⟨Dw, (↑(9 + ωN + cw : ℕ) : ℤ), fixed_witness_on_filter W domain lam ωN hO7 hO2 hM⟩
  exact ⟨δ, hδ⟩

/-- Install the attained minimum in the skeleton data and apply the existing
consumer. The lower bound covers every squarefree index of the specified
domain, including those above the finite weight cutoff used in the proof. -/
theorem depths_on_filter {A : ℕ} {CE CR Cper Cdet : ℤ}
    (h33 : F3At W A CE) (h34 : Gz34CompAt W Cper) (h35 : Eq35At W A CR)
    (hvis : VisAt (onFilter W domain) Cdet) (hprep : ∀ i n, domain i n → W.prepared n)
    (lam : ℕ → ℤ → ℤ) (ωN : ℕ) {Dw : ℤ} {cw : ℕ}
    (hO7 : Odd.ThetaComparison W.Mθ W.aθ lam domain ωN)
    (hO2 : WitnessValuation (onFilter W domain) lam Dw cw)
    (hM : Tendsto W.Mθ (W.stages : Filter ℕ) atTop) :
    ∃ C : ℚ, (∀ i n, domain i n → AppGEndpoints.QLe
      (min (W.Mθ i : ℚ) (AppGEndpoints.omega n - C)) (vZ (W.aθ i n))) ∧
      ∃ δ : ℤ, IsLeast (AppGEndpoints.DepthSet W.stages W.Mθ
        (fun i n => vZ (W.aθ i n)) domain) δ ∧
        ∀ B R : ℕ, 2 ≤ R → ∀ᶠ i in (W.stages : Filter ℕ),
          IntegerDepth (W.Mθ i) B R δ (fun n => domain i n) (W.aθ i) := by
  obtain ⟨C, hF5⟩ := coarse_on_filter W domain h33 h34 h35 hvis hprep
  obtain ⟨δ, hδ⟩ := minimum_on_filter W domain C hF5 lam ωN hO7 hO2 hM
  let D : RCData ℓ := { W.toRCData with admissible := domain, δo := δ }
  exact ⟨C, hF5, δ, hδ, fun _ _ hR =>
    integerDepth_of_data D domain hM C hF5 hδ hR⟩

/-- A restriction preserves a known intrinsic minimum exactly when it still
contains a bounded-weight sequence attaining that depth. -/
theorem restricted_minimum_iff (restricted : ℕ → ℤ → Prop)
    (hsub : ∀ i n, restricted i n → domain i n) {δ : ℤ}
    (hδ : IsLeast (AppGEndpoints.DepthSet W.stages W.Mθ
      (fun i n => vZ (W.aθ i n)) domain) δ) :
    IsLeast (AppGEndpoints.DepthSet W.stages W.Mθ (fun i n => vZ (W.aθ i n)) restricted) δ ↔
      δ ∈ AppGEndpoints.DepthSet W.stages W.Mθ (fun i n => vZ (W.aθ i n)) restricted := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  intro r hr
  obtain ⟨B, ns, hev⟩ := hr
  exact hδ.2 ⟨B, ns, hev.mono fun i hi => ⟨hsub i (ns i) hi.1, hi.2⟩⟩

#print axioms coarse_on_filter
#print axioms fixed_witness_on_filter
#print axioms minimum_on_filter
#print axioms depths_on_filter
#print axioms restricted_minimum_iff

end ZInQ.Manuscript.RC.AppGCoarse
