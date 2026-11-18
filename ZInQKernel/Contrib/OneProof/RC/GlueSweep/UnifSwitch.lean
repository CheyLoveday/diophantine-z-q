import ZInQKernel.Contrib.CloudB3RC53.UniformSwitch.Outer
import ZInQKernel.Contrib.OneProof.RC.Rings.OValuation

/-!
# Lane RC22 (glue sweep), share `Unif`: lane RC16's Proposition from the shared switching data

Manuscript `diophantine_zq.tex` (11/5), Proposition `ex:limits-uniform-lower-bound`
(tex 4909–5205).

Lane RC16's Proposition (`Uniform.exLimitsUniformLowerBound`; with its GLUE `ValuationOfO` removed by
lane RC20 as `Rings.exLimitsUniformLowerBound_genuine`) and its height-one regularity
(`Uniform.mem_lambdaHalf_of_regularity`) take Elliot's switching processes as inputs: `outer`
(instances of `OuterSwitchProcess`) and `regular`/`hreg` (instances of `RegularitySwitchProcess`).
The shared top layer (`ZInQ.Contrib.CloudB3RC53.UniformSwitch`) now builds both structures from
genuine models: `OuterSwitchData.toProcess` (outer models over `K_out`, inner minimal models over
`Frac 𝒪`; fields `pos` and `terminal` PROVED) and `HeightOneSwitchData`/`exists_process_of_switchData`
(two-term models over `Λ_𝔭`; fields `pos` and `terminal` PROVED), the switch fields coming from
GLUE inputs that carry the hypotheses of RC16's algebraic cores. This file states RC16's two
theorems with their process inputs replaced by exactly those data. Every theorem here is a bridge of
kind `PROVED` from the hypotheses that remain (the fields of the two data structures, listed in each
docstring).
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Unif

open Filter ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53

/-- **Height-one regularity `u ∈ Λ[1/2]` from the shared height-one switching data**
(tex 4976–5200). Lane RC16's `mem_lambdaHalf_of_regularity` asks, unless `u = 0`, for a
`RegularitySwitchProcess (RegularAtPrime 𝔭)` starting at `u` at every height-one prime `𝔭 ≠ (2)`;
these are produced by `UniformSwitch.exists_process_of_switchData` from switching data over the
genuine `Λ_𝔭` whose starting stage has coordinate `u`. This also applies at the unknown
full-corank-one base (tex 5196–5200).
Kind: PROVED, from `hreg`, i.e. the fields of `UniformSwitch.HeightOneSwitchData` at each `𝔭`: the
two-term stages (`TwoTermStage`: model, integral cycle, integral closed functional, coordinate), and
the GLUE fields `sign_sum` (tex 5035–5054), `primitive` (tex 4986–4992), `switch_mixed`,
`switch_single` (tex 4997–5003, 5116–5153; `CoordStep`, `QuadMixedDims`, `QuadSingleDims`,
`NonquadDims`). Consumer: `ZInQ.Manuscript.RC.Uniform.mem_lambdaHalf_of_regularity`; discharger:
`ZInQ.Contrib.CloudB3RC53.UniformSwitch.exists_process_of_switchData`. -/
theorem mem_lambdaHalf_of_switchData (u : FractionRing Lambda)
    (hreg : u = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
      ∃ (D : UniformSwitch.HeightOneSwitchData (UniformSwitch.toFracAt P)
          (IsLocalRing.residue (Localization.AtPrime P))) (S₀ : D.Stage), (D.stage S₀).u = u) :
    u ∈ lambdaHalfToFrac.range :=
  mem_lambdaHalf_of_regularity u (hreg.imp id fun h P _ hP hne => by
    obtain ⟨D, S₀, hS₀⟩ := h P hP hne
    exact UniformSwitch.exists_process_of_switchData P u D S₀ hS₀)

/-- **Proposition `ex:limits-uniform-lower-bound` from the shared switching data, over the genuine
`𝒪`** (tex 4909–5202). Lane RC20's `Rings.exLimitsUniformLowerBound_genuine` (RC16's Proposition
with its GLUE `ValuationOfO` discharged) with its two process inputs replaced:
* `outer`: for every sequence of instances, outer switching data
  (`UniformSwitch.OuterSwitchData` over `v = v_𝒪`, the fixed nonprincipal ultrafilter) whose starting
  stage has the primitive coordinates' valuations; RC16's `OuterSwitchProcess` is
  `UniformSwitch.OuterSwitchData.toProcess` (`pos`, `terminal` PROVED there);
* `regular`: at every height-one prime `𝔭 ≠ (2)`, height-one switching data over `Λ_𝔭` starting at
  the primitive coordinate, or the coordinate is zero; RC16's `RegularitySwitchProcess` is
  `UniformSwitch.exists_process_of_switchData`.
Kind: PROVED, from the fields of the two data structures: for `OuterSwitchData`, the stages
(`OuterStage`: outer model with a nonzero outer kernel vector, inner minimal models with cycles,
closed functionals and admissible complements) and the GLUE fields `minor_link` (tex 4706–4714,
4957–4959), `cycle_integral`, `functional_bound` (`v λ_j ≥ −a`, the paired-functional exponent) and
`switch` (tex 4940–4950; `NonquadDims`, `SwitchCoordData`); for `HeightOneSwitchData`, as in
`mem_lambdaHalf_of_switchData`. Consumer: `ZInQ.Manuscript.RC.Rings.exLimitsUniformLowerBound_genuine`
(hence RC16's `exLimitsUniformLowerBound`); dischargers:
`ZInQ.Contrib.CloudB3RC53.UniformSwitch.OuterSwitchData.toProcess`,
`ZInQ.Contrib.CloudB3RC53.UniformSwitch.exists_process_of_switchData`. -/
theorem exLimitsUniformLowerBound_switchData (A : ℕ) {Inst : Type*}
    (uprim : Inst → FractionRing Lambda) {Kout : Type*} [Field Kout]
    (outer : ∀ inst : ℕ → Inst, ∃ (a : ℕ)
      (P : UniformSwitch.OuterSwitchData (Kout := Kout) (J := ℕ) Rings.vO
        (Filter.hyperfilter ℕ) a) (S₀ : P.Stage),
      ∀ᶠ j in ((Filter.hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ),
        Rings.vO ((P.stage S₀).coord j) = Rings.vO (Rings.iotaO (uprim (inst j))))
    (regular : ∀ i, uprim i = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 →
      P ≠ Ideal.span {2} →
      ∃ (D : UniformSwitch.HeightOneSwitchData (UniformSwitch.toFracAt P)
          (IsLocalRing.residue (Localization.AtPrime P))) (S₀ : D.Stage), (D.stage S₀).u = uprim i) :
    ∃ C : ℕ,
      (∀ i, (((-C : ℤ)) : WithTop ℤ) ≤ Rings.vO (Rings.iotaO (uprim i))) ∧
      (∀ i, ∃ uh : LambdaHalf, lambdaHalfToFrac uh = uprim i ∧
        (2 : LambdaHalf) ^ C * uh ∈ (algebraMap Lambda LambdaHalf).range ∧
        ∀ (j_rc ω sh shk C₀ : ℤ) (P : Finset ℕ) (t : ℕ → ℤ),
          centralSpecialization uh ≠ 0 → (∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 2) → P.card ≤ A →
          |Padic.valuation (centralSpecialization uh) -
              (2 * j_rc - 4 * ω - sh - shk - ∑ p ∈ P, t p)| ≤ C₀ →
          2 * j_rc ≥ 4 * ω + sh + shk - ((C : ℤ) + (C₀ + 2 * A))) :=
  Rings.exLimitsUniformLowerBound_genuine A uprim
    (fun inst => by
      obtain ⟨a, P, S₀, h⟩ := outer inst
      exact ⟨a, P.toProcess Rings.vO _, S₀, h⟩)
    (fun i => (regular i).imp id fun h P _ hP hne => by
      obtain ⟨D, S₀, hS₀⟩ := h P hP hne
      exact UniformSwitch.exists_process_of_switchData P (uprim i) D S₀ hS₀)

end ZInQ.Manuscript.RC.GlueSweep.Unif
