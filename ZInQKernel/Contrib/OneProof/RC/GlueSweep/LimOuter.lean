import ZInQKernel.Contrib.OneProof.RC.Limits.Lemmas
import ZInQKernel.Contrib.OneProof.RC.Rings.LimitsBridge

/-!
# Lane RC22 (glue sweep, limits): the outer evaluation over the genuine `𝒪`

Manuscript tex 4719–4744, proof of Lemma `ex:limits-outer-evaluation`. Lane RC6
(`RC/Limits/OuterDVR.lean`, `RC/Limits/Lemmas.lean`) states (5.3) and its consequences for an
arbitrary DVR `R` with uniformizer `ϖ` and records "passing from `Λ_(2)` to its 2-adic completion
`𝒪`" as GLUE. Lane RC20 discharges this for the genuine `𝒪 = Determinant.OO`
(`Rings/OValuation.lean`: `instIsDiscreteValuationRingOO`, `irreducible_two_OO`, `instCharZeroOO`;
`Rings/Completion.lean`: `adicCompletionLambdaTwoEquiv : AdicCompletion (2) Λ_(2) ≃+* 𝒪`;
`Rings/LimitsBridge.lean`: `outerDVR_genuine`, (5.3) for copies of `𝒪`). The remaining RC6
consumer of the uniformizer is the approximate-cycle statement; its form over `𝒪` is below.
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Lim

open scoped Matrix
open ZInQ.Manuscript.RC.Limits ZInQ.Manuscript.RC.Rings ZInQ.Manuscript.RC.Determinant

/-- **Approximate cycles suffice, over the genuine `𝒪`** (tex 4740–4742). For copies `𝒪_j = 𝒪`
and the uniformizer `ϖ = 2`: if the crossed-homomorphism defect of `w_j` is an integral evaluation
`e_j(x, y)(dw_j)` with `v₂(dw_j) →_𝒰 ∞`, then the image `w_∞` in `𝒪_∞` is an actual crossed
homomorphism of the product group for the outer representation. PROVED, from no remaining input
beyond the data (RC6's DEPARTURE "stated for any DVR; 𝒪 is GLUE" is discharged).

Consumer: RC6's `ex_limits_outer_evaluation_approximate_cycles` (hypothesis `hϖ : Irreducible ϖ` and
the GLUE completion step); dischargers: lane RC20's `irreducible_two_OO`,
`instIsDiscreteValuationRingOO` (with `outerDVR_genuine` for (5.3) itself). -/
theorem ex_limits_outer_evaluation_approximate_cycles_O {ι : Type*} (U : Ultrafilter ι)
    {G : ι → Type*} [∀ j, Group (G j)] {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k]
    (ρ : ∀ j, G j →* Matrix n n OO) (w : ∀ j, G j → n → OO)
    (e : ∀ j, G j → G j → Matrix n k OO) (dw : ι → k → OO)
    (he : ∀ j (x y : G j), cocycleDefect ρ w j x y = e j x y *ᵥ dw j)
    (hdw : ∀ c, Filter.Tendsto (fun j => IsDiscreteValuationRing.addVal OO (dw j c))
      (U : Filter ι) (nhds ⊤))
    (g h : ∀ j, G j) :
    outerRep U (2 : OO) ρ g *ᵥ outerCochain U (2 : OO) w h - outerCochain U (2 : OO) w (g * h) +
      outerCochain U (2 : OO) w g = 0 :=
  ex_limits_outer_evaluation_approximate_cycles U irreducible_two_OO ρ w e dw he hdw g h

end ZInQ.Manuscript.RC.GlueSweep.Lim
