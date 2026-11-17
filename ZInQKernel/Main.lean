import ZInQKernel.Target
import ZInQKernel.Hypotheses.Height
import ZInQKernel.Hypotheses.HeightMin
import ZInQKernel.Hypotheses.Pole
import ZInQKernel.Model.Descent.MordellWeil
import ZInQKernel.Hypotheses.PrimePattern
import ZInQKernel.Hypotheses.PrimeAP
import ZInQKernel.Hypotheses.GreenTao
import ZInQKernel.Multiplication.Completeness.AP
import ZInQKernel.Assembly.Top
import ZInQKernel.Compiler.NodeBound

/-!
# The manuscript construction from H and pole completeness

PC is Theorem 5.2 for the manuscript's `x + 3ℓ` polynomial. This module keeps
the elementary assembly with a prime-pattern hypothesis. `MainGreenTao` proves
the progression input and gives the headline with only H and PC. Route K's
certified-rank assemblies are retired from the active build (issue #74).
-/

namespace ZInQ

/-- Every prime of `S_mul` is at most `D`: `p ≤ R = D`, where `R = D` comes from the catalogue
bound (`H_max, c_* < D`). -/
theorem Mult.le_heightD_of_mem_S_mul {p : ℕ} (hp : p ∈ Mult.S_mul) : p ≤ heightD :=
  (Mult.le_R_of_mem_S_mul hp).trans_eq ((Size.R_eq_D catalogueBound8).trans Mult.D_eq_heightD)

/-- **H implies its minimal form.** `SixContactMin` is the instance `S = S_mul`, `R = D` of the
six-contact estimate, admissible because `S_mul` consists of primes, contains the primes
`≤ 324`, and `max S_mul ≤ D` (`Mult.le_heightD_of_mem_S_mul`). -/
theorem sixContactMin_of_sixContactEstimate (hH : SixContactEstimate) : SixContactMin :=
  fun u hu => hH Mult.S_mul (fun _ hp => Mult.prime_of_mem_S_mul hp)
    (fun _ hp h => Mult.mem_S_mul_of_le hp h) _ le_rfl
    (fun _ hp => by exact_mod_cast Mult.le_heightD_of_mem_S_mul hp)
    (by exact_mod_cast Compiler.Precision.ten_pow_twelve_le_heightD) u hu

/-- The frozen target from H, manuscript PC and the fixed prime pattern. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_poleCompleteness
    (hH : SixContactMin) (hPC : PoleCompleteness)
    (h22 : FixedPrimePattern) : FrozenTarget :=
  Assembly.assembly Compiler.NodeCheck.haltingAddMulBound hH hPC
    (Mult.slopeRepresentation_of_fixedPrimePattern h22)

/-- The same construction using the proved route-AP assembly. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_poleCompleteness_goodPrimeAP
    (hH : SixContactMin) (hPC : PoleCompleteness) (hAP : GoodPrimeAP) : FrozenTarget :=
  Assembly.assembly_AP Compiler.NodeCheck.haltingAddMulBound hH hPC
    (Mult.slopeRepresentationAP_of_goodPrimeAP hAP)

end ZInQ
