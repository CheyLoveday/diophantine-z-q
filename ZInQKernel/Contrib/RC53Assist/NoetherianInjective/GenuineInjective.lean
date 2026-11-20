import ZInQKernel.Contrib.RC53Assist.NoetherianInjective.BassPapp
import ZInQKernel.Contrib.RC53Assist.NoetherianInjective.CochainFree
import ZInQKernel.Contrib.OneProof.RC.Local.TameLocalQuotientStage

/-!
# The genuine local cochain terms are injective

For every Noetherian self-injective stage coefficient ring, the actual
continuous local cochain modules with finite discrete free coefficients
are injective. Their freeness comes from the profinite locally constant
function description over an arbitrary scalar ring, not a local-ring or
nilpotent-maximal-ideal assumption. Baer's criterion supplies injectivity
for free modules of arbitrary rank. Degree zero is kept and only negative
zero-extension degrees are trivial.

This proves the original local-cochain proposition without a literature
print, a desired injectivity premise, or a changed coefficient topology.
Source: the local quotient at stage rings, manuscript tex 3470–3480.
-/

noncomputable section

set_option autoImplicit false

namespace ZInQ.Manuscript.RC.Local

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.NoetherianInjective

/-- Kind: PROVED. The original genuine local-cochain injectivity input is supplied outright. -/
theorem genuineCochainsInjective_proved : GenuineCochainsInjective := by
  intro K _ _ S k _ _ _ _ M _ _ _ _ _ _ _ _ _ w n
  letI : Module.Finite k M := Module.Finite.of_finite
  letI : Module.Free k
      ((localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) M w).X n) :=
    free_localCx_profinite k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) M w n
  exact injective_of_free_noetherian

/-- Kind: PROVED. The existing bounded-below local-complex consumer has no injectivity premise. -/
theorem genuineCochainsKInjective_proved : GenuineCochainsKInjective :=
  genuineCochainsKInjective_of genuineCochainsInjective_proved

end ZInQ.Manuscript.RC.Local
