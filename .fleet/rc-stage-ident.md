`inputs_of_selected` identifies the Appendix F theta stage with the selected
skeleton stage. The order has the newform level of the skeleton curve; the
prime and precision come from the selected sequence; the finite detector is
the evaluation in `actualForStages`. The index and Fourier support are stated
directly against `PMLocal.m` and `PMLocal.support`. The valuation and the source
use the same full intrinsic filter. The primes over 6ℓ belong to the Fourier
support, its primes divide the selected type conductor, and the operator
budget is `B - 1` with truncation `2`. The theorem supplies these data to
`inputs_of_pm`.

All three files in `ZInQKernel/Contrib/OneProof/RC/StageIdent/` compiled
individually with `lake env lean -j1`. The 23 axiom audits reported only
`propext`, `Classical.choice`, and `Quot.sound`. No new printed-form leaf.

The remaining inputs are the selected valid stage, actual `PMLocal`,
adelic and supersingular geometry, (O.7), exact Fourier vanishing, App G
depth, and the existing (O.12) constituent and local block inputs. The
inherited filter issue matters here: later address exclusions must not be
read as Fourier sieves. See `docs/research/rc-stage-ident.md` for the exact
hypotheses, owners, and manuscript checks; see `scratch/rc-stage-ident/log.md`
for verification results.

Lean, report, and log SHA: `f2902a3ad17eb326615abb90adaae26680b36136`.
The final branch commit is this status-only commit, whose SHA is reported
separately because it cannot appear in its own committed contents.
