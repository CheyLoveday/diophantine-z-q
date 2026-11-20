# (O.7) on the actual stage

Scoped stop. `DatumAt.inputs` constructs `Visibility.ComparisonInputs` on
`pmLift.geom` over `Adelic.levelOrder`. `thetaComparison_actual` proves
`Odd.ThetaComparison` given the listed arithmetic and pointwise geometry
inputs at every admissible pair. The actual support cannot be recovered
from the current `PMLocal` interface alone, and `PreLeaves.odd_staged`
remains open.

All 11 Lean files compile. The 44 theorem audits found only `propext`,
`Classical.choice`, and `Quot.sound`. Verified pieces include the
optimal embedding criterion, actual order-two stabilizer, split projector
classes, rational conjugacy and the single torus orbit quotient, trivial
norm descent at `D = 1`, and the reference reduction and orientation
congruences under the pointwise inputs.

Next: identify the actual weighted support with the oriented adelic
Picard fibers, derive the weight transports on the chosen representatives,
and supply norm descent for `D > 1` and the existing geometry and stage
joins. The Voight wording remains unverified; the report also records the
existing Jetchev–Kane level-one limitation. See
`docs/research/rc-o7-actual.md` for owners, precise boundaries, and the
manuscript check.

Final proof and report commit: `976e1688051e4bf88168f175f2ae3622d391ae1d`.
