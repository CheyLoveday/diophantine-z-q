# rc-picard-fibers

Scoped stop at two placewise inputs for the Picard torsor at the
actual (O.7) stage. The finite idele valuation map is onto the
nonzero fractional ideals. Its kernel is the integral ideles and its
diagonal field units give principal ideals. After rational framing,
admissible adelic representatives exhaust the actual weighted support
orbits. Within one orientation, the centralizing adeles act
transitively up to right integral units. The rational centralizer is
the embedded field unit group.

`picardFibers_of_local` gives one `ClassGroup (𝓞 F)` equivalence per
actual orientation, and `orbitFibers_of_local` supplies the existing
constructor when given the two local inputs. They are the completed
quadratic torus chart with the integral unit intersection, and a local
conjugating unit realizing each prescribed orientation. The full odd
filter includes splitting at all primes of `2N`. Voight remains the
existing GLUE input through `exists_reference_embedding`. No print or
leaf was added, and no new manuscript error was found in this step.

All 11 proof modules compiled. The audit checked 292 theorems and 59
definitions and found only `propext`, `Classical.choice`, and
`Quot.sound`. The report, log and per-theorem output are at
`docs/research/rc-picard-fibers.md` and `scratch/rc-picard-fibers/`.

Final proof and report SHA: `1e1aa792d0c26923b9e6ac62b058713ecdd061c4`.
The final branch SHA includes this handoff and is returned by
`git log -1 --format=%H -- .fleet/rc-picard-fibers.md`.
