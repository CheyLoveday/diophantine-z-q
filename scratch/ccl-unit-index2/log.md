# CCL unit-index log

## Step 1 — base and decision

**VERIFIED.** Base `c4d9b28eaf47ca591f1428fe97ca0a2d1ea5100f`. In
`ZInQKernel/OneProof/Main.lean:249–260`, `hRC` has type
`ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine` and is passed to
`poleCompleteness_of_restrictedConverseGenuine_casselsTatePairing` at line 259.
`ZInQKernel/Contrib/OneProof/SelmerTwoPower.lean:217–226` defines the type as
`ZInQ.Manuscript.RestrictedConverse SelmerCorankOne`. The closure of that
defining module and the closure of `ZInQKernel.OneProof.Main` both omit the
CCL module and every module in the older transport chain. This is sufficient
to exclude declaration dependencies, so an extra Lean import check is
unnecessary. [closure.py](closure.py) uses `git grep` on the base and
[closure.txt](closure.txt) records the results, including the default kernel
root and the separate RC proof candidate `Wiring.Leaves`. The latter imports
`PrintsArith.Bundle` and `PrintsArith.Heegner` but none of the older transport
modules. The bundle uses other declarations in `Heegner.lean`; its reference
to the CCL declaration is a comment. The staged comparison enters the shared
transport via `CommonCoordinate19E2.lean` importing `CommonCoordinate18E2.lean`.
**Decision: step 2a.**

**VERIFIED.** In `PrintsArith/Heegner.lean:138–177`, write
`Tr(d,q) = ∑ τ ∈ D.relGal d q, Affine.Point.map τ.toAlgHom (D.y (d*q))`
and `F = D.frob d q`.

- `D.Admissible d q := 0 < d ∧ Nat.Coprime d (2 * D.N * D.DK.natAbs) ∧ q.Prime ∧
  ¬ q ∣ 6 * d * D.N * D.DK.natAbs`.
- `D.NormRelations` is the conjunction of the following statements for every
  admissible pair. If `jacobiSym D.DK q = -1`, then
  `Tr(d,q) = (E.LFunction q : ℤ) • D.y d`. If `jacobiSym D.DK q = 1`, then
  `Tr(d,q) = (E.LFunction q : ℤ) • D.y d -
  Affine.Point.map F.toAlgHom (D.y d) - Affine.Point.map F⁻¹.toAlgHom (D.y d)`.
- `CCLThm2_15Applied E Anchor := ∃ D : HeegnerPointData E, D.NormRelations ∧ Anchor D`.
  `HeegnerPointData.zero_normRelations` proves the equations for the zero system.

The [base grep](consumer-refs.txt) records the CCL declarations and references.
The [consumer inventory](consumers.md) records the premises and downstream uses.
The previous modulo-16 proof and conductor bound are verified in
`scratch/ccl-unit-index/Check.lean`. The congruence at level divisible by four
reduces modulo 16 since `B² − D = 4AC` and `4 ∣ A`. Modulo 8,
`2² ≡ −4`.
