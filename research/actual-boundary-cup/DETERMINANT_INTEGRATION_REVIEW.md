# Independent determinant and integration review

Reviewer: Codex `/root/boundary_cup_attack`, 2026-11-09.
This reviewer did not author the determinant packet or root integration
argument. The reviewer did author the separate boundary packet; accordingly
this is **not** independent approval of that packet's own boundary proof.
Its independent review is supplied by the orthogonal agent. All reviews here
are internal model reviews, not external mathematical validation.

### 1) Verification target

Target1: the actual determinant-coordinate bridge in
`research/strict-determinant-bridge/DERIVATION.md`, with its application and
computational checks. Target2: the assembled root argument in
`research/arithmetic-switch-integration/{SPEC,DERIVATION}.md` and the
end-to-end finite-model checker. Exact reviewed hashes are retained in
`evidence/review/reviewed-inputs.json`.

The determinant ledger requires actual perfect triangles over one DVR/domain,
finite-side generic dimensions(1,1), actual nonzero localization, independent
boundary directions, actual quotient functionals and integral determinant
bases. The normalization qS=-qF is required only for the final corollary.
The integration adds the source's actual local cup/trace, actual permitted
orthogonal inverse, and the nonzero mixed-cup value for its rank inference.
None is inferred from a Lean or finite-model pass.

Source lookup read V13 paired-functional and coordinate definitions3842–4029,
strict derivative triangles5021–5093; frozen Coordinate.lean
`coordinate_of_closed_frame`183–199, CommonStrict.lean
`raw_side_coordinate`141–174, and UnitCriterion.lean
`unitRelated_scale_iff`50–62; source-bound prior arithmetic DERIVATION§5.
The earlier wedge method and common strict factor are reused, with the new
explicit match to the actual integral generator and frozen sign convention.
The model checker does not compute the actual global Galois objects.

### 2) Independent re-derivation (outline)

Use the basis B=[z,x] in the source and T=[y,Dx] in the target. The boundary
matrix becomes diag(0,1), the actual class becomes e1, and the actual closed
functional becomes λ(y)e1*. In that normal form adj(D)=diag(1,0), so the
class-functional coordinate is λ(y). Transporting the source and target
basis wedges back gives det(B)λ(y)/det(T). This independently fixes the
cofactor sign, without starting from either branch's claimed scalar formula.

For the finite branch T=[b,a], det(T)=-θ; for the singular branch T=[a,b],
det(T)=θ and det(JB)=δ det(B). Thus uMatF=-ηqF/θ and uMatS=δηqS/θ.
With qS=-qF, uMatS=δuMatF. A simultaneous alternative determinant convention
can multiply both by a common sign; a unilateral sign flip cannot preserve
the displayed exact equation. The packet explicitly distinguishes that shared
sign from valuation-invariant convention changes.

The determinant-line comparison is then one-dimensional tensor algebra.
Both triangles use the same map of the strict determinant line into
(det W)*. If e_str maps to cΩ*, both triangle generators map to c times
matrix generators. The actual tensor is independently identified through
its kernel/cokernel exact sequence, so its scalar in the integral triangle
generator is c^-1uMat. Arbitrary integral generator ratios αF,αS are units.
This is not the generally false claim that uActual itself directly satisfies
the unscaled HasCoordinate matrix equation.

For an additional common disk in degrees1,2 with differential d≠0, the
inverse determinant generator maps to d. Directly, the lower adjugate block
of diag(d,D) is d adj(D); therefore the full coordinate is uMat/d. Both
calculations agree. A nonunit d is not an integral contractible disk.

The integration rank deduction is valid with its stated nonzero guard:
finite exactness gives W dimension2 and a≠0; rF(a)=0 and rF(b)=qF≠0 prove
independence; derivative localization puts Jv in ker∂S and b≠0 forces
rank∂S=1. No singular-rank hypothesis is used to define λB: its source
definition applies to an actual retained class before the rank is known.
This yields the actual I=Empty matrices and closed rows. The shared c then
transports their matrix result to the stored actual determinant coordinate.

### 3) Checks

**Plug-back:** the normal matrix diag(0,1) gives coordinate1 for z=e1,
λ=e1*. In a second explicit frame, v=e1, x=e2, a=e1, b=e2, J swaps e1/e2,
AF=[[0,1],[0,0]], AS=[[0,0],[1,0]]. Direct outer products and adjugates give
uF=-qF and uS=-qS, agreeing with δ=-1 and the packet's formulas.

**Boundary cases:** λ=0 gives zero coordinate and is covered by the algebra;
it does not justify rank independence. v=0 violates the required area guard.
Fractional complements and c nonunit are permitted. The fully integral
Z_(2) disk2 example has coordinates(-1/2,+1/2), so common torsion shifts the
absolute valuation and still cancels from the comparison. Two different
strict scalars or an independent functional rescaling can change valuations.

**Computation rerun:** independently ran the current determinant script with
its sole output write intercepted in memory, so author evidence was not
modified. The generated JSON was byte-identical to its retained receipt.
Results:180 rank-one models,2160 full adjugate checks,360 triangle formulas,
1440 complement changes,1440 quotient-lift changes,1440 common nonunit-disk
checks, and five detected negative controls. The generic matrices are
explicitly labelled K-matrices; they are not misreported as integral models.

Independently reran the root end-to-end model checker:1836 exact rational
models,32 all-vector grid equations per model, and seven negative controls
passed. The checker constructs local cup evaluations before deriving rows,
checks cycle/closedness, verifies every cofactor entry, and retains shared
strict and unit basis factors. Rerun outputs are under `evidence/review/`.
All these are finite algebra diagnostics. They do not establish arithmetic
existence, rank hypotheses, actual global duality or group-ring descent.

### 4) Discrepancy report (if any)

No mathematical blocker found in the reviewed bounded determinant or root
integration inference. The old arithmetic §5 has an opposite shared global
sign; the new determinant packet correctly records this and does not alter
the old proof receipt. The valuation conclusion survives that convention.

Remaining source interfaces are explicit: actual cups/trace and isotropy,
localized inverse existence, the actual retained finite tuple and inner-limit
compatibility, nonzero local pairing for rank, and universal group-ring
integral descent. These are not silently discharged by the new coordinate
bridge. In particular the scalar field proof cannot instantiate a nontrivial
binary group ring as Subring K or infer an integral universal element solely
from characterwise unit values.

### 5) Certification result

**CERTIFIED under the displayed source and algebraic assumptions, within
this bounded internal review.** The determinant-coordinate inference and
root integration argument are sound at the exact hashes in the review binding.
The independent finite-check reruns support the signs, scaling, and adverse
interface guards. This is not certification of the entire arithmetic switch,
its full source constructions, a Lean determinant-functor formalization,
the restricted converse, or the main Diophantine theorem. The review's author
is not an independent reviewer of the separately authored boundary packet;
that packet requires its own nonauthor review.


### Editorial rebind and reader-document claim review

The integrator subsequently changed the combined DERIVATION's six display
blocks from `\[`/`\]` to `$$`. I independently reversed precisely its twelve
delimiter lines and recovered SHA-256
`9983b1cd77a423e346728589bc90b9605e68eec59a794bd62638c093f8cc0fe0`,
the exact original source reviewed above. Thus no mathematical byte changed.
The revised DERIVATION SHA-256 is
`b5e64b29ba2c5b2bcffc3d56ed4c6d512dad950d9c10c58d22ba7d62834295c4`.
The source/specification/Lean proofs and check scripts are otherwise unchanged.
I accept this editorial-only rebind without another proof build. The original
native receipt remains the original evidence, with its original hashes.
This was a source-fidelity check, not a target parser or visual typesetting check.

I also read the new integration README and VERIFICATION record for claim
accuracy and compared their stated root counts, axiom audit, source preservation,
finite-check counts and limitations with the retained combined receipts.
They correctly distinguish fourteen newly checked formal helpers, conditional
ordinary source-interface proofs, and unresolved full arithmetic constructions.
The development-profile claim is explicitly limited to those helper roots;
paranoid, external replay, clean reproduction and whole-paper acceptance are
not claimed. Their present local/uncommitted status is consistent with this
review's observation. Both documents are accepted at their hashes in the
updated reviewed-input binding. Detailed editorial evidence is retained in
`evidence/review/editorial-rebind.json`. This acknowledgment does not enlarge
the certification scope stated above.

I also read the final editorial-binding paragraph in VERIFICATION.md and
verified all native receipt input hashes: the combined DERIVATION is its only
changed input. The root-retained original copy has the exact original hash.
The final VERIFICATION hash accepted here is
`ec17b5f20cacbe94a921ca38f800c3b34ab86c5c7f1cb1c541b1c918cdcac386`.
