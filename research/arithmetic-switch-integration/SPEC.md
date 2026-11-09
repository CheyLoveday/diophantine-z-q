# Actual arithmetic switch interfaces — development specification

Date: 2026-11-09. Base: `fb29fe2bc6968e178a6458357c437574221b5338`.
Scope: the boundary–cup, orthogonal-comparison and determinant interfaces for
one eligible inner rank-one derivative switch. This is a research packet.
The canonical manuscript and the frozen 39-target packet are preserved.

## Objects and fixed conventions

Use the actual retained global cochains, local conditions, comparison maps,
cup products, isotropy homotopies and compact-support trace of V13. The actual
functionals are `PD(-, j_U^-1 c(z))`. The same trace and coefficient pairing
are used in both local conditions. A generic vector-space model is taken only
after the indicated inner construction and justified scalar localization.

For the cohomological rank-one consumer assume finite-side cohomology in
degrees one and two with dimensions `(1,1)`, and the actual finite class A
spanning H¹ with finite localization `v != 0`. Its actual derivative B has
coordinates `(0,Jv)`. Both strict triangles retain D⁰. No isomorphism between
the finite and singular Selmer complexes is required.

## Required interfaces

1. Evaluate the actual mapping-fibre product at a pure opposite boundary.
   The local-condition representative differs from the localization of the
   global partner by an actual coboundary. Derive that correction and its
   vanishing under the local trace. Identify the global compact-support
   trace square and both actual partners explicitly.
2. Construct the cone comparison from the actual local comparison and its
   homotopy. Prove its global component is the identity. A homotopy inverse
   must consequently preserve global cohomology and derivative localization.
   The existence of that inverse remains tied to the source's permitted
   localized contractions.
3. Set `W = H²(C_str ⊗ K)`. Derive dimension two and the actual boundary maps
   and pulled-back rows. Use the same closed functional, with its specified
   normalization, throughout. Prove independent boundary directions with
   the actual nonzero local trace/cross pairing, or a separately justified
   exact-annihilator argument. Zero-capable algebra alone is insufficient.
4. Compare the actual determinant tensors through the two distinct exact
   triangles. Write the image of their common strict integral generator as
   `c (w1 ∧ w2)*`. Prove `u_actual = c^-1 u_matrix` on both sides in compatible
   frames, allowing explicit integral-unit changes of retained bases. Retain
   strict torsion and allow fractional local complements.
5. Apply the unchanged conditional common-strict/unit theorem only after
   identifying its class vectors, maps, rows and determinant coordinates.

## Validation and claim boundaries

Local Lean assurance profile: **development**, for the new helper lemmas
only. Permitted transitive axioms: `propext`, `Quot.sound`, `Classical.choice`.
Compile the new modules with pinned Lean 4.35.0 and normal kernel checking,
inspect elaborated statements, and audit their transitive axioms. Native
compilation is distinct from external replay and from the arithmetic source
application. No local paranoid run is requested or claimed.

Use exact rational/cochain and determinant checks with adverse hypotheses.
The integration check generates rows from local cup evaluations before
checking the adjugate identities. It includes nonprimitive local classes,
fractional complements, non-diagonal involutions, nonunit common strict
factors, and distinct integral-unit basis factors. Independently rescaling
one functional or changing only one strict factor must break valuation
preservation. These finite checks detect errors; they prove no arithmetic
existence or universal statement.

Obtain separate-agent mathematical review after each proof packet is frozen.
Record source hashes and distinguish conditional/source-relative acceptance
from a full arithmetic construction. Changes after review require a renewed
review of the affected bytes. Reviews here are internal model reviews.

The following remain separate obligations unless explicitly discharged:
the full arithmetic realization in Lean; the construction and compatibility
of retained global diagrams through the inner limit; all localized inverse
existence premises; universal group-ring descent; outer rank-changing
objects; the restricted converse and the main Diophantine theorem.
