# Oka canonical-source compatibility port notice

Source: https://github.com/chrisflav/oka at
`9a9fc315498d58484ac1abc9668548212eb7c1ff`.

Selected files retain their upstream copyright, license and author headers.
The Apache License, Version 2.0, is copied unchanged as `LICENSE`.
Upstream authors include Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
and the other authors identified in individual files.

## Scope and current grade

The original selected union comprises 288 Oka modules. Its canonical selection now
contains 292 compilation units: the original union, one Weierstrass foundation
split, and three authoritative light-definition modules. Two additional RET
point-comparison support modules bring the staged source inventory to 294; they
are a separately checked extension over the UP84 cone, not extra premises or
replacement objects in the H278 mathematics. The selected original H278
mathematics has 282 compilation units. Original source selections,
per-member provenance, transformations and raw compiler logs are preserved in
private source/evidence capsules; their historical grades are not rewritten.

This is not yet a completed or independently reviewed GAGA contribution.
At the current project pin (Lean v4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`), the narrow 84-module Scheme/UP cone
has genuinely compiled from source, with exact source and dependency-output
bindings. Its two-module RET point-comparison extension has also source-compiled
as an 86-module cone; the original finite-type presentation, closed-point range
and point-injectivity statements have separate allowed-axiom controls. The RET
proofs construct the original open-subscheme object and inclusion directly where
those definitions otherwise arrived through heavier sheaf/closed-immersion
imports. No new global carrier, witness or assumption is introduced.
Light projectivity and selected Main/consumer checks are separate
component evidence. Full H278/H282 source, complete Main/PR35/37 coexistence,
exact-type/axiom census and independent-review gates remain open. No H-105
closure or full GAGA certification is asserted here.

## Mechanical parser expansion

The 22 originally selected local/scoped parser declarations were removed and
their uses expanded to ordinary Lean terms, as recorded in the transformation
manifest:

- 188 restriction-operator expansions to `TopCat.Presheaf.restrictOpen` or
  `modRes`, retaining the original order proofs;
- 43 structure-sheaf section expansions to `Y.presheaf.obj (op ...)`;
- 224 original projective-space notation expansions to the genuine Oka object;
- 182 local identifier-alias expansions for polynomial grading, affine topology
  and gluing data.

These are historical transformation counts, not a fresh declaration census.
Documentation attached to a removed parser declaration is retained as ordinary
comments. The notation-only `quotPrecheck` wrapper and a dangling scoped hygiene
option before an expanded section were removed. No replacement syntax, notation,
macro or custom elaborator was introduced.

## Canonical object names and definition ownership

Oka's projective-space type is not the different W07 object of the same old name.
Its unchanged mathematical definition and associated API are owned under
`AlgebraicGeometry.CloudB3W17bOkaProjectiveSpace`. Module/import paths remain
`ZInQKernel.Contrib.CloudB3W17bOka.Oka.AlgebraicGeometry.ProjectiveSpace.*`.
Actual conflicting helper declarations and named instances are campaign-qualified;
no empty alias or substitute model is used to repair a collision. The complete
compiler coexistence gate, not a lexical name scan, decides readiness.

Three lightweight modules own mechanically moved original definitions:

- `Analytification.SchemeLFTComplex`: `Specℂ`, local finite type and the actual
  `SchemeLFTℂ` full subcategory of schemes over `Spec ℂ`;
- `Analytification.GAGA.ProjectiveSpaceDefinition`: the actual Oka projective-space
  SchemeLFT object and its left/base-map facts;
- `Analytification.GAGA.ProjectiveDefinition`: the original `IsProjectiveℂ`
  closed-immersion predicate.

The original heavy modules import these owners and no longer duplicate the
moved declarations. Objects, left components, base maps and hypotheses are not
replaced or strengthened.

## Weierstrass split and compatibility repairs

The oversized Weierstrass file was split at the complete, closed top-level
`LocalOkaRing` namespace boundary after original line 655. Foundation declarations
live in `WeierstrassFoundation`; the original continuation imports that module.
No private declaration crosses the boundary. Original `Polynomial` and
`TopologicalSpace` openings and the root dimension binder were restored in the
continuation, because lexical scope does not cross an import.

Mathematical definitions and theorem statements are retained. Proof terms and
API spellings have required compatibility adaptations: explicit canonical module
and scalar-action projections, actual adjunctions and isomorphisms, current
polynomial coefficient/map-domain APIs, categorical application rewrites, and
scoped backward-elaboration transparency options. Redundant terminal proof steps
were removed only when the preceding kernel-checked step already closed the goal.
Each accepted scout delta is applied only by the canonical source owner and bound
by before/after hashes; source-only and exact-type/axiom grades remain distinct.

No source `sorry`/`admit`, new axiom, unsafe or opaque proof bypass,
`native_decide`, custom parser convenience, alternative scalar model, added witness
or stronger theorem premise is authorized by this port. The completed full source
admission, exact-type, allowed-axiom, size and coexistence audits remain required
before a review-ready contribution or any closing claim.
