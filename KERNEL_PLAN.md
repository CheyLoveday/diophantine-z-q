# Manuscript kernel assembly

The current route is `SixContactMin → PoleCompleteness → FrozenTarget`.
`ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness`
in `ZInQKernel/MainGreenTao.lean` assembles the existing construction with the manuscript's
`x(x−ℓ)(x+3ℓ)` pole polynomial. `ZInQ.OneProof.frozenTarget` supplies H from the unchanged
open bundles and leaves PC (Theorem 5.2) explicit. Its proof from the restricted converse
(Theorem 5.3) is not formalized; PC is an unrefereed manuscript claim.

Route K assemblies are excluded from active imports. The
[archive record](docs/openmath/issue74-manuscript-pole/ARCHIVE.md) preserves their revision
and records the tag/build gate. Existing lower helpers needed by H and density are retained.
The construction still uses route AP instead of Proposition 6.2 and the weaker CAT₈ bound.

The complete changed assembly has not yet been built. See the
[Open Math OS handoff](docs/openmath/issue74-manuscript-pole/HANDOFF.md) for all remaining
build, extraction, axiom and retained-export gates. Historical Route K build claims below
apply only to their original revisions.

## The polynomial is constructed in Lean

`FrozenTarget` asserts that a suitable polynomial *exists*. The development therefore
defines the polynomial by construction in Lean, mirroring upstream's generators: each
template and recipe is a Lean term, and the natural precision polynomial is the output of a
Lean compiler applied to a Lean description of the precision program. Witness-block
disjointness and the variable count are proved by construction, and the degree and
coefficient bounds compositionally. The saved files `construction/ordinary-integer-definition.json`
and `construction/precision-natural-polynomial.json` are cross-checks for an external
script, not inputs to the proof. The finite computations left in the proof are mathematical
certificates (the generator descent and height search, point counts, explicit comparisons).

## Milestones

1. **Reduction to finite computations.** Prove the main theorem from the hypotheses
   and a conjunction of finite, decidable statements. Everything else (the elliptic
   model and generator descent, multiplication, the compiler, the variable-shift bridge,
   the literal specification and the size bounds) is proved in Lean. The finite
   statements are first checked by `native_decide` or by external scripts, in a separate
   library outside the audited root package.
2. **Kernel certificates.** Replace each trusted computation by a certificate checked in
   the kernel, in the style of `AxiomMath/CFSG`: an external tool emits witness data,
   pinned data files become `Nat` literals, Boolean checkers built from the kernel's
   GMP-accelerated `Nat` operations are proved by `Eq.refl true`, and soundness lemmas
   connect each checker to the mathematical statement. The final build uses no
   `native_decide`.
3. **Classical inputs.** Formalize any classical input that milestone 1 states as a
   hypothesis. The Mordell–Weil theorem for `E/K₀` is done, and so is CAT, through an
   effective Dirichlet theorem ([docs/effective-dirichlet-plan.md](docs/effective-dirichlet-plan.md)).

Status (2026-11-07):

- Milestones 1 and 2 are done. `ZInQ.exists_bounded_integer_polynomial_defining_integers_of`
  (`ZInQKernel/Main.lean`) proves `FrozenTarget` from three hypotheses (H_min, CR₃, 22P; CAT is the
  theorem `ZInQ.catalogueBound8`, and PC, for the Route K pole polynomial, the theorem
  `ZInQ.poleCompleteness_of_certifiedRank`) with no `sorry` and
  no `native_decide`; `#print axioms` lists only `propext`, `Classical.choice` and
  `Quot.sound`.
- The last finite computation was the node statistics of the universal halting circuit. The
  proof needs only upper bounds on its addition and multiplication nodes
  (`ZInQ.Compiler.NodeCheck.haltingAddMulBound`), and these are proved by an upper-bound
  judgment over the construction monad that counts requested nodes and subtracts requests
  whose node is already present (`ZInQKernel/Compiler/NodeBound/`); the program-dependent part
  is four small `decide +kernel` computations (about 25 s).
- The exact node counts, which no theorem uses, are kernel proofs too
  (`ZInQ.Compiler.NodeCheck.haltingAddMulCheck`, `ZInQKernel/Compiler/NodeSkeleton/`): the
  run of the construction is split into 89 `decide +kernel` checks of a builder without a
  hash-consing table, guided by pinned oracle data, and a simulation proof relates it to the
  fast builder (about 10 min in all). No library in the repository uses `native_decide`.

## Finite computations

Every finite computation the proof needs (audit of 2026-11-06, updated as the formalization
landed). All of them are checked by the kernel; the audited library `ZInQKernel` uses no
`native_decide`.

| Status | Computations |
| --- | --- |
| Checked by the kernel | the small-height search (`ZInQ.Search.searchCheck_eq_true`: `Nat.rec` loops over Boolean tests built from the kernel's GMP `Nat` operations, closed by `decide +kernel` in about 60 s); the 324-primorial literal (a Boolean trial-division checker with a soundness lemma); the point counts modulo 17 and 23; the node statistics of the power template (about 35 s) and its translation statistics (about 1 min); the template parameter and witness tables; the shape of the 1,399-instruction universal interpreter and its equality with the compiled structured interpreter (a few seconds each); the size and validity of the wrapper program; the witness-count arithmetic; the closed comparisons and small constant bounds of the size chapter; the integer inequalities behind the height constants; the clearing arithmetic; the congruences of P₀ modulo 7; the height comparisons and the small residue and sign tables |
| Node statistics of the halting circuit | the bounds the proof uses (at most 125,307 additions and 98,361 multiplications among the 293,568 hash-consed nodes of the universal halting circuit) are kernel proofs, by the presence-only upper-bound judgment of `ZInQKernel/Compiler/NodeBound/`; the variable count, the constants and the call count are proved symbolically. The exact counts, used by no theorem, are kernel proofs as well (`ZInQKernel/Compiler/NodeSkeleton/`, 89 chunked `decide +kernel` checks) |
| Replaced by symbolic proofs | the other counts of the halting and precision circuits (from the counting lemmas of the packed compiler and the construction), the scope of the precision circuit, every statement about the astronomically large constants, the guard product over the false triples |
| Not computable, proved instead | the catalogue bound CAT, a closed statement about φ(4·324#) ≈ 7.5·10¹²⁹ residue classes; with the cutoff raised to 2^(W⁸) it follows from an effective Dirichlet theorem (`ZInQKernel/Progressions/`) |

The saved JSON constructions are compared with the Lean construction only by external
scripts; they are not inputs to the proof.

## Layout

| Path | Contents |
| --- | --- |
| `lean/` | Upstream's accepted helper snapshot, unchanged, required as the Lake package `z_in_q` |
| `ZInQKernel/` | This fork's Lean development (library `ZInQKernel`, namespace `ZInQ`) |
| `ZInQKernel/Hypotheses/` | The explicit hypotheses, and the statement of MW (now proved) |
| `blueprint/` | The Autoform blueprint: the informal dependency graph and its Lean status |
| `scripts/check_target.py` | Identity check between `FrozenTarget` and the frozen upstream statement |
| `scripts/print_axioms.lean` | `#print axioms` for the main theorems, their variants and the theorems that replace former hypotheses |

## Build

```sh
lake exe cache get
lake build
python3 scripts/check_target.py
lake env lean scripts/print_axioms.lean
```

The `autoform verify` workflow that used to audit every root-package declaration was removed on
2026-11-17. The `main build cache` workflow now builds `+ZInQKernel.OneProof.Main` on pushes to
`main` and fails unless the axioms of `ZInQ.OneProof.frozenTarget` are among `propext`,
`Quot.sound` and `Classical.choice`. No workflow audits the other declarations.
