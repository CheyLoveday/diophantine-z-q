# Issue #74 — Open Math OS execution and return

This branch implements #76–81. **The full headline build, fresh hypothesis
extraction, axiom checks and retained paranoid comparison remain NOT_RUN.**
The target-fork archive tag is also pending; see [ARCHIVE.md](ARCHIVE.md).
The [specification](SPEC.md), [comparison configuration](comparator.json),
[reference overlay](reference/overlay), [export roots](export-roots.txt) and
[source index](SOURCE.json) belong to this PR. No separate review pack is needed.

## Coordination update — 17 November 2026

[Jack's 14:26 update](https://github.com/Deicyde/diophantine-z-q/issues/74#issuecomment-6950868382)
assigns #76–78 builds and automatic landing to the project's build hosts. This
branch is a candidate contribution for that process; it does not replace the
project's integration authority. The separately active #83 is outside this PR.
Open Math OS supplies the additional retained paranoid comparison required by
Chey's verification boundary. No direct main push or automatic merge is requested.
The branch incorporates main `74395dcf08150196fb55fe85f6571ad6c6d42be1`;
that update adds an unconsumed contribution and preserves the H types used here.
Its new Igusa rating is retained in the generated board.

## Fetch, review and prepare

Fetch `CheyLoveday/diophantine-z-q`, branch
`codex/issue74-manuscript-pole`, at the full published handoff commit. Record
its SHA and confirm a clean checkout. Recheck issue #74 ownership and later
main changes before integration. Read SPEC.md and the actual changed source.

The reference freezes 11 target theorem types, 8 named definitions and their
source context. Only those 11 proof bodies have intentional `sorry` holes.
The original PR #75 predicate is retained separately. H sources, the accepted
helper package, target and dependency pins must match the recorded baseline.
Review those meanings before protecting the reference; author preparation is
not independent semantic acceptance. The solution must never import reference
files or admit `sorryAx`.

Use Python 3.12+ to run, with a new output path outside the checkout:

```sh
python3 -B scripts/check_issue74.py --self-test
python3 -B scripts/prepare_issue74.py --output /absolute/new/issue74-inputs
```

The preparer uses Python and Git only. It creates source-only solution and
reference projects, including the local `lean/` dependency and vendor sources,
adds a verification-only `Issue74Packet` library, and records every prepared
file hash in INPUTS.json. No Lean, cloud operation or dependency resolution is
performed. Confirm that all required inputs are present by the builds below;
an input inventory alone is not proof of build completeness.

## Native execution in Open Math OS

Use the unchanged Lean 4.35.0 and manifest pins, including Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Record actual dependency revisions,
cache provenance, OS/architecture and tool/checker hashes. Check the host's
available memory, disk and job limits before starting the full import closure;
this handoff provisions no infrastructure or spend. Keep existing failures.

1. Protect reference, configuration, source and result storage from candidate
   build writes. Use the pinned Lake Linux bubblewrap policy; retain the actual
   command/grants. Resolve dependencies separately; builds/exports have no
   network. A Linux label alone does not demonstrate isolation.
2. Build the solution's default target, the full headline and packet explicitly:
   `lake build ZInQKernel +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +Issue74Packet`.
   Also build `+ZInQKernel.Contrib.AllContrib` to check the repaired aggregator.
   The default build alone is insufficient. Keep complete logs and exit codes.
3. In the original source checkout at the same mathematical snapshot, reproduce
   `scripts/print_axioms.lean`, AxiomCheck.lean and DischargeCheck.lean after its
   targets build. Run `scripts/one_proof/check_axioms.py` against the headline's
   report. Inspect every selected theorem's transitive axioms: permitted are
   only propext, Classical.choice and Quot.sound. Retain `#discharges` output;
   changing the route does not discharge PC or an H field.
4. Run `lake env lean scripts/one_proof/OpenStatements.lean` in that checkout.
   Replace the provisional JSON with this actual extraction; regenerate the
   board and crosswalk using the existing scripts. Compare the H types against
   baseline/both the elaborated statement and the supplied source map: H plus
   `hPC : ZInQ.PoleCompleteness`, no Route K premises. Check target identity,
   `render_open.py --check` and the blueprint with the pinned existing workflow.
   Return generated documents as an evidence/finalization patch. Do not change
   mathematical source, H predicates, pins, or the trusted reference to get PASS.
5. Build reference `+Issue74Packet`. Export **Issue74Packet** separately from
   reference and solution using the bundled `leanexport MODULE -- ROOT...`,
   with all 52 lines of export-roots.txt in order. Stream stdout to persistent
   `challenge.ndjson` and `solution.ndjson` outside the build's writable paths;
   save stderr separately. Include the complete logical dependency closure.
6. Hash exports, then run from the prepared solution project:

   ```sh
   lake comparator --config ../comparator.json \
     --challenge-from-export /protected/returned/challenge.ndjson \
     --solution-from-export /protected/returned/solution.ndjson --paranoid
   ```

   Require matching target types/fixed definitions, the axiom policy, and
   acceptance from Lean default, Lean paranoid, lean4lean, nanoda, con-leche and
   con-ron. Record each checker separately. Missing/refusing checkers, source
   mismatch, unsupported containment or incomplete exports remain incomplete.
   Rehash exports afterward. No duplicate paranoid campaign is needed.

Use actual installed 4.35 help/source to resolve binary paths and environment.
The export-mode comparator does not itself establish source provenance: the
protected build/export records and input hashes are essential. Official basis:
[4.35 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/),
[pinned check source](https://github.com/leanprover/lean4/blob/v4.35.0/src/lake/Lake/CLI/Check.lean),
[comparison source](https://github.com/leanprover/lean4/blob/v4.35.0/src/lake/Lake/Check/Compare.lean).

## Durable return and local finalization

Return under `returned/`: both raw exports (compressed/split if needed),
INPUTS.json, source/config/export-list hashes, tools and dependency identities,
actual commands and sandbox grants, full build/export/axiom/comparator logs,
per-checker outcomes, generated-board patch, failure-attempt index and a
SHA-256 manifest. Bind every result to the exact source commit and input bytes.
Retain raw hashes and reassembly instructions for split archives. No caches,
credentials, or expiring job logs as the sole evidence.

Use odProof's existing claim/coverage reconciliation against authenticated
native readback where available. Its current project runner rejects this
fork's local dependency/configuration; no native odProof verification is claimed.
The local static integration test is explicitly synthetic. Do not expand this
PR into implementing missing odProof platform support.

Locally validate return integrity, roots/definitions, source/pin bindings,
complete build, actual extracted hypotheses, axiom set and all six outcomes.
Integrate generated documents and evidence, update the draft status, and rerun
affected checks after any mathematical change. Missing gates keep the PR draft.
The fork integrator supplies the verified Route K archival tag before #77 is
closed. [UPSTREAM-DRAFT.md](UPSTREAM-DRAFT.md) remains unposted for inspection.
