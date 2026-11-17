# ℤ is Diophantine in ℚ: the Lean proof

This fork formalizes in Lean 4 the main theorem of the manuscript
[*ℤ is Diophantine in ℚ*](diophantine_zq.pdf) (November 5, 2026, Theorem 1.1): there is a polynomial `P` with
integer coefficients such that a rational number `q` is an integer exactly when `P(q, w) = 0` for some
`w ∈ ℚ^292,890,231,904`. Lean states it as `ZInQ.FrozenTarget` ([`ZInQKernel/Target.lean`](ZInQKernel/Target.lean)).
The Lean result is conditional: it proves the theorem from the open hypotheses counted below, and those are not
proved in Lean.

## Manuscript route transition — issue #74

The proposed headline is `SixContactMin → PoleCompleteness → FrozenTarget`, using the
manuscript's curves `y² = x(x−ℓ)(x+3ℓ)`. Pole completeness (Theorem 5.2) is an explicit
**unrefereed manuscript hypothesis**; its restricted-converse proof is not formalized here.
The H part retains the existing open bundles. See the generated [board](docs/one-proof/OPEN.md).

**Draft evidence status:** focused local checks are recorded in the
[issue #74 handoff](docs/openmath/issue74-manuscript-pole/HANDOFF.md). A complete build,
fresh hypothesis extraction, axiom reports and retained paranoid comparison are pending
Open Math OS. Earlier Route K results do not verify this changed construction.

Route K's headline is retired from active imports. Its sources remain in Git, with the
[archival revision and tag gate](docs/openmath/issue74-manuscript-pole/ARCHIVE.md) recorded
for the integrator. [Why Route K existed](docs/research/rs-pole.md).
The active construction retains route AP (Szemerédi's theorem in the primes in place of
Proposition 6.2) and the weaker catalogue bound CAT₈.

## Upstream

Elliot Glazer's repository, [elliotglazer/diophantine-z-q](https://github.com/elliotglazer/diophantine-z-q), plans
to take this work in as staged pull requests once its Lean CI is fixed; [#139](https://github.com/elliotglazer/diophantine-z-q/pull/139)
holds this fork as of `c1e4ed1b`. Its topic issues
([#74](https://github.com/elliotglazer/diophantine-z-q/issues/74),
[#76](https://github.com/elliotglazer/diophantine-z-q/issues/76),
[#81](https://github.com/elliotglazer/diophantine-z-q/issues/81) to
[#86](https://github.com/elliotglazer/diophantine-z-q/issues/86), indexed in
[#37](https://github.com/elliotglazer/diophantine-z-q/issues/37)) list the open statements by area.

## Contribute

Start at [issue #14](https://github.com/Deicyde/diophantine-z-q/issues/14); a coding agent can follow it as written.

- **Prove a hypothesis in Lean:** pick an `open` row on [OPEN.md](docs/one-proof/OPEN.md), claim it on #14, follow
  [CONTRIBUTING.md](docs/one-proof/CONTRIBUTING.md), and open a pull request against this fork's `main`.
- **Check a statement against its printed source** (no Lean needed): follow
  [STATEMENT-CHECKS.md](docs/one-proof/STATEMENT-CHECKS.md); [pages-wanted.md](docs/one-proof/pages-wanted.md)
  lists the pages to read. A person's reading counts for more than an AI's: it is what clears a statement's flags.

## Check it yourself

Lean `v4.35.0`, Mathlib `56a00585`:

```
lake exe cache get
lake build +ZInQKernel.OneProof.Main
```

Then run `#print axioms ZInQ.OneProof.frozenTarget` in a file that imports `ZInQKernel.OneProof.Main`. Its output
lists axioms only: the open hypotheses are premises in the theorem's statement, so they do not appear there.
[`scripts/one_proof/check_axioms.py`](scripts/one_proof/check_axioms.py) checks that output.

A cold build is long. The default `lake build` does not build this theorem, so name the target as above. On a
12-core, 18 GB machine, 694 of the 5,225 project modules built in 41 minutes; on GitHub's hosted runners a cold
build has not yet finished within a job. Allow roughly 20 GB of disk and use a short checkout path, because Lake
writes a file of several megabytes per module that embeds absolute paths. Clone with
`git clone --depth 1 --single-branch`: the fork has several hundred branches.

## More

- [STATUS.md](STATUS.md): the detailed status. Its count block is regenerated after each landing; its prose is
  dated and describes the commit it names.
  [docs/research/frontier.md](docs/research/frontier.md): the project's dated survey of the open statements, with
  sources, ratings and history.
- The manuscripts: [diophantine_zq.pdf](diophantine_zq.pdf) ([TeX](diophantine_zq.tex)) and the earlier conditional
  [October 11 manuscript](October%2011%20Manuscript/README.md); the polynomial and its checks are in
  [construction/](construction/README.md). The copy here is the November 5 text that `ZInQ.FrozenTarget` was frozen
  against. Upstream has revised the manuscript since (version 19 when this was written), with corrections listed
  in its README.
- The previous, longer README, with the earlier five-hypothesis theorem and its trust statements, is
  [here](https://github.com/Deicyde/diophantine-z-q/blob/222c98bfaaade688e1c0afdef7c857ce59ab6081/README.md).
- [Blueprint site](https://deicyde.github.io/diophantine-z-q/) (a snapshot from 2026-11-13; it redeploys after
  the next main build cache run that passes on `main`).
- Licence: the fork's own material is under the Apache License 2.0 ([LICENSE](LICENSE)). It does not cover the
  manuscripts, `construction/` and `lean/`, which came from upstream, or the vendored libraries
  ([NOTICE](NOTICE), [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md)).
- Credits: the November 5 manuscript was produced by Elliot Glazer with Astra 6, Sol 6.1 and Opus 5.5, with auditing
  from Fable 5.1. Vendored libraries are credited in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md), and contributed
  proofs in the [credits section of OPEN.md](docs/one-proof/OPEN.md#credits).
