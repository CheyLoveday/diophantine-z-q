# ℤ is Diophantine in ℚ: the Lean proof

This fork formalizes in Lean 4 the main theorem of Elliot Glazer's manuscript
[*ℤ is Diophantine in ℚ*](diophantine_zq.pdf) (November 5, 2026, Theorem 1.1): there is a polynomial `P` with
integer coefficients such that a rational number `q` is an integer exactly when `P(q, w) = 0` for some
`w ∈ ℚ^292,890,231,904`. Lean states it as `ZInQ.FrozenTarget` ([`ZInQKernel/Target.lean`](ZInQKernel/Target.lean)).

## Status (fork `main`, 2026-11-17)

- **One theorem, [`ZInQ.OneProof.frozenTarget`](ZInQKernel/OneProof/Main.lean), proves `ZInQ.FrozenTarget` from
  35 open hypotheses.** Lean's kernel checks it with no `sorry` and only the standard axioms `propext`,
  `Classical.choice` and `Quot.sound`. Everything else, including every finite computation, is proved in Lean.
- **The hypotheses are `Prop`s, not axioms.** 29 belong to the six-contact height estimate (the manuscript's
  Theorem 4.1) and 6 to the positive-rank part (Tian–Yuan–Zhang and Gross–Zagier). Each is either a published
  theorem stated as printed or a step the project still owes. The live list, with each statement's source, rating
  and holder, is [`docs/one-proof/OPEN.md`](docs/one-proof/OPEN.md).
- **The list is shrinking:** 75 open statements on 2026-11-15, 35 on 2026-11-17.
- **AI caveat.** The project's Lean was written by AI coding agents. Whether each published hypothesis matches its
  printed source has so far been checked only by AI readers; no person has confirmed one yet.

## Upstream

Elliot Glazer's repository, [elliotglazer/diophantine-z-q](https://github.com/elliotglazer/diophantine-z-q), is
taking this work in as staged pull requests, starting from
[#139](https://github.com/elliotglazer/diophantine-z-q/pull/139) (this fork at `c1e4ed1b`). Its topic issues
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

Then run `#print axioms ZInQ.OneProof.frozenTarget` in a file that imports `ZInQKernel.OneProof.Main`.

## More

- [STATUS.md](STATUS.md): the detailed status, rebuilt after each landing.
  [docs/research/frontier.md](docs/research/frontier.md): every open statement with its source, rating and history.
- The manuscripts: [diophantine_zq.pdf](diophantine_zq.pdf) ([TeX](diophantine_zq.tex)) and the earlier conditional
  [October 11 manuscript](October%2011%20Manuscript/README.md); the polynomial and its checks are in
  [construction/](construction/README.md).
- Earlier route: `ZInQKernel/MainLiterature.lean` proves the target from five literature statements
  ([KERNEL_PLAN.md](KERNEL_PLAN.md), [docs/research/h-trust.md](docs/research/h-trust.md)). The previous, longer
  README is [here](https://github.com/Deicyde/diophantine-z-q/blob/222c98bfaaade688e1c0afdef7c857ce59ab6081/README.md).
- [Blueprint site](https://deicyde.github.io/diophantine-z-q/) (a snapshot from 2026-11-13).
- Credits: the manuscript is Elliot Glazer's (written with Astra 6, Sol 6.1 and Opus 5.5, audited by Fable 5.1).
  Vendored libraries are credited in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md), and outside contributions in
  the [credits section of OPEN.md](docs/one-proof/OPEN.md#credits).
