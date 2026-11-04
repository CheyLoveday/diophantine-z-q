# Z is Diophantine in Q

This repository accompanies the manuscript **Z is Diophantine in Q**, dated November 4, 2026. It contains the paper and a research archive with the constructions, computations, proof drafts, reviews, and partial Lean formalization developed during the project.

## Start here

| To… | Open… |
| --- | --- |
| Read the argument | [Paper PDF](diophantine_zq.pdf) |
| Inspect or edit the manuscript | [TeX source](diophantine_zq.tex) |
| Browse the polynomial and run its checks | [Curated construction](construction/README.md) |
| Build the paper or accepted Lean modules | [Build instructions](docs/building.md) |
| Inspect the formalization | [Accepted Lean helper snapshot](lean/README.md) |
| Find the construction, supporting calculations, or earlier approaches | [Research guide](docs/research-guide.md) |
| Download the saved research history | [Research handoff zip, 279 MB](https://github.com/elliotglazer/diophantine-z-q/releases/download/research-handoff-2026-11-04/z-in-q-research-handoff-2026-11-04.zip) |
| Check a download | [SHA-256 checksums](SHA256SUMS) and [verification instructions](docs/research-guide.md#verify-and-restore-the-archive) |
| Report a mathematical or implementation issue | [Contribution guide](CONTRIBUTING.md) |
| Cite the paper or archive | [BibTeX entries](CITATION.bib) |

All three main files are also available from the [November 4 research release](https://github.com/elliotglazer/diophantine-z-q/releases/tag/research-handoff-2026-11-04).

## What the paper proves

To say that the integers are **Diophantine in the rationals** is to say that being an integer can be expressed by one polynomial equation with rational auxiliary variables. The manuscript presents a construction of a fixed polynomial with integer coefficients such that

$$
q\in\mathbb Z
\quad\Longleftrightarrow\quad
\exists\,\mathbf w\in\mathbb Q^{292\,890\,231\,904},\quad P(q,\mathbf w)=0,
\qquad q\in\mathbb Q.
$$

The input is the ordinary rational number $q$. The witnesses are rational numbers as well. The same polynomial must work for every input.

The stated bounds for this polynomial are:

| Quantity | Bound |
| --- | --- |
| Total ambient variables, including the input | 292,890,231,905 |
| Total degree | Less than $2\uparrow\uparrow 7$ |
| Absolute value of each coefficient | Less than $2\uparrow\uparrow 8$ |

Here $2\uparrow\uparrow n$ is a right-associated tower of $n$ twos: $2\uparrow\uparrow 1=2$ and $2\uparrow\uparrow(n+1)=2^{2\uparrow\uparrow n}$. The variable count is an ambient bound; it does not assert that every variable occurs essentially. The construction is specified through finite formulas and substitutions, rather than an expanded list of monomials.

The paper derives three consequences:

- A refutation of Mazur's finite-connected-components conjecture for the closure of rational points in the real locus.
- A universal rational Diophantine polynomial with ordinary integer program and input parameters.
- Many-one equivalence of $\operatorname{HTP}(\mathbb Q)$ with the halting set $0'$.

The bounds above concern the integer-defining polynomial $P$. They do not automatically apply to the universal polynomial or its specializations.

## Relation to earlier work

The construction builds on OpenAI's preprint [*Hilbert's tenth problem over the rational numbers*](https://github.com/openai/math/blob/main/preprints/Hilberts-tenth-problem-over-the-rational-numbers-October-6-2026/main.pdf), dated October 6, 2026. The present manuscript concerns a Diophantine definition of the ordinary embedded integers and its stated quantitative bounds. Undecidability of the existential theory of the rationals is not presented here as a new corollary of this project.

The manuscript's bibliography and source-application appendices identify the other mathematical inputs. The [research guide](docs/research-guide.md#map-of-the-argument) connects the main arguments to their supporting files.

## Verification status

The manuscript presents an unconditional proof. The saved research record includes internal mathematical reviews; these are distinct from independent human peer review and from machine verification.

**The Lean formalization is incomplete.** At the November 4 handoff, the main bounded-polynomial declaration still contains `sorry`. The last accepted production snapshot is integration 31, containing 48 modules and 463 explicit public declarations. These counts include definitions and helper results; they are not a count of completed main-proof obligations. Later accepted work remains outside that integration.

The archive preserves superseded and unsuccessful approaches as well as later work. Start with its `CURRENT_STATE.json`, `START_HERE.md`, and `current/` directory before relying on a historical status report. See [the formalization notes](docs/research-guide.md#lean-formalization) for the remaining groups of obligations.

## Research archive

The handoff indexes 55,739 original file locations. Repeated byte-identical files share stored content. It includes a searchable offline `INDEX.html`, a manifest with hashes, a research timeline, and a utility for restoring the original directory layout. Conversational transcripts and credentials are excluded.

The paper files in this repository are the supplied versions, preserved byte for byte. The archive and release assets are a dated snapshot; subsequent documentation changes do not change that snapshot.

## Reproducible checks

The [curated construction](construction/README.md) provides the finite expression, its pinned input, and executable checks without requiring the historical archive. The [Lean directory](lean/README.md) contains the byte-identical accepted helper snapshot, its dependency pins, and a separate unproved target.

The [CI workflow](.github/workflows/research-checks.yml) checks construction regeneration and finite arithmetic cases, compiles the paper, and builds the accepted Lean modules with an axiom audit. See [build instructions](docs/building.md) for local commands and the limits of each check. A green CI run concerns those checks, not completion of the main proof.

## AI usage and attribution

The paper ends with an AI usage statement describing the contributions of OpenAI Codex and Anthropic Claude agents to the research, computations, reviews, and writing. That statement is part of the manuscript.

[CITATION.bib](CITATION.bib) supplies citation entries with the author field intentionally omitted. Identify a research artifact by the release tag and file hash as well. [Archival release notes](docs/archiving.md) explain the DOI status.

Licenses for original project material are awaiting the maintainer's selection. [Third-party notices](THIRD_PARTY_NOTICES.md) identify upstream software and mathematical sources; the project's license will not relicense those materials. The historical archive needs a per-source redistribution review before public release.
