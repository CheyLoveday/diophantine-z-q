# Z is Diophantine in Q

## Version 4

This repository contains the manuscript *Z is Diophantine in Q*, Version 4, dated November 6, 2026, and its explicit quartic polynomial in 4,973 variables. The complete polynomial, its source system, and the certificate checks accompany the manuscript.

The project uses the collective agentic notes from Gabe Conant, Sohail Farhangi, James Freitag, Elliot Glazer, Jenn Park, Caroline Terry.

| To | Open |
| --- | --- |
| Read Version 4 | [Manuscript PDF](quartic_4973.pdf) |
| Inspect or edit the manuscript | [TeX source](quartic_4973.tex) |
| Read the complete polynomial and check its certificate | [Quartic package](quartics/quartic-4973/README.md) |
| Inspect the proof dependencies and review evidence | [Version 4 evidence](docs/quartic-4973/README.md) |
| Build the manuscript or run the checks | [Build instructions](docs/building.md) |
| Download the newest research handoffs, November 6 revision 2 | [Full handoff](https://github.com/elliotglazer/diophantine-z-q/releases/download/research-handoff-2026-11-06-r2/z-in-q-version4-full-handoff.zip), [current-only handoff](https://github.com/elliotglazer/diophantine-z-q/releases/download/research-handoff-2026-11-06-r2/z-in-q-version4-current-handoff.zip), [contents and verification](handoff/README.md) |
| Read the collaborator notes and height replacement | [Research update](research/2026-11-06-collaborator-notes/README.md) |
| Read the October 11 manuscript | [October 11 manuscript and provenance](October%2011%20Manuscript/README.md) |
| Find earlier constructions and research history | [Research guide](docs/research-guide.md) |
| Inspect the partial formalization | [Accepted Lean helpers](lean/README.md) |
| Cite the manuscript or report an issue | [BibTeX](CITATION.bib), [contribution guide](CONTRIBUTING.md) |

The November 6 revision-2 research update preserves the Version 4 manuscript and polynomial. It adds the collaborator notes, an explicit height-input replacement and their source/verification records.

The full handoff combines the current public snapshot and selected research notes with the unchanged November 4 archive. The current-only handoff omits that embedded archive. The handoff guide specifies the included collections and verification procedure.

## The polynomial

The manuscript presents a fixed polynomial with integer coefficients such that, for every rational number $q$,

$$
q\in\mathbb Z
\quad\Longleftrightarrow\quad
\exists\,\mathbf w\in\mathbb Q^{4\,972},\quad P(q,\mathbf w)=0.
$$

The input and every auxiliary variable range over the rationals. The released polynomial has the following exact statistics.

| Quantity | Value |
| --- | --- |
| Total variables, including the input | 4,973 |
| Rational witness variables | 4,972 |
| Total degree | 4 |
| Nonzero monomials | 72,925 |
| Maximum absolute coefficient | 685,783,949,153,203,534,233,890, strictly less than $2^{80}$ |
| Quadratic residuals whose squares are summed | 4,552 |

The [full monomial table](quartics/quartic-4973/polynomial.expanded.txt) specifies the polynomial explicitly. Its SHA-256 is `094f6a7ed17e7cc8d5d17a2f809127bbaffd0fe343cb2a32d18ac97e61279876`. The [packaged verification receipt](quartics/quartic-4973/evidence/final-verification.json) records the endpoint checks; the [quartic package](quartics/quartic-4973/README.md) identifies the source and certificate. These are statistics of this construction, not a claim of minimality.

## Verification status

The certificate checks establish exact projection-preserving algebraic equivalence to the pinned source system and verify the full integer expansion. They check both directions of the algebraic transformations. They do not prove the source system's arithmetic characterization of the integers.

The [current source-status note](research/2026-11-06-collaborator-notes/source-status.md) explains the generator-era `EXPLORATORY SOURCE` label in the frozen source entry.

The manuscript supplies that arithmetic argument. The [Version 4 evidence](docs/quartic-4973/README.md) identifies its dependencies, source changes and review scopes. Version 4 uses the reviewed three-mode source with general roots, doubled targets, direct tangent equations, shared field squares and the first-norm denominator fusion. Optional scalar/J0 fusion is not used. The inventory preserves all five inherited source-version and proof-status qualifications and distinguishes them from the finite algebraic checks. The [earlier theorem-application inventory](docs/theorem-application-audit/README.md) contains 82 scoped decisions for its own frozen manuscript. Its recorded internal premises and version boundaries remain in force. It is not a blanket audit of every later statement.

The Lean formalization is incomplete. The accepted snapshot contains 48 helper modules; the main bounded-polynomial declaration still contains `sorry`. AI review and successful finite checks do not constitute independent human peer review or a completed formal proof.

## Earlier work and provenance

The October 11, 2026 manuscript, *A conditional Diophantine definition of Z in Q from four arithmetic inputs*, was produced by Sohail Farhangi with ChatGPT 6. Its PDF is preserved separately and without modification. Its provenance and conditional scope are distinct from Version 4.

The earlier November 5 manuscript was produced by Elliot Glazer with Astra 6, Sol 6.1, and Opus 5.5, with auditing from Fable 5.1. Earlier manuscript revisions remain in Git history. The [Version 3 manuscript](quartic_9625.pdf) and its [9,625-variable package](quartics/quartic-9625/README.md) remain historical references. The [Version 2 manuscript](quartic_12504.pdf), its [12,504-variable package](quartics/quartic-12504/README.md), and its [release](https://github.com/elliotglazer/diophantine-z-q/releases/tag/quartic-12504-version-2) remain historical references. The [November 4 research handoff](https://github.com/elliotglazer/diophantine-z-q/releases/tag/research-handoff-2026-11-04-r2) and its checksum identify a historical archive; that archive is not an updated copy of Version 4 or its quartic package. The original huge polynomial remains in the manuscript, and the [original large construction](construction/README.md) and its checks remain available for comparison.

The next manuscript version requires at most **2,486 total variables**, half the Version 4 count rounded down. This is a search target, not a result.

The project builds on OpenAI's October 6, 2026 preprint, [*Hilbert's tenth problem over the rational numbers*](https://github.com/openai/math/blob/main/preprints/Hilberts-tenth-problem-over-the-rational-numbers-October-6-2026/main.pdf). The manuscript's bibliography and dependency records identify the other mathematical inputs.

The manuscript author field is blank, and [CITATION.bib](CITATION.bib) intentionally omits author fields. See [archival notes](docs/archiving.md) for citation and DOI status, and [third-party notices](THIRD_PARTY_NOTICES.md) for source attribution and redistribution scope.
