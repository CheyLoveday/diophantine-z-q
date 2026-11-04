# Independent review of the height replacement

Four separate Astra reviewers examined the replacement of the von Kanel-Kret height argument. No unresolved mathematical gap was identified within the replacement and the geometric and numerical interfaces reviewed. This is independent AI review, not independent human peer review or formal verification of the manuscript.

The final reviewed TeX has SHA-256 `bfc4192de00ef7cfe27df586b9cdb8a9348efe3064495f566258be7152b5dec7`.

| Review | Outcome | Evidence |
| --- | --- | --- |
| Non-CM descent, oddness, modularity and compatibility | Accepted after clarifications | [Audit](descent/AUDIT.md), [final-text addendum](descent/ADDENDUM.md) |
| Local ramification and conductors | Accepted, including final Herbrand paragraph | [Audit and final-text addendum](conductor/AUDIT.md) |
| CM and quantitative height transfer | Accepted; reviewed text unchanged | [Audit](height/AUDIT.md) |
| Complete chain and geometric/numerical interfaces | Accepted, including final clarifications | [Audit](whole/REPORT.md), [final-text addendum](whole/ADDENDUM.md) |

The original text omitted the named implication from de Rham to potentially semistable needed for Pan's theorem. The revised text supplies Berger's published monodromy theorem. It also makes the constant coefficient convention, finite character twist, relative Frobenius comparison, and dyadic upper-numbering argument explicit. The reviewers checked those integrated edits against the final source, rather than accepting proposed changes in advance.

No new hypothesis, field-degree factor, or numerical allowance was required. The exponent 24, H6, the polynomial variable count, degree bound, and coefficient bound are unchanged. The main theorem, abstract, corollaries, polynomial construction, and restricted-converse argument are unchanged.

The scoped reports identify their premises and exclusions. Their conclusions combine across the stated interfaces; no single scoped report certifies every part of the paper. In particular this review is not a new audit of the separate restricted-converse proof. The main Lean statement remains unproved.

`FINAL_REVIEW.json` records source and report hashes. `clarifications.diff` records the exact changes made during review. The earlier author-only report in `work/remove-vkk-20261104/REPORT.md` describes the previous version and is retained as history.
