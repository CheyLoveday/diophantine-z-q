# Issue #74 specification

Baseline: Deicyde/main `bf691da2236b494bb429caabc2f907d4ea428c4d`.
Mathematical source: the unchanged 11/5 `diophantine_zq.tex`, Section 5,
labels `hyp:PC` and `hyp:RC`; the curve factors in lines 979–986.
The original PR #75 manuscript predicate at this baseline is retained in
`reference/PoleManuscript-original.lean.txt` for correspondence review.

For B and eleven rational witnesses b₀,…,b₅,e,z,r₁,r₂,w, retain the existing
multiplier m and set A=mB, H=A(A−B²). Use T₁=A(A−e)(A+3e) and
T₂=A(Az²−eH)(Az²+3eH). Q is B times the same sum of squares as the manuscript.
The pole template represents Q=0; its compiled polynomial is Q². Preserve the
input and witness indices, including all six bits.

PC quantifies over every rational B with square reduced denominator,
0<B<1/2, and vₚ(B)≥4 at every p in {2,3,5,7,13}; it concludes rational
solubility of Q. PC is a premise, not an axiom or a newly proved theorem.
The `Manuscript` polynomial, solubility and PC names are abbreviations of the
canonical kernel names. Do not compare to the former Route K predicate.

Use the existing upstream manuscript obstruction: for B≠0 and p prime not
dividing 2730, a solution rules out negative odd vₚ(B). The valuation of zero
does not justify dropping the B≠0 guard. No new nonzero-ordinate assumption is
permitted. The parity helper has p≠3, unlike the old congruent-number helper.

The unchanged H bundles at this baseline give SixContactMin through
`HDec.HSyn.sixContactMin_of_open67`. The current headline has those bundles
and one additional premise, manuscript PC. The already-proved route-AP
progression input removes the prime-pattern premise. FrozenTarget, its
292890231905 variables and both tower bounds remain byte-identical.

Changed definition meanings are authorized by #74; H statements, their
mathematical proofs, and the accepted helper snapshot are unchanged. Old Route K
headline APIs are retired. Shared helpers remain usable. No restricted-converse
proof, full Selmer definition, or new result about PR #15/#27 or E364 is claimed.

Assurance: release profile, permitting only propext, Classical.choice and
Quot.sound; all six bundled checkers in Open Math OS. Author source review is
not independent mathematical review. Full compilation, elaborated statement
review, fresh hypothesis extraction and protected comparison are pending.
