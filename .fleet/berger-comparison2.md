# Berger comparison handoff

**The period-ring comparison is proved.** In
`ZInQKernel/Contrib/OneProof/BergerComparison/`, the map from the actual
embedded maximal semistable ring to the actual Fontaine image applies
Witt Frobenius to coefficients and sends `log[p̃]` to `p log[p̃]`.
It commutes with Galois and intertwines the induced Frobenius maps.
`frobeniusTransport` and `bergerPaperStComparison` compile with no
literature hypotheses. The same work also proves the separate
`fontainePolynomialEmbedding`.

The constructed cyclotomic coordinate uses a residue lift whose choice
does not affect the logarithm. It agrees with the multiplicative branch
specified by the local logarithm and `log(p)=0`. Its adjunction to the
maximal ring gives the normalization used by the project, at every prime.
`bergerSurveyF_of_cyclotomic_basis` uses the paper-ring basis implication
to supply the unchanged `BergerThm06Print` draft and hence the existing
survey row, with the same witness extension. The focused `#discharges`
and axiom outputs are under `scratch/berger-comparison2/`.

The remaining input is the monodromy theorem in the paper's admissibility
form. The journal locator and branch wording still need a primary-source
check; the previously noted residue-denominator and locator issues are
described in `docs/research/berger-comparison2.md`. No new manuscript
error was found. Nothing is folded or counted in the registry here:
0 GLUE / 0 LEAF actual delta.
