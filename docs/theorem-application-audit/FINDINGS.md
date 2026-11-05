# Findings from the source application inventory

This report is bound to `diophantine_zq.tex` SHA256
`f880d559e9a76281573e4d5110852f347bc422af3f2daf0b483fbb7f01c62fb3`.
It records the source inspections and integrated repairs made on November 5, 2026. Historical line and page references below identify the baseline discussed in each report; current anchors are in the inventory. All 82 recorded application families now have scoped review decisions. This does not certify the main theorem.

## F001: the de Rham step needs a different comparison reference

**Application:** [A009](INVENTORY.md#a009), manuscript lines 711–714.

The baseline manuscript attributed the de Rham property of the Tate representation, followed by descent through a finite field extension, to Faltings's *p-adic Hodge theory*, JAMS 1 (1988), 255–299. The relevant general smooth-proper comparison in that paper is Chapter III, Theorem 4.1, printed page 298 (page 45 of the pinned PDF). Its conclusion is a **Hodge–Tate decomposition over the completed algebraic closure**. It is not the stronger de Rham comparison over the de Rham period ring. The introduction on page 255 states the same comparison.

Hodge–Tate does not imply de Rham. This citation therefore does not, by itself, justify the claim needed for the subsequent application of Berger and Pan. It is a source-strength mismatch, not evidence that the particular Tate representation fails to be de Rham.

### Applied replacement and explicit maps

Let `K = Q_l`, choose a place `v | l` of `L'`, and put `F = L'_v`. The variety `A/F` is an abelian surface, hence smooth and proper. Write `E` for the finite coefficient extension chosen in the manuscript.

1. Apply proper-smooth de Rham comparison to `H^1_et(A_Fbar, Q_l)`. A precise modern source is **Scholze, Corollary 1.8**, published pages 5–6, read together with his corrigendum. Applied to the rigid analytification of `A`, it says this representation is de Rham and identifies `D_dR(H^1_et)` with `H^1_dR`. To use this formulation, the algebraic/rigid étale and de Rham comparison maps must also be included. The inserted lemma cites Scholze Theorems 9.1 and 9.3, published pages 74–75, for these maps, and Milne AV I Theorem 12.1(a) for the canonical Tate dual identification. They are not a consequence of Hodge–Tate decomposition.
2. Use `V_l(A) = H^1_et(A_Fbar,Q_l)^vee`. De Rham representations are stable under duals, coefficient extension, and direct summands. Under the already constructed Morita decomposition, `V_l(A) tensor E = (r_l|G_F) direct-sum (r_l|G_F)`. Hence the restriction of `r_l` is de Rham. Brinon–Conrad, Theorem 5.2.1 and Proposition 6.3.3, give the admissibility and filtered-duality interfaces.
3. Descend de Rhamness from `G_F` to `G_K`. After replacing `F` by a finite Galois extension, set `D_F=(B_dR tensor r_l)^G_F`. There is a semilinear `Gal(F/K)` action and `D_K=D_F^Gal(F/K)`. Finite Galois descent gives `F tensor_K D_K = D_F`, so the full dimension of `D_F` gives the full dimension of `D_K`. This is **Brinon–Conrad, Proposition 6.3.8**, specialized to a finite extension. It is valid for de Rhamness; analogous descent of *semistability* is not asserted.
4. For an abelian surface the Tate-module weights are `0,0,-1,-1` in the manuscript's convention `HT(Q_l(1))=-1`. Both Morita summands are the same representation, so each has weights `0,-1`. This is a multiplicity argument; it does not follow merely from its dimension being two.
5. Berger's p-adic monodromy theorem then yields potential semistability. Pan is applied only after continuity, absolute irreducibility, finite ramification, oddness and these distinct weights have all been established.

The replacement reference is [Scholze's author PDF](https://people.mpim-bonn.mpg.de/scholze/pAdicHodgeTheory.pdf), with the [author corrigendum](https://www.math.uni-bonn.de/people/scholze/pAdicHodgeErratum.pdf). The descent and closure statements are in [Brinon–Conrad's June 24, 2009 notes](https://math.stanford.edu/~conrad/papers/notes.pdf). Their exact files are pinned in [SOURCES.md](SOURCES.md). The notes are preliminary exposition, not a published journal article.

The corrigendum changes the definition of pro-étale covers and corrects period-sheaf details; it says the main results remain intact with those corrections. Thus citing the uncorrected article alone is not the version choice made in this proposal.

**Disposition:** the replacement is inserted as Lemma H.1, with the algebraic/rigid bridge, coefficient extension, duality and finite filtered descent. The published article and corrigendum are now byte-pinned. The working manuscript builds with no TeX errors or unresolved references; pages 6, 12, 138 and 139 were visually inspected. The [separate Astra review](evidence/parallel-a009-independent.md) now accepts this bounded repair, including coefficientwise weights and finite filtered descent. This is not a complete reproof of the height argument.

## F002: printed division-polynomial sign and isogenous-curve coefficient

Silverman 2009, III Exercise 3.7, p.105, prints a plus in the omega formula where the author errata specify a minus. X Proposition 4.9, p.337, prints `a^2-b` where the preceding example and direct substitution require `a^2-4b`. The repository uses the correct short-Weierstrass recurrences and the correct isogenous curve. [Batch 2](evidence/closure-batch-002.md) supplies explicit maps and a direct proof of both squareclass kernels. The author errata were not retrieved in full, and no full inspection is claimed. The final argument instead cites the independently pinned Sutherland lecture statement and supplies the specialized recurrence calculation. This replacement closes the required source obligation; the unavailable errata are not an essential premise. See [batch 10](evidence/closure-batch-010.md).

The source uses the negative of one common normalization of the isogeny. Its ordinate denominator `x^2` is correct. An initial suspicion about that denominator was rejected by substitution and is not recorded as a source error.

## F003: withdrawn criticism of the rank inference order

The earlier audit incorrectly said that the rank-one conclusion had to wait for the two-prime torsion calculation. Full rational 2-torsion is already displayed in the manuscript. For a finitely generated abelian group `E(K_0)=Z^r+T`, one has `|T/2T|=|T[2]|=4`, regardless of higher-order torsion. Hence the index `|E/2E|=8` already implies `r=1` by Mordell-Weil. Rank zero with additional torsion cannot explain that index. The two-prime calculation is still needed to prove that the entire torsion group has order four. Moving the rank sentence after that calculation is harmless, but it was not a necessary repair. This criticism is withdrawn, and the bounded reports now distinguish the two deductions.

## F004: field-specific duality locator

At line 5008, the finite Kummer Selmer calculation over imaginary quadratic K cited Nekovar 5.7.1.6-5.7.1.7. Section 5.7 treats the case p=2 with real places. The applicable source here is 5.1.1-5.1.6, under condition (P), together with Theorem 6.3.4 for the actual orthogonal Selmer conditions. The working TeX now gives that locator. The later calculation over Q retains its Section 5.7 reference. This correction changes neither the duality shift nor the dimension formula; [batch 6](evidence/closure-batch-006.md) records the field and support checks.

## F005: order of selection for detecting lists

The evaluation argument now explicitly chooses and pads its finite detecting lists at the finite stages, before taking their common limit. This avoids reading the argument as assuming injectivity of limiting cohomology in order to prove that injectivity. The retained cone contractions establish the conclusion after coefficient extension. Batch 6 gives the construction, including the distinction between a compatible cochain tower and evaluations on a product of Galois groups. The later common-alphabet and finite-stage deductions are checked in batch 7 under A076. The finite nonabelian detector and trace realizations are checked in batch 8 under A067, retaining the listed source and representation inputs.

## Source checks that narrowed existing obligations

- **Faltings 1983/1984:** the one-page erratum changes the height-tower assertion in Satz 2 to eventual stationarity and explains that this suffices for subsequent conclusions. The semisimplicity, endomorphism and Hom conclusions used here are not withdrawn. The actual one-sided height-variation uses and product additivity are now checked in batch 3. An unused two-sided bound is not claimed as checked.
- **Pan:** Theorem 1.0.4 of the pinned arXiv v2 imports all assumptions of Conjecture 1.0.1. The extra local residual exclusion is only at `p=3`; it is absent at `p=5`. This does not discharge the other assumptions.
- **Poonen–Stoll:** for an elliptic curve, the obstruction class is zero. Corollary 7 and Theorem 8(3) supply alternation and the square-order statement for the 2-torsion of the quotient by the maximal divisible subgroup. No global finiteness assumption on Sha is required. Batch 3 checks the finite Kummer sequence, the primary-group alternatives and the exact direct-limit maps needed for corank one.
- **Fowler:** Proposition 2.7 covers all imaginary quadratic orders, not just maximal orders, and has no exceptional-field exclusion. Section 2.1 supplies the degree and integrality of the order class polynomial.
- **Chebotarev and reciprocity:** exact statements in Milne's CFT v4.03 have been located. Batch 8 now gives the finite compositum and nonempty compatible conjugacy condition at each registered Chebotarev application; batch 9 and its independent second review now check the separate reciprocity and ring-class maps under A068, retaining actual conductor support and conjugate Frobenius lifts.

## F006: local cochain compatibility

The earlier text did not supply all chain-level data required by the custom derivative local conditions. The integrated repair constructs the tame complex, adapted uniformizer, restriction and corestriction matrices, and compatibility homotopies. The extra factor of two kills the shear term at the required precision. The [initial review](evidence/parallel-forward-modularity-a080-report.md), [local repair](evidence/parallel-theta-local-a080-local-review.md) and [independent second review](evidence/parallel-forward-modularity-a080-local-second-review.md) record the sequence. This is a substantive justification added to the manuscript, not a citation-format change.

## F007: conventions and source identity

The final text distinguishes both dual operations in Carayol's representation and uses the actual level-normalizing matrix in the local Hecke calculation. Formal-logarithm bounds use the isometry radius, including the dyadic case. The forward rank argument cites the inspected Kolyvagin MPI/90-69 manuscript, not a different work titled *Euler systems*, and Kato's applicable corollary. Serre's local input is the inspected Cassels-Frohlich chapter. The Pazuki record distinguishes author and published versions, and the AFP input is pinned to an authenticated revision. Each correction is documented in its application record and source register.

## F008: coverage and dependency corrections

The inventory now includes the Mertens estimate used in the sieve and the quaternion classification and rational-embedding results. Repeated Dirichlet and CM-integrality uses have individual anchors. A054's record was narrowed to the automorphy and cusp holomorphy actually used; it no longer claims an unused all-cusp vanishing result. The stale `700X` summary was replaced by the manuscript's actual `10000*2^24 X` bound.

The finite-model record is split into construction, transport, duality and budget phases. Construction precedes duality; the later budget consumes duality. This prevents the coarse application IDs from presenting mutually dependent conclusions as their own justification. See [dependencies](DEPENDENCIES.md).

## What the inventory has not established

No unresolved source-application review item remains within the 82 recorded scopes. The [open-items register](OPEN_ITEMS.md) uses that bounded meaning. The audit has not independently proved every internal arithmetic lemma, certified semantic exhaustiveness of all implicit uses, or completed the Lean formalization. Published theorems are used as inputs, and preprints/notes retain their actual status. A successful hash, build or structural check is not mathematical verification.
