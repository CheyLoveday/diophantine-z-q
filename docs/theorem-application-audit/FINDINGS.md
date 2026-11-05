# Findings from the source application inventory

This report is bound to `diophantine_zq.tex` SHA256
`c59598ba474a1512dd03787c2bc9ff093a3c3a8a0604f96d5f8bcfa140c61693`.
It records the source inspections made on November 5, 2026. It does not certify the main theorem.

## F001: the de Rham step needs a different comparison reference

**Application:** [A009](INVENTORY.md#a009), manuscript lines 711–714.

The manuscript attributes the de Rham property of the Tate representation, followed by descent through a finite field extension, to Faltings's *p-adic Hodge theory*, JAMS 1 (1988), 255–299. The relevant general smooth-proper comparison in that paper is Chapter III, Theorem 4.1, printed page 298 (page 45 of the pinned PDF). Its conclusion is a **Hodge–Tate decomposition over the completed algebraic closure**. It is not the stronger de Rham comparison over the de Rham period ring. The introduction on page 255 states the same comparison.

Hodge–Tate does not imply de Rham. This citation therefore does not, by itself, justify the claim needed for the subsequent application of Berger and Pan. It is a source-strength mismatch, not evidence that the particular Tate representation fails to be de Rham.

### Proposed replacement and explicit maps

Let `K = Q_l`, choose a place `v | l` of `L'`, and put `F = L'_v`. The variety `A/F` is an abelian surface, hence smooth and proper. Write `E` for the finite coefficient extension chosen in the manuscript.

1. Apply proper-smooth de Rham comparison to `H^1_et(A_Fbar, Q_l)`. A precise modern source is **Scholze, Corollary 1.8**, page 4, read together with his corrigendum. Applied to the rigid analytification of `A`, it says this representation is de Rham and identifies `D_dR(H^1_et)` with `H^1_dR`. To use this formulation, the algebraic/rigid étale and de Rham comparison maps must also be included. They are an additional standard comparison input, not a consequence of Hodge–Tate decomposition.
2. Use `V_l(A) = H^1_et(A_Fbar,Q_l)^vee`. De Rham representations are stable under duals, coefficient extension, and direct summands. Under the already constructed Morita decomposition, `V_l(A) tensor E = (r_l|G_F) direct-sum (r_l|G_F)`. Hence the restriction of `r_l` is de Rham. Brinon–Conrad, Theorem 5.2.1 and Proposition 6.3.3, give the admissibility and filtered-duality interfaces.
3. Descend de Rhamness from `G_F` to `G_K`. After replacing `F` by a finite Galois extension, set `D_F=(B_dR tensor r_l)^G_F`. There is a semilinear `Gal(F/K)` action and `D_K=D_F^Gal(F/K)`. Finite Galois descent gives `F tensor_K D_K = D_F`, so the full dimension of `D_F` gives the full dimension of `D_K`. This is **Brinon–Conrad, Proposition 6.3.8**, specialized to a finite extension. It is valid for de Rhamness; analogous descent of *semistability* is not asserted.
4. For an abelian surface the Tate-module weights are `0,0,-1,-1` in the manuscript's convention `HT(Q_l(1))=-1`. Both Morita summands are the same representation, so each has weights `0,-1`. This is a multiplicity argument; it does not follow merely from its dimension being two.
5. Berger's p-adic monodromy theorem then yields potential semistability. Pan is applied only after continuity, absolute irreducibility, finite ramification, oddness and these distinct weights have all been established.

The replacement reference is [Scholze's author PDF](https://people.mpim-bonn.mpg.de/scholze/pAdicHodgeTheory.pdf), with the [author corrigendum](https://www.math.uni-bonn.de/people/scholze/pAdicHodgeErratum.pdf). The descent and closure statements are in [Brinon–Conrad's June 24, 2009 notes](https://math.stanford.edu/~conrad/papers/notes.pdf). Their exact files are pinned in [SOURCES.md](SOURCES.md). The notes are preliminary exposition, not a published journal article.

The corrigendum changes the definition of pro-étale covers and corrects period-sheaf details; it says the main results remain intact with those corrections. Thus citing the uncorrected article alone is not the version choice made in this proposal.

**Disposition:** a replacement chain is identified. It has not been independently reviewed or inserted into the frozen manuscript. The algebraic/rigid bridge and its exact source remain to be attached before this item can be marked closed. This audit does not label a citation repair as a complete reproof of the height argument.

## Source checks that narrowed existing obligations

- **Faltings 1983/1984:** the one-page erratum changes the height-tower assertion in Satz 2 to eventual stationarity and explains that this suffices for subsequent conclusions. The semisimplicity, endomorphism and Hom conclusions used here are not withdrawn. Isogeny-height normalization still has a separate review item.
- **Pan:** Theorem 1.0.4 of the pinned arXiv v2 imports all assumptions of Conjecture 1.0.1. The extra local residual exclusion is only at `p=3`; it is absent at `p=5`. This does not discharge the other assumptions.
- **Poonen–Stoll:** for an elliptic curve, the obstruction class is zero. Corollary 7 and Theorem 8(3) supply alternation and the square-order statement for the 2-torsion of the quotient by the maximal divisible subgroup. No global finiteness assumption on Sha is required for that statement.
- **Fowler:** Proposition 2.7 covers all imaginary quadratic orders, not just maximal orders, and has no exceptional-field exclusion. Section 2.1 supplies the degree and integrality of the order class polynomial.
- **Chebotarev and reciprocity:** exact statements in Milne's CFT v4.03 have been located. A finite nonempty compatible conjugacy condition must still be exhibited at each application; naming Chebotarev does not supply it.

## What the inventory has not established

The [open-items register](OPEN_ITEMS.md) gives every currently recorded unresolved obligation. Some are missing source locations or version equivalences; others concern mathematical applicability and could reveal genuine gaps. No conclusion that they are all routine, harmless, or already fixed is justified by the inventory.

In particular, source bytes, statement locations, numerical checks, and prior AI review reports are different types of evidence. None alone establishes the exact local-condition, pairing, reciprocity, or limit maps needed by the restricted converse. A claim that *every cited theorem has now been checked in its exact conventions* would still be premature.
