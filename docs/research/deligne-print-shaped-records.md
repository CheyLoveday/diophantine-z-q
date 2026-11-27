# Deligne row: record fixes for the D2 entries (Bourbaki 389)

Additive record, 2026-11-27, for the row `Y3Hodge.DeligneCanonicalModelY3EveryPrint`. It corrects and completes
the D2 entries of `ZInQKernel/Contrib/OneProof/DeligneY3Bridges/README.md` (locator rows 4.16–4.17, 4.19, 4.21 and
the D2 bullet). Nothing here changes a statement, a count or a rating. Evidence class: AI reading of legal copies,
page images checked; no human reading.

Source read: P. Deligne, *Travaux de Shimura*, Sém. Bourbaki 23 (1970/71), exp. 389, LNM 244, pp. 123–165
(numdam copy, SHA-256 `054847cecac9c396e2a6f568443db180786a0c5528ec08530fd464d5474bd534`; printed page = PDF
page + 121).

## 1. Corrections

1. **Deligne's [8] is Mumford's Math. Ann. note, not GIT.** The last sentence of the proof of Thm 4.21 (p. 152)
   reads: "On achève la démonstration en montrant ([8]) que pour tout u : (H,h') ⟶ (Gp, h₀) comme en 3.13, il
   existe v : (G,h) ⟶ (Gp, h₀) comme plus haut (pour L convenable) tel que uh' = vh." The bibliography (p. 165)
   gives "[8] D. MUMFORD - A Note on Shimura's Paper "Discontinuous groups and Abelian Varieties". Math. Ann. 181
   345-351 (1969)".
   - That paper (printed title: *A Note of Shimura's Paper "Discontinuous Groups and Abelian Varieties"*,
     Math. Ann. 181 (1969) 345–351, "Received November 4, 1968", p. 351) was **read in full** from the GDZ copy
     (SHA-256 `7dac40ebed041889f67c248696b659223f99104f250006055b95bdca2ab98c26`; printed page = PDF page + 343).
   - The step Deligne uses is the converse half of the proof of the second Proposition of §2 (p. 348): "if
     Hg(X_φ) is a torus algebraic group, then … the commutator of Hg(X_φ) in Hom(V, V)_ℂ and hence in Hom(V, V)_ℚ
     contains maximal commutative semi-simple subalgebras R′ … this implies by (*) that X_φ is of CM-type."
   - Open point for that route: Deligne needs the algebra L of 4.9 *with involution*; the note does not show that
     R′ can be chosen stable under the ψ-adjoint involution.
2. **GIT is Deligne's [6], and it enters at 4.16, not at 4.21.** Bibliography (p. 164): "[6] D. MUMFORD -
   Geometric invariant theory, Ergebnisse 34, 1965, Springer-Verlag." It is cited in 4.16 (p. 150) for the
   representability of the Siegel moduli functor: "Pour n ≥ 3, les objets classifiés n'ont plus d'automorphismes
   et le foncteur F est représenté par un ℚ-schéma _{K_n}M [6]." Not read (no legal free copy found).
3. **Thm 4.19 and [16].** The sentence before Thm 4.19 (p. 151) is now verified on the page image: "On renvoie à
   [16] pour la démonstration du théorème fondamental suivant." [16] is "G. SHIMURA and T. TANIYAMA - Complex
   multiplication of abelian varieties and its applications to number theory, Publ. Math. Soc. Jap., 6 (1961)"
   (p. 165). No legal online copy was found.

## 2. Locators now verified on page images

| item | page | status |
|---|---|---|
| Thm 4.7 (Riemann: polarized complex abelian varieties ↔ (V, ψ, V_ℤ, h)) | 146 | verified; the exposé gives no proof |
| sentence before Thm 4.19 and Thm 4.19 (4.19.1) | 151 | verified (quote above) |
| Thm 4.21 and the last sentence of its proof | 152 | verified (quote above) |
| 6.3 (reflex field) and Thm 6.4 (canonical model in the quaternionic case) | 161 | verified |

## 3. Effect on D2

D2 now splits as follows.

- **D2a** (Thm 4.19, cited to Shimura–Taniyama [16]): still open as a source question; [16] is not available.
- **D2b** (last step of 4.21, Mumford [8]): the cited note is read; what remains is the involution point in 1.
- **GIT [6]** concerns 4.16 only (representability of the Siegel functor), a different step from D2.

On the print-shaped route of the row (complex moduli over ℂ, reciprocity on the canonical model, and one comparison
statement), Deligne's 4.16–4.21 and 5.7 are not used, so D2b and [6] do not enter that route.
