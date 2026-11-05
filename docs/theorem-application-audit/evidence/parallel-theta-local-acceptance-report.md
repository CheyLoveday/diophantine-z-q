# Final source/application acceptance pass

Baseline SHA256: `a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e`. No shared files were changed. These decisions concern the listed external theorem applications. They do not certify every downstream argument. Named dependencies remain explicit; in particular A080 must be integrated before a baseline-only closure claim for the custom derivative interfaces.

Pinned sources were reread at the locators below, together with the exact baseline consumers. Lang p.557 was inspected as a rendered primary-source page. Milne and Nekovar statements and proofs were read from the pinned PDFs/extractions. Existing acceptance labels were not evidence.

## A022

Accepted within scope. Source: DD Theorem 1.8 (= Corollary 5.8), printed p.4; definition of rk_p immediately before Conjecture 1.4. Baseline consumers: 1632–1655; 7914–7951.

The curve is over a number field and has a rational degree-two isogeny, supplied by its rational nonzero two-torsion. The source exponent is the Z_2-corank of the entire 2-infinity Selmer group. Thus corank one gives root number -1 without removing a divisible Sha summand. The stronger finite-Sha hypothesis in the source Theorem 1.2 is not imported. Acceptance covers parity, not the separately established corank or analytic converse.

Dependencies: none beyond the stated internal hypotheses.

## A036

Accepted within scope. Source: Lang, Algebraic groups over finite fields, Theorem 1 and its corollary, p.557; Theorem 2 on the same page identifies torsors. Baseline consumers: 2876–2898.

The connected smooth special fiber is a connected commutative algebraic group over the finite residue field, even at bad reduction. Lang surjectivity kills its finite-field H1; inflation-restriction injects the finite residue-extension H1 into that group. Smooth reduction is surjective. For the kernel, the extension is unramified, a base uniformizer is Galois fixed, and each formal filtration quotient is the additive residue extension, induced by a normal basis. Successively corrected coboundaries converge in the complete formal group; finiteness of Gal allows simultaneous limits in every cocycle equation. Finally B(Fprime)/B0(Fprime) embeds into the geometric component group, so its order c_B kills its H1 and hence H1(Gal,B(Fprime)). No division by the extension degree, good-reduction assumption, or rational component count replaces this argument.

Dependencies: A071.

## A037

Accepted within scope. Source: Milne ADT I.2.3 p.28 and I.3.2–3.5 pp.41–44, especially the Kummer diagram in the proof on pp.42–43. Baseline consumers: 3164–3208; 3532–3560.

The field is a finite extension of Q_p of characteristic zero, including p=2. The canonical principal polarization of the actual elliptic twist identifies its Cartier dual. Milne makes the finite Kummer inclusion adjoint to projection onto H1(F,B)[2^a]; its kernel is precisely the Kummer image. M=B(F)^completion_2 includes all finite two-primary torsion. M[-1] reduced derivedly has M[2^a] in degree zero and M/2^a in degree one. The restricted integral pairing class belongs to Hom(M tensor M,Z_2); finite isotropy forces its values into every 2^a Z_2, hence zero. The negative-degree ambiguity group is zero by the standard t-structure. Quotient-to-dual comparison follows from finite local duality and derived Nakayama on the bounded perfect models. Old character triviality is checked before reduction: all sign evaluations of epsilon are one, so epsilon itself is one. This last implication uses separation of the elementary two-group by sign characters, not semisimplicity modulo two.

Dependencies: A075.

## A038

Accepted within scope. Source: Nekovar 5.1, 5.2.4, 5.4.3; 6.2.5–6.2.8 pp.139–141 and Theorem 6.3.4 p.143. Baseline consumers: 2612–2680; 3194–3208; 3532–3608.

The coefficient modules are finite free over A_i=(Z/2^i)[t]/t^i or A_i[G]. These finite complete-intersection coefficient rings are Gorenstein; the group-ring extension is symmetric, with pairing coefficient-of-1(ab) a permutation matrix. Thus the required dualizing module is the coefficient ring, without division by |G|. The actual conjugation pullback inverts the anticyclotomic character, while fixing t and the group basis in the coefficient ring; the pairing is e_2(v,rho_T(tau)w), so its adjoint is the actual dual twist. This verifies perfect coefficient duality. Old places are the fixed local quadratic types over the two Q_p completions because K splits at 2N. Their full torsion-bearing Kummer diagrams extend derivedly. K is imaginary, eliminating real Tate corrections. Exact local orthogonality and isotropy give zero error term in 6.3.4. The active/moving contractions after the stated localization and perfectness of retained models remain the separately audited A075 input; custom derivative maps/homotopies use the reviewed A080 repair. The theorem itself does not assert those contractions.

Dependencies: A037, A075, A080.

## A039

Accepted within scope. Source: Nekovar Proposition 7.8.8(i),(ii), pp.186–187; its finite-module excision proof on p.187. Baseline consumers: 3235–3250; 4344–4363.

The proposition starts with a G_{K,S}-module; this is the unramified-at-added-primes hypothesis. Each of the five listed applications satisfies it at the stage of use: binary augmentation, unused scalar q, scalar characteristic-two residual specialization, moving-character t=0 specialization, and a good new derivative prime outside h and r_i. Arbitrary old local conditions are retained. Replacing the newly unramified condition by full then creates the singular quotient by an additional cone triangle, rather than by 7.8.8 alone. At an active scalar prime characteristic two kills chi_h, but F_2[G] reduction alone does not kill epsilon; augmentation is expressly required. Finite t-truncations are not inverted: the inner limit precedes t inversion. No use on a still-ramified characteristic-zero coefficient system is licensed.

Dependencies: none beyond the stated internal hypotheses.

## A040

Accepted within scope. Source: Milne ADT proof of I.7.3 pp.97–100, equation (7.3.1) p.98 and its Poitou–Tate proof pp.99–100. Baseline consumers: 3772–3782 and ensuing isogeny comparison.

The source theorem heading is BSD invariance, but the algebraic identity proved in its proof follows from the kernel-cokernel product formula and duality, without assuming an analytic leading coefficient. Here A=Res_{K/Q} E^h and B=E^h times E^{hk} are principally polarized, with dual sum/difference maps composing to [2]. Characteristic zero makes degree four prime to the field characteristic. Forward simple-zero and nonzero companion results supply the finite Sha needed for nondegenerate Cassels–Tate pairings. On the rank-one free lattices IJ=2; canonical height functoriality gives Reg_B/Reg_A=2/I^2. Pullback measures, both real kernel/cokernel factors, and local component factors must all be kept. The valuation identity uses +v2(Reg_B/Reg_A), +v2(Omega_B/Omega_A), +v2(C_B/C_A), and 2g_A-2g_B. Component factors are the separate A069 calculation. This acceptance does not infer finiteness of Sha merely from Selmer corank one.

Dependencies: A020, A069, A082.

## A041

Accepted within scope. Source: Nekovar 6.4.1.1–6.4.1.6 and Proposition 6.4.2, p.144; Corollary 6.4.3, p.145. Baseline consumers: 3880–3926.

The primitive-to-relaxed map i and paired strict-to-primitive map j retain every old local map and its isotropy homotopy. At the new unramified prime their conditions are unramified-to-full and zero-to-unramified. These are maps of the actual local diagrams, so the source compatibility with pairings gives beta_R(v,iw)=beta_P(jv,w). The retained norm boundary and paired lift supply the two factors e_q; conjugation sends z to z^-1 and leaves e_q=a_q-z-z^-1 unchanged. Multiplying the two singular determinants gives delta_q=q^4 l_q. The assertion that the residual factor is a Lambda-unit uses the retained finite integral cone bases and unit-disk comparisons; it is not a conclusion of naturality alone. Acceptance of this application requires the coherent comparison models already audited in A075 and the custom local compatibility repair A080, rather than only equality of H1 coordinates.

Dependencies: A037, A038, A075, A080.

## A043

Accepted within scope. Source: Milne ADT I.2.3 p.28; I.2.8 p.31; I.3.3 p.41 for the local point-group rank. Baseline consumers: 4276–4314.

W is the trivial F_2 module of rank two. Local finite duality gives h0=h2=2. The local Euler characteristic gives h1=4+2d_w, with d_w=[K_w:Q_2] at two and zero elsewhere. Milne I.3.3 gives local completion rank d_w; finite two-primary torsion has exactly two generators because the rational two-torsion is all E[2]. Derived reduction therefore gives Kummer dimensions (2,2+d_w), including degree zero. Adding full-complex dimensions gives the table totals 12+3d_w,12,8,16,10,12,14. The final three use the D0-retaining derivative conditions, not zero/full conditions. There are at most two places above a rational prime and total dyadic degree two, yielding 30,24,32,28 as stated. A prime dividing k alone carries no charged local condition. This accepts local dimensions and their arithmetic bound, not the separate global rank estimate.

Dependencies: A075, A080.

## A044

Accepted within scope. Source: Nekovar Proposition 6.3.3 and Theorem 6.3.4, pp.142–143. Baseline consumers: 4566–4630; 4787–4817.

The local model has dual D0,D2 and paired rank-two finite/singular planes. All four conditions retain D0; relaxed omits D2. Thus quotient conditions are F[-1] and S[-1], and no extra preceding degree-zero quotient occurs in the H1 sequences. Strict/relaxed are exact orthogonal complements and finite/singular conditions are self-orthogonal, with the transported J pairing. Global duality then identifies the relaxed localization image with its exact annihilator after the stated fraction/test-field passage. In a nondegenerate four-dimensional local space that image has dimension two. The assumed old vector (v,0), v nonzero, and the actual derivative (0,Jv) are independent and hence span it; strict H1 vanishes by the old rank-one/nonzero-localization hypothesis. The finite arithmetic derivative identity and detection hypotheses are separate inputs. Fractional complements used for determinants cannot be replaced by an integral primitiveness assumption. The theorem application is accepted with A080 integration; it does not independently establish the determinant-switch arithmetic input.

Dependencies: A037, A038, A075, A080.

## A045

Accepted within scope. Source: Nekovar 5.1.1–5.1.6 and Theorem 6.3.4 p.143; for the real appendix 5.7.1.4–5.7.1.7, pp.131–132. Baseline consumers: 5001–5045; 7376–7425.

For imaginary K the finite cone has H0=E(K)[2] and H1=Sel_2, because the local degree-zero maps are isomorphisms and Kummer degree-one maps inject. Finite shift-three duality gives dimensions (2,d_K,d_K,2). Integral H0 vanishes because rational torsion is finite, and H1 torsion is E(K)[2-infinity]. The universal-coefficient spectral sequence over Z_2 gives H3=Ext1(H1,Z_2), of length t_K, and pairs the free parts of H1,H2. The full Selmer corank input gives both free ranks one, allowing divisible Sha; no finite-Sha inference is needed here. The separate rational-field appendix invokes 5.7, not the imaginary-field formula: real Tate terms are retained, compact real Kummer H1 is all H1, its discrete orthogonal is zero, and H2(R,T) remains in the sequence. Finite-level Mittag–Leffler and high-degree real localization justify the displayed limits. The corank-zero input and real exact-sequence construction remain bounded dependencies in A082, rather than consequences of imaginary duality.

Dependencies: A037, A038, A075, A082.

## Repairs and closure discipline

No additional mathematical replacement is proposed by this pass. The existing A080 replacement is a required dependency for the custom derivative interfaces in A038, A041, A043 and A044. A040 also depends on the A069 replacement already supplied. A037 and A038 do not establish global perfectness merely by invoking duality; retain the separately audited A075 construction. A045 uses A082 only for the explicitly stated corank and rational-field appendix inputs.

For easier source tracing, adding Milne I.3.3 to the A043 citation and Lang Theorem 2 to the A036 citation would be useful but is not necessary for mathematical closure: the present text gives the local completion fact and deduces finite-field H1 from the cited Lang corollary.

## Pinned primary sources

- `work/astra-weighted-theta-audit-001/primary/dokchitser-parity-2009.pdf`, SHA256 `b0c625d49e99cfd7af1ef95d8bd7ec729dc2eba4a762b4869838f6052b103707`.
- `work/astra-final-finite-arithmetic-audit-001/primary/lang-1956.pdf`, SHA256 `665286caefaa894cf789f3b4ce3027accdf4d583836e8b13aafeab744373b44d`.
- `work/astra-arithmetic-final-composition-001/milne-ADT-2006.pdf`, SHA256 `2c6195ec76a974f3f336c77cb71cc3845b018aad2d43136716b3477a3bc5fb31`.
- `work/nekovar-selmer-complexes-2006.pdf`, SHA256 `61c84e5ad3252a2e520747215ac57a282addc2b58c824a3637bcd77bbe02153f`.
