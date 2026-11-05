# A080: cochain functoriality and finite descent

Date: 2026-11-05. Baseline manuscript SHA256: `a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e`. This is a bounded continuation of the forward/modularity review. No shared manuscript or audit file was changed. The separate `A080-PATCH.diff` adds precise citations and the higher-degree transfer formula. It does not silently assert that the manuscript's custom local complexes satisfy every hypothesis of Selmer duality.

## Disposition

The finite descent, weighted transfer, inverse-deck coefficient map, ramified inertia transfer, and inverse-limit H^1 interface are supported. No missing inverse character or extension-degree denominator was found in H8–H9, H20–H21, K7, or K10. The provided higher-degree formula makes the chain-map assertion directly checkable.

The larger claim that every custom local finite/singular diagram and every cup-product/duality homotopy is thereby justified does not follow. Nekovar's Selmer-complex functoriality theorem has explicit local-map and higher-homotopy hypotheses. The manuscript records individual class witnesses in H22, but A080's six anchors do not establish all of those hypotheses for the D^0-retaining derivative conditions. This is a precise residual verification obligation, not a demonstrated counterexample to those local constructions. Recommend closing the elementary cohomological interfaces and retaining the local-complex compatibility part unless its independent application audit is attached.

## Source versions and locators

The directly inspected source is Nekovar, *Selmer complexes*, Asterisque 310 (2006), local file `work/nekovar-selmer-complexes-2006.pdf`, SHA256 `61c84e5ad3252a2e520747215ac57a282addc2b58c824a3637bcd77bbe02153f`. Printed page p corresponds to PDF page p+9. The selected-page text extracts in `primary/nek-p*.txt` preserve the page headings. The whole extracted text is searchable in `primary/nekovar-full.txt`.

| Interface | Exact locator | What is supplied |
|---|---|---|
| Continuous cochain differential, coefficient and group maps | 3.4.1.2–3.4.1.6, pp.82–83 | Inhomogeneous cochains and functorial chain maps for compatible pairs |
| Exact coefficient sequences | Proposition 3.4.2, p.83 | Exactness of cochain complexes in the stated admissible category |
| Cup products and total-complex signs | 3.4.5.2, pp.84–85 | Chain-level cup product with signs; not permission to discard homotopies |
| Finite discrete Hochschild–Serre sequence | (4.1.4.1), p.96 | Spectral sequence giving H8; use the finite discrete sequence, not the prime-to-p vanishing conclusion of Lemma 4.1.4 |
| Inverse-limit cohomology | Corollary 4.1.3, p.96 | Exact lim^1 H^{i-1} sequence |
| Shapiro and coefficient models | 8.1.1–8.1.3, pp.189–191 | Quasi-isomorphism, tensor basis with diagonal action, comparison to functions |
| Transfer formula and section changes | 8.1.4, p.191 | Explicit chain map; explicit integral homotopy for changing a coset section; strict transitivity with compatible sections |
| Transfer as coefficient trace/projection | Lemma 8.1.5 and 8.1.6.1–8.1.6.2, p.192 | Equality up to specified homotopy, not strict equality for arbitrary sections |
| Conjugation and group-ring involution | 8.1.6.3–8.1.6.5, pp.193–194 | Conjugation homotopy; inverse action on the second factor in group-ring pairings |
| Local decomposition and transported places | 8.1.7.1–8.1.7.6, pp.195–200 | Local Shapiro decomposition, conjugation, restriction/corestriction and their homotopies |
| Selmer-complex functoriality | Assumptions 8.6.2.1–8.6.2.4, pp.222–224; resulting 8.6.4.1–8.6.4.3, pp.224–226 | Requires actual local chain maps and compatible homotopies, including a 2-homotopy trivializing each specified cube |
| Unramified local complexes | 8.7.3–8.7.7, pp.228–230 | Explicit maps in the unramified extension situation; cannot be used to assert ramified local comparison without another argument |
| Finite local duality and global reciprocity | 5.1.3–5.1.6, p.114 | Cup pairing, invariant and sum-of-invariants; 5.1–5.6 assumes no real places when p=2 |
| Group-ring duality | 8.5.8–8.5.9, pp.220–221 | Unnormalized conjugate sum for the group-ring pairing |

Additional sources:

- Kato, Asterisque 295 (2004), `work/kato-2004.pdf`, SHA256 `3c6e14b11fa60262db8aff782ce3cf4d83e9100c0be83621a7e4ce502cec605d`, Section 8.2, pp.180–181. This defines H^q(R,T) using j_* and the inverse limit of T/p^n, with p invertible in the ring. It does not itself state the Leray kernel characterization.
- Stacks Project Theorem 59.53.1, Tag 03Q9, higher-direct-image stalks; Proposition 59.54.2, Section Tag 03QA, Leray spectral sequence. Exact HTML snapshots retrieved 2026-11-05 are in `primary/stacks-03Q9.html` and `primary/stacks-03QA.html`, with SHA256 respectively `5821c51ab4e389b75768e7325758209859c56f7c9a29d589c8a6be3d7d375f48` and `18b9c7e277b11ffb8b921386556b24fe5131277c3f41a81aba2bdce867ddf218`. See `primary/A080-downloads.json`. These are dated snapshots, not a claimed immutable Stacks release.
- Milne, *Arithmetic duality theorems*, second edition 2006, `work/astra-arithmetic-final-composition-001/milne-ADT-2006.pdf`, SHA256 `2c6195ec76a974f3f336c77cb71cc3845b018aad2d43136716b3477a3bc5fb31`, I.1, (1.1b), p.17, for the restriction normalization of local invariants. The source's introductory group-cohomology conventions are retained.

## H8–H9: one finite descent, without averaging

The objects are H=G_M normal open in G_B, quotient Gamma=Gal(M/B), and the finite discrete module V_a=E[2^a]. The five-term edge sequence is

`0 -> H^1(Gamma,V_a^H) -> H^1(G_B,V_a) -> H^1(H,V_a)^Gamma -> H^2(Gamma,V_a^H)`.

Use the ordinary continuous cohomology of these finite discrete modules. The spectral sequence (4.1.4.1) is stated for this setting. Its use here does not require the group H to have prime-to-two order; that additional hypothesis is needed only for the separate degeneration lemma in which Nekovar displays the sequence.

Conditional on the manuscript's independent bound H2, multiplication by 2^e kills V_a^H and therefore every cochain C^i(Gamma,V_a^H). Thus it kills both obstruction and ambiguity groups in H8. For invariant c, 2^e c has a lift b. If b' is another lift, b-b' comes from H^1(Gamma,V_a^H), so 2^e(b-b')=0. Therefore d_a(c)=2^e b is well-defined and res d_a(c)=2^{2e}c.

Additivity follows by choosing b_1+b_2 as a lift of 2^e(c_1+c_2). Coefficient reduction and conjugation follow by mapping a chosen lift and using uniqueness after the second multiplication. For a Cartesian finite field square, Mackey reduces restriction of transfer to transfer of restriction, with the transported places included. Transfer of b is therefore a permissible lift for the transferred c, and the same uniqueness proves compatibility of d_a. One must not replace this Cartesian hypothesis by an arbitrary field square: the latter has multiple double-coset terms. Whether the manuscript's class-field square is Cartesian is the separate H5/local-unit arithmetic input.

The denominator accounting is exact. There are two multiplications by 2^e, no division by 2^e, and no division by |Gamma|. They are applied once to the full relative extension. When I is empty the same recipe is multiplication by 2^{2e}. This audit does not independently re-prove the invariant-torsion bound H2 or the local component bound H10.

## H20–H21: check of actions and the full chain map

Write R(g)=theta(g)rho_T(g), where theta is trivial on G_{H_f}. The tensor model in Nekovar 8.1.3 has diagonal Tate action and left translation on [delta]. Thus

`v tensor [delta] -> theta(delta)v`

is equivariant into the theta-twist: mapping g v tensor [g delta] gives rho_T(g)theta(g)theta(delta)v. The theta in this formula is not inverted.

Choose r_delta representing the left cosets G_K/G_{H_f} and define h(g,delta) by g r_delta=r_{g delta}h(g,delta). The identity

`h(gk,delta)=h(g,k delta)h(k,delta)`

shows directly that the displayed H21 is a cocycle in the R-module. In fact, put delta_i=g_{i+1}...g_n delta. In every degree use

`(T_theta c)(g_1,...,g_n) = sum_delta R(r_{g_1...g_n delta}) c(h(g_1,delta_1),...,h(g_n,delta_n))`.

For n=0 this is sum_delta R(r_delta)c. With dQ(g)=R(g)Q-Q, its boundary equals the n=1 formula applied to dQ. In arbitrary degree the first differential term uses g_1 r_delta_1=r_top h(g_1,delta_1), middle terms use the identity for h, and the last term is a reindexing of the finite coset sum. Hence dT_theta=T_theta d. This is the left-coset form of Nekovar's right-coset formula 8.1.4. The patch supplies it rather than leaving a bare higher-degree assertion.

Changing the section does not preserve the literal cochain map, but Nekovar 8.1.4 supplies an integral homotopy. With product sections, iterated transfer is literally the single transfer formula. For arbitrary independently chosen sections it is naturally homotopic. This distinction matters when the manuscript retains witnesses: the section-change homotopy must be retained along with the cocycle.

For Kummer compatibility, choose Q with 2^a Q=P over an algebraic closure. The connecting cocycle is sigma Q-Q. The ordinary transferred cocycle is the connecting cocycle of sum_delta delta P, because sum_delta delta Q is a division point of that norm. Quadratic weights give the identical computation on the actual quadratic twist. At old places the varying character is trivial; the remaining fixed quadratic character is absorbed into the twist identification. Extra coefficients are finite linear combinations. No inverse norm or rational idempotent is used.

## K7 and K10: ramified transfer and inverse deck action

For j_K:Spec K -> Spec O_K[1/2], j_K is affine and hence quasi-compact and quasi-separated. Tag 03Q9 applies. At a geometric closed point the base change of Spec K to the strict henselization has the inertia group I_v as its absolute Galois group. Therefore the stalk of R^1 j_{K,*}M is H^1(I_v,M). Leray gives

`0 -> H^1(X_K,j_*M) -> H^1(K,M) -> H^0(X_K,R^1j_*M)`.

A sheaf section is zero if and only if all its geometric stalks are zero. This proves the asserted kernel characterization without rationalization. The prime two has been removed from X_K and requires no inertia vanishing here.

For a finite extension L/K, H=G_L is open in G_K. Restricting the transfer coset sum to I partitions the finite set G_K/H into I-orbits. Each orbit has stabilizer I cap gHg^{-1}; the orbit summand is the corestriction of the conjugated restricted class. This is exactly K7, including its conjugation direction. The stabilizer is the upper inertia group for the transported place. It remains open in I even though I need not be open in G_K. If every upper restriction is zero in H^1, every transferred term is zero. Ramification of L/K is immaterial for this argument. One must not substitute Nekovar's unramified-extension formulas 8.7.3–8.7.7 for this proof.

Finite-level extensions across X_K are unique because Leray gives an injection. Reduction in a commutes with the injection, so these extensions are compatible. Kato 8.2 defines the integral group by this inverse limit. For identification with completed degree-one cochains, Corollary 4.1.3 has only lim^1 H^0 as obstruction. The finite H^0 groups form a Mittag-Leffler system. This justifies H^1 here; it is not an unrestricted claim that inverse limits commute with all cohomology in later degrees.

K10 uses a different group-basis convention from H20. Its source basis has inverse deck action [s] -> [g^{-1}s], and its target has the same inverse action on Gamma_n and G, with scalar chi_0(g). The explicit calculation is

`Phi_n([g^{-1}s]) = chi_0(g) [bar g]^{-1}[psi(g)]^{-1} Phi_n([s])`.

The equality uses chi_0^{-1}=chi_0, since this is quadratic. It does not license the same formula for a general nonquadratic character. Character separation and the stated conductor divisibilities make chi_0 and psi well-defined on A_{F,n}. These are genuine integral module maps. Relabeling a basis [s] as [s^{-1}] converts left translation to inverse translation; it is an integral permutation, but the conventions must not be conflated before this relabeling.

Under Shapiro, projection of group bases to a smaller quotient is corestriction, by Nekovar 8.1.6.2. The matrix entries are 0 or 1, even when the kernel has even order. Evaluation at a quadratic character has entries +1 or -1. Therefore no factor 1/|G|, 1/[L:K], or (1+tau)/2 enters K10 or the real-subfield quotient. This confirms the denominator claim at these interfaces; it does not independently verify Kato's Euler factor identity E.1.

## Local witnesses, duality and the remaining obligation

For a fixed cocycle p satisfying a local cohomology condition, choose u_v and q_v with loc p-i_v u_v=dq_v. This is exactly the data of a degree-one cocycle in the shifted mapping cone, with differential convention

`d(x,u,q)=(dx,du,loc x-i u-dq)`.

Thus H22 is valid as an existence assertion for individual class witnesses. If a square of chain maps only commutes up to a homotopy H with f_loc j-j' f_source=dH+Hd, the induced cone map has third component f_loc q-H(x,u). The homotopy term cannot be omitted. Under a contraction with 1-ip=dh+hd and dz=0, z-ipz=d(hz); applying p'F gives exactly the boundary of p'Fhz asserted by the manuscript. These identities justify transport of already constructed witnesses, not existence of a bounded contraction.

The finite perfect Weil pairing is compatible with the actual dual coefficient map. If f:M->N, evaluation gives <f m,n^vee>=<m,f^vee n^vee>. Pushing both inputs forward through an arbitrary quotient does not preserve a perfect pairing. Nekovar 8.1.6.4–8.1.6.5 uses the inverse group-ring action on the dual factor; 8.5.9 gives the unnormalized conjugate sum. The coefficient pairing [1](ab) in the manuscript has permutation matrix delta_{h,g^{-1}}, so its inverse is integral even when |G| is even. This calculation is valid and involves no normalized trace.

For restriction/corestriction duality the relevant formula is <cor x,y>_K=<x,res y>_L, with the usual cup-product projection formula. Locally inv_L res=[L:K]inv_K and inv_K cor=inv_L. The second follows also from the first and cor res=[L:K], since restriction on Br(K)=Q/Z is surjective. Consequently no inverse degree occurs in the adjunction. Nekovar's finite local pairing is 5.1.3–5.1.4; the group-ring and transfer compatibility is 8.1.6.5 and 8.5.8–8.5.9. The global sum of local invariants is 5.1.5. Over the imaginary quadratic K, condition (P) in 5.1 is satisfied at p=2. Over Q, ordinary real cochains must instead be retained and Section 5.7 used; the imaginary-field version does not remove the real term.

Here is the exact unresolved interface. To invoke 8.6.4 for a custom derivative local condition, 8.6.2 requires actual local Shapiro/restriction/corestriction chain maps, homotopies comparing them to the ambient cochains, and a 2-homotopy trivializing the relevant cube. H19 supplies a relation between finite/singular coordinates of particular classes; H22 supplies degree-zero boundary witnesses for those classes. Neither statement alone provides the full local chain-map and 2-homotopy data required by 8.6.2. Likewise, Theorem 6.3.4 requires the specified orthogonality/isotropy diagrams, not merely equality of H^1 local subgroups. The separate derived-Kummer and derivative-plane constructions may supply these data, but they must be checked as those applications. The A080 citation package cannot certify them automatically.

No proposed patch claims to close that residual point. The mathematical corrections needed for the elementary interfaces are documentation and explicit-formula additions. The broader local-complex issue requires an independently checked diagram, not replacement of the theorem citation by a stronger-sounding one.
