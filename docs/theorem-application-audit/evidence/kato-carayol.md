# Kato and Carayol primary-input closure for the final RC review

Date: 2026-11-04. Scope: the two assigned primary-input rows of `work/astra-seven-review-wave-001/04_full_rc/{DATA.json,RESULT.md}`, matched to immutable V4f E07:8-126 and O08:387-483. This is a theorem-application and normalization audit. It is not a new proof of the published theorems, an audit of the entire restricted converse, or Lean acceptance. No manuscript, frozen declaration, runtime, or integration file was modified.

**Disposition.** No mismatch was found in these two applications. The OCR-sensitive Kato formulas have now been checked directly against original page images, including the original finite-coefficient/lattice construction and the precise module in Theorem 13.4(2). Carayol's original hypotheses and normalization fit the actual weight-two cuspidal constituents at every odd added prime, with coefficient prime two. The local-control, positive-complex, central determinant, and modular-form construction arguments remain separately identified below; they are not consequences of the cited theorems alone.

## 1. Evidence and what was actually read

The fresh whole-RC DATA and RESULT were read in full. Their verdict was conditional support, with incomplete fresh primary coverage; that verdict was not used as mathematical evidence.

P04 is Kato, *p-adic Hodge theory and values of zeta functions of modular forms*, Asterisque 295 (2004), 117-290, local `work/kato-2004.pdf`, SHA256 `3c6e14b11fa60262db8aff782ce3cf4d83e9100c0be83621a7e4ce502cec605d`. Its authoritative location is https://www.numdam.org/article/AST_2004__295__117_0.pdf. Fresh visual inspections in this task cover printed pp.142,143,153,156,179,180,181,182,185,186,189,220,224,225,226,227,228. Page 179 is context, not a separate theorem check. Eight Kato pages and a higher-resolution Carayol p.410 were newly rendered in this directory; the other original-page images are pinned in `work/astra-kato-primary-001`. Newly rendered p.186 resolves both norm exponents, and p.226 resolves the inverse Frobenius and the distinction between parts (2) and (3).

P99 is Kato, *Euler systems, Iwasawa theory, and Selmer groups*, Kodai Math. J.22 (1999), 313-372, local `work/astra-kato-primary-001/kato-1999.pdf`, SHA256 `483dc18c56b2fe9cfac4e37f2e6594399625c3f0ea98a05bb69116377c67fc06`, DOI 10.2996/kmj/1138044090. Its pp.318,358,359,365 were freshly visually inspected for the actual-class ideal and localization argument. The fuller derivative proof inspection in the prior Kato report is retained as prior evidence, not represented as reread here.

C86 is Carayol, *Sur les representations l-adiques associees aux formes modulaires de Hilbert*, Ann. Sci. ENS19 (1986), 409-468, local `work/astra-t3-opus-reconciliation-001/primary/carayol-1986.pdf`, SHA256 `d4a5fb6b1cd76f944f8948e06df1c7ad5656ae5ee14b9189178ee1e8f2b0dab8`, authoritative https://www.numdam.org/item/10.24033/asens.1512.pdf. Its original pp.409-411 were freshly read visually, including all of 0.3-0.7 and the weight-two application in 0.8.

The earlier Kato fixed-form, common-scalar and interface reports, the primary Kato report, and the T3 Carayol/Casselman report were used to locate issues and compare the actual interfaces. Their labels were not used as proofs. Source pins distinguish primary PDFs, images, current consumers, and prior reports. The rendering script's first PyMuPDF attempt failed because that module was absent; the saved images were successfully rendered with installed Poppler. The Poppler missing-display-font warnings do not obscure the inspected scanned formulas.

## 2. Exact retained class, coefficient lattice, and integral transfers

P04 8.1.3 (p.180) defines the smoothed class in

`H^1(Z[1/p,zeta_m], V_{O_lambda}(f)(k-r))`.

Section 8.2 defines arithmetic cohomology using `j_*` of the coefficient sheaf, at finite coefficients followed by inverse limits. Sections 8.3-8.4 (pp.181-182) use the image of integral modular cohomology to define the rank-two lattice. The construction in 8.4.3 starts with integral K2 symbols, takes the finite-coefficient Chern character, the stated coefficient map, trace, and the edge map to H1. The Tate twist is explicit: `T_p E = H_p^1(1)`, and the final twist is `k-r`. For k=2,r=1 this is the elliptic Tate representation, after the one fixed comparison with T2E. It is not a lattice chosen separately for each twist.

Section 8.9 (p.185) uses the integral trace from a full level L with m|L, N|L and prime(L)=S to the fixed Y1(N) space. Section 8.11 (p.186) projects this very class to f. No inverse degree of the modular-curve map occurs. This verifies the integrality input used at E07:9-25 and the claim that the lattice comparison is fixed before F, G or the character.

The additional transfer argument in E07:18-25 is correct and is a project argument rather than a quotation of Kato: the Leray edge sequence identifies H1 of j_* with the kernel of the inertia restrictions; Mackey restriction of corestriction is a sum of corestrictions of the upper inertia restrictions. Each is zero. Tensoring by a character is performed upstairs where that character is trivial. Consequently the construction remains integral at ramified transfers, including coefficient two. Dividing by an inertia index would not be justified and is not done.

The coefficient map `[a] -> chi_0(a)[a|Gamma][psi(a)]` is an integral group-basis map. P04 13.8 (p.228) writes the Shapiro action explicitly as `sigma tensor sigma_n^(-1)` and its limit as `sigma tensor sigma_infty^(-1)`. This matches E07:29-34. It is not a normalized character idempotent. In particular, neither phi(F) nor |G| enters as a denominator.

## 3. Norm relation and the full quadratic character

The original P04 8.12 (new rendering p.186) gives the norm multiplier

`product_{q in S' minus S} (1 - conjugate(a_q) sigma_q^(-1) q^(-r) + conjugate(epsilon(q)) sigma_q^(-2) q^(k-1-2r))`.

The conditions are m|m', S union prime(m') contained in S', and prime(c d_s) disjoint from S'. With the original rational weight-two form, trivial nebentype and r=1, this is exactly

`1 - (a_q/q) sigma_q^(-1) + (1/q) sigma_q^(-2)`.

Transferring `z_{dm} tensor e_chi` and using the same group-basis map multiplies the linear coefficient by chi(q); chi(q)^2=1 leaves the quadratic coefficient unchanged. Transitivity of actual corestriction therefore gives E.1, with one factor for every unused q|F/d. This is an equality of retained classes before applying any Euler-system bound.

The index set is S' minus S, not a multiset of primes and not a power of the field degree. Thus further powers of an already present two contribute no new Euler factor. This verifies the cofinal construction using |Delta_h|m. E.2 retains chi_2 times chi_odd; deleting chi_2 would change the representation. For a nontrivial restriction to Gamma the action changes by `1+t -> -(1+t)`, hence `t -> -2-t`; this is an integral automorphism. The finite sign quotient is also integral. All these statements hold at the level of the same transferred classes, not just at their L-values.

The auxiliary smoothers are coprime to the Euler-system indices: c,d_s are 1 modulo 3 N_odd F and odd. In P04 13.3 their prime factors belong to the excluded Euler-system set Sigma, while S in the displayed class is prime(mN). Excluding smoother primes from the index set does not invert them in the global cohomology scheme. This distinction is needed when identifying full-global local correction factors.

## 4. Smoothing and exact fixed-form reciprocity

The original formulas used here are as follows. In P04 4.2.4 (p.143),

`(u,v) = (r+2-k,r)` if r'=k-1, and `(u,v)=(k-r',r')` if r=k-1.

At k=2,r=r'=1 both give u=v=1. The smoothed modular element is obtained by the operators

`(c^2 - c^u diag(c,1)^*) (d_s^2 - d_s^v diag(1,d_s)^*)`.

The weight/range conditions in 4.2.1 and 5.2.1 are satisfied. The side condition for r=k-2 does not arise. For the SL2(Z) symbol case used here, Theorem 6.6(1) (p.163), with c=d_s=1 modulo N, states

`sum_{b in (Z/m)^*} chi(b) per_f(sigma_b({}_{c,d_s}z_m(f,r,r',xi,S)))^eps`
` = L_S(f^*,chi,r) (2*pi*i)^(k-r-1) gamma^eps`,

where

`eps=(-1)^(k-r-1)chi(-1)`,
`gamma=(c^2-c^u conjugate(chi(c)))(d_s^2-d_s^v conjugate(chi(d_s))) delta(f,r',xi)`.

The sum is literally unnormalized. The left weights are chi(b), while the smoothing factors on the right use conjugates. For general finite auxiliary characters these inverse/conjugate conventions must be retained; quadraticity only removes the distinction for the quadratic part. P04 p.156 defines the sign projection by `(1+eps*iota)/2`. That is a fixed rational period projection, not an integral projector at two and not a level-dependent averaging factor.

At k=2,r=1, f*=f, the power of 2*pi*i is zero and eps=chi(-1). For the central quadratic character, chi(c)=chi(d_s)=1: the odd conductor divides F, and e>=3 pays the entire permitted dyadic conductor. The smoothing scalar is therefore exactly

`c(c-1) d_s(d_s-1)`.

The condition e>=v2(N) also makes c,d_s=1 modulo the full level N, as required by 6.6. The congruences modulo 2^(e+1) give v2(c-1)=v2(d_s-1)=e and odd c,d_s, hence valuation exactly 2e. CRT allows these congruences simultaneously with the fixed odd congruence; sizes may grow with F, but this valuation does not. For a finite cyclotomic character eta the factors need not have that same valuation, but they are nonzero because c,d_s>1 and character values are roots of unity. Only the central valuation is used for the bounded error.

P04 9.7 (p.189) maps, by exp_f^*,

`H^1(Q(mu_m) tensor Q_p, V_{F_lambda}(f)(k-r)) -> S(f) tensor F_lambda tensor Q(mu_m)`

and sends the image of the smoothed p-adic class to the same smoothed modular element. There is no unsmoothing division in this theorem. Its hypotheses include 1<=r<=k-1 and at least one of r,r' equal to k-1; our parameters meet them. Coefficient prime two is not excluded. Thus 9.7 followed by the exact 6.6 formula is the fixed-form reciprocity used in E07, with the original delta(f,1,xi), not periods of newly normalized twist forms.

Composing a character-weighted transfer with the remaining cyclotomic weighted sum counts each original coset once. This explains directly why the sum above produces no hidden phi(d) or |G|. The quadratic Gauss relation is `tau(chi_h)^2=chi_h(-1)|Delta_h|=Delta_h`; it concerns a signed discriminant. Its two-adic valuation is a/2 when |Delta_h|=2^a d. Since only the fixed list a<=3 is permitted, this and the conversion from sqrt(|Delta_h|) to sqrt(|h|) are bounded local terms, not costs per prime.

## 5. The exact theorem 13.4(2), including its limitations

P04 12.2 (new p.220) defines global Hq by the trace inverse limit of `H^q(Z[zeta_(p^n),1/p],T)` with the 8.2 convention, and Hq_loc by the trace inverse limit of `H^q(Q_p(zeta_(p^n)),T)`. In 13.4 (new p.226), Z is generated by the actual cyclotomic Euler-system class and

`J=(h(Z): h in Hom_Lambda(H^1(T),Lambda))`,
`H^2(T)_0=ker(H^2(T) -> H^2_loc(T))`.

Under (i)-(v), part (2) bounds length of this H2_0 at every height-one prime not containing p by length of Lambda/J. It has no primitive-class, canonical-generator or residual-irreducibility assumption. Part (3), which would include primes above p, adds integral cokernel freeness, residual irreducibility and p!=2. None is imported into the present application. In particular the rational two-torsion in E does not satisfy residual irreducibility, and the present proof does not pretend otherwise.

Each hypothesis has the following actual match.

* (i) Generic nonzero Z in every height-zero component. The fixed symbol combination has both nonzero period projections. P04 13.5(2), p.227, allows only finitely many zero central L-values among characters with a fixed finite prime support. Combined with 6.6 and 9.7, nonzero smoothers and the retained full character, it gives infinitely many nonzero finite cyclotomic specializations in each sign. A torsion cyclic submodule in the one-variable component can support only finitely many such character primes. This is the argument of 13.7, not an inference from nonvanishing of an unrelated class.
* (ii) Both real eigenspaces have dimension one; quadratic twisting can exchange them but preserves their dimensions.
* (iii) The printed purity condition uses inverse arithmetic Frobenius. For the elliptic Tate representation the eigenvalue absolute values are q^(-1/2), so w=-1. The positive weight +1 would be the wrong convention here.
* (iv) The rational representation is irreducible over its coefficient field. The fixed curve is non-CM (V4f S03:3-8), and a quadratic scalar twist preserves invariant subspaces. The open-image input is a separate classical theorem, not proved by the Kato statement.
* (v) The image on the cyclotomic kernel contains an open subgroup of SL2(Z2); intersection with the quadratic kernel remains open. It contains a nonidentity upper unipotent, whose rational fixed space has dimension one. No assertion that its integral cokernel is free is needed.

Section 13.8 (p.228) also gives the rational nonabelian torsion-freeness argument. At a height-one DVR away from two, H1 in a sign component is rank-one free. If the retained class is a times a basis, J=(a). The bound therefore concerns this coordinate. Multiplication by retained smoothing or by an additional nonzero integral scalar increases the coordinate valuation and cannot invalidate the upper bound on H2_0.

P99 0.7 and Theorem 0.8, p.318, likewise define J from the supplied class xi. Fresh pp.358-359 show the finite-level inclusion `t J(xi) subset pi^e Lambda`, with t outside the tested prime, and its passage to the bound by localization. Page365 explicitly handles small levels at p=2 with an extra factor two; away from two that factor is a unit. This directly checks the relevant retained-class feature of the cited proof. P99 has a different global/local support convention; its H2 is not silently substituted for P04's H2_0. The entire published derivative proof and all of its references have not been re-proved in this task.

## 6. How H2_0 reaches the current full-global consumer

This is a separate argument in E07:106-126, not an unstated strengthening of 13.4. It has the right factors and hypotheses.

At two, P04 12.2 supplies torsion of local Iwasawa H2 and its local-duality description. Local derived control at t=0 identifies its top specialization with the finite-field local H2. For V=V2(E^h), self-duality up to the Weil-pairing twist and finiteness of E^h(Q_v)_tors imply H0(Q_v,V)=0 and hence H2(Q_v,V)=0. Thus the local torsion determinant has no factor t. This uses local control and local Tate duality separately. The finite list of allowed local quadratic types is fixed in advance; taking the product of their annihilating factors and clearing fixed denominators yields one integral F_E with F_E(0)!=0.

At a good unused odd q, inertia is trivial on V_h, so `H^1(I_q,V_h)=V_h(-1)`. Its Frobenius determinant is

`det(1-sigma_q^(-1) Fr_q | V_h(-1)) = 1-a_q chi(q) sigma_q^(-1)/q + sigma_q^(-2)/q`.

This is exactly the E.1 factor. The two-term local cone has this map in degrees one and two. Its nonzero determinant makes the map injective over A and its height-one localizations, even where the determinant is not a unit; its cokernel length is that determinant valuation. At an active good q the quadratic inertia action is -1 and two is invertible rationally, so the invariant local cone vanishes. At a bad prime the source correctly retains H1(I_q,V_h), rather than replacing it without justification by V_h^I(-1). Its central determinant has no zero by the same local H2 vanishing. These fixed bad factors can join F_E.

This confirms the allocation of factors and the nonzero-central-value reasoning. It does not freshly establish the general derived local control or duality theorem; those remain explicit inputs assigned to the broader primary-coverage audit. Likewise, the positive complex E07:128-187, its real H0 and saturation, and the central determinant E07:190-245 are separate project proofs. They are not furnished by reciprocity or by Theorem13.4.

The actual source continues to impose the necessary domain: S03:129-145 and E07:190 use the central determinant identity at corank-zero constituents, and E07:240 invokes the forward nonvanishing theorem to obtain corank zero and finite Sha. Finite Sha alone is not used as a replacement for corank zero. No such central valuation formula is applied here to the unknown corank-one base. Unrestricted integral membership and that corank-zero scalar formula remain distinct assertions.

## 7. Carayol for every actual cuspidal constituent

O08:387-394 first multiplies the actual weight-3/2 forms by theta, producing holomorphic weight-two forms. For a fixed stage and operator set U this is a finite-dimensional characteristic-zero space; its coefficient field may be enlarged finitely to contain all eigenconstituents. This is the weight-two application of C86, not an application to a weight-one or half-integral-weight form. Eisenstein constituents are explicitly kept and handled by their two characters.

C86 0.3 requires archimedean weights at least two of the stated common parity. The extra discrete-series finite place is required only when the totally real base has even degree. Here F=Q has degree one, so that requirement is absent. Sections0.6-0.7 and the continuation on p.411 give compatibility at every finite place whose residue characteristic differs from that of the coefficient place. The coefficient place is above two, and each p in U is odd. The theorem does not require residual irreducibility or odd coefficient characteristic. Consequently it applies individually to every cuspidal eigenconstituent in this actual finite space. Old copies retain the same representation and do not require a separate newform theorem with a changed residual hypothesis.

The exact normalization matters. C86 0.4 sends a uniformizer to geometric Frobenius. Its omega=|.| has geometric Frobenius value p^(-1). Section0.5 characterizes sigma(pi_p) by

`L(chi sigma(pi_p)^vee) = L(chi omega^(1/2) pi_p)`

and the corresponding epsilon equality (the small check over sigma denotes the contragredient), and gives for an irreducible principal series

`sigma(Ind(xi_1,xi_2)) = xi_1^(-1) omega^(-1/2) direct_sum xi_2^(-1) omega^(-1/2)`.

It also gives `det sigma(pi_p)=chi_(pi_p)^(-1) omega^(-1)`. Section0.8 identifies the weight-two rational instance with the natural representation on H1_et. To obtain the manuscript's arithmetic-Frobenius convention one takes the dual representation: eigenvalues of geometric Frobenius on sigma are exactly eigenvalues of arithmetic Frobenius on sigma^vee. The automorphic/classical Hecke convention is transported at the same time: the local factor in the displayed identity is that of the contragredient, not sigma without its check. This transports the local Euler factor as well as the good Frobenius polynomial, which is `X^2-T_q X+q<q>` in O08:400-408. Reversing Frobenius without dualizing would be incorrect.

The remaining local deduction can be checked directly. The level/character calculation before O08:462 gives a new constituent conductor at most one with primitive ramified quadratic determinant at p, hence conductor exactly one. A nonzero-monodromy special block has unramified determinant when the twist is unramified, and conductor at least two when the twist is ramified. Thus N=0. Artin conductor one then forces zero Swan conductor and a one-dimensional inertia-invariant space. The complementary character is precisely the ramified quadratic determinant. Frobenius preserves both distinct inertia characters (p is odd), so both lines split locally. The standard local newvector Euler factor has the Fourier-normalized bad U_p eigenvalue; by C86's equality of the local factors and the dualization above, that value is exactly the arithmetic-Frobenius eigenvalue lambda on the unramified line. Old multiplicities at other primes do not change this scalar. At a p-old unramified constituent inertia is trivial and no scalar claim about its full U_p action is needed.

For completeness, write rho(tau)=diag(1,-1), rho(phi)=diag(lambda,mu). If the lower-right entry of rho(g) is z, then

`t(g tau phi)-t(g phi)=-2 z mu`,
`t(g tau)-t(g)=-2 z`, and `d(phi)=lambda mu`.

Multiplication by U_p=lambda gives O.12 exactly. No division by two is made. Eisenstein character summands satisfy the same calculation. Unramified old constituents give zero on both sides. Hence the identity holds on the complete characteristic-zero space with every old multiplicity retained, and therefore on its preserved integral module; an integral eigenspace projector is unnecessary.

The newvector/conductor-to-Fourier-U_p input and the level-one/primitive-character calculation are separate from Carayol's existence theorem. Their original Casselman and raw operator verification is recorded in the pinned earlier T3 report (Casselman pp.301-314), not freshly reread in this bounded task. No residual semisimplicity at two, uniform coefficient-field degree, or blanket scalar action of U_p on old spaces has been inferred.

## 8. Coverage disposition and remaining boundaries

The fresh-review omission “every original integral-class/reciprocity normalization formula and fresh OCR-sensitive rendered pages” is addressed for the formulas actually consumed in E07:8-126: 4.2.4;5.2;6.6;8.1-4,8.9,8.11-12;9.7;12.2;13.1,13.3-8. Their twists, sums, signs, smoother constraints, excluded index primes, and H2_0 target have direct page evidence. This is application-level primary closure; it does not claim a full reconstruction of Kato's p-adic Hodge-theoretic proof or the proofs of every cited theorem.

The Carayol theorem-hypothesis and coefficient-two row is also addressed directly for O08:462-483, with the exact dual normalization. The supplied source already states the decisive local hypotheses and retains the necessary old and Eisenstein cases. No manuscript correction is required by this audit.

Still separate: modularity and the fixed lattice/parametrization comparison; the non-CM open-image theorem; the nonvanishing theorem quoted in P04 13.5; local derived control and Tate duality; the positive-complex and central-saturation calculation; the forward rank-zero theorem; the earlier operator-level/newvector proof; and all other RC producers. Their presence here is an explicit dependency, not a claim that this report independently re-proved or newly source-audited all of them. In particular, neither this report nor the whole-RC conditional review establishes global informal or formal closure.

DRAFT_ANCHORS: unchanged.
UNREGISTERED_SORRIES: not inspected or changed; no Lean claim.
DRAFT_IMPORT_VIOLATIONS: not inspected or changed; no Lean claim.
SEALED_THIS_TURN: this report, source pins, rendered-page evidence and receipt only.
