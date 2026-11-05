# T3 Opus reconciliation against V4a and original sources

4 November 2026. Auditor: `/root/astra_moving_filter_audit`.

This report audits the divided operators, trace lattice, local identity, omission rule, and special nonempty seed for the actual full-rational-two-torsion curves. It does not accept the restricted converse or a Diophantine definition of the ordinary integers. It makes no production edits. The preceding Kummer reconciliation was sealed first at `work/astra-kummer-reconciliation-001/REPORT.md`, SHA256 `7a1b9526154a91f1e125a3f9b11c111e504aea46b9ce33f03dc8efe4ef7c916c`.

## 1. Result and precise remaining work

The Opus report's internal mathematical reconstruction survives my checks in the consumed full-two-torsion specialization. Its five suggested wording changes mostly describe text already present in V4a or optional elaborations. I found one additional current-text scope omission: **V4a 08:335–367 states (O.9) without the odd-stage truncation.** The raw source CO:658–674 expressly limits the finite-stage bound to the minimum of the displayed right side and a prescribed integer R. That qualification must be restored to the current statement. The finite-budget proof and the downstream trace calculations use only the truncated bound, so this is not a found counterexample to those deductions.

I independently checked the primary Carayol theorem and obtained the original Casselman paper, including its local and global arguments. These supply substantially more of P5 than the Opus packet did. I did not obtain and inspect the original Shimura 1973 unary-theta theorem, nor an original proof of finite Chebotarev. Those remain explicitly named external inputs, with the exact unary statement recorded below. In particular, this report does **not** label all of P1–P6 independently closed.

The strongest conclusion justified here is conditional: given the actual even and odd coefficient forms with their specified characters, support, recurrence precision, and numerical bounds, together with the classical unary transformation and finite Chebotarev theorem, the finite-stage divided-operator construction gives the stated binary contraction and isolation rules. The special K-split seed also follows given the inherited even lower bound and the stated independence of K. The arithmetic lower bounds, theta producers, and final arithmetic contradiction are not consequences of this audit.

## 2. Sources and conventions

`CO` means `formalization/z-in-q/ProofSources/work/coefficients-frozen-4eaee875.tex`, SHA256 `5601423d1103cc61420d4d66db7d5b1b944aa9496f927f64699654e04d92a041`, 1029 lines. I read CO:644–1029, its referenced setup and producer interfaces, the full returned Opus result, and the original operator correction notes. `08` and `09` below mean the actual files in `drafts/z-in-q-candidate-preprint/review-v4a/`, not the V2 text supplied to Opus.

- `08-odd-source.tex`: SHA256 `1f67ce6c1a9070e68e0fb26a7fcf86709a1c75fbb6c12e1b41011c8249f58b1b`, 439 lines. Main operator range 297–439; support comparison 235–295 also read.
- `09-normalization-endpoints.tex`: SHA256 `1741bbe189d587db6e26af71ce71fbefd27acf4c35fd8177f4d35300b51abf5a`, 393 lines. In particular 121–177, 179–260, 263–330, and 372–374.
- Opus `work/opus-z-in-q/runs/ultra-falsify-theta-divided-operators-001/RESULT.txt`: SHA256 `dd6448dce60d718535a56db4fa0c71ed57abacbf6130d728e1478e13ac49d5d4`.

The full manifest in `SOURCE_PINS.json` also binds the previous T3 REPORT and CLOSURE and the three original operator/convention/conditional-coefficient notes. Their verdicts are not premises. My earlier moving-support report is used only for the adjacent finite-family interface described in section 9, not as proof of any T3 operator assertion.

The coefficient DVR in the operator proof is a finite extension of Z_2, with valuation normalized by v(2)=1. Reduction of Fourier expansions is modulo its maximal ideal. Divisibility before taking the unary quotient means divisibility by the integer 2. These cannot be interchanged. The fraction field and its degree may depend on the fixed theta stage and on U.

## 3. Original primary evidence

**Carayol.** I downloaded the original journal PDF from [Numdam](https://www.numdam.org/item/10.24033/asens.1512.pdf), saved it as `primary/carayol-1986.pdf`, SHA256 `d4a5fb6b1cd76f944f8948e06df1c7ad5656ae5ee14b9189178ee1e8f2b0dab8`, and rendered/read printed pages 409–411 (PDF pages 2–4). Sections 0.3 and 0.6 impose the relevant base-degree and unequal-residue-characteristic conditions; 0.7 Theorem A supplies the global two-dimensional compatible system and compatibility at every finite place away from the coefficient characteristic. Section 0.5 specifies the Hecke normalization through local factors, including the principal-series description. The extra discrete-series place condition is imposed when the totally real degree is even. The base here is Q, and the local variable prime is odd while the coefficient prime is 2. These hypotheses fit. The theorem includes existence; a separate uninspected Deligne citation is not needed to supply that same existence assertion for these cuspidal weight-two constituents. This is theorem-level primary verification, not a rereading of the complete 60-page proof.

**Casselman.** I obtained the original scan from the [research-hosted copy](https://lesesvre.perso.math.cnrs.fr/newforms-references/casselman.pdf), saved as `primary/casselman-1973.pdf`, SHA256 `7f91ebae1a8f5e695800f4afb9fc06d0e2ea0b3a476751a31a7c8c3f38ad537d`. I rendered/read all printed pages 301–314 (PDF pages 2–15). Theorem 1, p.302, gives the one-dimensional minimal-level vector space for an irreducible admissible infinite-dimensional local representation. Its proof, pp.303–306, treats supercuspidal, principal-series and special cases and gives the higher-level dimension formula. The conductor-factor comparison is on pp.306–307. Theorem 2, pp.307–308, is the global uniqueness statement; pp.312–313 explicitly relate common good eigensystems to one automorphic representation and compute classical multiplicities in Theorem 4. Its a-entry character convention is changed to the usual d-entry convention by contragredience/twisting; the level and dimension assertions are unaffected. Thus retaining old multiplicities, rather than replacing them by a single vector, is required and supported by the primary text.

**Ramsey.** I read the local original PDF `work/ramsey-2006.pdf`, SHA256 `c4dbde444169f075dc77dadb67a18f0348a450a9df32d16ef049e40e348ed0f4`, and directly inspected rendered printed pp.600 and 602. Its [published PDF](https://www.numdam.org/item/10.5802/aif.2195.pdf) has the theta multiplier (1.1) and the good-square-index Hecke formula in Theorem 1.1. At weight 3/2 that formula has middle coefficient psi(p)(-n/p) and last coefficient p psi(p)^2, matching the convention consumed in CO. Its overconvergent Theorem 1.2 is not a theorem about the classical bad operator needed here and is not used as one.

**Primary boundary.** The original Shimura 1973 article was located through the publisher, but its full text was not retrieved. No secondary note is counted as an original excerpt of that theorem. The unary transformation and finite Chebotarev remain external results in this reconciliation. A fully primary-bound P5 package should append the exact unary theorem below, and an identified finite Chebotarev statement. This is a documentation boundary, not a discovered false application of either theorem.

## 4. Levels, characters, and the precise unary input

The classical bad-operator claim at 08:313–320 can be checked directly and does not need Ramsey's overconvergent theorem. Let the old level be L with 4 dividing L and p not dividing L. For gamma=(a b;c d) in Gamma_0(Lp), conjugation by diag(p,1) gives (a pb;c/p d) in Gamma_0(L). In Ramsey's multiplier, the ratio of the quadratic factors is (p/d). The weight-3/2 multiplier therefore changes the scalar character to psi(p/·), while rational change of variable preserves cusp holomorphy. This proves the V_p claim.

For the extraction on the raised level, put delta_r=(1 r;0 p^2). The relation delta_r gamma=gamma_r delta_{r'} has r'=(b+rd)/(a+rc) modulo p^2 and

`gamma_r = ( a+rc, (b+rd-(a+rc)r')/p^2 ; p^2 c, d-c r' ).`

It is integral of determinant one and belongs to Gamma_0(Lp). Its lower-right entry is congruent to d modulo Lp. The map r→r' is a permutation because its fractional-linear determinant is one and a+rc is a p-unit. The theta multiplier is compatible: the lower-left entry gains the square p^2, and replacing d by d-cr' preserves the relevant quadratic and fourth-root factors since 4 divides c. The normalized square-determinant metaplectic sum is exactly coefficient extraction a(n)→a(p^2 n). Thus U_p=U_{p^2}V_p has the same raised level. Distinct fresh primes each enter only once. This supports 08:315 and the local argument, not a nonexistent good nonsquare-index Hecke operator.

The exact unary theorem consumed at CO:757–758 / 08:349–356 is: if lambda is an odd Dirichlet character modulo C (possibly induced, extended by zero on nonunits), then `sum_{m>0} lambda(m)m q^(m^2)` is a holomorphic weight-3/2 form on a level dividing 4C^2 with scalar character lambda chi_{-4}, in the theta-cubed convention. Choose C supported on the old S and divisible by the conductors and all sieved primes. Then lambda=eta chi_{-4}^i produces the prescribed coprimality sieve. Dilation by J changes the character to eta chi_{-4}^i(-J/·) and the level to a divisor of 4C^2 J. In particular each p|J has exponent one and p in U\J is absent from that unary term's original level.

This formulation avoids any assumption that the globally written symbol (p/·) has conductor p: when p is 3 modulo 4 its global conductor is 4p. Its **local p-component** is the primitive ramified quadratic character. All dyadic factors belong to the old support. The level and character assertions needed downstream are precisely local at p.

## 5. Integer divisibility and the missing odd-stage qualification

In the actual application every new prime is split in Q(E[2])=Q, n_U=delta+|U| is an integer, and e_U=0 (08:301–306). At index n=J r m^2, the originating squarefree coefficient is D=(U\J)r, as explicitly corrected at 08:322–325. Multiplication or division by the good square p^2 preserves every old local squareclass, including the current (D/ell_0)=1 support test. Off the exact filter the coefficient vanishes. The following calculation uses no CM comparison off that support.

After the eta phases are removed, the recurrence is b_0=1, b_1=a_p-kappa and b_{s+1}=a_p b_s-pb_{s-1}. If p|D, kappa=0, so b_s alternates 1,0 modulo 2 and the relevant difference is odd. Otherwise kappa is a sign and all b_s are odd, so the difference is even. The valuation before normalization is at least delta+|U\J|+omega(r)+|J|. Subtracting n_U leaves omega(r). This is the full-two-torsion form of CO:713–718.

At a fresh good p, full rational two-torsion gives a_p=p+1 modulo 4. Set Delta_s=b_{s+1}-b_s. All Delta_s are even, their recurrence makes Delta_{s+1}=Delta_{s-1} modulo 4, and direct subtraction gives

`Delta_1-Delta_0 = a_p^2-a_p kappa-2a_p+2kappa+1-p = 0 mod 4.`

Consequently Delta_s/2 has the claimed constant residue c_p(D) at every shell. No residual irreducibility assertion is involved.

Only r=1 can survive in B_U modulo the integer 2. On this shell factor `X=2^(|J|-n_U)a(D)`; the lower bound makes X integral. The divided recurrence differences have equal residues, and the remaining odd factors have residue one, so B_U[Jm^2]-B_U[J]eta(m) lies in 2O. The extra factor chi_{-4}(m)^i m is also one modulo the integer 2 because m is odd. Disjoint squareclasses J give divisibility of the entire unary-subtracted numerator by 2. This proves H_U integral without dividing by B_U[J], which may vanish or be even.

For an odd source this derivation is performed modulo 2^M, not with an exact eigenrecurrence. For a fixed bound W_U on |U| let N=max(0,delta+W_U), and prescribe an output precision R. Choose a weight threshold T with T-C_coarse>=N+R. Choose one actual stage satisfying M>=N+R, M>T+delta, and the stabilized minimum inequality through T. Above T the coarse bound alone pays N and leaves R; below T the minimum calculation applies. Every recurrence multiplier is integral, so arbitrarily many square-shell steps do not reduce the error valuation M. Expansion over the finitely many factors in U also retains that valuation before normalization. Thus at that stage, simultaneously for all Fourier indices and all |U|<=W_U,

`v(B_U[J r m^2]) >= min{R, omega(r)}`.

For the unused general bookkeeping the right-hand member is min{R,w(r)+#(simple p in J)/2-e_U}. Unary removal and the two-trace vanishing require only R>=2, with the normalization already paid. No infinite intersection of weight conditions is used.

**Correction R2.** Insert immediately before/after (O.9), 08:335–341: the even source satisfies the displayed estimate exactly; for the odd source fix W_U,R first, take one sufficiently advanced actual stage, and replace the right side by its minimum with R for all U of that budget and all Fourier indices. The two later sentences 08:365–367 and the proof 09:158–168 establish the needed truncated assertion, but do not make the displayed untruncated statement true as written. CO:658–674 already has the correct quantifiers. Finite-precision congruences do not bound arbitrarily high-weight coefficients beyond their precision. I found no use downstream requiring the stronger assertion.

## 6. Finite lattice, trace factor, and continuity

At a fixed stage and U, take the finite characteristic-zero space consisting of the good eigensystems occurring in theta H_U and the undivided corrections, with all old multiplicities and diamonds. Good Hecke operators act by scalars on each eigensystem and do not separate its old copies. Casselman's classical decomposition supplies the cuspidal interpretation; the Eisenstein part is treated by its two defining characters, not by pretending it is cuspidal. The weight-two good coefficient formula and the quadratic ratio between psi_U and each unary character prove integrality of every generator and translate of M, exactly as in 08:377–384.

For completeness the topological step at 08:385–390 has this short proof. Choose finitely many Fourier coordinates giving an injective linear map Phi:V→L^r. The integral module M maps into O^r and is therefore finitely generated over the noetherian DVR. A finitely generated O-submodule of L^r is closed (equivalently choose an O-basis in its span, or use compactness of O). Phi is a homeomorphism onto its finite-dimensional image. Scalar convergence on the finitely many eigensystems is convergence in End_L(V), even if a matrix changing to that decomposition has denominators. Hence a sequence of good T_q tending to t(g) sends each m in M to a sequence in M converging to t(g)m, and t(g)m belongs to M. The determinant case is identical. No integral projector, saturated lattice, or stage-independent denominator bound is needed.

Opus's alternate projector argument is valid after replacing V by the L-span of M: projectors preserve that span, and a common power of the uniformizer clears the finitely many matrices relative to an O-basis of M. It is an elaboration, not a missing premise. The precision needed for finite Chebotarev approximation may depend on the fixed stage; this changes how large the fresh primes must be, not their weight or the number of integer divisions in the theta source. It does not create a circular requirement that the theta stage anticipate its own spectral denominators.

For a fixed coefficient n and finitely many trace factors, choose distinct fresh good primes avoiding n and the level and approximating all involved Galois systems simultaneously. At every application the second Hecke term is zero, so the test becomes the original coefficient at n times the product of those primes. Different coefficients may use different testing primes; no one list must test every coefficient simultaneously.

The determinant scalar of a single character system reduces to one. On theta H_U the diamond formula leaves integral multiples of theta B_U[J]Theta_J. A fresh trace kills these modulo the maximal ideal because its new prime occurs to odd exponent in the tested index, while Theta_J has squareclass J and theta is one after reduction. Therefore d(u)t(v)=t(v), not a trace-free identity on all of M. The exact two-by-two trace identity then gives the two other displayed relations at 08:396–397. The current wording 08:392–394 expressly restricts their orbit; Opus's optional warning is already addressed.

In this specialization two fresh traces add two to omega(r), giving 4-divisibility in B_U and 2-divisibility after unary removal. Thus t(gu)t(u)=0 and the trace identity gives t(gu^2)=t(g) on the reduced test. Continuity and right-invariance under squares give invariance under the closed subgroup generated by them. The quotient is elementary abelian. Unramifiedness off S union U follows from the actual modular levels. This is a statement about the reduced test; it does not assert that the characteristic-zero representations are abelian.

## 7. Local identity and the actual omission calculation

The theta B_U term has local determinant character at p equal to the ramified quadratic character and admits a vector at exponent-one level. A unary term has this character when p|J and is from a level omitting p otherwise. In the ramified case conductor at most one and a ramified determinant force conductor exactly one. For a two-dimensional Weil–Deligne representation, a nonzero monodromy special block either has unramified determinant or, after ramified twisting, conductor at least two. With monodromy zero, conductor one forces zero Swan conductor and a one-dimensional inertia-fixed space. Its complement has the determinant's quadratic inertia character. Frobenius preserves these two distinct inertia characters because p is odd, so the two local lines split. This reconstructs the needed classification in this case.

Normalize the modular Galois representation so arithmetic Frobenius at a good q has polynomial X^2-T_q X+q<q>. Carayol's geometric-Frobenius/Hecke convention must be transported together with the dual convention, not changed by reversing Frobenius while leaving eigenvalues fixed. Local-factor equality then identifies the nontrivial degree-one Euler factor with the eigenvalue of the Fourier-normalized bad U_p on the minimal p-vector. Old copies at primes other than p carry that same scalar. At p-old constituents coming from the omitted level, inertia is trivial and no assertion that U_p is scalar is necessary.

Take tau with nontrivial quadratic inertia image and a Frobenius lift phi. Then rho(tau)=diag(1,-1), rho(phi)=diag(lambda,mu), and U_p=lambda on the ramified p-new vector. The quadratic tame character is the same for every ramified constituent, so one tau works for all. If z is the lower-right entry of rho(g), the differences t(g tau phi)-t(g phi) and t(g tau)-t(g) are -2z mu and -2z. Multiplication by lambda and lambda mu gives (O.12). It is an exact characteristic-zero identity. The visible 2 is never cancelled in a nonsaturated integral module. For Eisenstein constituents the two defining characters give the same calculation. This proves the identity on the indicated whole finite space, including all old multiplicities.

Put V=U\{p}. The omitted source is B_V or H_V formed from the **same** g, eta, psi, delta and stage. Its level omits the entire p. On applying (O.12) at coefficient one, fresh primes q'_0,q'_1 can realize g phi and g tau phi for both spaces simultaneously. Relative to the omitted-source normalization, the first-shell coefficient is

`2^(1+n_V-n_U-m_U+m_V) c_p(D') A(D'),  D'=V q',`

where m is the unary-division indicator. Here m_U=m_V=1 and n_U=n_V+1, so the factor is exactly one. Inertia flips the Legendre sign before division; consequently c_p(D'_1)=c_p(D'_0)+1 modulo 2. The omitted symbols agree since their representations are unramified at p. Summing gives exactly A(D'_0), with no depth change. Characters at every retained place multiply under the product Frobenius, including all external incidence characters. The restored ell_0 support is one such fixed condition, and p is different from ell_0. Both D'_i stay in that support when the original admissible product does.

At a vertex with trivial omitted label the trace is t(1)=2, hence zero after reduction. This is the asserted primary-isolation rule on nonempty configurations. It is not a rule deleting an empty configuration. The unused simple–simple multiplier would be 2 and thus zero; this audit does not need the general good-twin branch to obtain the actual E_ell application.

## 8. Special nonempty K-split seed

The premise is the inherited inequality 09:192–199, not merely the normalization a(1)=1. Once k is a minimum unit in the fixed negative even source, exact coefficient comparison for (D,k)=1 gives v(a_new(D))=v(a_old(kD))-v(a_old(k))>=omega(D). Under a supposed absence of nonempty K-split units, integral phase-removed valuations improve this by one on every nonempty admissible K-split product.

For p fresh and split in K, the positive-square-filter convention has psi/eta=chi_{-1}, hence eta odd and i=0. At the index-one squareclass kappa=1. With a=a_p(E^k), the recurrence gives a(p^2)=eta(p)(a-1), a(p^4)=eta(p)^2(a^2-a-p), and B_p[p]=eta(p)(a-2)/2. Subtracting the Theta_p shell gives

`H_p[p^3] = eta(p)^2 (a-1)(a-p-1)/4.`

The division is valid since a=p+1 modulo 4. The p-old Hecke polynomial and the ramified p-new line both imply U_p^2 t(phi)=U_p^3+d(phi)U_p. At coefficient one this is the relation on 09:209–210. A fresh p' approximating phi, split in K and with all fixed labels matched, makes pp' admissible. Its left term is eta(p)(a-1)a(pp')/4 up to the retained phase convention and vanishes modulo 2 by the improved bound. The determinant term at p vanishes after reduction: B_p and its Theta_p correction have identical characters and equal p coefficients; Theta_1 has none. Multiplication by theta does not alter this reduced computation. It is not an invocation of the invalid trace-free determinant assertion.

The remaining expression forces a=p+1 modulo 8 for every such p. Fresh ramification of K outside Q(i,sqrt(ell)) permits p=1 modulo 4, (ell/p)=-1, (k/p)=1. For E_ell the three nonzero rational two-torsion points have necessary halving differences -ell, ell and -4ell respectively; all are nonsquares. To see the criterion directly, for a proposed double at root e_i put u=x(P)-e_i, A=e_i-e_j, B=e_i-e_k. The tangent equations give u^2=AB and slope^2=2u+A+B, hence A slope^2=(u+A)^2 and B slope^2=(u+B)^2. The slope cannot be zero since A and B are distinct and nonzero. Thus both differences would be squares. No nonzero two-torsion point can be doubled, so the finite two-primary group has exponent two and order exactly four. Its point count is 4 modulo 8, as is that of its K-split twist. This contradicts the forced congruence.

Thus the nonempty seed deduction is valid for the actual curve and fixed independent K. This does not prove its inherited lower bound, or the prior availability of k. It does not extend the special conclusion to an arbitrary full-two-torsion curve with no corresponding nonsquare-halving prime class.

## 9. P1–P6 and the five optional items against current text

| Opus item | Current status and exact scope |
|---|---|
| P1 actual forms, phases, CM comparison | Still producer input here. 08:196–233 fixes the actual extraction and finite recurrence; 08:235–272 restricts the CM comparison to (D/ell_0)=1 and makes the complement zero. I verified T3 respects these statements, not the producer construction anew. T1/T2 primary reconciliations remain their owners' work. |
| P2 even lower bound and inherited E^k bound | The operator derivation is conditional on it. 09:192–199 explicitly derives the inherited bound from the exact source ratio and minimum, so the earlier danger of inferring a lower bound from a(1)=1 is absent in current text. The cyclotomic/common-scalar arithmetic establishing the original bound is outside T3. |
| P3 uniform odd lower bound | 09:121–156 puts the arithmetic bound before the odd minimum and proves the numerical ultrafilter implication. T3 uses only its stated coarse tail, bounded-weight stabilization, and fixed visible witness. This report does not prove the arithmetic inequality (F.4). |
| P4 one actual finite stage | Reconstructed in section 5 above; 09:158–168 and 237–260,320–330 use a finite budget then one stage. My separately sealed moving-support audit checked the compatible alphabet and every-address ell_0 support. Neither argument requires bounded coefficient-field degree as the stage varies. |
| P5 classical representation/Hecke inputs | Original Carayol and Casselman cover the cuspidal representation, local compatibility, newvector and multiplicity parts; Ramsey covers the multiplier and good-Hecke convention. Classical bad extraction is calculated above. The precise unary transformation and finite Chebotarev remain named external inputs with no original full theorem excerpt inspected in this task. |
| P6 graph/address realization | Separate from the operator proof. Current 09:249–330 gives the address construction; earlier moving-support report independently checked the common projection, nonempty packets, every-address support, and quantifier passage. That is adjacent-interface evidence, not independent T3 proof credit. No conclusion about the arithmetic endpoints follows from P6 alone. |

| Opus optional wording item | Reconciliation |
|---|---|
| Whole-prime omission via level, not only characters | Already explicit in current 08:429–431. Raw CO:983–985 is weak explanatory prose, but CO:995–997 has the same correct reason. No further V4a mathematical repair needed. |
| At least one trace factor in determinant identity | Already explicit in 08:392–397. The seed's separate bare determinant term is evaluated directly at 09:215–219. |
| Projector denominators / topology | A short elaboration is supplied in section 6. Current 08:385–390 is valid with the finite-dimensional topology argument and does not require an extra uniformity premise. |
| “Primitive” means the p-component | Current 08:405–418 is explicitly local, so its meaning is correct. A future stylistic clarification can say “determinant whose local p-component is ramified quadratic.” G-OPERATOR-JUNCTION's global parenthesis is less precise. |
| Requested raw line range ends at 1034 | CO ends at 1029. This is an audit-brief locator error, not a manuscript theorem defect. |

The additional R2 qualification to (O.9) is the only current mathematical statement-scope correction found here. It should be recorded separately from the already resolved optional items and from the uninspected primary inputs. The V4a sources and previous reports are unchanged.

## 10. Delivery boundary

`SOURCE_PINS.json` records exact inputs and primary-page identities; `RECEIPT.json` records final report hash and the verification of every pin. There are 19 directly read rendered primary pages in this task: Carayol 409–411, Ramsey 600 and 602, and Casselman 301–314. The extra Ramsey p.601 image was rendered but is not counted as directly read here.

No mathematical conclusion in this report uses a prior PASS label. No global closure, publication approval, Lean theorem acceptance, or proof of ordinary Z being Diophantine in Q is asserted.
