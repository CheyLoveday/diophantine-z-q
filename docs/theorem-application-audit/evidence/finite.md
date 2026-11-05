# Independent finite arithmetic class-production audit

4 November 2026. Reviewer: /root/astra_moving_filter_audit.

## 1. Result and exact interface

I found no new gap in the finite class production used by section 3 of the corrected RC report and RD182–409, for the actual fixed non-CM curve and permitted ring-class data. The dyadic argument does not use Howard's odd-prime theorem at two. It replaces the two inapplicable ingredients—unmultiplied unique descent and integral splitting into Frobenius signs—by a uniform two-step multiplier and an integral Frobenius identity, with an explicit extra bit of prime precision.

This report fills the finite-class input imported by work/astra-final-rc-limits-independent-001/REPORT.md. It is not a fresh proof of that limit theorem, of the moving-character theorem A4, of analytic nonvanishing, of RC as a whole, or of the ordinary-integer definition. No Lean or other formal-proof credit is asserted.

The precise finite output is as follows. Fix E/Q, its integral Tate lattice, its normalized modular parametrization and the finite permitted local twisting types at 2N. One integer

    L=C_cusp C_bad 2^(2e),   L != 0,

is chosen before K, the old conductor, the number of active/derivative primes, or the finite coefficient precision varies. For any finite permitted derivative set and any retained target precision, choosing the working torsion level and new-prime congruences sufficiently high constructs actual target Selmer-cone classes P_I with

    f(P_(I union {ell}))=0,
    s(P_(I union {ell}))=J f(P_I).

The lower class is the previously constructed class, the old singular conditions remain imposed, and the equalities have target degree-zero boundary witnesses. The output holds with scalar Artin coefficients and with one actual finite universal group ring, before any sign-character specialization. The bound on L does not grow with the number of primes or the degree of a ring-class field. This is an existence statement at every requested finite stage; it does not say that one numerical prime works at infinite precision.

The permitted data mean: K is imaginary, split at 2N and different from the two extra-unit fields; the old conductor f is prime to 2ND_K; the finite character factors through H_f/K; its scalar deformation is trivial at 2N (and the universal quadratic character is actually trivial there in the binary application); new derivative primes are distinct, inert and outside 6fND_K. These are domain hypotheses supplied by the construction, not consequences of the local switch.

The accepted A4 input is precisely work/root-a4-final-review-001/RECEIPT.json and its REVIEW.md. I read their scope and verified their pins. They supply actual compatible moving characters, primitive inertia, exact local triviality at 2N, simultaneous odd exponents, fixed trace/determinant bounds, and finite prime realization. They expressly do not supply Heegner descent or arbitrary later cochain-evaluation prescriptions. I do not repeat or enlarge that accepted scope here.

## 2. Sources and primary theorem hypotheses

RD is formalization/z-in-q/ProofSources/work/ring-determinants-frozen-4eaee875.tex, especially 182–409. FD is formalization/z-in-q/ProofSources/outputs/finite-heegner-descent-audit.txt, read completely. The immediate target is work/astra-final-rc-unconditional-closure-audit-001/REPORT.md, section 3, lines 49–81. The earlier finite arithmetic independent report was read as a locator and challenged against the actual formulas; its verdict is not a premise.

I freshly extracted original PDF text and rendered/read these primary pages:

* Cai–Chen–Liu, Heegner points on modular curves, Transactions AMS 370 (2018), printed 3721–3722 and 3730 (PDF pages 1,2,10). Page 3730 contains Theorem 2.15. The opening hypotheses and curve definition on 3721–3722 were also checked visually.
* Howard, The Heegner point Kolyvagin system, arXiv:1202.6340v1, printed/PDF 19–21: the norm and reduction congruence (13), descent formulas, and Proposition 1.7.4. The explicit assumptions of Theorem A on PDF page 2 were read from the original extracted text.
* Lang, Algebraic groups over finite fields, American Journal of Mathematics 78 (1956), printed 555–557, particularly Theorem 1 and its corollary at 557. In the local PDF these are pages 2–4; page 1 is the JSTOR cover. The relevant pages were directly rendered and visually read. Empty OCR output from this scanned PDF is not described as a successful text extraction.

The CCL norm theorem is geometric. Take its initial conductor c to be the ENTIRE old conductor f and set m=1. Its finite set S contains 6fND_K, and the new prime ell is outside S. This allows f to include the moving split prime, active conductor primes and all other already chosen derivative primes; f is not required to be an inert squarefree product. In the actual all-split level situation, every prime of N splits in K, so their N1=1 and X_K(N)=X_0(N). The hypothesis (f,N)=1 holds. No inert-level or ramified-level clause of their generalized Heegner condition is needed. K excludes Q(i) and Q(sqrt(-3)), so the unit factor u1=[O_K^times:Z^times] equals one. For inert ell, Theorem 2.15 is exactly the unaveraged sum relation

    sum_(sigma in Gal(H_(f ell)/H_f)) P_(f ell)^sigma=T_ell P_f,
    [H_(f ell):H_f]=ell+1.

The theorem does not require an odd coefficient prime, residual irreducibility or good ordinary reduction at two. Its separate split-prime formula is consistent with the old moving-prime norm, but only the inert formula is needed for the local derivative switch audited here.

Howard's page 19 confirms the same point norm and the reduction congruence in his narrower conductor setup. His Theorem A explicitly assumes p odd, p,D,N pairwise coprime, and surjective Tate image over K; page 20 invokes E(K[n])[p]=0 to make descent unique; page 21 uses the two Frobenius eigenspaces to prove an automorphism. The actual curve has rational E[2], so these arguments cannot be imported with p=2. I use his pages only as primary corroboration of the geometric relations and comparison of formulas. Sections 4–7 below give the separate dyadic proof.

Standard inputs retained as such are the fixed non-CM open-image theorem (already in accepted A4), ring-class reciprocity/CM moduli, potential good reduction for a CM elliptic curve, injectivity of endomorphism specialization, the ordinary/supersingular classification of elliptic p-divisible groups, the good-reduction prime-to-p torsion comparison, smooth Neron models, the Kummer exact sequence, inflation–restriction and finite-index Shapiro/Mackey. Their use and hypotheses are stated below. I do not claim to have freshly re-proved all those classical theories. The nonstandard finite adaptation is proved rather than left as a named contract.

## 3. The point relations at arbitrary old conductor

Choose the normalized map X_0(N) -> J_0(N) -> E, P -> [P-infinity] -> pi(P), so pi(infinity)=0. At ell not dividing N, the Hecke action on this fixed elliptic quotient is a_ell and T_ell(infinity)=(ell+1)infinity. Subtracting these equal-degree cuspidal terms from the CCL divisor relation and pushing through the fixed quotient gives

    Tr_(H_(f ell)/H_f)(y_(f ell))=a_ell y_f.

This is one sum, without division by ell+1, a class number or a group order. If the source's chosen point conventions introduce a fixed cusp difference, Manin–Drinfeld kills the finitely many such fixed differences with C_cusp chosen once. For the normalized correspondence just displayed the relation is already exact. No varying-conductor cusp multiplier is used.

The reduction congruence is not a formal consequence of the trace relation. Here is its local reason at an inert ell outside 6fND_K. The old order O_f is maximal at ell and its completion is the unramified quadratic order over Z_ell. The CM elliptic curve has potential good reduction. If that reduction were ordinary, its rational p-divisible endomorphism algebra would be Q_ell x Q_ell, which cannot contain the unramified quadratic field supplied by the CM action and endomorphism specialization. Thus the reduction is supersingular.

Over an algebraic residue field a supersingular elliptic curve has p-rank zero and a-number one. Its unique subgroup scheme of order ell is alpha_ell=ker(Frob_ell). Every characteristic-zero cyclic ell-isogeny kernel extends by finite flat closure after good reduction and has that special fiber. Each conductor-raising quotient therefore reduces to the Frobenius quotient. If a chosen lattice description gives the isogeny in the opposite direction, use its dual: the raising target is still a quotient of the old curve by a cyclic ell-subgroup. The cyclic N-level subgroup, with ell prime to N, is transported under this same quotient. Because X_0(N) remembers the subgroup rather than a chosen generator, this introduces no level-generator scalar. The normalized map pi extends at the good prime and commutes with reduction and Frobenius. Consequently at compatible places

    red(y_(f ell))=F_ell red(y_f).

This is the geometric relation corroborated by Howard (13), with rational arithmetic Frobenius. It depends on maximality at the NEW prime, not on the factorization of the old conductor elsewhere. It therefore holds at arbitrary f and after every old class-group translate, provided the place is transported too.

The K-prime above an inert ell is the principal ideal (ell), with rational generator prime to the old conductor. Its ring-class Artin symbol is trivial, so it splits completely in every old ring-class field not containing ell in its conductor. Hence the lower residue field is F_(ell^2), and F_ell^2 red(X)=red(X) for the lower point and all its old derivatives. The new relative ring-class extension has full inertia of order ell+1 at ell and is locally totally ramified. These facts are used separately: old splitting makes the lower finite coordinate a Kummer evaluation, while new total ramification permits the upper finite-coordinate calculation.

There is no mismatch between that Frobenius choice and the one used for finite localization. In the generalized dihedral group Gal(H_(fn)/Q), every element outside Gal(H_(fn)/K) has square one. A rational Frobenius at an inert prime lies in that coset; its square is therefore trivial on the whole upper ring-class field. Thus the same rational Frobenius square may be used inside the upper-field subgroup, not merely some unrelated Frobenius lift.

## 4. One uniform torsion bound and one descent

Fix d>=2 with 1+2^d M_2(Z2) in the Tate image of this fixed E. Put u=1+2^d, choose g with rho(g)=uI, fix complex conjugation tau, and set z=g^2 tau g^2 tau^-1. The square g^2 belongs to every quadratic subgroup. For every imaginary K and every ring-class conductor, complex conjugation inverts the abelian ring-class action, so z acts trivially on that field. Its Tate action is u^4 I. Therefore all its two-primary rational torsion is killed by

    2^e,  e=v2(u^4-1)=d+2.

The unit part is invertible on two-primary torsion. This is one exponent before K or the conductor varies. It does not claim E(H_f)[2]=0 and does not require a bound on a class number.

For n a product of distinct new inert primes prime to fD_K, the ring-class residue-unit sequence and CRT identify

    Gal(H_(fn)/H_f)=product_(ell|n) F_(ell^2)^times/F_ell^times.

The global units are +/-1 and have trivial image in each quotient. Each factor is cyclic of order ell+1, and the operators D_ell=sum_(j=1)^ell j sigma_ell^j commute. The exact group-ring identity

    (sigma_ell-1)D_ell=(ell+1)-Norm_ell

and the norm relation imply that c=kum(D_n y_(fn)) in H1(H_(fn),E[2^a]) is invariant under the entire relative group, provided 2^a divides every ell+1 and a_ell.

Let H=G_(H_(fn)), G0=G_(H_f), Q=G0/H and M=E[2^a]. The inflation–restriction segment is

    H1(Q,M^H) -> H1(G0,M) -> H1(H,M)^Q -> H2(Q,M^H).

The module M^H is killed by 2^e. Its cochains, and hence both outside groups, are killed by 2^e regardless of |Q|. Thus 2^e c lifts to some b in H1(G0,M). Define D(c)=2^e b. Two choices of b differ by an element killed by 2^e, so D(c) is well defined. Its restriction is 2^(2e)c. Additivity follows by lifting sums; coefficient naturality follows by pushing a lift through the coefficient map and using the same independence argument.

Intermediate-field compatibility is equally exact. If H is contained in G1 contained in G0, the restriction of b to G1 lifts 2^e c for that intermediate extension. Hence restriction of D(c) is the same one-time construction over G1. For the empty derivative set use D(c)=2^(2e)c. This convention is essential: the empty and nonempty lower classes have the same scaling. Nothing is descended successively prime by prime. An order-dependent power 2^(2e times number of primes) would be a different construction and is not needed.

The two multiplications do different jobs. An abstract map Z/4 -> Z/4 given by multiplication by two has kernel and cokernel killed by two, but the element one does not lift; the element two has two lifts whose difference is killed only after multiplying again. The source uses exactly the amount of scaling justified by the obstruction and ambiguity, not a fictitious unscaled inverse to restriction.

## 5. Local Kummer conditions at 2N and other old places

At every prime over 2N the conductor extensions are unramified. Let F'/F be any finite such local extension, including the case where F is itself an unramified completion of an old ring-class field. Let B be the actual permitted local quadratic twist. Its identity component has

    H1(Gal(F'/F),B_0(F'))=0.

Here is a proof without averaging by the possibly even degree. On the connected special fiber let Frob denote residue Frobenius and r=[k':k]. A cyclic cocycle is x with (1+Frob+...+Frob^(r-1))x=0. Lang's surjectivity on the connected algebraic group gives y over the algebraic closure with (Frob-1)y=x. Then (Frob^r-1)y=0, so y already belongs to the k'-points. This proves H1=0 in the special fiber, even when r is divisible by the residue characteristic.

For the formal kernel B_1(F'), each successive filtration quotient is an additive residue-field module with its unramified semilinear action. A normal basis identifies it with an induced cyclic module; H1 vanishes, also at residue characteristic two and even r. Induction in the finite filtration gives H1=0 for each finite quotient B_1/B_n. For a fixed cocycle the sets of formal points solving its coboundary equations modulo B_n are nonempty, closed, nested subsets of the compact B_1(F'). Their intersection is nonempty. Thus H1(B_1(F'))=0. Smooth reduction is surjective, and the exact sequence with connected residue points proves the assertion for B_0.

The quotient B(F')/B_0(F') embeds in the finite geometric component group. Its order kills H1(Gal(F'/F),B(F')), by the cohomology exact sequence. If a class in H1(F,B[2^a]) becomes Kummer over F', its image in H1(F,B) restricts to zero. Inflation–restriction identifies it with a class in that killed H1 group. Multiplying by the geometric component-group order therefore puts the original class into the local Kummer image.

Geometric component groups are unchanged by unramified base extension. There are finitely many old rational primes and permitted local twisting types. Their component orders have a single product C_bad, independent of the degree of F'/F and of the old ring-class completion F. This is why the possibly unbounded unramified degrees do not enlarge L. The descended class multiplied by C_bad is Kummer at all 2N places, for every working torsion level. No good-ordinary or semistable assumption at two appears.

At a good odd prime outside the conductor and N, the upper Kummer class is unramified. The extension is unramified, so the inertia subgroup is unchanged and lies in the upper group; restriction shows that the descended class is unramified there. The active and moving primes have the full local condition. Multiplying once by C_cusp C_bad preserves all existing conditions and equalities. Thus L=C_cusp C_bad 2^(2e) has exactly the uniformity claimed.

## 6. The singular coordinate at two, with the exact torsion error

Fix a new inert ell and apply all other commuting derivative operators first. Denote the resulting lower and upper points by X and Y. The point relations give

    Norm_ell Y=a_ell X,
    red(Y)=F red(X),  F^2 red(X)=red(X),
    F^2-a_ell F+ell=0.

The last equation is the endomorphism polynomial of arithmetic Frobenius on the reduced elliptic curve; it is not a mod-two approximation. Use the same L everywhere. Choose Q with 2^a Q=LX. Because the old lower field splits at ell, the finite localization of the old descended class is the Kummer coordinate

    f_old=(F^2-1)red(Q)=(a_ell F-(ell+1))red(Q).       (1)

This is the actual previous class: the intermediate-field compatibility of section 4 restricts it to the Kummer class of LX, without another descent multiplier.

Choose Z with 2^a Z=L D_ell Y. The upper descended class has restriction equal to that Kummer class over the upper field. Its cocycle b can be chosen with b(h)=(h-1)Z on the upper-field Galois subgroup H. Indeed any difference of these restricted representatives is a coboundary of an element of E[2^a]; subtract the same global degree-zero coboundary. This changes no class and makes the displayed equality literal.

For the oriented inertia lift sigma put

    U=(sigma-1)Z-b(sigma).

Comparing b(h sigma)=b(h)+h b(sigma) with b(sigma (sigma^-1 h sigma)) shows hU=U for every h in H. Thus U is an actual point of the UPPER GLOBAL RING-CLASS FIELD, not an arbitrary division point in an algebraic closure. Its multiple is

    2^a U=L((ell+1)Y-a_ell X).

If 2^a divides ell+1 and a_ell, the point

    U0=L((ell+1)/2^a)Y-L(a_ell/2^a)X

also belongs to that upper field and has exactly the same 2^a multiple. Therefore U-U0 is global upper-field two-primary torsion, killed by 2^e. This rationality check is indispensable: two arbitrary division points would not have a uniform torsion bound.

Inertia acts trivially on the geometric residue field. Reducing b(sigma)=(sigma-1)Z-U therefore gives -red(U). Substitute U0 and red(Y)=F red(X), then use 2^a Q=LX. The singular coordinate is

    s_new=(a_ell-(ell+1)F)red(Q)+epsilon,
    2^e epsilon=0.                                    (2)

Expanding in the endomorphism ring and using F^2=a_ell F-ell gives the exact identity

    (F-a_ell)(a_ell F-(ell+1))=a_ell-(ell+1)F.          (3)

Hence s_new=(F-a_ell)f_old+epsilon. Under T/2^a T=E[2^a], the coefficient quotient to T/2^m T corresponds to multiplication by 2^(a-m) on torsion points. Choosing a-m>=e kills epsilon. Choose the rational Frobenius on T to agree with the fixed conjugation matrix J modulo 2^(a+1). It then has a_ell=0 and ell=-1 to that precision. At retained level m equations (1)–(3) give

    s_new=J f_old.

No division by two in the Tate lattice, no integral J-eigenspace decomposition, and no residual irreducibility have been used. This is the replacement for the particular odd-prime comparison in Howard 1.7.4. It proves exactly the local relation needed in the finite diagram, without asserting Howard's entire odd-prime Kolyvagin-system theorem at p=2.

## 7. The new finite coordinate and its additional bit

The finite coordinate is separate from the singular one. All inertia translates of Y reduce to the same point. Thus

    red(L D_ell Y)=ell(ell+1)/2 * F red(LX).             (4)

If v2(ell+1)>=a+1, the right side is 2^a times a point fixed by F^2. The extension is locally totally ramified and the same rational Frobenius square lies in the upper-field subgroup, as checked in section 3. On that subgroup b is the Kummer cocycle of L D_ell Y. At the good odd prime ell the formal group is uniquely 2-divisible: the multiplication-by-two power series has unit linear coefficient, hence is an isomorphism on the formal group. Reduction identifies the finite Kummer quotient with the corresponding quotient of E(F_(ell^2)). Formula (4) is zero in that quotient. Therefore

    f_new=0,

already at the working level, and hence at level m. If one changed the representative or used the canonical descended class only up to its bounded ambiguity, the same projection a to m removes that ambiguity as in section 6.

The inequality a+1 cannot be replaced by a: if v2(ell+1)=a then v2(ell(ell+1)/2)=a-1, and (4) need not be divisible by 2^a. This is a genuine dyadic loss. It is paid by a stronger prime congruence, not by increasing L. The other loss a-m>=e removes the global torsion error. These are distinct requirements and both are present.

The full relative cyclic generator and its pro-two component give the same value on a two-primary local cocycle with trivial retained inertia action; its odd-order component contributes zero. One can choose the full generator with the prescribed pro-two component. Thus compatible orientations introduce no power of two or untracked odd-unit mismatch. Arbitrarily changing an orientation afterwards could change a unit factor; the source retains the orientation rather than making that change.

At every earlier derivative prime, repeat (4) with all the other commuting D operators applied first. Its finite coordinate remains zero. Repeating (1)–(3) gives its corresponding local comparison with the correct lower class. This directly proves preservation of old singular conditions; it is not inferred just from a dimension count.

## 8. Finite coefficient levels and prime choice

For a requested target A_m=(Z/2^m)[t]/t^m, or A_m[G], first choose an untwisted torsion working level a>=m+e. Choose all required Frobenius congruences at least to 2^(a+1), including the extra bit in section 7. The independent local pairing construction may also ask ell^2=1 modulo 2^(a+1), which is implied by ell=-1 to the stronger precision. Construct and descend the untwisted E[2^a]-class, project to E[2^m], and only then extend to the finite Artin coefficient ring and apply its finite character. This order avoids the false demand that a character on A_m lift to A_a.

For plain finite class production, a rational conjugation element tau already supplies the consistent inert Frobenius target in every finite compositum. In the later evaluation construction the actual target is tau u for u in the exact kernel; its restrictions are still automatically compatible. Finite Chebotarev is applied after this actual element is given, to a finite normal quotient including higher Tate precision, old finite characters and old fields, and outside a finite avoidance set. This is not an extra arbitrary prescription imposed on the A4 moving prime. A4 chooses r and the scalar character first; a NEW inert derivative prime is chosen afterwards. No prime-size bound or infinite-extension Chebotarev assertion is used.

At a later finite extension of the diagram, older derivative primes have their already chosen finite congruence levels. In a cofinal sequence, the common retained level can be lowered to the minimum of finitely many available cofinal precisions minus the fixed losses. This remains cofinal. At one isolated finite stage the asserted result is only at its available level, not at every higher level. The canonical cohomological descent is compatible with these reductions, so the old and new retained classes differ only by the actual boundary witnesses discussed next.

## 9. Unaveraged Shapiro push and target boundary witnesses

Let Delta=Gal(H_f/K) and let theta be the actual finite scalar character, or scalar times the universal group-valued character, trivial on G_(H_f). With the diagonal action on T_A tensor A[Delta], the map

    v tensor [delta] -> theta(delta) v

lands in T_A(theta) and is G_K-equivariant: applying g gives theta(g delta)rho(g)v=theta(g)rho(g)theta(delta)v. With the inverse convention one inverts BOTH appearances consistently. Finite-index Shapiro followed by this map is a finite coset sum in every cochain degree. No 1/|Delta|, character idempotent, or Fourier interpolation is used. The same formula is integral over A[G] before any sign evaluation.

The lower and upper weights agree because theta factors through the old field. Mackey decomposition expresses local restriction of this push as the sum of restrictions at transported places. If an old rational Frobenius is gamma, its transported version is delta^-1 gamma delta. The identity

    rho(delta)rho(delta^-1 gamma delta)=rho(gamma)rho(delta)

makes every transported term satisfy the same final J relation. Scalar/group-ring weights commute with these Tate matrices. At the inert K-prime, Frobenius square acts trivially on the old ring-class character. One does not extend an anticyclotomic character to a rational Frobenius without specifying an extension. The local coefficient module is identified over G_(K_ell), and the Tate gamma supplies J. Therefore both f_new=0 and s_new=J f_old hold after the unaveraged push, with exactly the same L.

At 2N, A4 gives actual local triviality of the scalar deformation. In the universal binary application, the actual universal quadratic character is also locally trivial before mod-two reduction, by the accepted graph/local-squareclass input to the arithmetic construction. In a permitted scalar twist, use B=E^(h) and the natural twist identification. Kummer restriction and corestriction commute with these maps: each local Mackey term is a Kummer class and the A-linear sum remains one. The assertion would be false if one replaced actual triviality by mere triviality modulo two; the actual source does not make that replacement.

Now choose cocycle representatives after the finite push. Membership in a local Kummer or plane condition means that a representative in the condition and a local degree-zero cochain compare its image with the global restriction. These entries form an actual cycle of the Selmer cone. Every local condition used for class detection maps isomorphically on H0 and injectively on H1: Kummer does so with its derived torsion H0, full conditions do so identically, and derivative finite/singular conditions retain the full H0. The cone long exact sequence then injects H1(Selmer) into global H1. Thus the additive/coefficient/norm equalities of the underlying global classes are equalities of the actual Selmer classes whenever both sides satisfy these conditions. No ghost local H0 class obstructs their comparison.

Equality of target H1 classes means by definition that the difference of target cocycles is d b for some target degree-zero cochain b. Retain that cochain. This is an existence of finite witnesses in the target, not a claim that cohomological equality alone prescribes their future limit. For a contraction (i,p,h) with pi=1 and 1-ip=dh+hd, retain pz and pb. Then

    z-z'=db  implies  pz-pz'=d(pb),
    p'f z-p'f i pz=d(p'f h z)

for a closed z and an original comparison map f. These formulas exhibit the retained boundaries for class comparison and for transport through a changed representative. Restriction, Shapiro and coefficient maps are actual cochain maps, with their natural comparison homotopies. Their push happens before compression, so there is no need to retain one target variable for every ring-class coset.

The finite source proves existence of all these cycles and boundary witnesses for every finite set of imposed comparisons. The separate limit theorem must retain them with the same original maps; the already sealed limits review checks that step. Neither finite class production nor that later retention is inferred from independent sign-character calculations.

## 10. Adversarial checks and exact conclusion

The following failure modes were explicitly tested against the construction.

* Rational two-torsion invalidates Howard's unmultiplied unique descent. The two factors 2^e kill obstruction and ambiguity, and the empty derivative set has the same 2^(2e) scaling.
* Descending separately at each prime would destroy uniformity. The actual operation is on the full relative group, with exact intermediate restriction compatibility.
* An even unramified degree prevents averaging. Lang, normal basis and compactness prove the needed H1 vanishing without division by that degree, including at residue characteristic two and over old unramified completions.
* A norm identity alone does not give the local comparison. The maximal-order supersingular reduction, the actual rational point U0 and identity (3) are all necessary and are supplied.
* A pair of arbitrary division points can differ by unbounded torsion. U and U0 lie in the same upper global ring-class field, so the fixed scalar bounds their difference.
* Precision a on ell+1 does not pay the factor 1/2 in (4). The explicit a+1 bit does. It is independent of the a-m>=e loss.
* A finite Artin character need not lift to a higher Artin ring. The construction works untwisted at higher torsion level, then reduces and pushes the already available character.
* The Frobenius square used for the upper finite coordinate must match the chosen rational Frobenius. Its generalized-dihedral square fixes the whole ring-class field, so it lies in the required upper subgroup.
* Separate characterwise constructions would not give an integral universal class. The diagonal induced-module map constructs it over A[G] before character evaluation.
* Equality of global or local classes does not choose a cochain boundary. Actual local representatives and degree-zero boundaries exist, are chosen in the finite target, and are retained by the explicit contraction formulas. The derived local H0 prevents additional invisible Selmer classes.

No new correction to the finite class-production source was needed on this scope. The review establishes the finite producer used by the existing limits review, conditional only on the stated classical geometric/cohomological inputs and the accepted A4 exports, with their exact domains preserved. It does not add a new project-specific arithmetic assumption. It also does not award global RC, ordinary-integer, or formal-proof acceptance.

All original reports, raw sources and primary PDFs were preserved. New artifacts consist only of this report, source pins, a receipt, and selected extracted/rendered primary pages. No finite computational replay, runtime job or manuscript edit was performed.
