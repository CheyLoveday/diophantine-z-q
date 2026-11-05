# A068 independent second review

Reviewed 2026-11-05 against the unchanged manuscript SHA256 `a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e`. Input under review is `work/theorem-application-audit-20261105/closure/BATCH-009.md`. No shared source or audit file was edited.

I accept the bounded A068 closure. The connecting-map sign, arithmetic Frobenius prescription, ray-to-ring quotient, relative derivative group, and norm compatibility are consistent. No mathematical correction to the manuscript is required by this review. Two qualifications should remain explicit: the conductor used for the finite coefficient character must contain its actual ramification support, and an exact equality between Frobenius scalars at opposite orientations uses conjugate lifts. Both are available in the existing construction. The universal correction is independent of any other lift choice.

## Source inspection and scope

I read the corresponding manuscript passages, including lines 2630–2646, 2690–2707, 2738–2750, 2813–2826, 2944–2947, 3282–3344, 3421–3436, 3964–4040, and 8870–8879. I independently extracted the relevant pages from the pinned Milne *Class Field Theory*, v4.03, August 6, 2020, at `work/astra-final-moving-character-audit-001/primary/milne-cft.pdf`. Its SHA256 is `50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`. The extraction is saved here as `A068-MILNE-EXTRACT.txt` with printed page markers.

The verified locators are V Theorem 1.7 and proof, pp.150–151; the Frobenius definition and paragraphs 1.9–1.10, pp.152–153; V Proposition 3.3, p.157; V Theorems 3.5–3.6 and Remark 3.8, p.158; V Proposition 5.2, p.178; V Theorem 5.3, pp.178–179, and Theorem 5.5, p.179. The [current author PDF](https://www.jmilne.org/math/CourseNotes/CFT.pdf) identifies the same version. The source's Frobenius is the residue map x↦x^q, not its inverse.

The ring-class identifications in batch 9 are explicit deductions from locally principal ideals and these class-field statements. Milne's ray-class theorem by itself is not a theorem identifying every nonmaximal-order ideal with an invertible ideal. The batch correctly uses invertible fractional O_f ideals. The finite Chebotarev and Tate-image construction is the separate batch 8 input. I checked the Kummer sign and the extension conditions here, not a new proof of every Tate-image assertion in batch 8.

## Ring-class quotient and its sign

For a finite idele a, the lattice `K intersect a hat(O_f)` is locally principal with completion a_v O_(f,v), hence an invertible fractional O_f ideal. Principal changes and unit changes give exactly `A_(K,f)^*/(K^* hat(O_f)^*)`. A uniformizer at a prime outside f maps to the positive prime ideal, so this convention fixes the ideal sign.

At p|f the identity `O_(f,p)^* = Z_p^*(1+f O_(K,p))` holds. In `a+fb`, the scalar a must be a p-adic unit; otherwise its reduction is not a unit. Factoring it proves the identity. This gives the asserted quotient of the ray group and also an open finite-index subgroup to which V.5.5 applies. K is imaginary, so its complex place contributes no finite Artin obstruction. Unit groups at primes outside f are killed; V.5.2 and the local unramified Artin statement identify this with unramifiedness there. Because K splits at 2N, the claimed completions above those rational primes really are unramified extensions of Q_p.

The delicate moving-prime sign is correct. Let u have components beta at the two r-adic places and 1 elsewhere. Its residue ratio at the chosen orientation is beta/bar(beta). The finite idele u beta^-1 has components 1 at r and beta^-1 elsewhere. Its locally principal ideal is therefore the inverse of `(beta)`, interpreted as the prime-to-r principal ideal in Pic(O_r). Thus

`delta(res(beta/bar(beta))) = -[(beta)]`.

This does not say a globally principal O_r ideal is nontrivial. The notation on the right denotes the lift from ideals prime to r, whose r-adic generator is fixed to 1. That lift need not be principal in O_r. Its image in Cl(K) is principal. With this convention the relation is precisely

`sum m_j q_j + delta(res(alpha)) = 0`.

Milne V.1.7 instead sends a residue representative beta to the positive principal ideal `(beta)` in the ray class group. Its residue map is consequently the negative of this local-idelic delta. Batch 9 correctly distinguishes these maps rather than changing the Frobenius convention to conceal the sign.

## Full relation lattice and arithmetic Kummer prescription

The chosen q_j project onto generators of Cl(K). If R is the full kernel of `Z^s -> Cl(K)`, the kernel F_r^* together with the q_j generates Pic(O_r). A relation projects to R; subtracting its integer basis expansion leaves a relation within F_r^*. Therefore prescribing xi on q_j and on F_r^* extends if and only if the basis relations hold. This is valid for nonsplit extensions and uses neither division by the class number nor linear independence of the radical classes.

Write m=2^n and choose r with m|(r-1), avoiding the fractional beta supports and all ramification of the finite realization field. At the selected place, all relevant roots are units and reduction is injective on mu_m. If b^m=alpha and arithmetic Frobenius acts by zeta^c on b, then reduction gives

`zeta^c = b^(r-1) = alpha^((r-1)/m)`.

The chosen identification mu_m≅Z/m therefore gives exactly `kappa_r(res(alpha))=c`. The negative exponent in manuscript (4.4a) yields the negative weighted sum in (4.4b). Geometric Frobenius would reverse this value; it is not the source convention used here.

The compatibility argument for the radical prescription also checks out. At each odd nonzero-weight prime, every finite layer of K(mu_(2^infinity))/K is unramified. If a product of the radicands is an m-th power in that field, normalized valuations at these primes show m divides the corresponding weighted relation coefficients. Summing against the weights proves the required multiplier relation. Weight zero at the dyadic primes is essential and is explicitly part of the construction. This argument covers unit relations as well: zero valuations at every nonzero-weight prime give zero exponent for the prescribed multiplier. It is not an assumption that the radicands are independent.

The power map F_r^*→mu_m is onto. Each factor of `(F_r^* x F_r^*)/diagonal(F_r^*)` is onto via the residue ratio, with opposite orientation. By V.5.2 their Artin images are inertia images, so xi is surjective on either inertia group. At 2N it is unramified and its Frobenius image is zero because the corresponding q_j had weight zero. The quotient of a decomposition group by inertia is generated topologically by Frobenius; hence xi kills the whole decomposition group. No claim that H_r itself splits at 2N is needed.

## Conjugation, derivative primes, and norms

For any finite idele a, the product a bar(a) is the embedded rational norm idele. A finite rational idele is a rational number times an element of hat(Z)^*, both killed in the ring-class quotient. Consequently conjugation is inversion on Pic(O_f), and the subgroup defining H_f is stable under conjugation. H_f is normal over Q, with the asserted action. In particular `g^2 tau g^2 tau^-1` has trivial image in Gal(H_f/K) whenever g^2 fixes K. This supplies precisely the ring-class part of the torsion argument, independently of its Tate scalar calculation.

At a split q outside f, the two prime classes multiply to `(q)` and their arithmetic Artin symbols are inverse. At inert ell outside f, the unique ideal is `(ell)` itself, so its Artin symbol is identity. It therefore splits completely in H_f/K; each residue field is F_(ell^2), the residue field of K, not F_ell. This verifies the premise used before (H13).

For squarefree n supported on new inert primes, the kernel of Pic(O_(fn))→Pic(O_f) is

`hat(O_f)^*/(hat(O_(fn))^* O_f^*)`.

Indeed `K^* intersect hat(O_f)^*=O_f^*`. The only units are ±1, and both already lie in the denominator. At a new inert ell, reduction gives `F_(ell^2)^*/F_ell^*`, cyclic of order ell+1. Independent local factors give the full product in (H5), not a quotient by an omitted global-unit group. There is no asserted splitting of the entire class group.

The local rational uniformizer ell contributes no additional unramified factor even in H_(fn). Its single-place idele becomes 1 at ell and rational units at every other place after multiplying by the principal idele ell^-1. It is thus trivial. Each relative local group is its full inertia image. The group-ring identity for D_ell follows by direct coefficient comparison using sigma^(ell+1)=1; it divides by no even integer. The point trace and CM congruence identities remain separate inputs, as batch 9 states.

For norm functoriality, the source assumption that the ambient extension be abelian is satisfied in the applications to rational quadratic characters. Use the biquadratic compositum `K Q(sqrt(h))` over Q, or `Q(sqrt(D),sqrt(h_*))` over Q. V.3.3 then applies directly. At a prime of residue degree f its ideal norm is p^f and its Artin action is the f-th power of rational arithmetic Frobenius. This proves the character formula with the norm and introduces no inverse or missing residue-degree factor.

In the genus-character passage, the filter gives coprime odd fundamental discriminants D and h_* and Dh_* fundamental, as stated at lines 7901–7904 and 8810–8822. The separate biquadratic discriminant identity gives discriminant `(Dh_*)^2`; the tower formula gives relative discriminant 1 over F=Q(sqrt(Dh_*)). F has no real places. Therefore the character factors through Cl(F), and V.3.3 identifies it with `chi_(h_*)(Norm(a))`. D=1 is the trivial restricted character. This accepts the reciprocity application while retaining the separate discriminant identity as its stated arithmetic input.

## Actual finite coefficient characters

The coefficient descent is valid with the actual conductor choice. Take f divisible by the moving prime and by the supports of the rational quadratic characters in the finite family. These primes are outside 2ND_K, so such f is permitted by lines 2690–2707. It is not true for an arbitrary f merely prime to 2ND_K, and batch 9 should not be read as saying so. The manuscript expressly treats theta as an actual character of Gal(H_f/K), and permits inclusion of all these primes.

For positive squarefree h≡1 mod 8, its rational quadratic conductor is h. At a split q|h, a unit in O_(f,q) has equal nonzero residues in its two factors. Its norm has square residue, and the ramified quadratic local character kills it. Away from h the character is unramified and kills units. The same reasoning applies to each rational quadratic generator q^*: its conductor is the odd prime q, even if q^* is negative or is not 1 modulo 8. Restriction to imaginary K has no real-place obstruction. Thus the universal rational quadratic family also factors through the chosen ring-class quotient. Multiplication by the moving character preserves this property.

At finite stage i, the prescription `Psi=(1+t)^xi` is a genuine finite character. For n_i>=2i and 1<=k<i,

`v_2(binomial(2^n_i,k)) >= n_i-v_2(k) >= i`.

All higher terms vanish modulo t^i, so `(1+t)^(2^n_i)=1` in `(Z/2^i)[t]/t^i`. The case i=1 is immediate. This explains why exponent reduction modulo 2^n_i is legitimate. It does not require a single moving character valid for all coefficient stages.

Since conjugation inverts the ring-class quotient, Psi^tau=Psi^-1. Each rational quadratic character is both invariant under conjugation and equal to its inverse. Hence alpha^tau=alpha^-1 in the finite coefficient rings. This is pullback on the Galois argument; it does not send the ring variable t to any other element or invert the abstract group-ring basis.

## Frobenius lifts and orientation

At a graph prime q only its own quadratic factor is ramified. Changing a Frobenius lift therefore changes its universal scalar by either 1 or g_q. The moving and other quadratic factors are unramified. In the quotient R/(g_q-1) both scalars agree; so do their expressions r_q. Thus `(1+g_q)(r'_q-r_q)=0`. Since R=O[G] is free over the two-torsion-free O, cancellation of 2 is valid after writing r_q=1+2v_q. This proves the asserted independence before character evaluation and without dividing by |G|.

For opposite K-orientations, choose conjugate Frobenius lifts to obtain exactly z_q^-1. Arbitrary independent lifts may instead produce g_q z_q^-1; the already-proved lift independence gives the same correction. The rational elliptic representation has conjugate Frobenius matrices at the two orientations, so its trace a_q and determinant q are unchanged. The expressions e_q and l_q are symmetric in z_q and z_q^-1. The orientation conclusion therefore follows, with this explicit interpretation of the lifts.

## Disposition

Accept batch 9 within its stated scope. Its main sign and local-group assertions pass an independent check against Milne's arithmetic convention and the pinned consumers. No manuscript repair is required. For maximum precision, its finite-character paragraph can say “choose f divisible by the finite character conductors,” and its final orientation paragraph can say “with conjugate Frobenius lifts.” These are clarifications of hypotheses and choices already allowed by the construction, not new mathematical assumptions.
