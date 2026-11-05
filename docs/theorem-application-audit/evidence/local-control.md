# Independent check of P19 local augmentation and the central correction factor

Scope: the newly added P19 and section 3 of `work/astra-rc-primary-coverage-002/REPORT.md`, and their consumer in V4f `07-even-source.tex:106–126`. This is an independent local argument, not acceptance of the ledger's verdict or of the global restricted converse. No manuscript, frozen declaration, runtime, or integration artifact was changed.

**Finding.** The stated local argument is sufficient for the actual elliptic Tate lattices. It produces a fixed integral correction factor with nonzero central value, without a finite-Sha assumption. I found no missing local hypothesis. Its conclusion concerns full local Iwasawa H2 and the specified inertia comparison cones; it does not prove Selmer control, specialization of H1, or central saturation. Those are separate inputs in the current sources.

## 1. Sources read and exact coefficients

I directly read the original rendered Nekovar pages 83, 96–97, 203–204, 214–215 and Milne ADT pages 26–28, 41. The first three Nekovar and four Milne renders are new artifacts in this directory. The other four Nekovar renders are the pinned originals in the primary ledger. The accompanying text extracts were used to navigate, not to resolve formulas against the images.

Nekovar 3.4.2 supplies exactness of continuous cochains for the admissible coefficient sequences used here. Sections 4.1.3 and 4.2.1–4.2.3 supply the inverse-limit sequence, finite-cohomology condition (F), its Mittag–Leffler consequence, and finite generation. Proposition 8.3.5(ii) identifies Iwasawa cohomology with the corestriction inverse limit. Proposition 8.4.8.1(ii), its displayed proof sequence (8.4.8.1.1), and Corollary 8.4.8.2 give derived augmentation and its cohomology sequence.

The module in the consumer is a fixed integral lattice in the elliptic representation V_h = V_2(E^h), with the actual quadratic character included. V4f E07:27–60 fixes the inverse-action Shapiro convention and retains the dyadic character. It is not the untwisted lattice evaluated after dropping that character. At a fixed local field F, one may first take T = T_2(E^h). A fixed commensurable G_F-stable lattice has the same rational conclusion: finite-index comparison has finite local cohomology at every relevant degree. The allowed local quadratic types are finite. None of these steps permits an arbitrary Tate twist of V_h.

## 2. The local finite-coefficient input includes residue characteristic two

Milne I.2.1, pp.26–27, assumes torsion order prime to char(F), not prime to its residue characteristic. Here char(F)=0, including F over Q_2. Thus finite 2-primary G_F-modules have finite cohomology. Corollary I.2.3, p.28, identifies

    H^r(F,M^D)  =  H^{2-r}(F,M)^*                 (r >= 1),
    H^0(F,M^D)^completion  =  H^2(F,M)^*.

For finite M the completion can be omitted. The same statement gives vanishing above degree two (apply it to the finite dual module). Consequently every finite extension F_n/F has the finite-cohomology condition (F) required by Nekovar and 2-cohomological dimension at most two for these modules. There is no exclusion of bad or supersingular reduction in this argument.

There is also a direct integral proof of the decisive rational vanishing. Set A=E^h/F. The Weil pairing identifies the finite dual of A[2^n] with A[2^n]. Milne I.2.3 therefore gives perfect pairings

    H^2(F,A[2^n]) x A[2^n](F) -> Q/Z.

They are functorial: the map induced by [2]: A[2^(n+1)] -> A[2^n] on the left is dual to inclusion on the right. Nekovar 4.2.2 identifies continuous cohomology with the inverse limit, because the preceding finite H1 groups satisfy Mittag–Leffler. Hence

    H^2(F,T_2 A)  =  Hom(A(F)[2^infinity], Q/Z).

Milne I.3.3, p.41, states that A(F) contains an open subgroup of finite index isomorphic to O_F^dim(A). This subgroup is torsion-free in characteristic zero. The torsion subgroup injects into the finite quotient, so A(F)[2^infinity] is finite. It follows that H^2(F,T_2 A) is finite and H^2(F,V_2 A)=0. This proves the vanishing used by P19 without any global Mordell–Weil, Selmer, rank, or Sha assumption. The proof uses Milne's stated local logarithm lemma; it does not claim a new proof of that theorem.

Equivalently, rational local duality gives H^2(F,V_h) dual to H^0(F,V_h^*(1)); the elliptic Weil pairing identifies the latter representation with V_h, whose invariants vanish by the same finite local torsion argument. The dual and the twist are essential.

## 3. Derived augmentation, finite generation, and H3

Take a genuine procyclic Z_2 quotient Gamma of G_F and Lambda=Z_2[[Gamma]], t=gamma-1. Use Nekovar's completed induced coefficient module with the inverse action, so its quotient by t is exactly T. It is finite free over Lambda. Multiplication by t gives the short exact coefficient sequence

    0 -> F_Gamma(T) --t--> F_Gamma(T) -> T -> 0.

Nekovar 3.4.2 applies to these admissible modules. The two-term free resolution [Lambda --t--> Lambda] and the resulting exact cochain sequence give, as in 8.4.8.1(ii),

    RΓ_Iw(F,T) tensor^L_Lambda Z_2  ≃  RΓ(F,T).

This is derived base change, not naive specialization of cohomology. In particular 8.4.8.2(i) gives precisely

    0 -> H^2_Iw(F,T)/t -> H^2(F,T) -> H^3_Iw(F,T)[t] -> 0.

Finite generation over Lambda is not being inferred merely from finite generation over Z_2. Apply Nekovar 4.2.3 to the Lambda-coefficient induced module: finite-length Lambda-modules are finite 2-primary groups, so the local (F) condition just verified applies. The proof of 8.4.8.1 on p.215 also explicitly records finite generation over the Iwasawa coefficient ring.

The H3 vanishing asserted by P19 is justified, but stronger than necessary. At every finite local level F_n, Nekovar 4.1.3/4.2.2 removes the lim^1 of finite H2 groups, while finite-coefficient cohomology vanishes in degree three. Thus H^3(F_n,T)=0. Proposition 8.3.5(ii), with its finite-length joint inverse-system proof on pp.203–204, identifies H^3_Iw with the corestriction inverse limit of these zero groups. This accounts for the possible inverse-limit degree shift; simply citing discrete cohomological dimension would not suffice.

For the desired conclusion, the displayed injection alone is enough: after inverting 2 its middle term vanishes, so H^2_Iw(F,T)[1/2]/t=0, irrespective of the last term.

## 4. What Nakayama proves, and the finite sign group

Let N=H^2_Iw(F,T). Localize at the height-one prime (t) of Lambda. Here 2 is invertible. The preceding injection and finite generation imply N_(t)/t N_(t)=0, so Nakayama gives N_(t)=0. Choose finitely many generators of N. The definition of localization supplies, for each generator, an annihilator outside (t); their product annihilates N and is still outside (t). Therefore one can choose an integral annihilator a(t) with a(0) nonzero. This argument supplies an annihilator, not just a characteristic ideal whose support might overlook smaller-dimensional torsion.

It does not assert that N=0 or that a(0) is a 2-adic unit. Fixed 2-primary factors and positive valuation of a(0) are allowed. They are paid by the fixed integral correction/denominator in the consumer.

The finite order-two cyclotomic sign part cannot be averaged away integrally. One first retains it, or passes to the finite base field over which the remaining quotient is Z_2. The preceding proof holds for that finite local field as well. After inverting 2, finite-group invariants, isotypic projections, and descent are exact. Their central fibers are local cohomology of the appropriate actual finite character twists and therefore vanish in degree two by section 2. Finite induction and finite sums over primes preserve this conclusion. If an open subgroup uses t'=(1+t)^d-1, then t'/t has nonzero constant d and is a unit after localization at (t). Thus changing the procyclic open subgroup does not introduce or conceal a central factor. The argument never divides by the sign-group order before rationalization.

## 5. The actual local comparisons and one F_E

E07:106–112 starts with Kato's H2_0, the kernel of localization at two. The quotient of full H2 by that kernel is a submodule of the full local Iwasawa H2. An annihilator of the latter pays for this quotient. This is the module to which sections 2–4 apply; no ordinary or finite Selmer local condition is substituted for it.

At a fixed odd bad prime use W=H^1(I_F,V_h), exactly as E07:125–126 requires. The local Hochschild–Serre sequence, the prime-to-residue coefficient characteristic, and the cohomological dimension-one inertia/residue terms identify

    H^2(F,V_h)  =  coker(Fr-1 : W -> W).

Here W is finite dimensional. Section 2 makes this cokernel zero. Therefore Fr-1 is invertible on W, and the determinant of the specified j_*-to-full cone has nonzero value at central specialization. This conclusion is independent of arithmetic/geometric Frobenius inversion as long as the displayed cone convention is used consistently. Replacing W by V_h^I(-1) at an arbitrary bad prime is not justified or needed.

At active good primes the actual quadratic inertia action is -1, and after inverting 2 the inertia cohomology in question vanishes. At unused good primes E07:114–124 retains the separately displayed cone and the explicit factor E.1. Those varying factors are not put into a supposedly fixed F_E. This review verifies the local nonvanishing input and which comparison module it applies to; the exact E.1 normalization is the distinct pinned Kato primary review.

There are only finitely many quadratic squareclasses over each fixed local field and only finitely many fixed bad places. Choose the factors for those actual local types, take their product before h varies, and clear the finitely many fixed lattice denominators. Each factor has nonzero central value, so their product F_E does too. This construction is sufficient for the fixed-factor assertion; it does not require a uniform torsion bound over an infinite family of unrelated local fields.

The moving-character complexes in A03a are a different family. A03a:120–145 defines actual Kummer local conditions at 2N using local triviality of the moving character and derived scalar extension; A03a:158–186 states the support comparison with its unramified hypotheses. P19 neither proves these Kummer duality statements nor identifies their H1 by naive augmentation. The consumer keeps them separate, so the use of full local cohomology here does not change those conditions.

## 6. Refutation checks and remaining boundary

The argument would fail for a general representation. For example V=Q_2(1) has H^2(F,V) nonzero. Likewise the abstract complex [Lambda --t--> Lambda] in degrees one and two has H2=Lambda/(t): derived augmentation holds but does not exclude t-torsion when the central H2 is nonzero. Thus derived control alone is not the proof; the elliptic duality and finite local torsion input is indispensable and was checked above.

Finite generation is also indispensable for Nakayama. The module Lambda[1/t]/Lambda has N/tN=0 but N_(t) nonzero. It is not a counterexample to the current argument because it is not finitely generated, and the actual local module has the independently checked finiteness property.

No finite-Sha premise enters any step in sections 1–5. The unknown global point may have infinite Sha without altering this local conclusion. This review does not assert a value or a primitive nonzero class at that point, and it does not use the central Kato scalar formula outside its corank-zero domain. Global duality, central saturation, the retained class's integral normalization, and the final RC contradiction remain the separately scoped arguments already named by the project.

**Disposition:** P19 and its no-central-t-factor application are independently validated within the exact scope above. No correction to the current local-control claim is required.

DRAFT_ANCHORS: unchanged. UNREGISTERED_SORRIES: not inspected or changed. DRAFT_IMPORT_VIOLATIONS: not inspected or changed. SEALED_THIS_TURN: only this directory's report, source pins, receipt, and seven rendered primary pages.
