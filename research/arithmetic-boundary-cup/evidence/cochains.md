# Finite cochains, local conjugation, and the boundary–cup signs

Model subagent `/root/arithmetic_cochains`; 2026-11-08. This is an independently derived, bounded source review, not a whole-proof certificate or an independent acceptance of a new manuscript revision. No frozen source, Lean packet, evidence register, or branch was changed; no Lean/cloud run was performed.

### 1) Verification target

The target is the actual finite arithmetic and local boundary–cup input for `BoundaryCupIdentity` and `integral_boundary_cup_adapter`, not a global map between the finite and singular Selmer complexes. In particular, this report assumes no identity-on-strict square and constructs no strict automorphism.

Reviewed checkout: `e653d6ff295ae4e0535710a7d64aa255d294d211` in `derivative-switch-review`; the checkout was clean at inspection.

| Read source | SHA-256 |
| --- | --- |
| `manuscripts/quartic_v13.tex` | `9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd` |
| `lean/Research/DerivativeSwitch/BoundaryCup.lean` | `64750e7706f82cf0a47b76c80503bcab0577c2aa18f9703c09b4b8288be0df90` |
| `research/scalar-ratio/CONTRACT.md` | `7d7d69aa9fb2cae043ba29c93a0de5099ad552d387e1f53b09f9f58909cc4aca` |
| `research/scalar-ratio/inputs/ARITHMETIC_CONTRACT.md` | `99e5dbbc3e1c5eb71e98350ca0955cd045d4cdeaab800b20c1023588144a3f9a` |
| `docs/audit-history/issue2/evidence/determinants.md` | `648a83cfec26f3032dc75aa04be03870c1864173c60daed3ff082935db703bd5` |
| `../audit-output/2026-11-08/sources/nekovar-2006.pdf` | `61c84e5ad3252a2e520747215ac57a282addc2b58c824a3637bcd77bbe02153f` |
| Text extraction of that PDF, `nekovar-2006.txt` | `67f0226d14de2afd088707b79f8baade46a5adcf78ebf8d7c7b4cccab787f77f` |

The PDF hash agrees with the repository's primary-source inventory. It is J. Nekovář, *Selmer complexes*, Astérisque 310 (2006), [publication record](https://www.numdam.org/item/AST_2006__310__1_0/). The publication record could not be retrieved by the web tool in this turn; the pinned local publication was read. Its Sections 6.1–6.3 and 8.6.2 were used, with the existing image of printed page 142 inspected to resolve the displayed maps and signs. This report does not re-audit the entire book or each finite Heegner/descent premise.

The bounded historical lookup read the determinant excerpt itself. It invokes an earlier Section 9 rather than reproducing its proof. The full origin was not located in this bounded search. Thus the historical disposition is **prior components located**, not a claim that no earlier full justification exists. The current source contains explicit local transport and an identity comparison at derivative primes that are relevant beyond the excerpt.

The source contract is stronger than the local derivative relation alone. The actual row must be `lambda_z = PD(-, j^{-1}c(z))`, with the retained duality, conjugation and orthogonal comparison. The target adapter allows different normalizers `cF,cS`; it needs their ratio to be an actual integral unit. Equality of the two normalizers is not necessary.

### 2) Independent re-derivation (outline)

#### A. Finite arithmetic does not introduce a new normalization factor

The source's actual finite statement is at lines 2995–3015. The one fixed multiplier is

`L = m0 C_pi C_bad 2^(2e)`

at H11, lines 3210–3223. Both old and derivative classes use this same `L`. It is not divided out in the later definition of the functional (4001–4008).

H12 fixes `J = rho_T(tau)`, `J^2=1`, `det J=-1`, and requires rational Frobenius congruent to `J` modulo `2^(a+1)` (3225–3233). The source works at retained precision `m` with `a >= m+e`.

The exact identity behind H16 is valid:

`(F-a_l)(a_l F-(l+1)) = a_l-(l+1)F`,

because `F^2=a_l F-l`. The bounded error is killed on reduction from level `a` to level `m`; the extra bit in H12 pays for the factor `1/2` in H18. These yield exactly

`f(B)=0, s(B)=J f(A)`

at retained precision, not merely proportionality (3323–3337). The finite relation uses the actual cocycles of the fixed-multiplier classes. This review checked the displayed endomorphism calculation and the role of the precision, while retaining the earlier descent/torsion propositions as source premises.

H20–H21 apply the coefficient push to both classes and their witnesses by an unaveraged finite sum (3344–3386). For example, the degree-one cocycle check follows directly from

`h(gk,delta)=h(g,k delta)h(k,delta)`

and `R(r_(gk delta)) rho(h(g,k delta)) = R(g)R(r_(k delta))`, where `R=theta rho`. Reindexing the first sum gives `T(b)(g)` and the second gives `R(g)T(b)(k)`. No division by the number of cosets occurs. The same transported places, bases and weights are used for old and derivative classes, yielding (4.2), lines 3405–3414. No assertion that arbitrary change-of-place matrices commute with an untransported `J` is needed.

H22 supplies actual local cycles and degree-zero boundary witnesses. Their projections under a contraction satisfy the same boundary relation, with the displayed correction `p' F h z` when changing models (3509–3542). Consequently the local relation is a relation of the retained data, not a choice of new cohomology generators after the switch.

#### B. The local transfer factors satisfy adjunction without division

At retained precision the tame model has zero differential. The source keeps the mixed pairing, the `D0/D2` pairing, and the isotropy data (3434–3453). In the order `D0,F,S,D2`, it gives

`res = diag(1,f,e,ef)`, `cor = diag(ef,e,f,1)`.

These factors are adjoint under the complementary pairings: for the `F/S` term, restriction multiplies the first coordinate by `f`, while corestriction multiplies its paired `S` coordinate by the same `f`; for `S/F` both use `e`. The `D0/D2` terms similarly use `1` and `ef`. This calculation works even when `e` is even or noninvertible in the finite coefficient ring. The derivative extension has residue degree one; split Mackey terms have `e=f=1`. The shear is killed at retained precision as stated at 3466–3470.

The transferred inclusion/composition homotopies and the second coherence maps in 3474–3507 matter. They are the type of data required by Nekovář 8.6.2.1–8.6.2.4, not merely equality of induced maps on cohomology. This review identifies and checks the displayed local matrix adjunction; it does not independently construct all the global comparison homotopies anew.

#### C. Derive the boundary adjunction on the actual row

Use the explicit mapping-fibre convention

`C_U^n = G^n + U^n + L^(n-1)`,

`d(g,u,l) = (dg,du, loc(g)-i(u)-dl)`.

This is the convention of H22 and Nekovář 6.1.2. The quotient from the relaxed condition to the finite condition is `S[-1]`. Lifting a local singular vector `s` by `(0,s,0)` gives the connecting representative

`partial_S(s) = (0,0,-s)` in degree two of `C_F`.

Likewise `partial_F(f)=(0,0,-f)` in `C_S^2`. These are two different target complexes; no map between them has been used.

Nekovář 6.2.2 gives the local cone pairing, and 6.3.3, first diagram, says that the inclusion of the local cone into the global Selmer cone is adjoint to localization of the second Selmer argument. Thus, with a fixed common trace convention,

`lambda_A(partial_S(s)) = - inv_v( s cup loc_v(A_perp) )`,

`lambda_B(partial_F(f)) = - inv_v( f cup loc_v(B_perp) )`.       (BC)

These identities hold for **all** local `s` and `f`. They are the desired same-row identities because the source defines precisely

`A_perp=j_F^{-1}c(A)`, `B_perp=j_S^{-1}c(B)`,

`lambda_A=PD(-,A_perp)`, `lambda_B=PD(-,B_perp)`

at 3873–3891 and 3974–3999. The finite/singular derivative local conditions retain `D0` and are their own orthogonal conditions. At a derivative prime, the source explicitly specifies the comparison `j` to be the identity under these integral local maps (5350–5368). Therefore inverse corrections at active/moving places cannot change these derivative-local cohomology coordinates. Representatives differing by boundaries give the same values in (BC), by the chain-map pairing identity.

There is an important timing restriction: the actual inverse `j^{-1}` and functional are formed **after the inner limit and localization**, where the stated contractions exist (3843–3861, 3876–3889). One should retain the finite local equations first and then apply (BC) in those localized models. There is no assertion here that every finite Artin model already admits the global inverse `j^{-1}`.

#### D. The conjugation sign changes which adapter is appropriate

This is the key independent sign check. Let `e` be the alternating Weil form in a fixed oriented Tate basis and put

`Q(x,y)=e(x,Jy)`.

Since `J^2=1` and `det J=-1`, `Q(x,y)=Q(y,x)`. The coefficient pairing in the source already contains `J` (2935–2957); do not insert this coefficient `J` a second time.

Let `kappa` denote the fixed local invariant/coordinate factor before composing with conjugation. With the compatible finite and tame generators, the raw mixed cup between `M` and `tau^*M` is

`P((f,s),(f',s')) = kappa[ Q(f,s') - Q(s,f') ]`.       (LC)

The minus is the interchange of the two degree-one scalar Galois cochains; `Q` itself is symmetric. Both same-plane cups vanish by the retained local isotropy calculation.

At an inert derivative prime, rational Frobenius fixes its square, the finite Frobenius generator. It conjugates tame inertia by the `l`th power. Thus pullback contributes `+1` on the finite coordinate and `l^{-1}` on the singular coordinate. The retained congruence makes the latter `-1`. The full ordinary conjugation action includes the coefficient `J` and is `(J,-J)`, explicitly derived in V13 5196–5218. Removing the `J` already present in `Q`, the raw pullback entering (LC) has coordinate action

`c_0(f',s')=(f',-s')`.

The same local computation uses triviality of the coefficient character at the derivative prime; it does not require globally quadratic moving coefficients. The globally quadratic specialization is where the manuscript uses the result to split cohomology signs. If the chosen global-to-local conjugation transporter contributes a coefficient-character scalar, it is the same invertible scalar on both local degree-one planes. Transporting the bases or absorbing that scalar into the shared `epsilon` preserves the calculation below. Individual numerical normalizers depend on this common convention; their ratio does not.

Consequently the effective self-pairing is

`P(x,c_0(y)) = -kappa[ Q(f,s') + Q(f',s) ]`.           (TC)

This is symmetric hyperbolic, as the source explicitly requires at 5221–5239. Omitting the singular pullback sign would instead produce the raw alternating cross form and would not agree with that passage.

For clarity choose the effective cross convention

`beta(f,s) = epsilon Q(f,s)`, `epsilon=-kappa`.

Then (BC), (TC), `loc A=(v,0)`, and `loc B=(0,Jv)` give

`lambda_A(partial_S(s)) = -beta(v,s)`,

`lambda_B(partial_F(f)) = -beta(f,Jv)`.               (SR)

A simultaneous opposite cone/trace convention changes both displayed signs. Crucially, both actual evaluations have the **same** effective `beta` sign.

The frozen adapter, however, is written

`lambdaF(AS s)=cF beta(v,s)`,

`lambdaS(AF f)=-cS beta(f,Jv)`.

Hence (SR) instantiates it with `cF=-1`, `cS=+1`, or with their simultaneous negatives if the common trace convention is reversed. Equivalently,

`cF = (-1) cS`.

Using the raw convention `epsilon=kappa` instead gives `(cF,cS)=(1,-1)`; the ratio is unchanged. The arithmetic normalizer ratio is the actual integral unit `-1`. A demand for `cF=cS` would discard the tame conjugation sign in these conventions. This is not a defect of the frozen conditional theorem: its `integral_boundary_cup_adapter` explicitly allows this unit discrepancy (BoundaryCup.lean 119–132).

For the fixed cofactor convention, the cross values satisfy `qF=-qS`. With `det J=-1`, the general scalar formula consequently yields `uF=-uS`, rather than the exact numerical `uF=uS` provided by the more restrictive common-normalization theorem. Their valuations and generated integral fractional ideals agree. Changing a determinant orientation may reverse this numerical sign without changing that conclusion.

### 3) Checks

- **Plug-back:** The two boundary representatives arise by applying the same cone differential to the local quotient lifts; both are negative local cochains. The minus signs therefore cannot be chosen independently to force an adapter result.
- **Conjugation check:** With `J=diag(1,-1)` and `e((a,b),(c,d))=ad-bc`, `Q((a,b),(c,d))=-ad-bc` is symmetric. Inserting the singular pullback `-1` makes (TC) symmetric, agreeing with the manuscript's hyperbolic-plane argument.
- **Derivative check:** `J^2=1` gives `beta(v,Jx)=epsilon e(v,x)` and `beta(x,Jv)=-epsilon e(v,x)`. The same-sign identities (SR) therefore give opposite cross scalars, exactly the `cF/cS=-1` adapter case.
- **Multiplier check:** `L` is already included in both actual classes. The functional is linear in that actual class. No primitive generator is substituted; no division by `L`, the local vector, or a coset count occurs.
- **Divisible-vector check:** All local identities are linear on the actual vectors and valid before choosing complements. A nonprimitive `v` introduces no scalar mismatch in (BC) or (SR). Integral common-strict presentation/determinant bookkeeping is a separate integration obligation, not proved solely by this check.
- **Exceptional scalar check:** `-1` is a unit at every relevant localization, including the two-adic localization and `(t)`, `(t+2)`; no use of `1/2` occurs in the sign comparison. At characteristic two the two signs coincide, but the intended fraction-field determinant argument is characteristic zero.
- **Zero case:** The full identities do not divide by the class or functional. The nonzero-localization hypothesis enters the rank-one/common-strict algebra separately. The unit adapter itself retains its zero cases.
- **Computation:** No new bounded computation or Lean run was used. The checks above are symbolic identities. Earlier packet test counts are not evidence for the arithmetic identities.

### 4) Discrepancy report (if any)

The conditional algebraic packet is not refuted. The discrepancy is between a hoped-for **common** boundary normalizer and the actual conjugate-dual finite/singular coordinate convention. The full local conjugation action is `(J,-J)`; retaining only the coefficient `J` loses the tame pullback sign. The source's symmetric hyperbolic local form independently detects this omission.

The source material does not print (BC) and its translation into the frozen matrix rows as one application lemma. This report supplies the cochain derivation and identifies the unit ratio, under the retained source duality and localization constructions. A completed integration must identify `AF,AS` with these actual cone boundary columns, use the same `lambda` rows, and carry this statement through the retained model maps and required localizations. It must not normalize new rows after the switch. The separate reviewer/root owns those broader integral-presentation and retained-limit checks.

The earlier historical excerpt is insufficient on its own to classify this derivation as new mathematics. Current V13 already contains the key derivative, conjugation, paired-functional, and local identity-comparison ingredients. The present status is an explicit connecting derivation from those ingredients, pending integration/non-author review; it is not evidence of an arithmetic counterexample.

### 5) Certification result

**CERTIFIED under the stated retained source inputs:** finite H19–H22/local-transfer data carry no derivative-dependent normalizing denominator; the actual boundary/PD adjunction reduces to (BC); the source's conjugate-dual convention gives an adapter normalizer ratio `cF/cS=-1`, an integral unit. This supplies a viable valuation-preserving route through the existing `integral_boundary_cup_adapter` without a global Selmer-complex isomorphism and without common normalizer equality.

**NOT CERTIFIED by this bounded report:** every global finite arithmetic premise, a fully instantiated common-strict integral matrix model at all required localizations, every retained-limit application, a formal arithmetic bridge, or the whole restricted converse. These must be distinguished from the sign/normalization calculation just derived. No manuscript acceptance or upstream submission follows from this report alone.
