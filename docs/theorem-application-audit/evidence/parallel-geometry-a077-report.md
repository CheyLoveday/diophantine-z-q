# A077: AFP source and translation audit

Date: 2026-11-05. Consumer manuscript SHA256 `a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e`, lines 5522–5702. Compiler: `construction/integer-diophantine-compiler.js` in the same repository. This report concerns source identity and mathematical translation, not Lean or Isabelle build status.

Recommendation: close A077 after recording `A077-source-manifest.json` and the exact declaration mapping below. The three source files are authenticated against public bytes at one named revision. The alpha and power systems match the actual compiler. I found no missing guard or changed mathematical condition. `A077-PATCH.diff` adds the presently missing precise citation in the manuscript; it changes no equation.

## Exact public revision

All three local pins are byte-for-byte equal to the files at AFP git mirror revision [b4f3b892d0ae25cea27412ba4007cdb63e44b0eb](https://github.com/isabelle-prover/mirror-afp-devel/commit/b4f3b892d0ae25cea27412ba4007cdb63e44b0eb), dated 2026-05-10T07:38:12Z. The directory is `thys/DPRM_Theorem/Diophantine/`, not the parent session directory. The commit message is “made usage of proof reconstruction with Z3 prover explicit”. The downloaded commit metadata and per-file histories are saved here.

| File | SHA256 | Git blob SHA1 |
|---|---|---|
| Alpha_Sequence.thy | `76a9dfa6bcebaebe17492d1aef32be7b1fec241529cc3fec3378e0c6d1210c23` | `e50259505e265eff7d034400460e5379ce0e18f2` |
| Exponential_Relation.thy | `515093945cfd56a09622c9bb6536f61c2dcc8f6d6798af1f28efafcd42a95069` | `d1f089781d787d02f134c8723bcb3148a4c46d07` |
| Exponentiation.thy | `203431b551fd0ca218722583a2ba62c5959d8e72aea8c47eca975118e74f0946` | `5d2287f03f4ad1357513a16cd0ed33d8b74214df` |

I also downloaded each file at the then-current git mirror revision `5320b2191f741874956adbfe452efbdde5878bfa` and obtained the same hashes. Per-file history says Alpha_Sequence last changed at `d3dcdd19289504090cd73a2d7dccb61ec4faeaab`, 2024-09-23, for mixfix notation; the other two last changed at the May 2026 revision above. This authenticates a common precise source revision. It does not recover the original local download date, assign an unsupported Isabelle release number, or assert that every intervening AFP commit was built here.

The [official AFP entry](https://isa-afp.org/entries/DPRM_Theorem.html) names the DPRM_Theorem session and all three theories, credits Jonas Bayer, Marco David, Benedikt Stock, Abhik Pal, Yuri Matiyasevich, and Dierk Schleicher, and dates the entry to 6 June 2022. The [official download page](https://isa-afp.org/download/) distinguishes stable distributions from the development repository. The authenticated object here is the development git mirror revision, not a guessed stable release. Commit-addressed raw URLs and local downloaded copies are recorded in `A077-source-manifest.json`.

## Definition and lemma correspondence

Line numbers in the source column refer to the authenticated `.thy` bytes. Prefix `E` denotes Exponentiation.thy, `A` Alpha_Sequence.thy, and `R` Exponential_Relation.thy. Declarations inside the locale have the prefix `Exp_Matrices`; the final `exp_alpha` and `alpha_equivalence` declarations are outside that locale.

| Manuscript lines | Exact source | Match and hypotheses |
|---|---|---|
| 5588–5591 | E67–70, `Exp_Matrices.alpha` | `nat -> nat -> int`, with values 0,1 and integer recurrence. Manuscript b,n are natural, U is initially integer-valued. |
| 5592–5593 | E73 `alpha_strictly_increasing`; E99 `alpha_superlinear`; E106 `alpha_nonnegative` | Source monotonicity allows b>=2; growth and nonnegativity use b>2. Manuscript uses b>=3. |
| 5594–5599 | E157 `A`, E162 `B`, E173 `A_pow`, E185 `A_det`, E190/208 `alpha_det1/2`, E430 `div_coprime` | Manuscript M is source B(b). Its displayed matrix power is for n>=1, correctly avoiding the separate A(b,0)=identity clause and truncated predecessor. |
| 5600–5604 | E714 `congruence`; E111 `alpha_linear` | Source `congruence` changes the parameter, not the index. It assumes equality of b1,b2 modulo q and concludes equality of their alpha values modulo q. Parameter 2 is allowed. |
| 5606–5611 | E214 `alpha_char_eq`; E268 `alpha_char_eq2` | First result requires y<x; second removes ordering and requires b>2. Manuscript explicitly supplies the unordered descent and uses that stronger statement for u and x. |
| 5613–5622 | E469 `divisibility_alpha`; E498 `divisibility_equations`; E617 `divisibility_congruence`; E631 `divisibility_alpha2` | First divisibility equivalence uses b>2,k>0. Squared equivalence uses b>2,m>0, including k=0. Manuscript records m>0 and treats k=0 separately. |
| 5624–5631 | E971 `361`; E996 `362`; E1022 `36` | Source distinguishes positive and negative index reflection, with strict guards in the negative case. Manuscript extends to negative integer indices and retains the independent value sign `(-1)^l*epsilon`. Boundary j=0 is harmless. |
| 5633–5643 | E1038–1055 `alpha_equations`; A11 `alpha_dioph`, local DR1–DR6 at A24–31 | Exactly the fifteen conditions, in exactly the same eight outer witnesses r,s,t,u,v,w,x,y. Source a,b,c correspond to manuscript X,b,N. |
| 5650–5658 | E1058–1215 `alpha_equiv_suff` | Same two-stage recovery: first X=alpha_b(j) from the modulus v and size bound, then N=j from modulus u and its independent size bound. |
| 5660–5669 | E1228/1254 `one_odd/oneodd`; E1289 `chinese_remainder_nat`; E1345–1535 `alpha_equiv_nec` | Manuscript chooses a large odd U_k, sets m=kU_k, uses coprimality of u,v, and applies CRT. This also supplies X=N=0. |
| 5633–5669 as a whole | E1688 `alpha_equivalence`; A8 `alpha`; A11 `alpha_dioph` | Existential system iff b>3 and int(X)=alpha_b(N), with no bound on N. Source A adds relation syntax and eight-variable parameter shifting. |
| 5671–5686 | R9 `exp_equations`; R16 `exp_repr`; R73 `exp`; R76 `exp_dioph` | Natural P,Q,R; the exact three branches Q=R=0, Q=0<R, and Q>0. Source R introduces b,m,a0,a1,a2, matching the manuscript. |
| 5681 | E128 `alpha_exponential_1`; E1595 `89` | Lower bound alpha_(Q+4)(R+1)>=(Q+3)^R, then m>Q^R for Q>0. |
| 5682–5685 | E1540 `86`; E1574 `860`; E1588 `88`; E1622 `exp_alpha` | Same integer congruence and interval argument. R16 is the more convenient subtraction-free natural formulation actually compiled. |

The remaining machine-packing and binomial/bit passages in the requested range do not reuse declarations from these three files. Lines 5522–5537 describe a specialized saved circuit and pairing wrapper, 5539–5585 give the repository's packed-machine construction, and 5688–5701 derive binomial and bit macros. The three AFP files do not certify those constructions or their saved hash. Their use of the alpha/power interfaces is mapped below. This distinction prevents a claim of whole-compiler certification based on an AFP bibliography entry.

## Literal compiler comparison

Builder.alpha at compiler lines 63–79 maps X,B,N to source a,b,c. Its fifteen conjuncts, in order, are:

1. B>3.
2. 1+B*u*t=u²+t².
3. 1+B*s*r=s²+r².
4. r<s.
5. u² divides s.
6. v+2r=B*s.
7. B congruent to w modulo v.
8. 2 congruent to w modulo u.
9. 2<w.
10. 1+w*x*y=x²+y².
11. 2X<u.
12. 2X<v.
13. x congruent to X modulo v.
14. 2N<u.
15. x congruent to N modulo u.

These are the source's equations 3.41–3.55. Equality and congruence reversals are symmetric; no inequality was reversed. The source's compact outer eight-witness block expands in the compiler to 23 natural witnesses: eight named alpha witnesses, six strict-inequality differences, one divisibility quotient, and eight witnesses for four congruences. I instantiated the builder read-only and verified those counts.

Builder.power at lines 80–95 implements R76's S1–S4. Its Q>0 branch calls alpha at `(a0,Q+4,R+1)`, `(a1,b,R)`, and `(a2,b,R+1)`, then imposes b=a0+Q²+2, m+Q²+1=bQ, P<m, and P+b*a1 congruent to Q*a1+a2 modulo m. Each alpha call supplies its own fresh variables. The standalone power call introduces 79 witnesses, including those three alpha expansions, five outer witnesses, the positive-branch guards, and final congruence witnesses. A source-level existential block and this flattened block therefore differ only by expanding defined predicates and assigning distinct variable indices.

Builder.fresh calls variable, whose index is the current variable-list length. Thus separately introduced witnesses cannot alias. Structural node caching uses that index, not the human-readable witness name. Flattening quantifiers across conjunction is valid with these disjoint private variables. Across disjunction it is valid because the unused branch's natural variables can always be assigned, for example, zero. Source parameter shifting via `push_param` prevents capture in its syntax; fresh numerical indices perform the corresponding job here.

The primitive replacements at compiler lines 49–62 are exact over N. For A<B, the nonnegative difference witness is B-A-1. Divisibility uses an unrestricted natural quotient. Congruence uses A+M*u=B+M*v; for M>0 this is equivalent to equality of residues by separating the positive and negative parts of the integer quotient. At M=0 it reduces to A=B, which agrees with Isabelle's mod-zero convention. I also downloaded the same revision's Modulo_Divisibility.thy: its line 35 defines MOD A B C as equality of the two residues modulo B. The equality convention is therefore checked against the actual dependency, not inferred from the name MOD.

## Domain, subtraction, and boundary checks

The source alpha sequence is integer-valued even though both arguments are natural. For b>3 every alpha value used by the relation is nonnegative. For the special comparison parameter 2, alpha_2(n)=n. The internal CRT parameter w needs only w>2 because no separate alpha_dioph call is made at parameter w; its Pell solution uses alpha_char_eq2. Requiring w>3 instead would be an unjustified strengthening, and the compiler correctly uses w>2.

For the power macro, Q>0 implies Q+4>=5, a0>=1, and b=a0+Q²+2>=4. All three alpha relation guards are therefore satisfiable. The equation m+Q²+1=bQ gives the ordinary integer difference m=bQ-Q²-1 without natural-subtraction truncation. Its bound m>Q^R follows because

`m = Q*a0 + (Q^3-Q^2+2Q-1)`,

where the parenthesis is positive for Q>=1 and Q*a0>=Q^R. Thus both the power value and P lie in [0,m), which is necessary for the congruence to force equality. The cases R=0 and Q=1 satisfy the same argument; Q=0 is handled by the two separate branches, including 0^0=1.

For alpha soundness the strict guard 2X<u ensures u>0, so u=U_k forces k>0. The ordered Pell pair has s>r>=0, so its recovered m is positive. Therefore the squared divisibility theorem is applied with its actual hypotheses. The value reflection sign and the index reflection sign need not agree; the manuscript keeps them separate. Since both relevant values are strictly below half the modulus, each signed congruence has exactly the asserted outcome, with the negative case forcing the zero boundary. The recurrence at n=0 and the alpha formula at X=N=0 are both included.

For completeness, consecutive alpha terms are coprime and hence not both even. Since the sequence is strictly increasing and unbounded, odd terms can be chosen arbitrarily large. Taking m=k*u gives u²|U_m. A common divisor of u and v is odd, divides s, and divides 2r, hence is one. CRT produces w in the required residue classes and permits w>2. This discharges the existential premise rather than assuming source correctness from theorem names.

## Downstream uses within the requested lines

Builder.binomial, lines 96–106, calls the power macro three times for base=2^(N+1), total=(1+base)^N, and place=base^K. Its integer equation and strict remainder bounds are exactly manuscript lines 5688–5694. Every binomial coefficient is at most 2^N<base, so there are no carries; K>N gives a zero digit. N=K=0 works with base=2 and place=1.

Builder.orthogonal and mask, lines 108–116, use oddness of binomial(A+B,A) and binomial(B,A), respectively. The manuscript proves the needed mod-two coefficient identity directly. The least overlapping bit argument is valid because there is no smaller overlapping bit to generate an incoming carry. Builder.bitAnd, lines 118–122, then uses the three pairwise-disjoint conditions exactly as lines 5700–5701. These are independently justified downstream mathematical constructions using the verified power interface; they are not attributed to nonexistent lemmas in the three pinned theories.

The packed histories at lines 5539–5585 call these power and bit interfaces. This audit verifies their required input domain and relation semantics. It does not promote this source comparison into certification of the separate interpreter, source S23, or the 1,305,811-variable saved polynomial. Those are separate application obligations.

## Proposed inventory update

Set A077's source locator to `AFP development git mirror revision b4f3b892d0ae25cea27412ba4007cdb63e44b0eb; Exponentiation.alpha_equations/alpha_equivalence, Alpha_Sequence.alpha_dioph, Exponential_Relation.exp_equations/exp_repr/exp_dioph`, with the line mapping above. Mark its source authentication and exact mathematical translation verified. Replace the open item with an empty value. Preserve the explicit statement that the JavaScript implementation was compared mathematically and has not itself acquired an Isabelle or Lean certification.

The proposed manuscript patch adds this attribution without altering the formulas. For the bibliography, append the exact git revision and directory from `A077-source-manifest.json`; retaining the official AFP entry URL is appropriate. No saved polynomial or compiler code needs to change for A077.
