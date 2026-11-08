# Arithmetic boundary–cup normalization for the derivative switch

Date: 2026-11-08. Author: Codex `/root`, with source investigations by
`/root/arithmetic_cochains`, `/root/arithmetic_functionals` and
`/root/arithmetic_duality`. This is an ordinary mathematical research note,
not an addition to the frozen 39-target Lean packet.

**Result under the retained arithmetic inputs:** the two actual paired
functionals have normalizers differing by the integral unit $-1$ in the
frozen adapter's convention. This supplies its unit-normalizer hypothesis.
It does not supply that adapter's stronger equality-of-normalizers hypothesis.
The determinant argument below works through the two separate triangles and
requires no morphism between the finite and singular Selmer complexes.

This conclusion is relative to the manuscript's constructed cones, duality,
orthogonal comparisons and retained limits, identified below. It is not a
fresh proof of those entire constructions, a formalization of arithmetic
Poitou–Tate duality, or acceptance of the restricted converse. Manuscript
incorporation and formal arithmetic instantiation remain separate work.

## 1. Frozen target and sources

Repository commit: `e653d6ff295ae4e0535710a7d64aa255d294d211`.
Manuscript: `manuscripts/quartic_v13.tex`, SHA-256
`9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`.

The target is the class-functional comparison in
`ex:limits-derivative-switch`, lines 5021–5093, used for inner determinant
valuations in `ex:limits-uniform-lower-bound` and height-one regularity.
It is not a claim about equal outer cohomology ranks.

| Source passage | Input used |
| --- | --- |
| 2898–2967, `ex:arith-conjugate-duality` | Conjugate coefficients, coefficient pairing containing $J$ once, fixed coefficient ring |
| 3210–3233, H11–H12 | One multiplier $L$; $J^2=1$, $\det J=-1$; extra retained precision |
| 3323–3337, H19 | Actual derivative relation with no new normalization |
| 3340–3551, H20–H22 | Integral unaveraged transfer, local generators, cup diagrams, actual cone witnesses |
| 3842–4012, `ex:arith-paired-functional` | $\lambda_z=\operatorname{PD}(-,j^{-1}c(z))$, same generic functional, localization-specific integrality |
| 4562–4637, `ex:limits-inner-limit` | The same localization, duality, cup maps and compatibility homotopies survive compression and the inner limit |
| 5021–5075 | Four local conditions retaining $D^0$, two separate common-strict triangles |
| 5193–5243 | Explicit rational-Frobenius action on finite and tame coordinates and transported cross pairing |
| 5330–5374 | Actual derivative class after each switch; identity orthogonal comparison at a derivative place |

Primary source: Jan Nekovář, *Selmer complexes*, Astérisque 310 (2006),
[published volume](https://www.numdam.org/item/AST_2006__310__R1_0/),
[PDF](https://www.numdam.org/item/AST_2006__310__R1_0.pdf).
The PDF read has SHA-256
`61c84e5ad3252a2e520747215ac57a282addc2b58c824a3637bcd77bbe02153f`.
We checked the explicit cone product in Proposition 1.3.2 (p. 41), the
local boundary products in 6.2.2–6.2.4 (pp. 138–139), the global boundary
diagrams in 6.3.3 (p. 142), and the functoriality requirements in
6.4.1–6.4.4 (pp. 144–145). The inference below is the pure-boundary
specialization of those formulas, independently computed here.

Historical lookup included `docs/audit-history/issue2/evidence/determinants.md`
and the determinant-switch, boundary-scalar and scalar-ratio research packets.
The historical excerpt points to a section 9 in a full report not located
in this bounded lookup. Accordingly the historical classification is
**prior components located; completeness of earlier justification unresolved**.
This note does not claim discovery of a previously unknown paper defect.
The manuscript already states the conclusion; the explicit connecting
calculation supplied here is not yet incorporated into it.

## 2. Objects and applicability

Work after the retained inner construction, over a required coefficient
domain $R$ and its fraction field $K$. For the valuation application these
are the completed two-adic DVR or a primitive scalar height-one DVR.
Assume the manuscript's actual perfect integral Selmer diagrams and their
retained cup maps. At the new derivative place the local character is
trivial, and the local model is

$$
D^0\oplus(F\oplus S)[-1]\oplus D^2[-2].
$$

Both planes are free of rank two. The strict condition retains $D^0$;
the finite and singular conditions add $F[-1]$ and $S[-1]$, respectively.
The common strict complex is $C_{\rm str}$. Its two integral triangles
give boundary maps $\partial_F:F\to H^2(C_{\rm str})$ and
$\partial_S:S\to H^2(C_{\rm str})$. Let

$$
\delta_S:H^1(S[-1])=S\longrightarrow H^2(C_F),\qquad
\delta_F:F\longrightarrow H^2(C_S)
$$

denote their composites through the common strict complex. These are
the *opposite* local boundary directions consumed by the scalar-ratio
packet, not a proposed identification of the two boundary maps.

Let $A$ be the actual old class, with $f(A)=v\ne0$, spanning
$H^1(C_F\otimes K)$, and with generic dimensions $(1,1)$ in degrees
one and two and no other generic cohomology. Let $B$ be its actual
H19–H22 derivative. Then $f(B)=0$ and $s(B)=Jv$ with the same $L$.
The functionals throughout this note are exactly

$$
\lambda_A=\operatorname{PD}(-,j_F^{-1}c(A)),\qquad
\lambda_B=\operatorname{PD}(-,j_S^{-1}c(B)).
$$

No primitive replacement or independent rescaling of either row is made.
In particular the source does not define $\lambda_B$ by transporting
$\lambda_A$ through a determinant-line map.

## 3. The actual boundary–cup adjunction

Use the cone convention

$$
C_U^n=G^n\oplus U^n\oplus L^{n-1},\qquad
d(g,u,l)=(dg,du,-\operatorname{loc}g+iu-dl).
$$

In this convention a lift of $s\in S$ in the larger local condition has
differential $(0,0,s)$. Its image in $C_F^2$ represents $\delta_S(s)$.
The corresponding representative of $\delta_F(f)$ in $C_S^2$ is
$(0,0,f)$. These signs agree because both are obtained by adding a
local degree-one summand to the *same* strict cone. The H22 convention
uses the opposite sign for the third entry; changing to it changes
both signs together.

In the cone cup product choose parameter $r=0$. With first argument
$(0,0,l)$, all global and local-condition products and all bilinear
homotopy terms vanish. The remaining term is

$$
l\mathbin{\cup}i(u^\perp).
$$

After the common trace this is the local cup of the boundary direction
with the localization of the actual orthogonal partner. Thus there is
one common convention factor $\kappa$, not two separately chosen
normalizing scalars. In a fully fixed trace convention it is fixed by
that trace and the cone sign. The following proof never needs to
declare $\kappa$ an integral unit.

At the derivative place $j_F$ and $j_S$ are the identity under the
retained integral comparisons. Consequently the localizations of the
orthogonal partners are the conjugate transports of the localizations
of $A$ and $B$. An inverse comparison at an active, moving or old place
cannot alter this derivative-place cohomology class: applying the local
map to $j j^{-1}c(z)=c(z)$ gives the same class. Changing a cochain
representative adds a boundary and does not change the cup evaluation.
This is where the *actual* definition of the two functionals is used.

## 4. Local conjugation and the sign

Write $e$ for the alternating Tate-module form and set

$$
Q(x,y)=e(x,Jy),\qquad \beta(x,y)=\varepsilon Q(x,y).
$$

Since $J^2=1$ and $\det J=-1$, $Q(x,y)=Q(y,x)$. This computation uses
no eigenspace projectors and no division by two. The coefficient $J$
is already in $Q$ and must not be inserted again when transporting
the cochain argument.

With compatible finite and tame generators, the raw mixed cup of the
primal and conjugate coefficient systems is

$$
\Omega((f,s),(f',s'))
 =\varepsilon\{Q(f,s')-Q(s,f')\}.
$$

This follows by expanding in the unramified and tame degree-one
characters: their mixed cup values have opposite signs. Their squares
vanish in the source's retained model, including at two by the extra
precision and adjusted uniformizer in lines 3434–3454.

Let $\varphi$ be the local rational Frobenius representative. Its square
is the finite Frobenius generator. Conjugation fixes that generator and
sends tame inertia to its $\ell$-th power. Pullback therefore fixes the
finite cochain coordinate and multiplies the tame one by
$h=\ell^{-1}$ (the opposite Artin convention gives $\ell$). H12 makes
$h=-1$ at retained precision and in the retained inner limit.
After the coefficient $J$ has been accounted for in $Q$, the two
conjugate local partners are consequently

$$
A^\perp_{\rm loc}=(v,0),\qquad
B^\perp_{\rm loc}=(0,-Jv).
$$

This is the calculation behind the manuscript's actions $J$ on $F$
and $-J$ on $S$. It applies with a globally nonquadratic character:
only triviality of that character at the derivative place is used.
Changing places transports the Tate basis, Frobenius and coefficient
pairing together, as H21 prescribes. An additional coefficient-character
value is shared by the two local transports and is a unit. It can be
included in the same convention factor, not in two independent ones.

Inserting these partners into the adjunction of section 3 gives, for
**every** $s\in S$ and $f\in F$,

$$
\boxed{\lambda_A(\delta_Ss)=-\kappa\beta(v,s),\qquad
\lambda_B(\delta_Ff)=-\kappa\beta(f,Jv).}
$$

Both evaluations have the same displayed sign. Reversing the common
cone or trace convention reverses both together. Before imposing the
retained congruence, the second displayed coefficient is $\kappa h$;
the relative normalizer is already an odd local unit. In the actual
retained model it is exactly the sign above.

The frozen `BoundaryCupIdentity` instead writes

$$
\lambda_A(\delta_Ss)=c_F\beta(v,s),\qquad
\lambda_B(\delta_Ff)=-c_S\beta(f,Jv).
$$

Thus the source calculation instantiates it with

$$
\boxed{c_F=-\kappa,\qquad c_S=\kappa,\qquad c_F=(-1)c_S.}
$$

The witness $-1$ lies in $R^\times$ for every required ring. This is a
division-free unit relation, including zero normalizers. The unit-ratio
adapter applies. Its stronger common-normalizer and numerical-equality
corollaries should not be substituted for this application.

## 5. Determinant tensors through the two triangles

Here is a determinant-functor bridge that does not demand a simultaneous
integral two-term matrix presentation. The integral triangles give

$$
\mathcal D_F\simeq\mathcal D_{\rm str}\otimes\det F,
\qquad
\mathcal D_S\simeq\mathcal D_{\rm str}\otimes\det S.
$$

Define $\Phi_{\det}$ using identity on the strict determinant line and
$\det J$ on the local plane. It is an integral line isomorphism.

Over $K$, strict $H^1$ vanishes because $H^1(C_F)\to F$ maps its
generator to $v\ne0$. Put $W=H^2(C_{\rm str})$; the finite triangle
gives $\dim W=2$. Choose any $x\in F_K$ with
$\eta=e(v,x)\ne0$, and put

$$
a=\partial_Fx,\qquad b=\partial_S(Jx),\qquad
q_F=\lambda_A(b),\quad q_S=\lambda_B(a).
$$

Here each functional is evaluated after the appropriate quotient
$W\to H^2(C_F)$ or $W\to H^2(C_S)$. The boundary identities give

$$
q_F=-\kappa\varepsilon\eta,\qquad
q_S=\kappa\varepsilon\eta=-q_F.
$$

For the actual perfect local pairing and normalized duality this common
factor is nonzero. In particular $a,b$ are independent: $a\ne0$ by the
finite exact sequence, whereas $\lambda_A(a)=0$ and
$\lambda_A(b)\ne0$. The derivative class puts $Jv$ in the kernel of
$\partial_S$, while $b\ne0$ gives its rank one. The singular triangle
then shows its generic $H^1,H^2$ have dimensions $(1,1)$, with $B$
spanning $H^1$. This verifies the rank-one consumer without assuming
a global triangle lift or rank preservation for the outer object.

For an explicit tensor calculation use the ordered bases $(v,x)$ of
$F_K$, $(Jv,Jx)$ of $S_K$ and $(a,b)$ of $W$. The finite long exact
sequence contributes $q_F(v\wedge x)/(a\wedge b)$ to
$\mathcal D_{\rm str}\otimes\det F$. The singular sequence uses $b$
as its boundary direction and $a$ as quotient lift, and contributes

$$
q_S\frac{Jv\wedge Jx}{b\wedge a}
 =-q_S\frac{Jv\wedge Jx}{a\wedge b}.
$$

Since $q_S=-q_F$, these agree under $\Phi_{\det}$ in this compatible
determinant convention. Different determinant sign conventions give
a sign unit. In particular the actual two tensors are related by an
integral unit under the integral determinant-line comparison.

The use of $K$-bases in this calculation does not rationalize away
strict torsion: the calculation expresses both tensors using the
*same integral strict determinant line*. Its lattice factor, including
all torsion contributions, cancels only because it is common. The
complement $x$ need not be integral. A divisible $v$ therefore creates
no extra factor. Relative to any retained integral determinant bases,
the comparison differs by an $R$-unit and the two valuations agree.

In the frozen matrix convention this same calculation reads
$q_S=-q_F$ and $\det(J)u_F=u_S$. With $\det J=-1$ it gives
$u_S=-u_F$ for the corresponding coherent frames; valuation preservation
is the convention-independent conclusion. It does not justify asserting
$u_F=u_S$ for arbitrary retained bases.

## 6. Localizations, limits and non-claims

The argument does not construct $j^{-1}$ over every finite Artin ring.
It first retains the finite local identities and H19–H22 witnesses,
then uses the actual localized orthogonal comparison that defines
$\lambda_z$. This is the order in the manuscript.
Lines 4562–4637 retain the duality/localization homotopies and transport
the fixed finite diagram through inclusion and projection maps. The
boundary–cup computation is an identity in that diagram. Its local
finite equalities survive the retained matrix identities; the inverse
orthogonal comparison is then applied only in its justified localization.
No arbitrary isomorphism of limiting cohomology is substituted for this
process.

| Ring or scope | Why the same comparison applies |
| --- | --- |
| Completed two-adic DVR, scalar constituent | The source constructs the old/active/moving orthogonal comparison integrally; the derivative comparison is identity. The proof uses no $1/2$ or integral eigenbasis. |
| Primitive $\Lambda_{\mathfrak p}$, $\mathfrak p\ne(2)$ | The same generic functionals have the source's separate integral representatives. The local boundary calculation is unchanged. |
| $\mathfrak p=(t)$ | Use the source's central-Frobenius contraction for the moving place; no inversion of $t$ is introduced in this calculation. |
| $\mathfrak p=(t+2)$ | Use the source's inertia contraction. Global quadraticity changes prime selection, not the local normalizer. |
| Further finitely many derivative switches | The new actual class keeps $L$; each added orthogonal local comparison is identity, as checked in lines 5351–5374. |
| Outer rank-reducing test object | No equality of its ranks or class-functional coordinates is asserted. Apply this comparison separately to each eligible inner instance. |

The universal relaxed functional at other height-one primes is not
silently substituted for the primitive scalar functional. Its separate
correction/regularity argument remains the manuscript's own input.

The following are not newly established here: existence and bounded
size of the retained global models; the entire finite Heegner descent;
the complete passage through both limits; all old Kummer duality
constructions; the restricted converse; or a Lean instantiation of these
arithmetic objects. The new result is the explicit missing composition
of the actual functional definition, local conjugation, and boundary–cup
adjunction, together with its determinant-line consequence relative to
those source inputs. A successful cloud run of the frozen packet would
verify its conditional algebraic theorems, not this arithmetic proof.

## 7. Application obligations and review disposition

| Obligation | Required / constructed / matching argument |
| --- | --- |
| Source hypotheses | The actual cone product needs a coefficient pairing and compatible local isotropy data. Source lines 2898–2967 and 3434–3551 supply them; section 3 evaluates that product on a pure local boundary. Global perfect duality is a retained input, not freshly reconstructed. |
| Constructed objects | $A,B$ are the H19–H22 classes; the rows are exactly $\operatorname{PD}(-,j^{-1}c(z))$, not chosen functionals with similar kernels. |
| Domain/index coverage | Every opposite local vector is tested, not only the chosen complement. The argument applies separately to each admissible inner rank-one constituent and finite switched list. |
| Maps | Two strict triangles; opposite boundaries; identity derivative-place comparison; conjugate local pullback; local cup and trace. Sections 3–4 compute the composite and its relative sign. |
| Consumed object | Section 5 compares the actual tensors $[A]\otimes[\lambda_A]$ and $[B]\otimes[\lambda_B]$ in the specified determinant lines. |
| Coefficients/normalization | $J$ occurs once, $L$ is common, no averaging or primitive rescaling occurs, and the relative normalizer is the actual unit $-1$, not merely a nonzero field element. |
| Local conditions | $D^0$ is retained in all four conditions; derivative-place $j$ is identity. Section 6 separates completed and primitive height-one comparisons. |
| Exceptions | Nonprimitive $v$, nonunit common multipliers, two-adic lattices without integral eigenbases, nonquadratic global characters, and $(t),(t+2)$ are included. The derivative-switch application still requires $v\ne0$ and the retained duality hypotheses. |
| Downstream | Supplies inner valuation preservation. No outer triangle isomorphism, new rank-zero converse, or whole-paper acceptance follows. |

The separate `REVIEW.md` and `README.md` record the review and delivery
status of these exact bytes. No current manuscript, frozen Lean source,
challenge, manifest or cloud target is changed by this research note.
