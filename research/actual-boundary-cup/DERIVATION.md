# Actual boundary–cup adjunction: cochain proof and source interface

Author: Codex agent `/root/boundary_cup_attack`, 2026-11-09.
This is a research proof packet. It does not modify the manuscript or frozen
39-target packet. The arithmetic application is subject to independent review.

### 0) Problem restatement (brief)

For the actual finite and singular Selmer complexes, prove the identity

$$
 \operatorname{PD}_U(\delta_U(l),y)
   =\sigma\operatorname{inv}_v(l\cup\operatorname{loc}_v y),\qquad \sigma\in\{1,-1\},
$$

with one common sign and trace, and then apply it to
$y_A=j_F^{-1}c(A)$ and $y_B=j_S^{-1}c(B)$. The desired rows must be the
actual $\lambda_z=\operatorname{PD}(-,j_U^{-1}c(z))$.

**Lookup scope and exact revision.** Research head
`fb29fe2bc6968e178a6458357c437574221b5338`; V13
`manuscripts/quartic_v13.tex` SHA-256
`9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`.
Read the actual source passages, existing `research/arithmetic-boundary-cup`
proof and application, the separate `ArithmeticBridge.lean`, and the preceding
boundary scout. Primary source: Jan Nekovář, *Selmer complexes*, Astérisque310
(2006), [published volume](https://www.numdam.org/item/AST_2006__310__R1_0/).
The locally examined PDF SHA-256 is
`61c84e5ad3252a2e520747215ac57a282addc2b58c824a3637bcd77bbe02153f`.
Exact source locators and identities are recorded in `SOURCES.json`.

**Reused versus new.** The prior research note already contains the
pure-boundary argument and desired tensor conclusion, conditional on retained
source constructions. The frozen pure-boundary Lean lemma evaluates a defined
bilinear expression, without constructing its cohomological descent. The new
step here prints the precise coboundary between pairing with the local-condition
component and pairing with the global localization. Seven new Lean lemmas
prove this correction and local representative invariance from the ordinary
Leibniz and chain-trace identities. This is an incremental interface proof,
not a new proof of the whole arithmetic switch.

### 1) Assumptions ledger

| Input | Actual source / use | If absent |
| --- | --- | --- |
| Actual mapping fibres and common strict/relaxed condition retaining $D^0$ | V13 H22 at3509–3542; switch5021–5075 | Cannot identify $\delta_F,\delta_S$ with pure local cone entries. |
| Actual global/local coefficient cups and local isotropy homotopies | V132898–2967,3431–3508; Nekovář1.3.1–1.3.2 and6.2.1–6.2.4 | A bilinear scalar formula alone does not define PD. |
| One compact-support target and trace, with local-invariant square | Nekovář6.3.1 pp140–141; V13 retained duality map | Two arbitrary PD normalizations would leave a relative scalar unproved. |
| Partner is a closed cycle and comparison respects restriction on cohomology | V13 paired-functional3842–4012; companion orthogonal proof | Cannot substitute conjugate local coordinates for the actual partner. |
| Correct mixed local cup and isotropic same-plane cups | V133431–3456 and cross pairing5070–5072 | Extra same-plane terms or a second $J$ invalidate the normalization. |
| Actual retained finite diagrams and their inner transport | V13 inner-limit4577–4636 | Finite cochain identity is proved; its limiting arithmetic application remains conditional. |

The adjunction itself does **not** use perfectness or nonzero trace. Those are
needed separately for rank deductions. The formal local correction works over
any commutative ring and introduces no division or field embedding.

### 2) Lemma-by-lemma resolution

**L1 — Actual connecting representative. PROVED from the stated cone diagram.**
Use Nekovář's convention

$$
 C_U^n=G^n\oplus U^n\oplus L^{n-1},\qquad
 D(g,u,q)=(dg,du,-\operatorname{loc}g+i_Uu-dq).
$$

For $s\in S=H^1(S[-1])$, lift $s$ in the quotient of $C_S$ by
$C_{\rm str}$ by $(0,s,0)$. Its differential is $(0,0,s)$ in strict
cochains. The composite to $C_F^2$ represents $\delta_S(s)$.
Likewise $(0,0,f)$ represents $\delta_F(f)$ in $C_S^2$.
These are cycles because the derivative local model has zero differential
on $F\oplus S$. No triangle isomorphism is involved.

In H22's coordinate $q_{\rm H22}=-q$ the differential is
$\operatorname{loc}g-i_Uu-dq_{\rm H22}$; both pure-boundary signs reverse
together. This change does not give an independently selectable sign for
each local condition.

**L2 — Product before trace. REUSED construction; explicit specialization PROVED.**
Nekovář1.3.2(i), parameter $r=0$, applied exactly as in6.3.1 has

$$
 E_3=\operatorname{Cone}\bigl(C^\bullet(G_{K,S},J(1))
           \longrightarrow\!\bigoplus_w C^\bullet(K_w,J(1))\bigr)[-1].
$$

Its local-condition summand is $B_3=0$. The input global complex, target
$E_3$, and trace $r_J:E_3\to J[-3]$ are independent of whether the first
local condition is $U_F$ or $U_S$. At degree $(2,1)$, bilinearity kills
all terms involving the zero global and local-condition components of
the first input. For a partner cycle $y=(g,u,q)$,

$$
 (0,0,l)\cup_{0,h}y=(0,0,l\cup i_Uu).                 \tag{B1}
$$

The actual global Selmer duality map in6.3.1 is the adjoint of
$r_J\circ\cup_{0,h}$. Thus this evaluation applies to the source's actual
PD-defined functional, rather than to a newly chosen pairing.

**L3 — The missing representative correction. PROVED; formally checked.**
Since $y$ is a cycle, $i_Uu=\operatorname{loc}g+dq$. Since $dl=0$,
Leibniz at degrees $(1,0)$ gives

$$
 d(l\cup q)=dl\cup q-l\cup dq=-l\cup dq.
$$

Consequently

$$
 l\cup i_Uu=l\cup\operatorname{loc}g-d(l\cup q).      \tag{B2}
$$

At the compact-support cone level this is the exact equality

$$
 (0,0,l\cup i_Uu)-(0,0,l\cup\operatorname{loc}g)
       =D_{E_3}(0,0,l\cup q).                        \tag{B3}
$$

This correction is useful: literal equality of the two local cochain
entries was not proved and is not required. The new Lean results
`closed_cup_differential` and `pure_boundary_correction` formalize(B2).
`traced_left_boundary`, `traced_right_boundary`, `traced_change_left`, and
`traced_change_right` prove local representative invariance. These are
consequences of Leibniz and a trace killing differentials, not assumptions
of the desired normalized adjunction.

**L4 — Common trace and actual adjunction. PROVED relative to the source's
specified product and trace; source construction REUSED.**
The defining trace square in Nekovář6.3.1 says that the composite of the
local inclusion $C_3[-1]\to E_3$ with $r_J$ induces the sum of the
specified local invariant maps. It holds up to a retained chain homotopy,
which gives equality on cohomology. The same trace kills(B3). For a
boundary supported at $v$ this proves

$$
 \operatorname{PD}_U(\delta_U(l),[y])
   =\sigma\operatorname{inv}_v([l]\cup\operatorname{loc}_v[y]). \tag{B4}
$$

Here $\sigma=1$ for the displayed convention with the source's compatible
inclusion/trace; H22 changes the common sign. The source diagram, not a
choice of scalar functional, fixes this normalization. If the local
coordinate formula includes a scalar $\kappa$, it is the one coordinate
factor of this same local invariant pairing; it cannot be selected
separately on F and S. The new `traced_pure_boundary` checks the trace
consequence of(B2). The whole global compact-support trace square is
ordinary source mathematics, not a new Lean construction.

**L5 — Transfer through contractions and the inner diagram. PROVED
functorial identity; applicability remains the manuscript's retained-data input.**
For a retained contraction $1-ip=dh+hd$, a chain map $b$ from the local
boundary space, and a cycle $l$, one has

$$
 ip\,b(l)=b(l)-d\,h b(l).
$$

For a closed partner $y$, the chain-map Leibniz formula for the cup product
shows that replacing the first factor by $ip\,b(l)$ changes the product
by a boundary, namely the negative differential of
$\cup(hb(l),y)$. The analogous computation in the second slot uses its
cycle equation. The trace kills these boundaries. Hence the transferred
cup and transferred connecting map induce(B4) on the retained models.
This uses the actual inclusion, projection and homotopy, not abstract
cohomology isomorphisms.

The required finite tuple is: the two cone inclusions/connecting maps,
localization maps, coefficient cup maps, isotropy homotopies, compact-support
trace and its local-invariant comparison homotopy, class cycles, and H22
witnesses, together with their contractions. V134577–4636 states transport
of just such fixed finite diagrams, including the second homotopies.
The new correction is a polynomial identity in this tuple. It therefore
survives the same coefficient-precision/ultrafilter transport if this tuple
is the one retained. There is no inversion of $t$, $2$, or a group order in
this step. The existence/boundedness of the retained arithmetic models and
their full limiting construction are reused manuscript inputs, not newly
certified by the finite checks below. A tuple retaining only cohomology
ranks or only the local conjugation unit would not suffice.

**L6 — Actual local normalizers. PROVED algebraically after the companion
orthogonal identification; its arithmetic applicability is separately reviewed.**
Let $Q(a,b)=\epsilon e(a,Jb)$ be the coefficient pairing and

$$
 \Omega((f,s),(f',s'))
       =\epsilon\{e(f,Js')-e(s,Jf')\}.
$$

The coefficient $J$ occurs once. Its symmetry follows from $J^2=1$ and
$\det J=-1$, without dividing by two. Same-plane cups vanish by the
source's actual isotropy calculation. At two, graded commutativity alone
would be insufficient: V133431–3456 supplies the adjusted uniformizer
and the extra precision making its self-cup zero.

By the companion orthogonal comparison, the actual partners satisfy

$$
 \operatorname{loc}y_A=(uv,0),\qquad
 \operatorname{loc}y_B=(0,-uJv),
$$

where $u$ is the common local conjugation unit previously derived on
actual H1. The same actual classes already contain the fixed multiplier
$L$; none is divided out. Substituting in(B4), and absorbing the one
trace/cone factor into $\kappa$, gives

$$
 \begin{aligned}
 \lambda_A(\delta_Ss)&=-\kappa u\epsilon e(v,Js),\\
 \lambda_B(\delta_Ff)&=-\kappa u\epsilon e(f,v).
 \end{aligned}                                      \tag{B5}
$$

The first equality also uses the symmetry of $Q$. For $s=Jx$, $f=x$,

$$
 q_F=-\kappa u\epsilon e(v,x),\qquad
 q_S=+\kappa u\epsilon e(v,x)=-q_F.                 \tag{B6}
$$

The frozen adapter therefore receives opposite normalizers $c_F=-\kappa u$,
$c_S=\kappa u$, related by the integral unit $-1$. No division by $q_F$,
$\kappa$, or $u_F$ is used. If rank independence is inferred from(B6),
its nonzero value must separately use actual nondegeneracy of the retained
local invariant pairing and $e(v,x)\ne0$; the formal unit algebra permits
zero normalizers and cannot supply this nonzero inference.

### 3) Main theorem

**PROVED as an ordinary cochain consequence of the named retained source
constructions:** the actual global paired functional evaluates a local
connecting class by the same local invariant cup pairing, and the actual
finite/singular partner construction gives(B5)–(B6). The crucial new
explicit equation is(B3), which removes the representative mismatch.

**OPEN as a complete formal arithmetic theorem:** Lean does not construct
the actual global Galois mapping fibres, compact-support trace, retained
isotropy homotopies, H19–H22 cycles, or their limiting comparison. The new
formal result covers the local cochain correction and representative
invariance. The determinant-functor and stored matrix identifications are
owned by the companion determinant packet. This note alone does not prove
the restricted converse, a universal group-ring unit theorem, or the main
Diophantine claim.

**Review status:** independent review required before describing these
exact application bytes as accepted. Existing earlier review labels do not
accept this revised route automatically.

### 4) If refuted: repaired statement

No contradiction was found to(B4) under its exact source premises. Three
weakenings of those premises fail in explicit computation: a nonclosed
boundary direction adds a $dl\cup q$ term; an arbitrary scalar evaluation
of local degree-two cochains need not kill the correction; reversing only
the correction sign fails before trace. Rescaling only $\lambda_B$ by2
also breaks the desired dyadic normalization while leaving many rank and
closedness conditions intact. These are failure tests of proposed weaker
interfaces, not counterexamples to the manuscript's arithmetic construction.

### 5) Verification plan for the verifier role

1. Recompute the degree-(2,1), $r=0$ product using Nekovář1.3.2 and the
   actual target in6.3.1. Check that all three product components, not only
   the third component, have the claimed pure-boundary form.
2. Recheck the cycle equation, Leibniz sign, explicit compact-support
   boundary(B3), and source trace square. Check H22's coordinate change
   reverses both boundary signs together.
3. Recheck actual partner localization with the independent orthogonal
   packet, preserving coefficient carriers and the single $J$.
4. Verify the finite tuple retained inL5 really covers the source-to-limit
   comparison. Treat existence of that tuple and its rank bounds as reused
   manuscript premises, not computationally certified facts.
5. Run `python -B research/actual-boundary-cup/check_cochains.py`.
   The exact torus model has nonzero local cup pairing and nonzero cochain
   corrections; its negative controls detect omitted closedness, a wrong
   sign, and a non-chain trace. It is a cochain-identity check, not arithmetic
   evidence for the actual global Galois objects.
6. Rebuild only `ActualBoundaryCup.lean` under native Lean4.35 and inspect
   all seven theorem statements and axiom dependencies. No paranoid or
   independent external checker result is claimed for these new lemmas.
