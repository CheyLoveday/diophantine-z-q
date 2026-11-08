# Review of the arithmetic boundary–cup normalization

### 1) Verification target

**Accepted within the stated inherited-source scope.** The reviewed note
derives the relative normalizer $c_F=-c_S$ for the actual paired
functionals and gives a valid ordinary determinant-line bridge. It does
not independently certify the whole retained arithmetic construction or
instantiate those objects in Lean.

Date: 2026-11-08. Reviewer: non-author Codex model agent
`/root/arithmetic_normalization_review`, inherited GPT-6 Astra host model.
I did not author or edit the reviewed derivation, manuscript, frozen
Lean packet, or finite checker. This is internal model review; shared
context and model correlation remain, and no human acceptance is claimed.
I used read-only source inspection, local primary-source PDF/text,
SHA-256 binding checks, and the stated exact finite checker. A separate
bounded challenge by `/root/arithmetic_normalization_review/transport_check`
checked the local transporter and upper-Frobenius compatibility. Its
argument is recorded below, not counted as an independent whole-proof
review.

The decision binds these exact bytes:

| Target | SHA-256 |
| --- | --- |
| `research/arithmetic-boundary-cup/DERIVATION.md` | `007cd09ea0f50f073d9a48e6d44ffb12a53b4233b585e4753e112182ce63ecd2` |
| `manuscripts/quartic_v13.tex` | `9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd` |
| `lean/Research/DerivativeSwitch/BoundaryCup.lean` | `64750e7706f82cf0a47b76c80503bcab0577c2aa18f9703c09b4b8288be0df90` |
| `research/scalar-ratio/DERIVATION.md` | `02fbb34ccd76ff3d3894b812416b722cf6f044322d16d35b4d0f11e39561e733` |
| `research/scalar-ratio/inputs/ARITHMETIC_CONTRACT.md` | `99e5dbbc3e1c5eb71e98350ca0955cd045d4cdeaab800b20c1023588144a3f9a` |
| Published Nekovář PDF | `61c84e5ad3252a2e520747215ac57a282addc2b58c824a3637bcd77bbe02153f` |

The base commit is `e653d6ff295ae4e0535710a7d64aa255d294d211`.
The primary source is Jan Nekovář, *Selmer complexes*, Astérisque 310
(2006), [published PDF](https://www.numdam.org/item/AST_2006__310__R1_0.pdf).
I read the explicit cone product in 1.3.2, local boundary formulas in
6.2.2–6.2.4, global product and boundary diagrams in 6.3.1–6.3.3, and
the manuscript passages identifying the coefficient pairing, actual
classes, functionals, derivative local comparisons and retained limits.

The hypotheses accepted as source inputs are the actual perfect
integral Selmer diagrams and their retained duality; the H19–H22
classes and witnesses; the localized orthogonal comparisons; the
inner-limit retention of these maps and homotopies; and the old
generic rank-one/nonzero-localization condition. They are not replaced
by the desired normalizer or determinant conclusion. The historical
lookup is the bounded source lookup in the note; the full historical
section 9 remains unresolved, so this review makes no priority or
whole-history claim.

### 2) Independent re-derivation (outline)

**Boundary maps and the actual rows.** In the cone convention
$d(g,u,l)=(dg,du,-\operatorname{loc}g+iu-dl)$, adjoining a local
degree-one vector gives the boundary representative $(0,0,l)$.
This sign is identical for the two separate strict triangles. In
Nekovář's product with parameter zero, pairing this representative
against a degree-one orthogonal partner leaves only its local cup
with the partner's local-condition component. The first global and
first local-condition entries vanish, so every bilinear homotopy term
also vanishes. Neither old-support homotopies nor an independently
chosen normalization can contribute a second scalar to this expression.

The source defines the partner as $j_U^{-1}c(z)$. Since the derivative
local component of $j_U$ is identity, its local cohomology class is
exactly the conjugate local class of $z$. This statement requires no
equality between $j_F$ and $j_S$ globally and no map $C_F\to C_S$.
Thus the evaluated rows really are the source's $\lambda_A,\lambda_B$.

**A check of local transport beyond the quadratic specialization.**
Let $r=\rho_T\alpha$ and choose a local rational Frobenius $d$ satisfying
H12. Put $a=d\tau\in G_K$. For a cocycle $p$,

$$
p(a^{-1}xa)=r(a)^{-1}\bigl(p(x)+(r(x)-1)p(a)\bigr).
$$

At the retained derivative precision, $r$ is trivial on the local
$K$-decomposition group. Moreover
$r(a)=\rho_T(d)J\alpha(a)=\alpha(a)I$ at that precision. Since
$\tau g\tau^{-1}=a^{-1}(dgd^{-1})a$, raw conjugate pullback is the
same character unit $\alpha(a)^{-1}$ times pullback by $d$, for both
$A$ and $B$. This calculation does not use $\alpha^2=1$ globally.

The square $d^2$ is an allowed finite Frobenius generator in H19.
The finite descent field is the ring-class field $H_{fn_I\ell}$,
before the H20 coefficient push. Its Galois group over $\mathbf Q$
is generalized dihedral, so the image of $d$ has square one; hence
$d^2$ lies in the upper absolute group. The local extension over $K$
is totally ramified and the old ring-class field splits. Thus this
choice agrees with the required upper-subgroup Frobenius. A compatible
alternative differing by tame exponent $ek$, $e=\ell+1$, gives shear
$ek(\ell-1)=k(\ell^2-1)$, zero at the retained precision. This does
not license an arbitrary untransported change of generator.

Pullback fixes the finite coordinate and multiplies the tame coordinate
by $\ell$ or $\ell^{-1}$ according to orientation; both equal $-1$
at retained precision. The shared character unit can be included in
the common convention factor. The coefficient $J$ still occurs only
once, in $Q(x,y)=e(x,Jy)$.

**Relative sign.** The raw coefficient cup on the two degree-one planes
is the alternating block form

$$
\varepsilon\{Q(f,s')-Q(s,f')\}.
$$

Because $Q$ is symmetric, composing its second argument with raw
conjugate pullback $\operatorname{diag}(1,-1)$ gives a symmetric
transported cross form. Evaluating on the two opposite boundary
directions gives the same effective sign:

$$
\lambda_A(\delta_Ss)=-\kappa\beta(v,s),\qquad
\lambda_B(\delta_Ff)=-\kappa\beta(f,Jv).
$$

The frozen adapter places an additional minus sign before its singular
normalizer. Accordingly $c_F=-\kappa$ and $c_S=\kappa$. The witness
$-1\in R^\times$ is explicit; no inference from a nonzero field scalar
to an integral unit is used. Absolute signs depend on the shared cone,
trace and local orientation convention, while this unit comparison
does not.

**Determinant-line comparison.** Independently of simultaneous integral
matrix presentations, use the generic long exact sequences. The old
rank-one class with nonzero localization makes strict $H^1$ zero and
$W=H^2(C_{\rm str})$ two-dimensional. For a complement $x$, put
$a=\partial_Fx$, $b=\partial_SJx$. The first cross evaluation is
nonzero under the actual normalized local trace and perfect pairing,
so $a,b$ are independent. The derivative cycle kills $Jv$ under
$\partial_S$, whose image has dimension one. This proves the new
rank-one dimensions rather than importing the desired rank conclusion.

The exact-sequence determinant formula uses $(v,x)$ and $(a,b)$ on
the finite side, and $(Jv,Jx)$ and $(b,a)$ on the singular side.
Consequently its two coefficients are $q_F$ and $-q_S$. The boundary
calculation gives $q_S=-q_F$, so the tensors agree under the local
$\det J$ comparison up to the fixed determinant sign convention.
This confirms section 5's bridge. It also explains why the stronger
numerical equality theorem for common normalizers is not the intended
arithmetic specialization of the frozen Lean source.

### 3) Checks

- **Plug-back:** The opposite boundary maps use the same strict cone
  and exactly the source's two rows. The all-vector identities imply
  the complement evaluations with the correct alternation sign.
  The tensor formula reproduces the frozen cofactor relation
  $\det(J)u_F=u_S$ in its coherent frames.
- **Nonprimitive vectors and torsion:** No integral complement to $v$
  is required. Both generic tensor expressions use the same integral
  strict determinant line, so its torsion and lattice contribution is
  retained and common. A common nonunit factor is not replaced by a unit.
- **Two-adic and exceptional cases:** The calculation does not use
  eigenspace projectors or division by two. The note correctly separates
  the completed two-adic comparison from primitive height-one
  representatives, and invokes the source's different contractions at
  $(t)$ and $(t+2)$. The derivative-place comparison itself is identity.
- **Zero cases:** The adapter's division-free normalizer relation allows
  both normalizers zero. The arithmetic rank argument in section 5
  separately uses the actual nonzero normalized local trace and pairing;
  it does not infer rank one from a zero evaluation. The excluded
  $v=0$ case is not silently included.
- **Limits:** The finite local identities are retained first; the
  orthogonal inverse defining the functional is used only after its
  justified localization. No finite-Artin inverse of $t$ or outer
  rank-preservation assertion is introduced.
- **Binding checks:** I recomputed the whole manuscript hash, all ten
  passage hashes in `SOURCES.json`, the frozen cloud manifest hash, and
  all 99 bound cloud input hashes. All matched.
- **Finite checks:** I inspected and reran the author's
  `python -B research/arithmetic-boundary-cup/check_local_signs.py`.
  All 675 exact cases passed. Its nonunit row rescaling, double-$J$
  and omitted-tame-sign controls were rejected as stated. This is a
  repeat of finite sign/tensor evidence, not independent verification
  of Galois classes or the retained arithmetic diagrams. I ran no Lean,
  cloud, paranoid, or external-kernel verification.

### 4) Discrepancy report (if any)

No change is required to the reviewed derivation within its declared
scope. Its relative sign differs from the stronger *common-normalizer*
specialization considered in the earlier algebraic packet, but that is
an intended correction of the application, not a defect in the frozen
conditional theorem. The existing unit-normalizer theorem has the
required strength.

The new note still inherits the manuscript's existence, perfection and
compatibility of its integral Selmer diagrams and limits. This review
checks the proposed composition using those inputs; it does not turn
them into freshly verified or formally instantiated constructions.
Its direct determinant-line argument removes the need for a simultaneous
matrix model in the ordinary proof. An actual Lean invocation would
still need the formal object/model bridge, so that formal arithmetic
application remains unfinished.

### 5) Certification result

**CERTIFIED under the explicit retained-source assumptions in section 2
of the bound derivation**, in the limited sense of internal non-author
mathematical review: the actual boundary–cup normalizers differ by an
integral unit, and the separate common-strict triangles compare the
actual class-functional tensors up to an integral unit. Hence their
valuations agree in the stated inner instances.

This is not whole-paper certification, human acceptance, formal arithmetic
verification, or manuscript incorporation. It does not alter the frozen
39-target packet or infer any result from the cloud job. The historical
arithmetic-open statuses of the earlier frozen packets remain accurate
for those packets; this later ordinary source-level result should be
reported separately, with its inherited assumptions and review scope.
