# Deriving the common local transport unit

This is a proof of the local-conjugation calculation needed by the separate
arithmetic bridge. It is not a proof of the determinant-switch theorem.
The finite calculation is formalized in `ConjugateLocalTransport.lean` and
`ConjugateLocalH1.lean`; the arithmetic occurrence and retained-limit application
below are human arguments relative to the manuscript inputs in `APPLICATION.md`.

## 1. The actual representation determines the unit

Use the notation of `SPEC.md`. All scalars lie in the commutative coefficient
ring $R$; no field, domain or invertibility of 2 is required. Put

$$
\sigma(h)=\alpha(h)T(h),\qquad d=\varphi\tau^{-1},\qquad
u=\alpha(d)^{-1}\in R^\times.
$$

The equality $T(\varphi)=T(\tau)$ gives $T(d)=1$. Therefore
$\sigma(d)=\alpha(d)\operatorname{id}$ and
$\sigma(d^{-1})=u\operatorname{id}$. This is derived from the actual
twisted representation; the scalar action is not a new normalization premise.
Also, $F=\varphi^2$, $\tau^2=1$, and $\alpha(F)=1$ give
$\sigma(F)=1$. The separate assumptions $T(I)=1$, $\alpha(I)=1$
give $\sigma(I)=1$.

For a crossed cocycle $p$, expand $p(a(a^{-1}xa))=p(xa)$ and apply
$\sigma(a^{-1})$. This proves the full formula

$$
p(a^{-1}xa)=\sigma(a^{-1})\bigl(p(x)+\sigma(x)p(a)-p(a)\bigr).
$$

It includes the coboundary term. Only trivial action at the relevant local
element removes that term. When $\sigma(I)=1$, induction gives
$p(I^n)=n p(I)$ for every natural $n$, including zero.

Since $\varphi=d\tau$, one has

$$
\tau h\tau^{-1}=d^{-1}(\varphi h\varphi^{-1})d.
$$

The element $\varphi$ fixes $F=\varphi^2$ under conjugation, while the
tame relation gives $\varphi I\varphi^{-1}=I^\ell$. Thus the raw pullback
$c_\tau(p)(h)=p(\tau h\tau^{-1})$ satisfies

$$
c_\tau(p)(F)=u p(F),\qquad c_\tau(p)(I)=u\ell p(I).
$$

At the retained finite precision $\ell=-1$, so

$$
\operatorname{loc}(c_\tau p)=(u f(p),-u s(p)).
$$

The unit is defined by the fixed representation and transporter. It is
independent of $p$, so exactly the same unit works for the old class and
the derivative class. Zero and divisible local vectors are included. No
projector, primitive vector, nonzero class, division by a local vector, or
global quadraticity of $\alpha$ is used.

## 2. Cohomology and coefficient types

The raw pullback is a crossed cocycle for
$\sigma^\tau=\sigma\circ\operatorname{Ad}_\tau$. It need not be a cocycle
for $\sigma$. This distinction matters for the nonquadratic moving character.
The coefficient pairing into the dual is separately
$e_2(x,T(\tau)y)$; raw conjugation does not insert a second $J=T(\tau)$.

A coboundary has value $\sigma(h)v-v$. It vanishes at $F,I$. It also
vanishes at $\tau F\tau^{-1},\tau I\tau^{-1}$, since their actions are
conjugates of the identity. Consequently both ordinary and conjugate local
coordinates depend only on the respective cohomology classes.

The Lean file `ConjugateLocalH1.lean` makes this descent explicit for
Mathlib's cohomology of the inhomogeneous cochain complex. It constructs:

- evaluation maps on $H^1(H,\sigma)$ at trivially acting elements;
- pullback $H^1(H,\sigma)\to H^1(H,\sigma^\tau)$;
- local coordinate maps on both groups;
- their shared-unit identity for every cohomology class.

These maps factor through Mathlib's actual `H1π`, using its kernel theorem.
They are not maps on an invented abstract class type. The construction does
not identify the two coefficient representations and does not assume global
triviality of either representation. Its use for continuous arithmetic classes
is through the following finite quotient; continuous Galois cohomology is not
constructed by the new Lean modules.

## 3. A common quotient makes the tame relation legitimate

At a fixed finite coefficient stage the module is finite and 2-primary.
At a good odd derivative prime, the coefficient character is locally trivial;
good reduction makes Tate inertia trivial. In the inert quadratic local field,
the finite generator acts trivially by H12 and $F=\varphi^2$. Thus the entire
local action is trivial. Restricting either continuous cocycle to this local
group gives an additive homomorphism.

Wild inertia is pro-$\ell$, with $\ell\ne2$. Its image under a continuous
homomorphism to a finite 2-primary additive group is both an $\ell$-group
and a 2-group, hence trivial. This also holds at the conjugate place. This
argument proves vanishing of the actual cocycles, not just vanishing of an
abstract cohomology group.

For a finite continuous cocycle $p$, the affine action
$h:v\mapsto p(h)+\sigma(h)v$ is a homomorphism into a finite group.
Its kernel is open and normal in $H$, kills $p$, and kills $\sigma$.
Use the intersection of these kernels for both actual cocycles, their raw
conjugates, the character, and the Tate representation. Then intersect with
its $\tau$-conjugate. Because $H$ has index two in the arithmetic group,
the result is normal in that group. It still kills wild inertia: the action
and all the cocycles vanish on the relevant wild groups and their conjugates.

The resulting common finite quotient preserves the two cocycles, both
coefficient systems, $\tau,\varphi,d,F,I$, and the representation identities.
The tame relation is exact there. On the tame quotient over $\mathbf Q_\ell$,
arithmetic Frobenius satisfies $\varphi I\varphi^{-1}=I^\ell$; over the
inert quadratic field the finite generator is $F=\varphi^2$.
Nekovář, *Selmer complexes*, §7.1.1 p.155 and §7.2.1 p.156, uses geometric
Frobenius $f$ and relation $If=fI^L$. Taking $\varphi=f^{-1}$ gives
the stated arithmetic-Frobenius convention. An inverse convention yields
$\ell^{-1}$, which also equals $-1$ at the retained precision.

The prerequisites here are finite coefficients, continuity, the index-two
arithmetic subgroup, good odd derivative primes, and actual local triviality.
They are source inputs; the arbitrary-ring Lean theorem does not imply them.

## 4. Retain the unit and its inverse in the same inner diagram

A fixed natural prime cannot equal $-1$ in characteristic zero. The finite
Lean theorem must therefore not be applied directly over the characteristic-zero
field of `ArithmeticBridge.lean` with that premise. Nor need the moving
characters at different stages be restrictions of one character: V13 explicitly
says otherwise at 4456–4464.

The manuscript's `ex:limits-inner-limit` instead fixes one nonprincipal
ultrafilter on finite coefficient stages. At stage $i$, adjoin

$$
u_i=\alpha_i(d_i)^{-1},\quad v_i=\alpha_i(d_i),\quad u_i v_i=v_i u_i=1
$$

to the same finite retained tuple containing the original and conjugate local
coordinate maps, classes and their comparison witnesses. These are two scalar
entries, independent of model rank and of the choice between the two classes.

Here is the required compactness argument explicitly. For any fixed coefficient
precision $n$, stages sufficiently far out reduce into the finite ring $R_n$.
The ultrafilter selects exactly one value for the reduction of $u_i$, and
exactly one for $v_i$, because a finite partition has exactly one cell in an
ultrafilter. Call these values $u_n,v_n$. Intersect their selected cells with
the cofinal set where the finite identity holds. It follows that
$u_n v_n=v_n u_n=1$. Reducing a selected value from precision $n+1$ to
precision $n$ gives another selected value at precision $n$; uniqueness
therefore proves compatibility. The two compatible systems give $u,v$ in
$\Lambda$ (or $\Lambda[G]$) with $uv=vu=1$.

The same finite-partition argument applied to the whole retained tuple preserves
the polynomial equations
$\operatorname{loc}(c p)=(u f(p),-u s(p))$ for the two stored actual classes.
Adjoining these two entries does not change any pre-existing entry's limit:
the ultrafilter was already fixed, and the selected value of each entry is
unique. There is no new rescaling of the actual class or functional. Keeping
the inverse establishes an integral unit, rather than a nonzero fraction-field
scalar.

There is a further quantifier issue if one needs the identity for *every*
limiting cohomology class, as in `PairedBoundaryData.conjugate_local`. Finite-stage
equalities on cohomology alone do not justify that assertion: new cycles can
appear after a nonflat coefficient reduction. Here is the required argument
using the retained contractions rather than an unproved cohomology base change.

Fix a cycle $z$ in the limiting finite free model, and fix a precision $n$.
Its reduction $z_n$ is a cycle in the reduced model $C_n$. On a set in the
fixed ultrafilter, the stage model ranks, differential matrices, coordinate
maps, conjugation comparison, and $u_i$ all agree modulo precision $n$
with their retained values. View the *same vector* $z_n$ as a cycle of
$C_i\otimes R_n$ for a stage in that set; no lift of $z_n$ to a cycle
over $R_i$ is asserted or needed.

The retained inclusion/projection/contraction identities survive tensoring
to $R_n$, because they are actual chain identities, not merely stagewise
quasi-isomorphisms. The continuous cochain modules commute with this finite
coefficient reduction: they are filtered colimits of finite free function
modules on finite clopen partitions, for which the assertion is immediate.
Thus the model inclusion supplies an actual reduced global cocycle, with the
retained local and conjugation comparisons. Apply the finite theorem at
precision $n$ to that cocycle. H12, local triviality, and the explicit unit
all reduce to that precision. Coboundary terms from the comparison homotopies
do not affect the coordinates by Section 2. Therefore the required local
identity holds for $z_n$. Since $n$ and $z$ were arbitrary and the
coefficient ring is separated, it holds for every limiting class. This proves
the needed universal statement without assuming that cohomology commutes with
nonflat base change.

This application is relative to the source's finite-model/retained-inner-limit
construction and its required bounded ranks, actual local comparison maps and
contraction witnesses. It does not re-prove that construction in Lean. It shows
that failure of stagewise coherence of the moving characters is not, by itself,
an obstruction to retaining this particular unit. Subsequent ring maps preserve
the unit and its inverse; identifying the actual later model and local maps is
still required, not replaced by that algebraic observation.

## 5. What this supplies and what it does not

The new calculation supplies the common local-conjugation factor from the
twisted representation/H12 data. On actual finite $H^1$ this is formalized;
the source application and the explicit inner-unit argument are ordinary
mathematical proofs relative to the named arithmetic inputs. It supplies the
local content of `PairedBoundaryData.conjugate_local` when the retained model
and coordinate maps are the ones just specified.

It does not construct the global boundary–cup adjunction, identify the actual
orthogonal comparison inverse at every needed localization, realize the
common-strict matrices, identify the stored degree-two functional rows, or
prove determinant-functor/base-change compatibility and occurrence. Those are
the remaining steps between this result and the determinant tensors. No
finite/singular triangle isomorphism, identity-on-strict lift, or repaired
restricted converse is claimed.
