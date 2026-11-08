# Boundary–cup adjunction and the actual orthogonal partner

Research note, 2026-11-08. Author: internal model reviewer
`/root/arithmetic_duality`. Scope: independently derive the boundary evaluation
needed by the scalar-ratio adapter from the actual Selmer-cone pairing. This is
neither whole-paper acceptance nor a new Lean replay.

## Target and sources

Reviewed worktree: `derivative-switch-review`, delivery commit
`e653d6ff295ae4e0535710a7d64aa255d294d211`. Manuscript:
`manuscripts/quartic_v13.tex`, SHA-256
`9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`.
Read the repository AGENTS instructions, audit-history protocol, research-review
protocol, `research/scalar-ratio/inputs/ARITHMETIC_CONTRACT.md`, and the actual
historical excerpt `docs/audit-history/issue2/evidence/determinants.md`.

Principal manuscript locations:

- 2897–2967: conjugate coefficient pairing and transported local duality;
- 3225–3233: derivative congruence H12;
- 3421–3509: retained small local model, transfers, cup maps and homotopies;
- 3842–4012: actual functional `lambda_z = PD(-, j^{-1} c(z))`;
- 5020–5093: derivative-switch consumer;
- 5350–5368: the orthogonal/conjugate comparison is the identity at a
  derivative prime, including after a singular switch.

Primary published source: Jan Nekovář, *Selmer complexes*, Astérisque 310
(2006), [Numdam full text](https://www.numdam.org/item/AST_2006__310__R1_0.pdf).
The exact retrieved PDF has SHA-256
`61c84e5ad3252a2e520747215ac57a282addc2b58c824a3637bcd77bbe02153f`.
Relevant locations are Proposition 1.3.2, p. 41; §§6.2.2–6.2.4,
pp. 138–139; §§6.3.1–6.3.4, pp. 140–143; and §§6.4.1–6.4.4,
pp. 144–145. PDF page number is printed page plus nine.
The supplied manuscript's bibliographic URL ending `__1_0/` did not resolve in
this retrieval; the `__R1_0.pdf` file is the published book.

Historical status: the retained determinant excerpt refers back to its
section 9 for functional construction and switch preservation, but that
section is not reproduced in the excerpt. This note supplies a direct
derivation; it does not assert that no previous derivation existed.

## What the duality source actually supplies

Nekovář uses a cone with entries `(a,b,c)` and differential

    d(a,b,c) = (da, db, -res(a) + i(b) - dc).

The Selmer pairing has degree three: degree two in the first complex pairs
with degree one in its orthogonal dual. Orthogonal local conditions require
specified isotropy homotopies; perfectness additionally requires the local
quotient-to-dual comparisons to be quasi-isomorphisms. Theorem 6.3.4 gives the
global duality under these hypotheses. Sections 6.4.1–6.4.4 make functoriality
depend on actual comparison maps and homotopies, including second homotopies.
An abstract isomorphism of cohomology groups does not replace this data.

For the present calculation, Proposition 1.3.2 is more explicit than the
duality theorem alone. Its product with parameter `r=0`, when the first input
is a pure local boundary `(0,0,x)`, is

    (0,0,x) cup (a,b,c) = (0,0, x cup i(b)).

All isotropy and comparison homotopy contributions vanish in this expression.
Applying the global trace identifies this with the local invariant of the
displayed local cup product. This is also the boundary part of Proposition
6.3.3's commutative diagrams. These assertions use the source's actual cone
formula, not an inference from the existence of perfect duality.

Write `delta_S : S -> H^2(C_F)` for the connecting map from
`C_F -> C_rel -> S[-1]`, and `delta_F : F -> H^2(C_S)` similarly. Equivalently,
these are the common-strict boundary directions followed into the other
complex. Lifting `s` as a local-condition entry in `C_rel`, its differential
has local component `s`; hence both boundaries have the same cone sign.
In the source convention they are represented by `(0,0,s)` and `(0,0,f)`.
The manuscript H22 convention `res(p)-i(u)=dq` corresponds to `q=-c` and
changes both boundary representatives together.

Consequently, for the actual orthogonal partners,

    lambda_A(delta_S s) = kappa * Omega((0,s), loc(A_perp)),
    lambda_B(delta_F f) = kappa * Omega((f,0), loc(B_perp)).

Here `Omega` is the fixed local coefficient cup/invariant pairing and
`kappa` is one shared sign accounting for a simultaneous cone/trace
convention. There are no independently adjustable normalizing factors at
this step. A common scalar in the chosen coefficient trace would multiply
both equations equally. The formula alone does not permit replacing
`A_perp` or `B_perp` with an arbitrarily selected generator.

## Actual conjugate partners at the derivative prime

The actual definition is

    A_perp = j_F^{-1} c(A),    B_perp = j_S^{-1} c(B).

The manuscript explicitly identifies `j_F` and `j_S` with the identity at
this prime: finite and singular conditions are their specified integral
orthogonal complements, and conjugation preserves them. The other local
comparisons can change representatives by boundaries, but cannot insert a
scalar into their localization at this prime. In cohomology this gives

    loc(A_perp) = loc(c(A)),   loc(B_perp) = loc(c(B)).

This is the essential use of the orthogonal-partner definition. It prevents
the arbitrary rescaling that would be possible if only generic rank-one
duality were known.

The conjugate local coordinates must still be calculated; they are not
identical to the original coordinates in both summands. At the inert prime
choose a local representative `sigma = Fr_ell` of the nontrivial element of
`Gal(K_v/Q_ell)`. The unramified generator over `K_v` is `sigma^2`. On tame
inertia, conjugation by `sigma` raises a generator to its `ell`th power.
Thus pullback of a degree-one cochain fixes its finite coordinate and
multiplies its singular coordinate by `ell` (or `ell^{-1}` if inverse
pullback is used). The difference between global conjugation and this
local representative is handled by the usual inner-conjugation transport
of the coefficient system and place; it is not an independent scalar
normalization. The manuscript already transports the Tate basis and local
pairing with the chosen place.

H12 gives `ell = -1` at every retained coefficient precision. Thus either
pullback convention gives, in the transported coordinates,

    c_v(f,s) = (f,-s).

The Weil identification of the conjugate coefficient system is a separate
map. In the retained basis it contributes `J`, with `J^2=1`, `det J=-1`.
Keeping these two operations separate avoids counting `J` twice or losing
the singular minus sign.

Let `e` be the alternating Weil form and put `Q(x,y)=e(x,Jy)`. The relation
`J^t e J=-e` implies `Q(x,y)=Q(y,x)`. After fixing the common local trace
generator, denote its scalar by `epsilon`. The mixed cup product is

    Omega((f,s),(f',s'))
      = epsilon * (Q(f,s') - Q(s,f')).

Its minus sign is the degree-one cup interchange sign; it must be retained
even at the prime two. The coefficient form `Q` is symmetric. The finite
and singular self-cups vanish in the retained model, as established in the
manuscript local-diagram construction.

The old and derivative classes have

    loc(A) = (v,0),           loc(B) = (0,Jv),
    loc(A_perp) = (v,0),      loc(B_perp) = (0,-Jv).

Substitution in the boundary identities now yields, for all `s` and `f`,

    lambda_A(delta_S s) = -kappa * epsilon * Q(v,s),
    lambda_B(delta_F f) = -kappa * epsilon * Q(f,Jv).

These identities use the actual partners and the actual derivative, not
their primitive replacements. Define the frozen adapter's pairing by
`beta(f,s)=epsilon*e(f,J s)`. Its convention is

    lambda_F(A_S s) = c_F * beta(v,s),
    lambda_S(A_F f) = -c_S * beta(f,Jv).

The displayed source derivation therefore gives

    c_F = -kappa,    c_S = kappa,    c_F = (-1) * c_S.

In particular, equal normalization is not the correct claim in this
explicit convention. The required integral unit relation does hold.
Changing a common cone convention changes `kappa` and preserves the
relation. A different retained basis can insert determinant units but
cannot justify an unrecorded nonunit rescaling.

With `det J=-1`, the existing scalar-ratio formula then gives `u_F=-u_S`
in its stated cofactor orientation, and therefore equal valuations.
This sign statement is relative to the explicit boundary and cup
conventions above. The basis-independent consequence needed by the
manuscript is the unit relation.

## Integral, localization and limit checks

1. No inverse of `v` was used. The identity holds for a divisible actual
   localization vector. A fractional complement is needed only when
   extracting the matrix coordinate, where the existing scalar-ratio
   proof cancels its volume.
2. The boundary is supported at the derivative prime. Its pairing with
   the orthogonal partner depends only on that partner's local class.
   Old-support contractions do not contribute a new local scalar.
3. A fixed multiplier `L` already present in both actual classes is
   carried into both orthogonal partners by linear maps. It is not divided
   out, and the identities are linear in the actual vector `v`.
4. If a common additional denominator-clearing factor is used for both
   functional representatives, it multiplies both `c_F,c_S` and cancels
   in their unit comparison. Different independent clearing factors would
   not be justified. The manuscript's strengthened integral construction
   in fact asserts `a=0` over `O[G]` with its actual multiplier retained.
5. The only new ratio here is `-1`. It is a unit over the integral
   coefficient rings, the completed two-adic DVR, and every height-one
   localization, including `(t)` and `(t+2)`. No division by `2`, `t`,
   `t+2`, or a Frobenius determinant occurs in this calculation.
6. Before replacing `ell^{+/-1}` by `-1`, the corresponding ratio is an
   odd integer or its inverse, also an integral unit. H12 makes the
   replacement exact at the retained precision. The retained identities
   are finite matrix/cochain identities and survive the specified inner
   passage if its stated retention of maps, pairings and homotopies is
   accepted. This note does not independently reprove that construction.
7. The boundary formula does not require a global map `C_F -> C_S`, an
   identity-on-strict triangle lift, or a nonidentity strict automorphism.
   The previously rejected triangle proposal remains rejected.

## Certification scope and remaining work

The normalization issue is not inherently underdetermined once the actual
orthogonal comparison and conjugate local coordinates are included. The
published cone product and the manuscript's specified derivative-local
data force an integral unit ratio. This is a source-level candidate
closure of the **boundary–cup normalization step**, relative to those
retained arithmetic inputs. It is stronger than merely assuming
`c_F/c_S` is a unit, and does not claim that bare abstract self-duality
forces the normalization for arbitrary functionals.

Before calling the full scalar-ratio arithmetic application accepted, a
separate reviewer must check this derivation, particularly the actual
conjugate transport convention and the identification of the matrix
columns with these boundaries. The common-strict integral presentation
or determinant-functor bridge, all source occurrence and limit claims,
and downstream application coverage remain distinct obligations. This
note supplies no new acceptance for the restricted converse, does not
modify the frozen 39-target packet, and does not count as a cloud paranoid
run.
