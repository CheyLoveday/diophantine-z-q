# Binary-family sign and signed calibration

## Status and scope

The binary sign criterion and signed-curve calculations below are mathematical results. The rank argument is a proved conditional implication from the actual coefficient/Selmer/descent data specified below, not a declaration that those original comparisons have been constructed.

An integration receipt received on 19 November 2026 records the eight RC36 signed-calibration files as merged with [PR 141](https://github.com/Deicyde/diophantine-z-q/pull/141) at main commit `740aa8edc`, byte-identical to `68637bf4b`. The external review at integration commit `35d83d594119f7fb570d2ac8064997565883c1c6` rated RC36 SOUND, reporting a clean project-source rebuild, exact signed rank-one type match, and standard logical axioms. This is a dated integration/review receipt, not continuous verification of the remote branch or a proof of the whole restricted converse.

The merged implementation remains conditional on its explicit coefficient comparison, finite-generation, rational-corank and calibration-book inputs. Classical support for an input is not a Lean inhabitant of it. The actual `KummerCorankOneGlue` explicitly requires ellipticity, `Module.rank ℤ A.toAffine.Point = 1` and `Finite (sha A)` before concluding corank one. Mordell–Weil and algebraic rank one alone do not supply that finite-Sha premise. At covered addresses, `selmerCorankOneOverKSigned_of_forward` uses analytic rank one and the BCDT/Kolyvagin `Prints` to obtain both algebraic rank one and finite Sha, then invokes the Kummer/Mordell–Weil glue. Those Prints and that Glue remain explicit theorem arguments; a standard-axiom census does not inhabit them. RC37's concrete comparison and ellipticity correction are separate from this RC36 landing.

## Exact binary-family sign criterion

Let Addr(b)=F_2^b. For a finite set of positive odd primes q and linear forms λ_q:Addr(b)→F_2, write

q*=(-1)^((q-1)/2)q,

h_x=∏_q(q*)^val(λ_q(x)),

ε_q=((q-1)/2) mod 2,

σ_F=Σ_q ε_q λ_q.

Here val takes the values zero and one. Put N_x=Σ_q((q-1)/2)val(λ_q(x)) and P_x=∏_q q^val(λ_q(x)). Since P_x>0,

h_x=(-1)^N_x P_x,  and  N_x mod 2=σ_F(x).

Thus h_x>0 if and only if σ_F(x)=0. All members are positive if and only if σ_F is the zero linear functional. It is sufficient to test the b standard basis vectors. The cases b=0, x=0 and empty products are included; the central address has h_0=1.

The displayed standalone admissibility conditions do not universally imply positivity. For example, take b=1, Q={7}, S={2,3,11}, k=-3 and λ_7(x)=x_0. The prime 7 is odd and outside S, λ_7 is nonzero, and (-3/7)=1 because -3 is congruent to the nonzero square 4 modulo 7. Yet h_1=-7.

This is a counterexample to positivity from standalone admissibility, not to the full final-family predicate or its analytic-rank/local-type requirements. It is not a claim about every fixed companion k. An actual binary-character construction can supply a common-real-sign condition; its transport to this particular family must be proved, not added as a new positivity field to the final predicate.

## Signed curves must keep their sign

For the specified model

C(t)=<0,2t,0,-3t²,0>,

the affine equation is y²=x(x-t)(x+3t). With the specified quadratic-twist convention,

qtwist(C(t),d)=C(td)

coefficientwise for all rational t,d, including negative values. Its invariants include

c4=208t²,  c6=-2240t³,  Δ=2304t^6.

Consequently it is elliptic exactly when t≠0. The zero parameter gives the singular curve y²=x³. For nonzero t, C(t) and C(-t) are not Q-isomorphic: c6 reverses sign, whereas an admissible change of Weierstrass variables over Q scales c6 by a nonzero rational sixth power or its inverse, which is positive.

Replacing a negative parameter by its absolute value changes the rational isomorphism class. Truncating a negative integer to a natural number produces zero and the singular model. Neither operation represents the original signed address curve.

The twist identity commutes with the actual characteristic-zero base change. Given the original central-curve binding, the central curve is the base change of C((ℓ:Q)(h_x:Q)), and the companion is C((ℓ:Q)(h_x:Q)(k:Q)). Positivity is not needed for those literal coefficient identities.

## Coefficient contract required for the rank argument

Let R=Z_2, F=Q_2 and D=F/R. Retain the actual compact complex C, its rational complex C_F and the specified termwise coefficient quotient C_D for the actual elliptic curve, field, support, Galois action and Kummer local conditions. Put M_i=H^i(C).

The argument requires:

1. The actual canonical coefficient triangle C→C_F→C_D→C[1]. Under the rational base-change maps φ_i:H^i(C_F)≅F⊗_R M_i, its actual first map α must satisfy φ_i(H^i(α)(m))=1⊗m, at least in degrees one and two. An unlabelled module isomorphism is insufficient.
2. For the specified termwise C_D, actual degreewise R-flatness/torsion-freeness of C, or an actual compatible quasi-isomorphism from the derived quotient to that very C_D, preserving quotient and connecting maps. Neither finite generation of cohomology nor finiteness of point torsion supplies this comparison.
3. The specified quasi-isomorphism from the truncation through degree one of the integer-scalar restriction of C_D into the actual discrete Selmer construction, with that construction's own H1 identification with the genuine Selmer group over K. A different complex merely named Selmer is not the required target.
4. Finite generation of M_1 and M_2 over R.

These are object/map comparisons, not a desired-rank premise or permission to replace the original coefficient quotient.

## Universal coefficients and rank

With those inputs, the coefficient triangle has the cohomology segment

M_1→F⊗M_1→H^1(C_D)→M_2→F⊗M_2.

The last kernel is T_2=tors_R M_2; right exactness of tensoring R→F→D→0 identifies the first cokernel as M_1⊗D. Composing with the specified Selmer comparison gives

0→M_1⊗_R D→Sel_(2∞)(E/K)→T_2→0.

A finitely generated Z_2-module has a finitely generated free quotient and finitely many cyclic torsion summands R/(2^a). The residue field is F_2, so each R/(2^a) is finite as a set. This proves set-finiteness of T_2; a general DVR with infinite residue field would not give that conclusion.

If r=rank_R M_1, then M_1⊗D≅D^r since D is divisible and kills the torsion of M_1 under tensoring. The same actual integral free quotient supplies both these coordinates and the rational F^r coordinates. Hence

corank_R Sel_(2∞)(E/K)=rank_R H^1(C).

Torsion in M_1 or M_2 need not vanish. The finite T_2 term is retained in the exact sequence, not replaced by an arbitrary defect. Rationalization kills finite torsion for the rank calculation; it does not prove that the integral torsion vanishes.

## Quadratic descent and remaining bindings

For K/Q quadratic, provide actual maps

f:Sel_(2∞)(E/Q)⊕Sel_(2∞)(E^(k)/Q)→Sel_(2∞)(E/K),

g:Sel_(2∞)(E/K)→Sel_(2∞)(E/Q)⊕Sel_(2∞)(E^(k)/Q),

with gf=fg=[2], compatible with restriction, corestriction, the actual twist identification and every Kummer local condition. With cofinite generation, Pontryagin duality followed by tensoring with Q_2 makes multiplication by two invertible and proves corank additivity. A point-level isogeny alone does not supply the Selmer comparison. Integral half-sum projectors (1±σ)/2 are not used.

The current named inputs are not discharged by the conditional calculation: the signed coefficient comparison and its actual maps, degreewise flatness or derived-to-termwise comparison, the finite-level Selmer description through G_(K,S), genuine finite-generation and rational-corank inputs, quadratic/Mordell–Weil corank glue, the nine calibration book statements, and the further original duality/retained-model/disk-order joins. The integration-only comparison reportedly splits `KcArithSelmerLevel` into `KcSelOfLoc` and `KcLocOfSel`, each retaining ellipticity. The first direction reduces to a named `KcSelOfLocFinite` PRINT + GLUE input; the Milne ADT I.3.8, pp. 46–47, locator for its unramified part remains unverified by a second reader. Local-map compatibility at S remains GLUE. The reverse direction `KcLocOfSel` remains named, with its Silverman X.4.4 locator unverified. This is a conditional dependency reduction, not proof of those inputs or a claim that RC37 is on main.

The recorded calibration-source locators include Milne, *Arithmetic Duality Theorems*, second edition, I.2.1 p. 27, I.2.3 p. 28, I.3.2 p. 42, I.3.4 p. 43, I.3.5 p. 44, I.4.10(c) p. 57 and I.4.15 p. 62; and Nekovar, *Selmer complexes*, 5.4.1 and 5.4.3(ii), p. 127. These are recorded dependency locators, not certification here of every printed-formal predicate or supporting definition. See the existing [literature-link index](../literature-links/README.md).

## Zero and roadmap discipline

Keep three different cases distinct: curve parameter t=0 is singular; address x=0 has h_0=1; torsion exponent n=0 means order 2^0=1, not order zero. The original all-level quantifier includes n=0, and finite dyadic-place conditions are not dropped.

The public roadmap should distinguish the proved sign/curve calculations, the reviewed conditional rank argument, the implementation's separate external review/landing state, and the unproduced original comparisons. None of them establishes the whole restricted converse, pole-completeness theorem or original Z-in-Q/H10 conclusion by itself.
