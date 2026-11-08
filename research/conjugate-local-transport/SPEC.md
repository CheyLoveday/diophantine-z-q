# Actual local conjugation interface: specification

Source revision: `3a7dce59e3d0601a3758cf924810563a6e5f0a98`.
The foundation and frozen 39-target packet are outside this change. This work
targets `PairedBoundaryData.conjugate_local` in the separate arithmetic bridge.
It does not assume that interface as a premise.

## Source lookup and exact remaining gap

V13 `manuscripts/quartic_v13.tex` is unchanged, SHA-256
`9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`.
The coefficient twist and conjugate pullback are at 2898–2967, H12 at
3225–3233, actual transferred classes/local triviality at 3405–3417,
the tame model at 3431–3456, actual paired functional at 3842–3908,
and finite/tame conjugation at 5193–5225. Earlier investigation is retained
in `research/arithmetic-boundary-cup/`; its generic crossed-cocycle lemma
assumes the transporter's scalar action and is stated over a field.

The new target derives that scalar action from the coefficient twist and H12,
then derives the finite/tame coordinates over an arbitrary commutative ring.
This includes the finite Artin coefficient rings at two. Nonquadratic global
characters, nonprimitive local vectors and zero classes are allowed.

## Formal statement

Let R be a commutative ring, V an R-module, Γ a group and H a normal subgroup.
Let T : Γ → End_R(V) be a representation and α : H → R× a character.
Define the actual twisted representation σ(h)=α(h)·T(h). Let p:H→V satisfy
the crossed-cocycle equation for σ.

Choose τ,φ∈Γ and d∈H with φ=dτ, τ²=1 and T(φ)=T(τ). Choose F,I∈H and
an integer ℓ≥0 such that F=φ², φIφ⁻¹=I^ℓ, α(F)=α(I)=1, and T(I)=1.
All group equalities involving H are interpreted after its inclusion in Γ.
Define the raw conjugate cochain cτ(p)(h)=p(τhτ⁻¹), with no extra coefficient J.

With the actual unit u=α(d)⁻¹, prove

    (cτ(p)(F), cτ(p)(I)) = (u·p(F), u·((ℓ:R)·p(I))).

If (ℓ:R)=-1, deduce the shared-factor identity

    loc(cτ(p)) = (u·f(p), -u·s(p)).

The same unit must work for every cocycle p on these fixed data, hence for the
actual old and derivative classes. Do not independently choose or rescale u.
Prove invariance of these local coordinates under adding a coboundary; the
statement must concern the actual cohomology classes, not preferred cocycles.
Construct the coordinate and conjugation maps on Mathlib's
`groupCohomology.H1`, with original and conjugate coefficient systems kept
distinct. The formal theorem is at finite precision; do not instantiate
`(ell:R)=-1` for a fixed natural prime in characteristic zero.

## Actual arithmetic application to be checked

Use Γ=G_Q and H=G_K through a suitable common finite quotient, T the retained
Tate representation, α the actual finite coefficient character and p the
actual H20–H22 global cocycle. The local rational Frobenius φ and complex
conjugation τ have the same nontrivial K/Q coset, so d=φτ⁻¹ lies in H.
H12 makes T(φ)=T(τ) and (ℓ:R)=-1 at retained precision. Triviality of α on the
derivative decomposition group gives α(F)=α(I)=1. Good reduction at the odd
prime gives T(I)=1.

The tame relation must not be asserted for arbitrary lifts modulo wild inertia.
Justify a common finite quotient on which it is exact: local action on the
finite 2-primary coefficient module is trivial, so local cocycles are additive
homomorphisms and vanish on pro-ℓ wild inertia. Use a common quotient for both
actual cocycles, their conjugates, the character and Tate action. Record any
remaining source-occurrence or continuity premise explicitly.

Raw conjugate pullback carries no second J. The coefficient identification
with the dual already contains J in e(x,Jy). Forward rational-Frobenius
conjugation gives ℓ; an inverse convention gives ℓ⁻¹. At retained precision
both equal -1. The coefficient ring is fixed throughout.

## Hinge lemmas and acceptance criteria

1. Construct σ and prove the general crossed-cocycle conjugation/power identities
   over R (no field assumption).
2. Derive T(d)=1, σ(d)=α(d)·id and σ(F)=σ(I)=id from the stated data.
3. Derive both coordinates with the same explicitly defined integral unit.
4. Prove representative independence and bind the finite arithmetic application
   to actual source premises, including the tame-quotient issue.
5. Obtain non-author review of the new derivation/application and native Lean
   compilation/axiom evidence for the new module only. No new paranoid campaign.

6. Check the actual retained-inner-limit route: the source uses a fixed
   ultrafilter, not compatible moving Galois characters. Adjoin the explicit
   unit and its inverse to the same finite tuple and prove that both survive,
   without changing its pre-existing entries. This is a human source-application
   proof relative to `ex:limits-inner-limit`, not a new Lean formalization of
   that lemma or of continuous Galois cohomology.

Do not claim the whole arithmetic switch repaired. Global duality/boundary-cup
adjunction, common-strict model realization, determinant functors and
exceptional-localization occurrence remain separate obligations. The finite
identities may be carried through retained maps only with their source
construction cited; this work does not rebuild the whole limit construction.
