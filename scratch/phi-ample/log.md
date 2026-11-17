# phi-ample results log

Base c1e4ed1b8 (wip/phi-ample). Build tree reflink-copied from ~/dzq-wt/sga3-nbhd (no ZInQKernel diff vs base).

## Route chosen: (a), K(L) finite, proved over any field K inside PhiAmpleIsogeny's context

PhiAmpleIsogeny quantifies over rep, B, j (IsPicZero), L ample, lam with lam ≫ j = phiL rep L, so the
representation of Pic is available without a new hypothesis. Plan (Mumford's argument, irreducible-subset form,
no translation by non-rational points needed):
1. Ker := pullback lam.left η_B.left (closed subscheme of A).
2. Z ⊆ Ker closed irreducible, Zs := reduced induced subscheme (integral; vendored isIntegral_subscheme_vanishingIdeal).
3. i : Zs → A, i ≫ lam = const η_B ⇒ i ≫ phiL = const η_P ⇒ (comp_classify, homEquiv_symm_one, Θ_inj with
   pushforwardUnitUniversal) (1×i)^*Λ(L) = 1 in Pic(A ×_K Zs).
4. Pull back along z ↦ (−z, z): i^*(L ⊗ (−1)^*L) = 1 in Pic(Zs).
5. i^*L and i^*(−1)^*L ample (isAmple_pullback); sections s, t nonvanishing at x; s^m ⊗ t^n ↦ global function f
   with x ∈ D(f); Γ(Zs,O) is a field (Mathlib isField_of_universallyClosed) ⇒ f unit ⇒ Z(s) = ∅ ⇒ Zs affine ⇒
   Zs ≅ Spec(field) ⇒ Z is one point.
6. Ker noetherian, irreducible components points ⇒ Ker finite ⇒ finitely many K̄-points in ker lam ⇒
   finiteOfFiniteKerPts.
Target theorem: PhiAmpleIsogeny from MumfordPhiSurjectiveAC alone (removes mumfordKLFiniteSectionAC).

## Compile log
