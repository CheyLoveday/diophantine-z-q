# c8-conrad3 results log

Base: wip/c8-conrad3 = origin/wip/c8-conrad2 5938de123 (origin/main is an ancestor: checked below).
Build: copied c8-conrad2's .lake/build and lean/.lake/build (cp -a); `lake build ZInQKernel.Contrib.OneProof.C8CFT` no-op.

## Targets (verbatim, ZInQKernel/Contrib/OneProof/C8LocAlg.lean, C8CFT.lean)
- InertiaAtPDecomp (C8LocAlg L178), MinkowskiInertiaQ (C8CFT L192), TwistCharHTWt0 (C8CFT L488).

## Plan (tree inputs found, VERIFIED by reading)
- B3b (HDecomp/B3Unram/B3b.lean, namespace GlueB3Unram): places of Qbar vs primes of B = integralClosure ℤ Qbar;
  le_of_center, exists_smul_eq (profinite transitivity), inertia_conj, mem_inertia_of_center,
  inertia_le_of_unramifiedAt, exists_inertia_neg (stabilizerHom_surjective_of_profinite template).
- G15.Ladic (Contrib/G15/LadicBridge.lean): decomp_spec (jQ), decompEquivLj : Gal(L_j/Q_p) ≃* D_P, tauOf_eq_restrictNormal.
- TauCeti: inertiaSubgroup = fixing subgroup of K^ur; mem_inertiaSubgroup_iff_pow_natCard_pow_eq_self.
- HodgeSplit (OneProof/H/TailS, TailT): Ysp, Ysp_linearIndependent, htMult_eq_finrank_Ysp (E Galois),
  htMult_eq_of_lifts, liftGL; tateTwistInvariants_proof, axSenTate_proof (Contrib, proved).
- Chebotarev: ZInQ.Contrib.frobeniusDense; C9Rhof.eq_of_eq_on_arithFrob.
- Mathlib: NumberField.exists_not_isUnramifiedAt_int_of_isGalois; IsAlgClosed ℂ_[p].
Merged origin/main b1615c9b1 (igusa-drop fold: TailZ79, Main, IgusaDrop only).

## MinkowskiInertiaQ — PROVED (VERIFIED, compiled: scratch/c8-conrad3/C8Mink.lean, 10:40)
`MinkDict.minkowskiInertiaQ_proof : MinkowskiInertiaQ`, #print axioms = [propext, Classical.choice, Quot.sound].
Proof: F = normalClosure ℚ(x); conjugates of x are fixed by all inertia groups (inertia_conj), so F is;
if [F:ℚ] > 1, Mathlib exists_not_isUnramifiedAt_int_of_isGalois gives p; P = center of a place over p in 𝓞 F;
every σ ∈ I(P) lifts to an inertia element of a place of ℚ̄ (exists_inertia_lift: profinite transitivity +
stabilizerHom_surjective_of_profinite for G_F on B = algebraic integers, as in B3b.exists_inertia_neg),
which fixes F, so I(P)=1, e(P)=1 (card_inertia_eq_ramificationIdxIn), IsUnramifiedAt (ramificationIdx_eq_one_iff): contradiction.
