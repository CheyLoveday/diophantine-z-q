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

## InertiaAtPDecomp — PROVED (VERIFIED, compiled: scratch/c8-conrad3/C8Dec.lean, ~11:15)
`DecDict.inertiaAtPDecomp_proof : InertiaAtPDecomp`, #print axioms = [propext, Classical.choice, Quot.sound].
Helper: ZInQKernel/Contrib/OneProof/C8Ladic.lean = verbatim copy of G15 LadicBridge §1, §2, jField, §5, decomp_spec
(namespace HDec.G0Galois.C8Conrad.Ladic). Reason: importing ZInQKernel.Contrib.G15.LadicBridge next to C8CFT fails:
"import ZInQKernel.Contrib.Different.Local failed, environment already contains 'PkgI6.TraceContainsRamificationIdx'
from ZInQKernel.HDecomp.Textbook.Different" (VERIFIED).
Proof: v₀ = {‖jQ ·‖ ≤ 1}; v = g•v₀ (B3b center lemma + profinite transitivity); τ' = g⁻¹τg ∈ I_{v₀};
finite Galois K: τ'|_K stabilizes primeOf(jQ|K), lifts to G_{Q_p} (G15 exists_lift = Tau Ceti
exists_algEquiv_apply_eq_of_norm_apply_eq); compactness of G_{Q_p} (IsCompact.inter_iInter_nonempty) gives σ with
decomp σ = τ'; σ ∈ I_{Q_p} via Tau Ceti mem_inertiaSubgroup_iff_pow_natCard_pow_eq_self + Padic.natCard_residueField:
roots of X^{p^f}-X are jQ(ζ), ζ^{p^f-1}=1, fixed by τ' (inertia_fix_root, core of B3b cycUnram).

## TwistCharHTWt0 — PROVED (VERIFIED, compiled: scratch/c8-conrad3/C8Twist.lean, ~12:30)
`TwistHT.twistCharHTWt0_proof : TwistCharHTWt0`, #print axioms = [propext, Classical.choice, Quot.sound].
No new cited input. Inputs: R14 (hyp EigenformRepExists), R13 (hyp EigenformHT), Chebotarev (ZInQ.Contrib.frobeniusDense,
proved), Tate's two theorems (tateTwistInvariants_proof, axSenTate_proof, proved), hodge-split's Ysp machinery (proved).
Steps: (1) tr r = ψ tr ρ_g on G_ℚ (eq_of_eq_on_arithFrob); det r = ψ² det ρ_g (2 det M = tr² M − tr M²);
(2) values of ψ|G_Q5 in a finite Galois E (open G_M where tr ρ_g ≠ 0 + coset representatives; no Baire);
(3) Y_0, Y_1 vectors of r and ρ_g over G_E: d = det(y0,y1) ≠ 0 (Tate–Sen independence), d·det ρ(σ) = χ(σ)σ(d);
y = d_r/d_g has σ(y) = ψ(σ)² y; (4) c = √y in ℂ_p (IsAlgClosed): σ(c) = ±ψ(σ)c; sign continuous (orbit map
continuity proved), so σ(c) = ψ(σ)c on G_{E'}; (5) htMult_eq_finrank_Ysp + Tate–Sen: weights of ψ_{E'} are {0}.
No semisimplicity of r needed (determinant route).
