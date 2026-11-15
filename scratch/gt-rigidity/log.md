# gt-rigidity results log

Target: `LeafQM.AV.R1UnivRigid.MumfordRigidityCore` (ZInQKernel/OneProof/H/TailZ16.lean L463).

## Setup
- Base a454ad64. Build tree copied from ~/dzq-wt/gt-qm (same base, no ZInQKernel diff). `lake build +Main +Discharges`: only Main rebuilt (96 s). VERIFIED.

## Plan (decided)
- GIT Thm 6.14 (existence of the group law) is not provable from Mathlib 4.35 (needs deformation theory of the group law, Grothendieck existence). Kept as leaf `MumfordGroupLaw` (Core minus clause (a)).
- Clause (a) (GIT Cor. 6.4) to be PROVED in Lean from the printed rigidity lemma (GIT Prop. 6.1, leaf `RigidityLemma`, S connected).

## Step 1 (11-14 23:20): reduction compiled — VERIFIED
- scratch/gt-rigidity/MR.lean (imports TailZ16): `mumfordRigidityCore_of_printed : MumfordGroupLaw → RigidityLemma → MumfordRigidityCore`; `#print axioms` = [propext, Classical.choice, Quot.sound].
- Glue proved on the way: noetherian space ⇒ connected components open; locally noetherian scheme ⇒ connected components open; `eq_of_rigidity` (rigidity on each connected component, via restriction to the open component and `Scheme.hom_ext_of_forall`); `isPullback_jr` (x ↦ (x,1) is the base change of η along snd); `fibre_value`; `defect_eq_one`; `isMonHom_of_rigidity` (GIT Cor. 6.4 for endomorphisms of a group object proper smooth geometrically connected over a locally noetherian base).

## Step 2 (11-14 23:40): contribution file — VERIFIED
- ZInQKernel/Contrib/OneProof/MumfordRigidity.lean (imports TailZ16 only). `lake build +Main +Discharges +MumfordRigidity`: success.
- #discharges (scratch/gt-rigidity/Discharges.lean; output in discharges-output.txt):
  DISCHARGES [OpenResearchLeaves16.mumfordRigidityCore] by ZInQ.Contrib.MumfordRigidity.mumfordRigidityCore_of_printed
    still assumes: [MumfordGroupLaw, RigidityLemma]; axioms: [propext, Classical.choice, Quot.sound]
  (67 open hypotheses, 514 theorems checked, 1 discharge one)
- `mumfordGroupLaw_of_core : MumfordRigidityCore → MumfordGroupLaw` compiled (the existence leaf is strictly weaker).
