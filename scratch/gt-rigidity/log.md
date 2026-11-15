# gt-rigidity results log

Target: `LeafQM.AV.R1UnivRigid.MumfordRigidityCore` (ZInQKernel/OneProof/H/TailZ16.lean L463).

## Setup
- Base a454ad64. Build tree copied from ~/dzq-wt/gt-qm (same base, no ZInQKernel diff). `lake build +Main +Discharges`: only Main rebuilt (96 s). VERIFIED.

## Plan (decided)
- GIT Thm 6.14 (existence of the group law) is not provable from Mathlib 4.35 (needs deformation theory of the group law, Grothendieck existence). Kept as leaf `MumfordGroupLaw` (Core minus clause (a)).
- Clause (a) (GIT Cor. 6.4) to be PROVED in Lean from the printed rigidity lemma (GIT Prop. 6.1, leaf `RigidityLemma`, S connected).
