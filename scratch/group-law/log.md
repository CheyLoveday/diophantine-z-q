# group-law results log

Base 0caafe66 (wip/group-law). Build tree copied from ~/dzq-wt/gaga-serre (base + Contrib files only);
`lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.MumfordRigidity`
replayed 13698 jobs, frozenTarget standard axioms (VERIFIED, 11-16 12:31).

## Statement
- Field `mumfordGroupLaw : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw`
  (ZInQKernel/Contrib/OneProof/MumfordRigidity.lean L82), in OpenResearchLeaves26 (and every generation 14..26).

## Consumers (VERIFIED, scratch/group-law/ClosureCheck.lean -> closure_check.txt)
- Direct users in frozenTarget's closure: only `LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw`
  (TailZ40), called by HDec.HSyn.x6Rows_of_open14, researchLeaves9_of_open14 (TailZ23) and
  DCY3Used.y3Connected_of_leaves (Contrib, via TailZ34). So the chain needs only
  `QMFamilyGroupLaw` (S proper smooth curve over Q, F a QMFamily with QML3 field fibres).
- rigid-prune's sites N1 (MCRGlue.QuotientP1Coordinate, modelCoordinateResidue_of_quotient') and
  N2 (HDec.ModelGlue.exists_genFib_to_Y, heckeVertWitness_of_curveBijIso) are NOT in the closure any more.
- RigidScan (rigid-prune's scan rerun, scan_*.txt): 34 constants mention R1univProps in their value;
  new since rigid-prune: SGRDirect.elkies_coordinate (univ applied to Elkies' family obtained from an
  Ab clause: fine on abelian schemes) and GapST.cm_pointW (destructures R1fpProps; no univ application in
  its source text). Non-Ab R1fpProps occurs in field types only of old generations (OpenResearchLeaves<=9,
  OpenAddedLeaves<=8, OpenGlue<=7): current bundles carry only Ab forms.

## Lean: ZInQKernel/Contrib/OneProof/GroupLawGlue.lean (VERIFIED compiles, `lake env lean`, 11-16 ~15:30)
- `isAbVarFibre_of_isPullback`, `fibreHyp_of_isPullback`: fibre hypothesis passes to base changes.
- `LocalLaw F e`: open immersion j : T → S, base change P of F along j with GrpObj, identity = base change of e.
- `mulP_pt`, `invP_pt`: on field points the local law is the fibre abelian variety's law
  (via the chain's `isGrpFibre_of_rigidity`).
- `glue_of_rel`: gluing over the cover by preimages of the local opens, compatibility on field points of
  reduced overlaps (`hom_ext_pts`).
- `exists_grpObj_of_localLaws`: [IsReduced F, F⊗F, (F⊗F)⊗F], e section, FibreHyp, local laws through every
  point ⇒ ∃ GrpObj F, η[F].left = e. No sorry.
