import ZInQKernel.OneProof.H.TailZ35
import ZInQKernel.Contrib.OneProof.SGRFold

/-! # OneProof H, sgr-fold: `sixContactMin_of_open30` (hand fold, r6-nf style)

Fields removed (bypassed at their single consumer `HeckeRestNV.HeckeVertWitness`, which TailO's `glue4_of_open6` now
fills by sgr-direct's route NV, `SGRDirect.heckeVertWitness_of_nvSqrtAny`; pruned from every generation by PruneScan):
`shimuraIntegralModelRep` (`OpenAddedLeaves17`) and `quotientP1Coordinate` (`OpenGlue7`).
Fields added (new glue): `nvLocalInertia` (`SGRDirect.NVLocalInertia`, h-b1 §3 Lemma NV step 3).
`HeckeSqrtBranchAny` is proved from `elkiesX6StarPrinted` (`SGRFold.heckeSqrtBranchAny_of_open29`).
docs/research/sgr-fold.md. -/

namespace HDec

namespace HSyn

/-- **The glue still open** (sgr-fold): `NVLocalInertia` only (replaces `OpenGlue7`'s `quotientP1Coordinate`). -/
structure OpenGlue8 : Prop where
  /-- sgr-direct, GLUE (h-b1 §3 Lemma NV step 3; consequence of Abhyankar's lemma and Zariski–Nagata purity): for
  `E/ℚ(X)` finite Galois of degree `< p` with branch data in `S ∪ {∞}`, `S` `p`-integral and distinct mod `p`, and
  `b ∈ S` whose residue fields are unramified at `p`, every vertical inertia element at `p` has a conjugate in an
  inertia group over `X − b`. -/
  nvLocalInertia : SGRDirect.NVLocalInertia

/-- `OpenGlue7` from `OpenGlue8`: `HeckeSqrtBranchAny` by the contribution (Elkies' printed model). -/
theorem openGlue7_of_OpenGlue8 (r : OpenResearchLeaves22) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves17)
    (g : OpenGlue8) : OpenGlue7 where
  nvLocalInertia := g.nvLocalInertia
  heckeSqrtBranchAny := SGRFold.heckeSqrtBranchAny_of_open29 r t l

/-- **G0 with only the open leaves and the open glue** (sgr-fold). -/
theorem sixContactMin_of_open30 (r : OpenResearchLeaves22) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves17)
    (g : OpenGlue8) : ZInQ.SixContactMin :=
  sixContactMin_of_open29 r t l (openGlue7_of_OpenGlue8 r t l g)

end HSyn

end HDec

#print axioms HDec.HSyn.sixContactMin_of_open30
