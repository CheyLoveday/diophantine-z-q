import ZInQKernel.Contrib.OneProof.CMBranch2
import ZInQKernel.Contrib.OneProof.CoxProperLattice

/-! # cox-lattice: cm-branch2's CM-branch hand-fold without the leaf `CoxProperLattice` (dry run)

`CMBranch.CoxProperLattice` is proved (`HDec.CMBranch.coxProperLattice_proof`), so the CM-branch inputs shrink from
cm-branch2's `CMInputs2` (6 statements) to `CMInputs3` (5: the glue `CMFibreSplit` and the leaves `FowlerProp27`,
`CMjDegree`, `CMPotentialGood`, `CMHeight62`). -/

namespace HDec
namespace CMBranch

/-- The CM-branch inputs after cox-lattice: `CMInputs2` without `coxProperLattice` (proved). -/
structure CMInputs3 : Prop where
  cmFibreSplit : CMFibreSplit
  fowlerProp27 : FowlerProp27
  cmjDegree : CMjDegree
  cmPotentialGood : CMPotentialGood
  cmHeight62 : CMHeight62

/-- `CMInputs3` gives `CMInputs2`, the sixth field by `coxProperLattice_proof`. -/
theorem CMInputs3.toCMInputs2 (c : CMInputs3) : CMInputs2 :=
  ⟨c.cmFibreSplit, c.fowlerProp27, c.cmjDegree, c.cmPotentialGood, c.cmHeight62, coxProperLattice_proof⟩

end CMBranch

namespace HSyn

/-- **Theorem 1.1's height hypothesis from the open statements and the five remaining CM-branch inputs**
(cox-lattice fold dry run: cm-branch2's `sixContactMin_of_open72_cmbranch2` with `CoxProperLattice` proved). -/
theorem sixContactMin_of_open72_cmbranch3 (r : OpenResearchLeaves53) (t : OpenTextbookLeaves18)
    (l : OpenAddedLeaves27) (c : CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  sixContactMin_of_open72_cmbranch2 r t l c.toCMInputs2

end HSyn
end HDec
