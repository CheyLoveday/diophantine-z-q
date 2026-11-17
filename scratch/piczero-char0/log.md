# piczero-char0 log

## Setup
- Base wip/leaf-fold33b 0e3c31258; origin/main (c1e4ed1b8) already an ancestor (merge not needed). VERIFIED.
- Build: reflink copy of ~/dzq-wt/leaf-fold33b/.lake/build and lean/.lake/build (same commit). VERIFIED.

## Step 1: taint of the bundle field `picZeroAbVar` (scratch/piczero-char0/Taint.lean -> taint_out.txt), VERIFIED
- Closure of `ZInQ.OneProof.frozenTarget`: 270,264 constants. Carriers: OpenAddedLeaves13..20.
- 45 constants depend on a `*.picZeroAbVar` projection. Non-forwarding readers (the field used, not copied):
  * `HDec.HSyn.addedLeaves12_of_open13` (TailZ24): `t09SymmIsogenyExists := T09Pic.t09SymmIsogenyExists_of_four l.picRepresentableAbVar l.picZeroAbVar ...`
  * `HDec.HSyn.openAddedLeaves19_of_OpenAddedLeaves20` (TailZ47): `mumfordKLFiniteSectionAC := PhiAmple.mumfordKLFiniteSectionAC_of_open n.picRepresentableAbVar n.picZeroAbVar`
  * `HDec.HSyn.openTextbookLeaves13_of_OpenTextbookLeaves14_hf` (Contrib HomFreeFiniteAlgClosedReroute, the copy of TailZ46's map
    in use): `poincareComplement := PoincareComplement.poincareComplement_of_open l.picRepresentableAbVar l.picZeroAbVar (...)`
  * the rest are forwarding maps (`picZeroAbVar := n.picZeroAbVar`) and the top wrappers.
