import ZInQKernel.Contrib.OneProof.JavanpeykarRebase
import ZInQKernel.Contrib.OneProof.MumfordTorsionAlgClosed
import ZInQKernel.Contrib.OneProof.GeomConnOfRationalPoint

/-! # javanpeykar-direct, supporting: well-posedness of `IsStableHeightBar` (not used by the fold)

`IsStableHeightBar` of `JavanpeykarDirect.lean` §1 is repeated verbatim (scratch files cannot import each other).

* `isStableHeightBar_of_iso`: `IsStableHeightBar` is invariant under isomorphism of `W`.
* `isPrintedStableHeight_unique`: for a fixed model `V` over a number field, height-fix's printed stable height
  is single-valued, given the leaves N1 (`NeronModelExists`) and SS2 (`SemistableNeronBaseChange`) (printed ⇒
  kernel height by T35 and Stacks 04KV, both proved; the kernel's height is single-valued by
  `ZInQ.HeightSplit.isStableFaltingsHeight_unique`). Independence of the model `V` is not proved here. -/

noncomputable section

namespace JavanpeykarDirectWP

open CategoryTheory AlgebraicGeometry Limits
open JavanpeykarDict

/-- Verbatim copy of `JavanpeykarDirect.IsStableHeightBar`. -/
def IsStableHeightBar {Kbar : Type} [Field Kbar] (W : AbelianVariety Kbar) (x : ℝ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra L Kbar) (V : AbelianVariety L),
    Nonempty ((AbelianVariety.baseChange L Kbar).obj V ≅ W) ∧
      ZInQ.HeightFix.IsPrintedStableHeight (ofVendored V) x

/-- `IsStableHeightBar` is invariant under isomorphism of the abelian variety over `ℚ̄`. -/
theorem isStableHeightBar_of_iso {Kbar : Type} [Field Kbar] {W W' : AbelianVariety Kbar} (e : W ≅ W')
    {x : ℝ} (h : IsStableHeightBar W x) : IsStableHeightBar W' x := by
  obtain ⟨L, i1, i2, i3, V, ⟨f⟩, hx⟩ := h
  exact ⟨L, i1, i2, i3, V, ⟨f ≪≫ e⟩, hx⟩

/-- **The printed stable height of a fixed model is single-valued**, given N1 and SS2 (T35 from
`uniformizationLeafAll_proof` and `mumfordTorsionAlgClosed_proof`; Stacks 04KV from
`geomConnOfRationalPoint_proof`). -/
theorem isPrintedStableHeight_unique (hN1 : ZInQ.H5Neron.NeronModelExists)
    (hSS2 : ZInQ.HeightSplit.SemistableNeronBaseChange) {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} {x y : ℝ} (hx : ZInQ.HeightFix.IsPrintedStableHeight A x)
    (hy : ZInQ.HeightFix.IsPrintedStableHeight A y) : x = y := by
  have hT35 := AvSplit.Final.h38 uniformizationLeafAll_proof
    ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  exact ZInQ.HeightSplit.isStableFaltingsHeight_unique hN1 hSS2
    (ZInQ.HeightFix.isStableFaltingsHeight_of_printed hT35 geomConnOfRationalPoint_proof hx)
    (ZInQ.HeightFix.isStableFaltingsHeight_of_printed hT35 geomConnOfRationalPoint_proof hy)

/-- Hence, for a fixed model `V` of `W`, `IsStableHeightBar` read through `V` is single-valued. -/
theorem isStableHeightBar_unique_of_model (hN1 : ZInQ.H5Neron.NeronModelExists)
    (hSS2 : ZInQ.HeightSplit.SemistableNeronBaseChange) {L : Type} [Field L] [NumberField L]
    (V : AbelianVariety L) {x y : ℝ} (hx : ZInQ.HeightFix.IsPrintedStableHeight (ofVendored V) x)
    (hy : ZInQ.HeightFix.IsPrintedStableHeight (ofVendored V) y) : x = y :=
  isPrintedStableHeight_unique hN1 hSS2 hx hy

end JavanpeykarDirectWP

end

#print axioms JavanpeykarDirectWP.isStableHeightBar_of_iso
#print axioms JavanpeykarDirectWP.isPrintedStableHeight_unique
