# gr512-bridge results log

Base: wip/leaf-fold33b 75d94fe7 (origin/main is an ancestor: checked 11-17 01:56).

## Facts (VERIFIED, read in tree)
* Field `gonzalezRotgerThm512X6 : GRDict.GonzalezRotgerThm512X6` in OpenResearchLeaves (TailZ59..TailZ67);
  consumer: TailZ59 L78 `GRX6AbPrint.gonzalezRotgerX6Ab_of_print n.gonzalezRotgerThm512X6 ...`.
* Mathlib 4.35 has `ClassGroup.equivPic (R) [CommRing R] [IsDomain R] : ClassGroup R ≃* CommRing.Pic R`
  (Mathlib/RingTheory/PicardGroup.lean L876): the ClassGroup ≃ Pic bridge exists for every domain.
* Tau Ceti `Pic O := ClassGroup O.toSubalgebra` (Orders/Picard.lean L35); `finrank_ringClassField :
  finrank K (ringClassField O) = Nat.card (Pic O)` (RingClass/Field.lean).
