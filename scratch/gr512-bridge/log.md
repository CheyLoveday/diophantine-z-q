# gr512-bridge results log

Base: wip/leaf-fold33b 75d94fe7 (origin/main is an ancestor: checked 11-17 01:56).

## Facts (VERIFIED, read in tree)
* Field `gonzalezRotgerThm512X6 : GRDict.GonzalezRotgerThm512X6` in OpenResearchLeaves (TailZ59..TailZ67);
  consumer: TailZ59 L78 `GRX6AbPrint.gonzalezRotgerX6Ab_of_print n.gonzalezRotgerThm512X6 ...`.
* Mathlib 4.35 has `ClassGroup.equivPic (R) [CommRing R] [IsDomain R] : ClassGroup R ≃* CommRing.Pic R`
  (Mathlib/RingTheory/PicardGroup.lean L876): the ClassGroup ≃ Pic bridge exists for every domain.
* Tau Ceti `Pic O := ClassGroup O.toSubalgebra` (Orders/Picard.lean L35); `finrank_ringClassField :
  finrank K (ringClassField O) = Nat.card (Pic O)` (RingClass/Field.lean).

## Compile outcomes
* 11-17 02:40 `lake build ZInQKernel.Contrib.OneProof.GRDict`: ok (12939 jobs; build-grdict.txt).
* 11-17 02:50 `lake env lean scratch/gr512-bridge/GR512Bridge.lean`: 0 errors; VERIFIED axioms
  `[propext, Classical.choice, Quot.sound]` for `gonzalezRotgerThm512X6_of_rcf`, `picEquiv`, `grD6_ne_one_iff`.
  Contents: `toOrder` (Tau Ceti order of a finite-index subring of 𝓞_k), `picEquiv : Pic O ≃* CommRing.Pic R`
  (Mathlib `ClassGroup.equivPic` + functoriality), `isPrime_span_iff` (pR prime in R ↔ p𝓞_k prime, p ∤ f),
  `grD6` (GR's D(R) at D=6 from R), `grD6_ne_one_iff`, new leaf `GonzalezRotgerThm512X6RCF`
  (ℚ(x) ≃ₐ[ℚ] ringClassField O if D(R) ≠ 1; else ≃ an index-2 ℚ-subfield of H_R), `gonzalezRotgerThm512X6_of_rcf`.
* 11-17 03:10 `scratch/gr512-bridge/N1Maximal.lean`: 0 errors; `N1.O_maximal` VERIFIED standard axioms
  (any subring O' ⊇ LeafQM.O of B with all elements integral over ℤ equals LeafQM.O). Python check (no sympy):
  no x ∈ O^# \ O has nrd(x) ∈ ℤ (2304 dual points scanned); 576-residue congruence checked in Lean by decide.
* 11-17 03:20 contributor file `ZInQKernel/Contrib/OneProof/GR512Bridge.lean` (bridge + N1):
  `lake build +ZInQKernel.Contrib.OneProof.GR512Bridge` ok (12941 jobs).
