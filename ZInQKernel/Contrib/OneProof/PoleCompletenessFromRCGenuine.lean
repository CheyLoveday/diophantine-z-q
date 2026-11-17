import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRC
import ZInQKernel.Contrib.OneProof.PoleS12.Realization
import ZInQKernel.Contrib.OneProof.PoleS12.Leaves
import ZInQKernel.Contrib.OneProof.PoleS12.CountS12

/-!
# Theorem 5.2 from the printed Theorem 5.3 (fork issue #83, round 2)

Task pc-s12. Report: `docs/research/pc-s12.md`.

`poleCompleteness_of_restrictedConverseGenuine` proves `Manuscript.PoleCompleteness` (Theorem 5.2)
from `SelmerTwoPower.RestrictedConverseGenuine` (Theorem 5.3 as printed: the Selmer condition is
`corank_{ℤ₂} Sel_{2^∞}(E_ℓ/ℚ) = 1` over Tau Ceti's Galois cohomology), with

* `MatrixRealization` proved (`PoleS12.matrixRealization`, from S12's
  `par:simultaneous-matrices`, ELLIOT (supplement));
* Lemma 5.4 as a printed leaf over the genuine `Sel₂` and `Sel_{2^∞}` (`PoleS12.Lemma54`) and the
  Kummer identification `#Sel₂(E_ℓ/ℚ) = #SelM ℓ` (`PoleS12.KummerSelmerM`, textbook GLUE);
* Lemma 5.5 from the printed leaves `PoleS12.BCDTThmA` and `PoleS12.KolyvaginThm1` (with finite
  `Ш`), and Mordell's theorem;
* the local images of the Kummer map of `E_ℓ` (round 1's GLUE Props; see `PoleS12.LocalS12` for
  their status).

The abstract-`P` development (`poleCompleteness_of_restrictedConverse_final`) is kept; this file
instantiates `P := SelmerTwoPower.SelmerCorankOne`.
-/

namespace ZInQ.Manuscript.PoleS12

open ZInQ.Manuscript.PoleRC ZInQ.Manuscript.SelmerTwoPower

/-- **Theorem 5.2 from the printed Theorem 5.3, with round 1's local-image Props** (kept for
comparison; superseded by `poleCompleteness_of_restrictedConverseGenuine`). -/
theorem poleCompleteness_of_restrictedConverseGenuine_local (hRC : RestrictedConverseGenuine)
    (h54 : Lemma54) (hKum : KummerSelmerM) (hB : BCDTThmA) (hK : KolyvaginThm1)
    (hMW : MordellWeil) (hTwo : LocalTwo) (hThree : LocalThree) (hBad : LocalBad)
    (hGood : LocalGood) : Manuscript.PoleCompleteness :=
  poleCompleteness_of_restrictedConverse_final SelmerCorankOne hRC
    (lemma54At_of_printed h54 hKum) (kolyvaginRankOne_of_printed hB hK) hMW matrixRealization
    hTwo hThree hBad hGood

/-- **Theorem 5.2 from the printed Theorem 5.3** (`diophantine_zq.tex` L1019–1121): the final
form. Proved in Lean: the bookkeeping, the rescaling, the complete 2-descent, `MatrixRealization`
(S12 `par:simultaneous-matrices`), every necessary local condition and the local solubility of
the eight classes at `2`, `3`, `ℝ` and the primes of `ℓ` (S12 `par:descent`). Remaining:
Theorem 5.3 (`RestrictedConverseGenuine`), the printed leaves `Lemma54`, `BCDTThmA`,
`KolyvaginThm1`, `MordellWeil`, and the GLUE statements `KummerSelmerM` (the Kummer
identification `#Sel₂(E_ℓ/ℚ) = #SelM ℓ`) and `LocalGoodUnram` (unramified classes are local at
primes of good reduction). -/
theorem poleCompleteness_of_restrictedConverseGenuine (hRC : RestrictedConverseGenuine)
    (h54 : Lemma54) (hKum : KummerSelmerM) (hB : BCDTThmA) (hK : KolyvaginThm1)
    (hMW : MordellWeil) (hG : LocalGoodUnram) : Manuscript.PoleCompleteness :=
  poleCompleteness_of_restrictedConverse SelmerCorankOne hRC (lemma54At_of_printed h54 hKum)
    (kolyvaginRankOne_of_printed hB hK) hMW descentGlueM matrixRealization (dimThreeCount_S12 hG)

end ZInQ.Manuscript.PoleS12
