# gt-blr results log

## 2026-11-14 21:15 start
- Target: `CToPrinted.BLR_1_2_4` (TailZ19 L63), field `blr_1_2_4` of OpenResearchLeaves (TailZ22 L199, TailZ23 L656). VERIFIED (read).
- Consumers of `blr_1_2_4` (VERIFIED, grep): all go through `CToPrinted.neronLocalizesDVR_of_printed` (TailZ19 L138,
  which uses only `.mp`, at R = 𝓞_L, 𝔭 = center of O, R𝔭 = O). `semistableNeronBaseChange_of_printed_full` (TailZ19 L1650) uses
  `hB` only in `have hL := neronLocalizesDVR_of_printed hB` (L1656). Fold sites: TailZ23 L767 (`ss1_ss3_of14`),
  TailZ23 L794 (`researchLeaves9_of_open14.semistableNeronBaseChange`), TailZ22 L308 (`blr_1_2_4 := r.blr_1_2_4`, field passing).
- Plan (math): .mp holds for ANY commutative ring R, prime 𝔭, fraction field K: given smooth Y/R𝔭,
  (i) uniqueness: Y_K → Y is scheme-theoretically dominant (flat base change of Spec K → Spec R𝔭,
  Mathlib `IsSchemeTheoreticallyDominant.of_isPullback`), Y_K reduced (smooth over a field), hence Y reduced
  (`IsSchemeTheoreticallyDominant.isReduced`), and `ext_of_isDominant_of_isSeparated` with X separated over R;
  (ii) existence on an affine open V: spread V out to a smooth W over Spec R[1/s] (EGA IV 8.8.2(ii), 17.7.8(ii), both
  PROVED in ZInQKernel/Contrib/CloudW01Spread), W is smooth over R (Spec R[1/s] → Spec R open immersion) with
  generic fibre V_K, extend by the Néron property of X over R, glue by (i).
  The risk flagged in gap-triage A10 ("needs a smooth model over all of R") does not arise: W/R[1/s] smooth ⇒ W/R smooth.
