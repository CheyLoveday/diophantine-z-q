# c-to-printed results log

Base e38375b3. Compile harness: `scratch/c-to-printed/run.sh FILE.lean` (lean with LEAN_PATH on ~/ctp-lib, a copy
of the e38375b3 build). One Lean process at a time.

- T0.lean: `import ZInQKernel.OneProof.H.TailZ14; #check @ReductGlue.NeronLocalizesDVR` compiles (VERIFIED, 4.7 s).

## Field statements (VERIFIED, read in ZInQKernel/OneProof/H/)
- shimuraFamily: `QMSplit.Moduli.ShimuraFamily`, TailU.lean:1952.
- semistableNeronBaseChange: `ZInQ.HeightSplit.SemistableNeronBaseChange`, TailY.lean:145.
- faltingsLemma5BC: `ZInQ.HeightSplit.FaltingsLemma5BC`, TailY.lean:609 (base form FaltingsLemma5 :560).
- neronLocalizesDVR: `ReductGlue.NeronLocalizesDVR`, TailZ14.lean:882.

## Part N: neronLocalizesDVR (Neron.lean)
- Leaf `CToPrinted.BLR_1_2_4`: BLR 1.2 Prop. 4 (UNVERIFIED number/wording) over any Dedekind domain R with
  fraction field K, X smooth separated quasi-compact over Spec R: `IsNeronModelOver R K X ↔ ∀ maximal 𝔭, ∀ R𝔭 with
  IsLocalization.AtPrime R𝔭 𝔭 (and R → R𝔭 → K), IsNeronModelOver R𝔭 K (X ×_R R𝔭)`.
- Definition `IsNeronModelOver R K X` (BLR 1.2 Def. 1): smooth, separated, locally finite type, quasi-compact, and
  `Hom_R(Y,X) → Hom_K(Y_K,X_K)` bijective for every smooth R-scheme Y. Mathlib objects only.
- Glue proved: `isLocalization_center` (a DVR O of a number field L is `IsLocalization.AtPrime O (center O)` for
  `toOL`), `isNeronModelOver_of` (kernel `GroupModel.IsNeronModel` ⇒ printed property of `𝒩.G`).
- `neronLocalizesDVR_of_printed : BLR_1_2_4 → ReductGlue.NeronLocalizesDVR` COMPILES, axioms
  [propext, Classical.choice, Quot.sound] (VERIFIED, ~5 s).
