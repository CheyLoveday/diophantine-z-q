# c-to-printed results log

Base e38375b3. Compile harness: `scratch/c-to-printed/run.sh FILE.lean` (lean with LEAN_PATH on ~/ctp-lib, a copy
of the e38375b3 build). One Lean process at a time.

- T0.lean: `import ZInQKernel.OneProof.H.TailZ14; #check @ReductGlue.NeronLocalizesDVR` compiles (VERIFIED, 4.7 s).

## Field statements (VERIFIED, read in ZInQKernel/OneProof/H/)
- shimuraFamily: `QMSplit.Moduli.ShimuraFamily`, TailU.lean:1952.
- semistableNeronBaseChange: `ZInQ.HeightSplit.SemistableNeronBaseChange`, TailY.lean:145.
- faltingsLemma5BC: `ZInQ.HeightSplit.FaltingsLemma5BC`, TailY.lean:609 (base form FaltingsLemma5 :560).
- neronLocalizesDVR: `ReductGlue.NeronLocalizesDVR`, TailZ14.lean:882.
