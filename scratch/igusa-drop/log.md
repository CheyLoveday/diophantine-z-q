# igusa-drop results log

Base wip/leaf-fold33b 97247ce1 (top `sixContactMin_of_open71`, TailZ78). Build tree copied (reflink) from
~/dzq-wt/leaf-fold33b (same HEAD, byte-identical Main.lean).

1. Readers of `igusaGL2DSGalSome` on the live chain (VERIFIED, grep of ZInQKernel/OneProof/H/TailZ7[5-8].lean):
   TailZ78 `openResearchLeaves51_of_OpenResearchLeaves52` passes it through; TailZ77's composite
   `openResearchLeaves36EBCF_of_OpenResearchLeaves51` reads it once, in
   `r16CoreY := AfTateLam.r16CoreY_of_ds965 … (X1Igusa.igusaGL2DS_of_igusaGL2DSGalSome n.igusaGL2DSGalSome) …`;
   the result bundle `OpenResearchLeaves36EBCF` has no Igusa field. `r16CoreY_of_ds965` passes hI to
   `r16CoreY_of_printed`, which uses it only as `X1Igusa.x1PointsConjugate_of_igusaGL2DS hI` (AfTateLambda.lean:868).
2. New module ZInQKernel/Contrib/OneProof/IgusaDrop.lean (imports R16CoreYDS965 (→ AfTateLambda), RLeaf.T40,
   OneProof.ModularEquationGeneric):
   * `AfTateLam.x1PointsConjugate_proof : R16IsJ1Dict.X1PointsConjugate :=
      X1Igusa.x1PointsConjugate_iff_igusaTransitive.mpr (ZInQ.RLeaf.igusaTransitive_iff_x0Transitive.mpr FltCqj2.x0Transitive_proof)`
   * `AfTateLam.r16CoreY_of_printed_x0 (h1 : HeckeJ1DS) (h2 : AfShimura) (h3 : AfTateDSLambda) (hM : AvSplit.MumfordTorsionAlgClosed) : R16Split.R16CoreY`
     (proof of r16CoreY_of_printed verbatim, the one use of hI replaced)
   * `AfTateLam.r16CoreY_of_ds965_x0 (h1) (h2) (h3 : AfCharpolyDS965) (hM) : R16Split.R16CoreY`
   `lake build ZInQKernel.Contrib.OneProof.IgusaDrop`: Build completed successfully (12092 jobs); all three
   `#print axioms`: [propext, Classical.choice, Quot.sound] (VERIFIED). Import acyclic (new leaf module; nothing imports it).
