# gr56-prove: González–Rotger Prop. 5.6 on `X₆` from Eichler's count and the lattice model

Task gr56-prove (2026-11-15). Base: fork main 43513d87 (leaf-fold25). Target: the research field
`gonzalezRotgerProp56X6 : GRCountX6.GonzalezRotgerProp56X6` of `HDec.HSyn.OpenResearchLeaves22` (TailZ35 L69).
Contributor file: `ZInQKernel/Contrib/OneProof/GR56Lattice.lean` (namespace `GR56`, plus a rerouted copy of the
chain's consumer in `HDec.FS5NoCM`; imports `ZInQKernel.Contrib.OneProof.QMLattice` and
`ZInQKernel.Contrib.OneProof.GRCountX6`; no `sorry`). Scratch: `scratch/gr56-prove/`.
Marks: VERIFIED (compiled or read), STANDARD, SPECULATIVE, UNVERIFIED (theorem numbers from memory).

(Draft; the final version follows.)

## 1. Result

The count is **not proved outright** (it needs Eichler's optimal-embedding theorem for every order of conductor prime
to 6, and the existence of CM points; neither is in Mathlib or the kernel). What is proved (VERIFIED, standard axioms):

* the **CM-point map** `CM(R) → Emb(R, 𝒪)/𝒪^×` (classes of QM pairs over `ℚ̄` with `End_𝒪 ≅ R` to
  `𝒪^×`-classes of optimal embeddings) is **injective** from the textbook fields `uniformizationLeafAll`,
  `gagaMorphism`, `mumfordTorsionAlgClosed` alone (`GR56.cmMap_injective`), and **bijective** with two existence
  statements (`GR56.cmMap_surjective`, `GR56.cmPointsOptEmb6_of`);
* hence the field from Eichler's count `GRCountX6.EichlerOptEmbCount6` (pure quaternion-order algebra) and the two
  existence leaves (`GR56.gonzalezRotgerProp56X6_of_leaves`; autofold spec `scratch/gr56-prove/autofold.json`);
* and, from Eichler's count and the textbook fields only, the upper bound `GR56.R5fpCountLe`, which is all the
  chain uses (`GR56.r5fpCountLe_of_eichler`), with the chain's one consumer rerouted to it
  (`HDec.FS5NoCM.fibreComTrivialFull_of_leaves''_le`); manual fold in §4.
