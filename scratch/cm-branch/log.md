# cm-branch results log

- 2026-11-17 06:10 start; base d67ea55f6 (origin/main ancestor). Top: HDec.HSyn.sixContactMin_of_open67 (TailZ74), OpenResearchLeaves48 has x6CoarseModuliIdeal, elkiesX6StarEveryIdeal, gonzalezRotgerThm512X6RCF (VERIFIED grep).
- Trace (VERIFIED by grep/reading, TailZ74/EichlerBoundCopy/PicZeroCharZeroCopy):
  * gonzalezRotgerThm512X6RCF -> gonzalezRotgerThm512X6 -> GRX6AbPrint.gonzalezRotgerX6Ab_of_print (with x6CoarseModuli, shimuraMainThmIDeligneY3AbU) -> gonzalezRotgerX6Ab:
    (a) x6Rows_of_open14_hf_gm_pz_eb (`gonzalezRotger :=`) -> LeafAdopt.R1R2fpRepW (whole moduli row: X6Props AND R5ptProps) and X6ConicModel;
    (b) gonzalezRotgerCountX6Ab (TailZ27 L105).
  * x6CoarseModuliIdeal -> x6CoarseModuli -> gonzalezRotgerX6Ab and GRX6AbPrint.x6ModuliWitness_of_coarse -> elkiesX6StarFunctionField.
  * elkiesX6StarEveryIdeal -> elkiesX6StarEvery -> elkiesX6StarFunctionField -> elkiesX6StarPrinted (TailZ36) and babaGranathRationalAb (TailZ37) -> R2X6PropsIff / pi6 (the coordinate of the family).
  * NoCM conclusion = G0FibreSimple.FibreComTrivial (FS5), built in gluePieces_of_open4_hf_pz_eb (EichlerBoundCopy ~L2660) from R1R2fp (R5ptProps), r5count, x6KummerFibre (x6ConicModel), cmOptimalEmbedding; consumed by (i) fibreSimple (G5-G6 -> Poincare, glueOutputs Or.inl path) and (ii) KernelFieldExists (kernelFieldExists_of_split_hf'' -> modularConstituent).
  * Consumer interface: GlueAssembly.GlueOutputs already has the disjunct `NonCMOutput ... ∨ CMOutput hA` (HDecomp/Assembly.lean L533-555) and the CM arithmetic hA <= C_cm is proved there (cm_numerics, cm_branch_nat). The chain always takes Or.inl.
  * FINDING: x6CoarseModuliIdeal and elkiesX6StarEveryIdeal also feed the moduli row R1R2fpRepW (X6Props, R2X6PropsIff, pi6) used by every step, so re-routing the CM branch alone cannot take them off the route; only their NoCM uses (R5ptProps, r5count, X6ConicModel/x6KummerFibre) go. gonzalezRotgerThm512X6RCF feeds only R5ptProps + the count (NoCM uses) -- to verify with a clause-use scan.
- Upstream audit docs/reviews/height-replacement/height/AUDIT.md read Fowler Prop 2.7 (printed pp. 615-616) and cmheight (6.2) (pp. 13-14) from the publisher/author prints (AUDIT-READ). Network blocked here (WebFetch to arxiv refused), so no own reading.
