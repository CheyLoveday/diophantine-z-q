# sgr-direct results log

Base 43513d87 (leaf-fold25). Marks: VERIFIED (read/compiled/computed), STANDARD (published, reference), SPECULATIVE;
theorem numbers from memory UNVERIFIED.

## 1. Consumer map of `shimuraIntegralModelRep` (VERIFIED, read in ZInQKernel/OneProof/H)

- TailZ34 `openAddedLeaves16_of_OpenAddedLeaves17`: `shimuraGoodReductionNoGuard := SGRSplit.shimuraGoodReductionNoGuard_of_printed n.shimuraIntegralModelRep` (only use).
- TailX l.266: `shimuraGoodReduction := CurveSplitGR.shimuraGoodReduction_of_noGuard (R1R2fp_of_rep r.r1r2) _`;
  TailX l.272: `modelCoordinateResidue := MCRGlue.modelCoordinateResidue_of_quotient' g.quotientP1Coordinate`.
- TailN l.255 / TailO l.2910: `heckeVertWitness := heckeVertWitness_of_leaves5 l.shimuraGoodReduction r.r1r2 (torsionStructure_ofK5 t.t5) ..`
  (= ModelGlue.heckeVertWitness_of_curveBijIso: ShimuraGoodReduction, R1R2fp, T5, ModelCoordinateResidue, CurveBijIso).
- TailK l.318: `g.heckeVertWitness` -> `propTSAll_of_pieces3` (TailI l.77) -> `HeckeRestAll.coverModelOfHecke_of_heckeRest`
  -> `CoverModelOfHecke` (NoVerticalRam of the Hecke cover E/Q(X) at every p > 324) -> `PropTSAll` (Beckmann-type
  specialization) -> `FibreUnramified` -> `fibreCoverExists_of_propTSAll'` -> `modularConstituent`.
- So the true need is `HeckeRestNV.HeckeVertWitness` (TailG l.10216): for the Hecke cover E/Q(X) (any E carrying the
  normalization chart of the R1fp/R2fp curve), every p > 324 has an unramified vertical prime; equivalently (Galois,
  compiled `heckeNoVertRam_of_witness`) `HeckeNoVertRam`. A statement about function fields: no abelian scheme.

## 2. Route analysis (summary; details in docs/research/sgr-direct.md)

- The consumer need is NoVerticalRam of the Hecke cover (a function-field statement). Good reduction of the QM surfaces at
  the points used (NOS r7a, Raynaud, SGA 7 IX, Neron, Serre-Tate CM) does not by itself give it: an inertia element at
  the Gauss prime (or at p above a point over t = J(u)) acts through 𝒪-linear automorphisms of the reduced surface,
  and excluding those needs either the integral model (the field), char-p moduli (End of the reduction), or the local
  tame-cover analysis of h-b1 Lemma NV (Abhyankar + Zariski-Nagata purity at (p, X - b)). SPECULATIVE-but-argued.
- Route NV uses existing fields only through hCM (branch fibres are CM points) and Elkies' model (elkiesX6StarPrinted);
  its local algebra uses purity in dim 2 (proved in the chain: PropTSGlue.PurityGlobalDim2 / t-purity3) and T2.
- Simplification found here: only ONE branch point (-16/27, e | 2) and ONE square root (sqrt(-(27X+16)) in Q(X6)) are
  needed for NV step 4 (h-b1 used two branch points and the W-group). VERIFIED (compiled, §3).

## 3. Lean (scratch/sgr-direct/NV.lean) — compiled, standard axioms (VERIFIED, lake env lean, 2026-11-15)

- `SGRDirect.heckeVertWitness_of_nv : R1R2fp → TorsionStructure → QMAutCard → SerreRigidity3 → ALFixedPoints →
  NVLocalInertia → RamifiedSqrtInertia → VertInertiaTrivial → HeckeBranchFibreUnram → HeckeSqrtBranch →
  HDec.HeckeRestNV.HeckeVertWitness`. `#print axioms`: propext, Classical.choice, Quot.sound.
- helpers proved: gal_fix, gal_sq, conj_fix, algebraMap_int_injective, exists_vertPrime, vert_fix,
  vertUnramWitness_of_nv.
