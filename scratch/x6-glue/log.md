# x6-glue results log

Base e38375b3 (wip/w62). One Lean process at a time (`lake env lean`).

## Step 0: state of the two fields at the base (VERIFIED by reading)
- shimura-split: `r1r2fpRep_of_printed_t5 : DeligneComponentsX6 → GeomConnOfAlgClosure → T5 → BabaGranathX6' →
  ReciprocityCanonical → GonzalezRotgerX6 → R1R2fpRep`; `x6ConicModel_of_elkies_t5` from `ElkiesConicX6`, r1r2, T5.
- shimura-glue (already in the base, scratch/shimura-glue/): the X6 double coset and the X6 Deligne leaf are
  done: `pi0_Kfull_eq_one` (`ℚ^×_{>0}\𝔸_f^×/nrd(𝒪̂^×)` is a point; `nrd(𝒪̂^×) = ℤ̂^×` by local Hensel
  representations; `𝔸_f^× = ℚ^×_{>0} ℤ̂^×`), `deligneComponentsX6_of_printed : DeligneComponentsX6Printed →
  DeligneComponentsX6`; `ElkiesConicT` (Elkies' coordinate `t`, points form) with
  `elkiesConicX6_of_t' : ElkiesConicT → ElkiesConicX6`; `BabaGranathRational`, `RayClassCM`.
- Remaining non-printed leaves on the two fields: `ElkiesConicT` (points form of Elkies §3) and `RayClassCM`
  (ray-class consequence of Shimura reciprocity).

## Step 1: re-check of the Deligne X6 computation in this tree
- scratch/x6-glue/DeligneX6.lean = scratch/shimura-glue/Deligne.lean verbatim. `lake env lean`: 0 errors,
  1 min 29 s; all 6 `#print axioms` lines `[propext, Classical.choice, Quot.sound]` (incl.
  `ShimuraGlue.deligneComponentsX6_of_printed`, `printed_of_deligneComponentsX6`). VERIFIED.
