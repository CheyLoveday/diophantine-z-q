# shimura-cft results log

Build: `.lake/build` and `lean/.lake/build` are symlink trees (`cp -rs`) of ~/dzq-check2 (e38375b3) builds;
check with `scratch/shimura-cft/run.sh <file>` (= `lake env lean`).

## Step 1 (11-14 17:23): verbatim copies compile
- `ShimuraCFT.lean` Part A = R1UnivLeaves.lean lines 10-564 (R1UnivRigid core) + c-to-printed Shimura.lean
  (minus import) + `ShimuraFamilyAb` def. Imports TailZ12 + R1UnivLeaves' imports + Tau Ceti
  `Global.Reciprocity`, `Adeles.FiniteBaseChange`. COMPILED 13 s, 8.6 GB, 3 axiom lines standard. VERIFIED.
