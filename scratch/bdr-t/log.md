# De Rham period checks

- VERIFIED (source): the base is `be73b91c5`. `tt_ne_zero`,
  `tt_not_mem_sq`, `bdREquivAwayT` and `fontaineTwistT` are present.
  `git grep` found the one-generator `isGenEps_eps0` and the generic
  `transport_extends`, but no identification of the two logarithms or
  concrete intertwiner for `bdrAct`.
- VERIFIED (build): the first `lake build +ZInQKernel.Contrib.OneProof.DeRhamScholzeT`
  invocation launched multiple compilers by default and was interrupted.
  The retry used a compiler lock and checked the host load and available
  memory before each compiler start. Missing build artifacts were recovered
  locally only for matching source files, toolchain and dependency manifest;
  Lake replayed most traces but also scheduled lengthy dependency rebuilds.
  The target and three missing prerequisites were instead built directly,
  one at a time with `lake env lean -o`. The full Lake target build was
  interrupted, including the attempt to reuse artifacts with `--old`.
- VERIFIED (Lean): the resulting import passed all 79 `#check`s in
  `scratch/bdr-t/CheckBase.lean`. The fourth textual copy of `BdR` was
  read in `ZInQKernel/OneProof/H/TailC.lean`, outside the import closure
  as required.
- VERIFIED (Lean): `DeRhamPrint.BdRT.tt_eq_logTeich` identifies the two
  logarithms for every `RootSystem p`. The coefficient comparison uses
  `IsUnit.map_ringInverse`; the tail after degree `n` lies in
  `(xi)^(n+1)`. The axiom check gave `propext`, `Classical.choice`,
  and `Quot.sound`.
- VERIFIED (Lean): `isGenEps_eps` gives a generator for every `RootSystem p`.
  `bdrPlusMap_tt` and `bdrAct_tt` give `sigma(t) = chi(sigma) * t` in
  the positive ring and the kernel's period field, respectively. All four
  checks so far gave the three standard axioms.
