# javanpeykar-rebase log

- 2026-11-16 15:02 start. Merged origin/main (e41a7169), origin/wip/integrate-w82 (5e235a40, not on main), height-fix 49e6d97d (no conflicts).
- Build tree: copied ~/dzq-wt/height-fix/.lake/build and lean/.lake/build (copy, not symlink).
- Consumers of ConstantFieldExtensionUnramifiedFull (grep, VERIFIED): only JavanpeykarFix.isBelyiFunction_baseChange_full,
  used by belyiBaseChange_of_full at L = AlgebraicClosure K (an infinite algebraic extension). So the consumer needs
  an infinite K'/K; plan: prove the algebraic case from the finite case in Lean (directed union of finite subextensions).
- 15:14 build1 (PrintedStableHeight, JavanpeykarFix): OK, 12777 jobs. VERIFIED.
- Finite.lean (Stichtenoth finite leaf, full_of_finite): compiles clean. VERIFIED.
- ZInQKernel/Contrib/OneProof/JavanpeykarRebase.lean: `lake build +Main +Discharges +JavanpeykarRebase` OK (14114 jobs). VERIFIED.
- #discharges (scratch/javanpeykar-rebase/Discharges-output.txt): javanpeykarBound by
  JavanpeykarRebase.javanpeykarBound_of_printed_rebase, still assumes [JavanpeykarRebase.JavanpeykarPrintedMap,
  JavanpeykarRebase.ConstantFieldExtensionUnramifiedFinite, UniformizationLeafAll, MumfordTorsionAlgClosed,
  ZInQ.HeightFix.SemiAbelianDescendsPerfect]; standard axioms. full_of_finite, finite_of_full,
  javanpeykarPrintedMap_of_fix: standard axioms. VERIFIED.
