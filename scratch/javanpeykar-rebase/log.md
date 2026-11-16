# javanpeykar-rebase log

- 2026-11-16 15:02 start. Merged origin/main (e41a7169), origin/wip/integrate-w82 (5e235a40, not on main), height-fix 49e6d97d (no conflicts).
- Build tree: copied ~/dzq-wt/height-fix/.lake/build and lean/.lake/build (copy, not symlink).
- Consumers of ConstantFieldExtensionUnramifiedFull (grep, VERIFIED): only JavanpeykarFix.isBelyiFunction_baseChange_full,
  used by belyiBaseChange_of_full at L = AlgebraicClosure K (an infinite algebraic extension). So the consumer needs
  an infinite K'/K; plan: prove the algebraic case from the finite case in Lean (directed union of finite subextensions).
