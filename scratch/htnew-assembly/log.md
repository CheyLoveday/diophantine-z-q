# htnew-assembly log

Base: wip/htnew-assembly = origin/wip/leaf-fold33b 4dfb7e58 (contains 8ba86099 and origin/main). Top bundle:
`HDec.HSyn.OpenResearchLeaves42` (TailZ67, `sixContactMin_of_open60`); target field `modularHTPrinted :
EigenformHTPrinted.ModularHTPrinted` (verbatim copy: `ModularHTPrinted-copy.lean.txt`).

## Statements
- New leaf `HTNewAssembly.ModularHTCoeff` (ZInQKernel/Contrib/OneProof/ModularHTCoeff.lean §4): existence over a
  finite E ⊆ Qbar_l (print's K_{f,lambda}/F_lambda embedded), HT weights on the print's side
  dim_E (V ⊗_{Q_l} C_l(±w))^{G_{Q_l}} (Mathlib TensorProduct), disjunction arithmetic+conv(+1) {0,k-1} /
  geometric+conv(-1) {0,k-1}; trace clause only.
- Assembly lemma `printHTMult_eq`: PrintHTMult ρ w = htMult (dualE ρ) (-w) (trace-form iso V⊗C ≅ Hom(E^n, C)).
- `kernel_of_print`: print-side weights S ⇒ kernel HasHTWeightsAtSelf S (via HTDual).
- Discharge `modularHTPrinted_of_coeff : ModularHTCoeff → EigenformHTPrinted.ModularHTPrinted`.

## Compile outcomes
