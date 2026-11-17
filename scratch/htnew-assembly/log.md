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
- 2026-11-17 02:09-03:03: `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.EigenformHTPrinted`: success, 16073 jobs, 54 min (load 40-57). VERIFIED.
- 03:03-03:10: `lake env lean ZInQKernel/Contrib/OneProof/ModularHTCoeff.lean`: 3 iterations (instance timeouts for the
  E-module on V ⊗_{Q_p} C_p fixed by explicit instances + synthInstance.maxHeartbeats 400000; `ext` on Pi domain;
  coercion). Final: success, ~21 s, warnings only. VERIFIED.
- `lake build +ZInQKernel.Contrib.OneProof.ModularHTCoeff`: success. `Axioms.lean` → `axioms.txt`: modularHTPrinted_of_coeff,
  eigenformHTNew_of_coeff, printHTMult_eq, kernel_of_print, reading_arith, reading_geom: [propext, Classical.choice, Quot.sound]. VERIFIED.
- `lake env lean scratch/htnew-assembly/Discharges.lean` → `Discharges-output.txt`: `DISCHARGES [OpenResearchLeaves42.modularHTPrinted] by
  HTNewAssembly.modularHTPrinted_of_coeff / still assumes: [HTNewAssembly.ModularHTCoeff] / axioms: [propext, Classical.choice,
  Quot.sound]`; footer `39 open hypotheses, 13436 theorems checked, 26 discharge one`. VERIFIED.
- `python3 scripts/one_proof/autofold.py scratch/htnew-assembly/autofold.json --dry-run` → `autofold-dryrun.txt`: `strict count:
  12/22 on 34 -> 13/21 on 34; strictest 11/23 -> 12/22`. Line 1 stripped → `FoldDryRun.lean` (renamed `.lean.txt` after the check):
  `lake env lean` success, `HDec.HSyn.sixContactMin_of_open61` depends on [propext, Classical.choice, Quot.sound]. VERIFIED.
- The three helper instances made `local instance` (no global instance added by the contribution); recompiled: module build
  success, axioms unchanged (standard), `#discharges` unchanged, FoldDryRun recompiled: standard axioms. VERIFIED.
- Scan of ModularHTCoeff.lean for #eval/run_cmd/initialize/syntax/notation/macro/elab/axiom/sorry: none (only the word in comments: none). VERIFIED.
