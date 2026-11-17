# htnew-assembly (2026-11-17)

**Result.** The bundle field `modularHTPrinted : EigenformHTPrinted.ModularHTPrinted` (OpenResearchLeaves42/45, rated
GLUE "consequence" by the strict review) is discharged in Lean by one new leaf `HTNewAssembly.ModularHTCoeff`, the
printed existence form over the print's coefficient field: a finite `E/ℚ_ℓ` inside `ℚ̄_ℓ` (`K_{f,λ}` / Kato's `F_λ`
embedded), continuous `ρ : G_ℚ → GL₂(E)` unramified outside `Nℓ`, every level, Hodge–Tate weights `{0, k−1}` in the
print's definition `dim_E (V ⊗_{ℚ_ℓ} ℂ_ℓ(±w))^{G_{ℚ_ℓ}}` (Mathlib tensor product), Frobenius normalization and sign
convention as a disjunction (all four printed readings reduce to the two disjuncts in Lean), trace clause only.

**Compiles (standard axioms, VERIFIED).** `ZInQKernel/Contrib/OneProof/ModularHTCoeff.lean` (imports only
EigenformHTPrinted): assembly lemma `printHTMult_eq` (`dim_E (V⊗ℂ_ℓ(w))^G = htMult(ρ^∨, −w)` via the trace-form iso
`V⊗ℂ_ℓ ≅ Hom(Eⁿ, ℂ_ℓ)`), `kernel_of_print` (print side ⇒ kernel `HasHTWeightsAtSelf`, via HTDual),
`modularHTPrinted_of_coeff` (the discharge), `eigenformHTNew_of_coeff` (consumer chain). `#discharges`:
`OpenResearchLeaves45.modularHTPrinted` by `modularHTPrinted_of_coeff`, still assumes `[HTNewAssembly.ModularHTCoeff]`
(after merging leaf-fold33b beafc63d, top TailZ71). Autofold dry-run (`scratch/htnew-assembly/autofold.json`): strict
10/24 → 11/23, strictest 10/24 → 11/23; `sixContactMin_of_open65` compiles with standard axioms (on the earlier
top TailZ67: 12/22 → 13/21).

**Review grounds.** R1 (HT dual-side assembly) closed in Lean. R4 (coefficient extension for `K_{f,λ}` prints)
closed by stating the leaf over the print's coefficient field (extension to `ℚ̄_ℓ` proved; only the naming of
`F_λ` as its image `E ⊆ ℚ̄_ℓ` is transport of structure). R3 does not apply (no `dsThm965Printed`; trace from the
printed char. poly.). **R5 open only if the print is read over `ℚ̄_ℓ`** (Gee): Baire descent + base change not in Lean.
Proposed rating: LEAF (`published`, flag `unread`, locator UNVERIFIED); under the `ℚ̄_ℓ`-only reading, consequence
(count-neutral). R2, R6, R7 of the review could not be checked (review notes not in this tree).

**Remains.** Integrator: real fold, kinds.tsv, locators.md row (proposed in docs/research/htnew-assembly.md §3).
Optional: Baire descent for R5. Report: docs/research/htnew-assembly.md; log: scratch/htnew-assembly/log.md.
