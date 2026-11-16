# javanpeykar-fix log

Base: wip/javanpeykar-dict d3868494 + merge origin/main 0caafe66 + merge origin/wip/height-dict 15cc5a60.
Build tree: copied (reflink) from ~/dzq-wt/javanpeykar-dict/.lake/build; `lake build ZInQKernel.Contrib.OneProof.HeightDictionary` OK (12753 jobs).

Verbatim copies: OldField.lean.txt (JavanpeykarBound), JavanpeykarPrinted.lean.txt, ConstantFieldExtensionUnramified.lean.txt.

## Steps
- 13:10 PartA.lean COMPILED (VERIFIED, standard axioms):
  - `fullConstantField_of_bijective`: `F ⊗_K L ≅ FL`, `L` alg. closed ⇒ `K` algebraically closed in `F`.
  - `ConstantFieldExtensionUnramifiedFull` (Stichtenoth leaf + full-constant-field hypothesis),
    `isBelyiFunction_baseChange_full`, `belyiBaseChange_of_full : ConstantFieldExtensionUnramifiedFull → BelyiBaseChange`.
  - `exists_jacBar` (step d): tensor-compatible `Pic⁰_{X/K}` rep `V` ⇒ ∃ tensor-compatible `Pic⁰_{X_L/L}` rep `W`
    with `(AbelianVariety.baseChange K L).obj V ≅ W` (vendored `baseChangeIso`).
