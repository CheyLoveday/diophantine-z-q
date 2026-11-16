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
- 13:20 PartC.lean COMPILED: `exists_closedImmersion_projectiveSpace` (step c) — smooth proper integral curve over a field has a
  closed immersion into `ℙ(n; Spec k)` over `k` (vendored Chow lemma + `exists_hom_of_valuationRing_stalk`; section of separated map).
- 13:30 Contrib `ZInQKernel/Contrib/OneProof/JavanpeykarFix/Basic.lean` BUILT (lake build): PartA + PartC, `P1 = Proj k[X₀,X₁]`,
  `IsBelyiMap`, leaf `JavanpeykarPrintedMap`, glue `BelyiMapOfFunction`, `javanpeykarBound_of_map`.
- 14:xx scratch BelyiMap1.lean COMPILED (no sorry): chart `Spec k[s] ≅ D₊(X₁)`, `ptT = [t:1]`, `exists_extension` (valuative
  extension), `isClosed_of_ne_genericPoint`, `finite_of_isClosed_of_genericPoint_notMem`, `isFinite_beta` (proper + finite fibres),
  chart preimages of `D₊(X₀)`, `D₊(X₀−X₁)`, main identity `stalkMap_secR`, `exists_sub_const_mem` (residueFieldIsoBase),
  `wOf` (valuation subring `𝒪_{C,x}`), `unramified` (ramification index 1 at closed points over ℙ¹∖{0,1,∞}).
