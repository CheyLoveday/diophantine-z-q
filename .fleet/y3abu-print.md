# y3abu-print (fleet summary)

**Result.** The composite GLUE field `shimuraMainThmIDeligneY3AbU` is proved in Lean
(`ZInQKernel/Contrib/OneProof/ShimuraY3Print.lean`, namespace `Y3ABUPrint`) from two printed-form leaves, one object each:
- `Y3FineModuliAb := ∃ Y Φ, R1fpPropsAb Y Φ`: the fine moduli scheme Y₃ over ℚ with its universal family, a consequence of
  representability (Buzzard 1997 §1; Boutot–Carayol; Milne 1979; locator UNVERIFIED; reading risk: no polarization).
- `DeligneCanonicalModelY3Every := ∀ Y Φ, R1fpPropsAb Y Φ → ∃ Ψ, DeligneBodyAt ∧ ModuliAtUnits`: the field's body, verbatim,
  on every witness. Source: Deligne, Sém. Bourbaki 389 §§4-5, where the PEL moduli scheme is the canonical model; Milne,
  ISV §§8, 14. Locator UNVERIFIED. Reading risks: the locators.md R1 qualifications, and whether Milne §8 and §14 count
  as one theorem.
- Discharge `shimuraMainThmIDeligneY3AbU_of_print`. The converse `print_iff_field` holds too. The every-witness leaf is
  never stronger than the field: two witnesses are compatibly isomorphic (`compare_iso_ab`, copied from elkies-print),
  and every clause transports along the isomorphism. Holomorphy transports via the new lemmas `regVal_comp` and
  `isHolFamily_comp`.

**Compiles (VERIFIED).**
- `lake build +Main +Discharges +ShimuraY3Print` succeeds; all theorems use only the standard axioms.
- `#discharges`: DISCHARGES `OpenResearchLeaves28.shimuraMainThmIDeligneY3AbU`, still assuming the two leaves.
- `scratch/y3abu-print/autofold.json` dry-run: strict 16/21 → 18/20 (**−1 GLUE**); `FoldCheck.lean` compiles.
- Combined with grx6ab-print and elkies-print (`autofold-combined.json`, branch merged): 16/21 → 21/18 (**−3 GLUE**);
  `FoldCheckCombined.lean` compiles.

**Clause analysis.**
- Read by the chain: R1fpPropsAb, surjectivity, DCRel ⇒ equal, holomorphy at g = 1, reciprocity, ModuliAtUnits.
- Unread: equal ⇒ DCRel, and the analytic half of holomorphy for g ≠ 1.
- Not narrowed: narrowing changes no rating and would need a bypass through 11 generations.

**Remains.**
- Locator readings (no network).
- If `deligneCanonicalModelY3Every` is rated composite (Milne §8 + §14), the solo fold is count-neutral.
- A three-leaf split would need a level-structure pin `η_u(a) = (1/3)ι(a u⁻¹)(τ,1)ᵀ`, because gt-rayclass's
  counterexample rules out the version without it. It is proposed in the report §4.2, not done.

Report: docs/research/y3abu-print.md.
