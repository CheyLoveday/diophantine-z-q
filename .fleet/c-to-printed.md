# c-to-printed — summary

**Verdict.** Three of the four fields are now Lean theorems from published-form leaves alone, with no glue left.
These are `neronLocalizesDVR`, `faltingsLemma5BC` and `semistableNeronBaseChange` (SS2). The fourth,
`shimuraFamily`, is proved from the fullest statable form of Shimura 1967 Main Thm I. It stays a consequence of the
print, because the reciprocity law needs global class field theory, which Mathlib 4.35 lacks. No statement changed,
and none was found false or vacuous; one independent model review agreed. Every locator is UNVERIFIED, since there
was no network.

**What compiles.** Both files are sorry-free and axiom-free, and every `#print axioms` line is
`[propext, Classical.choice, Quot.sound]`.

`scratch/c-to-printed/CToPrinted.lean` (imports TailZ14, about 11 s, 14 axiom checks):
- `neronLocalizesDVR_of_printed : BLR_1_2_4 → ReductGlue.NeronLocalizesDVR`. The leaf is BLR 1.2 Prop. 4, the full
  "iff" over any Dedekind domain, with `IsNeronModelOver` (BLR 1.2 Def. 1) defined over Mathlib.
- `faltingsLemma5BC_of_printed : FaltingsLemma5Printed → RaynaudKernelBound → FaltingsLemma5BC`. The leaves are
  Faltings' Lemma 5 identity, with `log #s*Ω¹_{G/S}` built from stalks of the kernel of the Néron isogeny
  (`kerOmegaLog`), and Raynaud's bound.
- `semistableNeronBaseChange_of_printed_full`, from five leaves: `BLR_1_2_4`, `SGA3_VIB_3_10` (`G⁰` open, with
  `idCompSet` defined), `SGA7_IX_3_3` (`N⁰⊗R' ≅ N'⁰`), `EGAIV_8_10_5_openImm`, and the existing bundle leaf
  `AVGlue.GeomConnOfRationalPoint` (Stacks 04KV). Proved along the way:
  - reduct-glue's leaf `OpenImmersionOfLocal` (`Spec O = lim Spec 𝓞_L[1/a]`);
  - `IdentityComponentOL` (an open subgroup scheme on `𝒢⁰`, via `GrpObj.ofRepresentableBy`);
  - `G⁰` is closed under the group law, and it commutes with base change;
  - `G⁰ → S` is geometrically connected.
- `CToPrintedLeaves`, `fields_of_leaves` and `reductGlue_leaves_of_printed`, for integration.

`scratch/c-to-printed/Shimura.lean` (a verbatim copy of shimura-split's file, which still compiles):
- `shimuraFamily_of_mainThmI : ShimuraMainThmIY3 → ShimuraFamily`.
- The leaf combines a fine witness, a holomorphic `y_τ` with the moduli clause, and fibres equal to `Γ(3)`-orbits.

**What remains.**
- `shimuraFamily` still needs the literal print. The missing pieces are the global Artin map for Shimura's
  reciprocity law, and the canonical model `V_S` over `ℚ(ζ₃)` with Deligne's comparison `Y₃ ⊗ ℚ(ζ₃) = V_S ⊔ V_S^σ`.
- Reading risks:
  - BLR 1.2/4 may be printed with strict henselizations.
  - The numbers SGA 3 "3.10" and Raynaud "2.1.3" are unconfirmed.
  - Faltings' Lemma 5 is unread; locators.md could not read it.
- Report: `docs/research/c-to-printed.md`. Results log: `scratch/c-to-printed/log.md`.
