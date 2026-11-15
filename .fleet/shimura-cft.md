# shimura-cft — summary

**Result.** Shimura's Main Theorem I for the level-3 group of `B = (2,−3 | ℚ)` is now one Lean Prop over genuine
definitions, reciprocity law included: `ShimuraCFT.ShimuraMainThmIDeligneY3Ab`. It is in Deligne's adelic form, on the
moduli scheme `Y₃/ℚ`. Both fields follow from it with no glue:
- `shimuraFamilyAb_of_mainThmI : ShimuraMainThmIDeligneY3Ab → QMSplit.Moduli.ShimuraFamilyAb`;
- `shimuraFamily_of_mainThmIAb : MumfordRigidityCore → ShimuraMainThmIDeligneY3Ab → QMSplit.Moduli.ShimuraFamily`.

The leaf asks for `Ψ : ℍ × (B⊗𝔸_f)^× → Y₃(ℂ)` with four clauses:
1. a bijection from `B^×_+\(ℍ × G(𝔸_f))/K₃`;
2. holomorphic in `τ`;
3. the moduli clause at `g = 1`;
4. `σΨ(z,g) = Ψ(z, q̂(s_f)^ε g)` at every CM point, for every idele `s` and every `σ ∈ Aut(ℂ)` that equals
   `[s, K]` on `K^ab`.

Clause 4 uses Tau Ceti's `ideleClassArtinMap` and adelic base change `finiteAdeleBaseChangeAlgEquiv` (vendored), and
Mathlib's adeles, ideles and schemes. The conventions `ε` and `δ` are existential, so the leaf is a consequence of the
print and not stronger. No canonical-model definition is missing. Shimura's `V_S` over `ℚ(ζ₃)` and
`Y₃ ⊗ ℚ(ζ₃) = V_S ⊔ V_S^σ` come out of clauses 1 and 4 with Deligne's comparison, so no `ℚ(ζ₃)`-model is named.

**Also proved.**
- `mainThmIY3_of_mainThmI`: the new leaf implies c-to-printed's `ShimuraMainThmIY3`, via `K₃ ∩ B^×_+ = Γ(3)`
  (`dcRel_one_iff`).
- `qHat_algebraMap`: `q̂` extends `q`.
- `exists_artinCondC`: every `σ` fixing `κ(K)` is `[s, K]` on `K^ab`, from t5-glue's proved surjectivity of the
  absolute Artin map.
- `recip_hyp_nonempty`: the clause-4 hypotheses can be met (`ℚ(√−3)`, `j`, `z = i√3`) for either `δ`.

**What compiles.** `scratch/shimura-cft/ShimuraCFT.lean`, one file: 0 errors, about 20 s and 8.8 GB, no
`sorry`/`axiom`. All 17 `#print axioms` lines, including the one for the leaf definition, give
`[propext, Classical.choice, Quot.sound]`. One independent model review found no PROBLEM; its one wording RISK is
fixed.

**What remains.**
- Locators (Shimura 1967 Main Thm I and §§2-3; Deligne, Bourbaki 389 §§3-4) are UNVERIFIED: there was no network.
- Inherited caveats: Lemma QP (polarization), and the reading "`Y₃ = Sh_{K₃}`" (the same reading as
  `DeligneComponentsY3Printed`).
- Not done: Shimura's per-`S` form over `ℚ(ζ₃)` as a separate Prop, and a proof that it follows from the Deligne form.

Report: `docs/research/shimura-cft.md`; log: `scratch/shimura-cft/log.md`.
