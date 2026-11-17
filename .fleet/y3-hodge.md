# y3-hodge (2026-11-17)

**Result.** y3-fix's research leaf `Y3Fix.DeligneCanonicalModelY3EveryH` (queue11: consequence, GLUE) is restated
as its print, `Y3Hodge.DeligneCanonicalModelY3EveryPrint`, and proved **equivalent** to the old leaf:
`print_iff_deligneH`. With `printPM_iff_field`, it and `Y3FineModuliAbP` are together equivalent to the field. The
new leaf: `Ψ` on `ℍ^± × G(𝔸_f)` with fibres the print's double cosets `DCRelPM`, and the moduli clause
`IsHodgeH1Print` stated over genuine definitions:
* `H₁(A(ℂ), ℤ) = π₁(A(ℂ), 0)ᵃᵇ`;
* `𝒪` acting on it by functoriality (`h1Act`);
* `Lie A` given through a holomorphic homomorphism `e = exp_A ∘ L`.

All three review items and the sign check are Lean theorems:
1. `print_iff_hodge : IsHodgeH1Print ↔ Y3Fix.IsHodgeH1` (pel-hodge's `h1Form_iff` ported to the base's classical
   topology, plus a monodromy argument for the `𝒪`-action).
2. `lemmaP_H1`: on the genuine `H₁` there is exactly one principal Riemann form of type `μ`, and it is `E₀`
   (uniqueness: `eq_smul_E0` run on `𝒪`, then sign by `riemann_sign`; existence: `E₀ ∘ c⁻¹`).
3. `dcRelPM_iff` and `exists_upper` (`μ = 1+i`, `nrd μ = −1`), plus the retraction lemmas.
4. Sign: `F0_iff` (`F⁰ = {M : M(τ,1)ᵀ = 0}`, holomorphic in `τ`), `iota_mul_Jmat`, `adjugate_Jmat`. The leaf's sign
   is correct; **no statement change**. y3-fix's docstring phrase "`h_τ(i) = J_τ`" holds for right multiplication;
   with Deligne's left convention `h(i) = −J_τ`.

**Compiles (VERIFIED, standard axioms).**
* New module `ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean` (= `scratch/y3-hodge/Hodge.lean`): `lake build` OK.
* `#discharges`: field discharged by `Y3Hodge.deligneH_of_print`; 13528 theorems checked.
* Autofold spec `scratch/y3-hodge/autofold.json` (leaf kind consequence, "pending review (new leaf, GLUE until a
  reviewer rates it)"): dry run strict 11/23 on 34 → 11/23 on 34.
* `FoldCheck.lean.txt` compiles (`sixContactMin_of_open61` standard axioms).
* The −1 strict GLUE comes when a reviewer re-rates the new row.

**Remains.**
* Reading risks: R1 (the PEL print; passing to `Y` needs Lemma P over `ℂ`, now proved on `H₁`, plus Riemann's theorem,
  STANDARD); Milne §8/§14 read as one statement.
* Locators unread (no network).
* No combined fold with other specs.

Report: docs/research/y3-hodge.md.
