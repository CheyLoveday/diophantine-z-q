# Deligne row: print-shaped statements and bridges

Additive record, 2026-11-27, for the open row `Y3Hodge.DeligneCanonicalModelY3EveryPrint`
(`ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean`, §7). Lean: `ZInQKernel/Contrib/OneProof/DelignePrintShaped/`.
No existing statement changes; nothing is folded.

## 1. The statements

| name | kind | print | what it states (kernel form) |
|---|---|---|---|
| `DelignePS.VoightQMComplexModuliPrint` (T2a) | print-shaped | Voight, *Quaternion Algebras* (GTM 288, 2021), 43.6.12, Main Thm 43.6.14, Prop. 43.6.28 (pp. 819–822 of the print) | every `τ ∈ ℍ` is the period of a complex QM surface `(A, ι) ≅ (ℂ²/Λ_τ, ι_τ)`; every complex QM surface with a principal polarization of type `μ` has such a period; two periods of one surface are `Γ¹(𝒪)`-equivalent (level 1) |
| `DelignePS.CornutVatsalCMReciprocityPrint` (T2b) | print-shaped | Cornut–Vatsal, Doc. Math. 10 (2005), §3.1.1 (p. 291), Lemma 3.7 (p. 296), §3.2.4 (p. 298), Lemma 3.11 (p. 299) | a smooth curve `M` over `ℚ` with `ψ : ℍ^± × (B ⊗ 𝔸_f)^× → M(ℂ)` onto, fibres the `B^× \ · / K₃` classes, holomorphic, and `σ = rec_K(λ)` acting on CM points by `λ^ε` |
| `DelignePS.FineModuliCanonicalModelGlue` (W-a) | **GLUE** | none (see §3) | every such `(M, ψ)` is isomorphic to every fine-moduli witness `(Y, Φ)`, carrying the moduli point of `[z, g]` to `ψ(z, g)` |
| `DelignePS.BoutotCarayolModuliPrint` (T2c) | print-shaped | Boutot–Carayol, Astérisque 196–197 (1991), III.0.1 (p. 125), Thm 1.1, 1.2(a) (p. 128), 1.3–1.4 (p. 129) | some witness of the polarization-free fine moduli problem at `U(3) = K₃` over `ℚ` whose complex points are uniformized by the double quotient |
| `DelignePS.BoutotCarayolPolarizationPrint` (T2c′) | print-shaped | Boutot–Carayol, Prop. (1.5) (p. 129), proved there | every complex QM surface with full level-3 structure has a principal Riemann form of type `μ` (`HasPrincipalRiemannMu`) |

Each docstring quotes the print verbatim with its page, lists the identifications (the quaternion algebra of
discriminant 6, `𝒪`, `K₃ = U(3)`, `ℍ^±`, the normalization of the reciprocity map, CM points versus `IsCMPoint`)
and the dropped or changed clauses. A principal polarization of type `μ` over `ℂ` is written as a Riemann form on a
uniformization (`DelignePS.HasPrincipalRiemannMu`), read through Riemann's theorem.

The moduli description of `[z, g]` is `DelignePS.IsLevelPoint`: `(ℂ²/Λ_τ, ι_τ, η_w)` for a representative `(τ, u)`,
`τ ∈ ℍ`, `u ∈ 𝒪̂^×`, with `η_w(a) = ℓ_τ(a w)/3` and `w ≡ u⁻¹ (mod 3)`. This is the lattice form of
`[h_z, g] ↦ (ℂ²/ι(L_g)(z, 1)ᵀ, ι, level from g)`, `L_g = B ∩ 𝒪̂ g⁻¹`; the level points on `ℂ²/Λ_τ` are the
computation behind Shimura, J. Math. Soc. Japan 13 (1961), Prop. 4.1, done in Lean (`DelignePS.levelObj`).

## 2. Which statement supplies which clause

| clause of the row | from | Lean |
|---|---|---|
| onto, fibres (both directions, so the reverse fibre clause at CM points) | T2a + T2c′ + level-3 classification over `ℂ`, on every witness (B2.1, no model identification); or T2b through W-a | `moduli_clauses_of_print`; `deligneCanonicalModelY3EveryPrint_of_prints` |
| moduli clause in `H₁` form at `g = 1` and at every `u ∈ 𝒪̂^×` | T2a (first clause) + level marking + the proved dictionary `Y3Hodge.print_of_lattice` | `exists_levelPoint_unit` |
| holomorphy (every `g`) | T2b (§3.1.1) through W-a | `deligneCanonicalModelY3EveryPrint_of_prints` |
| reciprocity at every CM point, every idele, every `g` | T2b (Lemma 3.11) through W-a, with Cornut–Vatsal's geometric normalization turned into the kernel's arithmetic one (B2.4: `ε ↦ −ε`) | `recip_kernel_of_cv` |

## 3. The GLUE W-a

W-a is the one comparison no printed statement read for this row makes: the fine moduli `ℚ`-scheme of QM abelian
surfaces with full level-3 structure, with its complex moduli description, is Shimura's canonical model at `K₃`.
Boutot–Carayol describe both structures on `S_U` (III.0.1: "Sa ℚ-structure a été définie par Shimura"; 1.4: the moduli
problem "est en fait défini et représentable sur le corps ℚ, et l'on peut le prendre comme définition de la
ℚ-structure sur S_U") without comparing them. The statement also uses the uniqueness of canonical models
(Cornut–Vatsal §3.1.2: "Among the models of M_H^an, the Shimura curve M_H is characterized by specifying the action
of Galois (the "reciprocity law") on certain special points"). It would be closed by Shimura, Ann. of Math. 85
(1967), Main Theorem I, in moduli form, if that print states it at level `K₃`.

## 4. Status

All Lean below compiles on `main` at `9c5f7262` with only `propext`, `Classical.choice`, `Quot.sound`
(`#print axioms`), no `sorry`, and only `set_option autoImplicit false`.

| module | content |
|---|---|
| `DelignePrintShaped.Prints` | the statements of §1, `HasPrincipalRiemannMu`, `IsQMTorusAt`, `IsLevelTorusAt`, `IsLevelPoint` |
| `DelignePrintShaped.Bridges` | level marking (`levelObj`), `exists_levelPoint(_unit)`, `moduli_clauses_of_print`, `recip_kernel_of_cv` (B2.4), the discharge `deligneCanonicalModelY3EveryPrint_of_prints`, `y3FineModuliAbP_of_boutotCarayol` |
| `DelignePrintShaped.LevelOnto` | `levelOnto_of : VoightQMComplexModuliPrint → BoutotCarayolPolarizationPrint → LevelOnto` (with the adelic unit `u ≡ w⁻¹ mod 3`, built from the idempotent of `ℤ̂` at `3`) |
| `DelignePrintShaped.LevelClass` | `levelClassification_of : ZInQ.HomLattice.GAGAMorphism → LevelClassification` (isomorphisms of the moduli objects are the double cosets, both directions) |
| `DelignePrintShaped.Assembly` | `moduli_clauses_of_prints` (B2.1 in full) and `moduli_map_eq_of_glue` |

The discharge:

```
deligneCanonicalModelY3EveryPrint_of_prints :
  VoightQMComplexModuliPrint → CornutVatsalCMReciprocityPrint → FineModuliCanonicalModelGlue →
    Y3Hodge.DeligneCanonicalModelY3EveryPrint
```

B2.1 without any GLUE: `moduli_clauses_of_prints : VoightQMComplexModuliPrint → BoutotCarayolPolarizationPrint →
ZInQ.HomLattice.GAGAMorphism → ∀ Y Φ, ∃ Ψ, onto ∧ (fibres ↔ DCRelPM) ∧ (Ψ is the moduli map) ∧ moduli clause at
`g = 1` ∧ `ModuliAtUnitsHP`` (`GAGAMorphism` is an existing textbook field).

What remains open: W-a itself (GLUE; §3), and holomorphy and reciprocity without W-a (they need an identification of
a printed model's uniformization with the moduli map: T2c gives a holomorphic uniformization of the witness, but the
print does not specify which one).
