# htnew-assembly: `modularHTPrinted` from the printed form over the print's coefficient field

Task htnew-assembly, branch `wip/htnew-assembly`, base `origin/wip/leaf-fold33b` 4dfb7e58 (contains 8ba86099 and
`origin/main` at the start), 2026-11-17; `origin/wip/leaf-fold33b` beafc63d (top TailZ71, `sixContactMin_of_open64`,
bundle `OpenResearchLeaves45`) merged in afterwards and every check re-run on it. Lean: `ZInQKernel/Contrib/OneProof/ModularHTCoeff.lean` (same text in
`scratch/htnew-assembly/ModularHTCoeff.lean`). Log: `scratch/htnew-assembly/log.md`. Nothing else under `ZInQKernel/` was
edited. Model work, no human review.

Marks: **VERIFIED** = compiled, or read in a file on this host. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number, locator or printed wording recalled without a source
(no network on this host).

## 0. Verdict

**The bundle field `modularHTPrinted : EigenformHTPrinted.ModularHTPrinted` (OpenResearchLeaves42, strict GLUE
"consequence") is discharged in Lean by one new leaf, `HTNewAssembly.ModularHTCoeff`, which states the theorem in the
print's own terms: coefficients in the print's finite coefficient field (`K_{f,λ}`, Kato's `F_λ`, embedded in
`ℚ̄_ℓ`), Hodge–Tate weights in the print's definition (`dim_E (V ⊗_{ℚ_ℓ} ℂ_ℓ(w))^{G_{ℚ_ℓ}}`, Mathlib's tensor product),
and the print's Frobenius/sign conventions as a disjunction. Every step from the leaf to the field is proved
(VERIFIED, standard axioms). Dry-run fold on the current top (TailZ71): strict count 10/24 → 11/23, strictest 10/24 → 11/23
(GLUE −1, no new glue), if the leaf enters as `published` flagged `unread` (on the earlier top TailZ67: 12/22 → 13/21,
strictest 11/23 → 12/22).** No statement was changed. The field is not false,
vacuous or inert (it follows from the new leaf; the leaf holds by Deligne–Faltings–Saito–Kato).

Review grounds (strict leaf review, 2026-11-17, as quoted in the task; the review notes themselves,
`crowd-kit/ckpt/leaf-review/queue10-verdict.md`, are not in this tree):

| ground | status for `modularHTCoeff` |
|---|---|
| R1: the HT dual-side assembly is a step until written in Lean | **closed** (VERIFIED): `printHTMult_eq` (`dim_E (V ⊗ ℂ_ℓ(w))^G = htMult(ρ^∨, −w)`) and `kernel_of_print` (print-side weights `S` ⇒ kernel `HasHTWeightsAtSelf S`, via `HTDual`) |
| R3: "charpoly or satisfies" does not give the trace | **not applicable to the new leaf**: it no longer goes through `dsThm965Printed`; it asks the trace, which the existence theorem's printed Frobenius clause (characteristic polynomial / `det(1 − Frob·X)`, or the trace itself) gives (`EigenformHTPrinted.trace_of_charpoly`). A print saying only "satisfies" would not give it; no such print of this theorem is known (SPECULATIVE) |
| R4: coefficient extension for `K_{f,λ}` prints | **closed by the statement form** (VERIFIED for the Lean part): the leaf is over the print's coefficient field `E`; extension to `ℚ̄_ℓ` (`toGR`), the traces (`trace_toGR`) and the Hodge–Tate weights over the same `E` (no change of `E` needed, `LocalHasHTWeights` takes the witness `E`) are proved. What is not in Lean is the identification of the abstract completion `K_{f,λ}` with its image `E = τ̂(K_{f,λ}) ⊆ ℚ̄_ℓ` (transport of structure along the continuous embedding extending `ιL ∘ ιC⁻¹`; §3) |
| R5: finite-`E` descent (Baire + base change) for `ℚ̄_ℓ` prints | **open, for `ℚ̄_ℓ`-coefficient prints only** (Gee's survey form, UNVERIFIED wording). Not needed when the print is read over `K_{f,λ}` / `F_λ` (Deligne; Kato's `V_{F_λ}(f)`, the statement the locator audit read, row R13) |

Rating proposed: **LEAF (kind `published`, flag `unread`, locator UNVERIFIED)** as the printed existence form over
`K_{f,λ}`/`F_λ`; if a rater holds that the only print is over `ℚ̄_ℓ`, R5 remains and the leaf is the print plus a
standard descent (consequence, GLUE, count-neutral).

## 1. The statements

```lean
-- the field (EigenformHTPrinted.lean L983, unchanged; verbatim copy scratch/htnew-assembly/ModularHTPrinted-copy.lean.txt)
def EigenformHTPrinted.ModularHTPrinted : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) [NeZero N] (k : ℤ) (f : HeckeRing.GL2.Newform N k), 2 ≤ k →
    ∃ ρ : GaloisRep ℓ 2,
      ((∀ p, p.Prime → ¬ p ∣ N * ℓ → ρ.UnramifiedAt p ∧ ∀ α, ιC α = coeff f p → ∀ v σ, LiesOver v p →
          IsArithFrob σ v p → (ρ.mat σ).trace = ιL α) ∧ ρ.HasHTWeightsAtSelf ℓ {0, 1 - k}) ∨
      ((∀ p, ... (ρ.mat σ⁻¹).trace = ιL α) ∧ ρ.HasHTWeightsAtSelf ℓ {0, k - 1})

-- print-side Hodge–Tate weights (ModularHTCoeff.lean §1), E : IntermediateField ℚ_[p] (PadicAlgCl p), V = Eⁿ
def twistAct ρ w σ : (Fin n → E) ⊗[ℚ_[p]] ℂ_[p] →ₗ[ℚ_[p]] _ :=
  TensorProduct.map ((Matrix.toLin' (ρ σ)).restrictScalars ℚ_[p]) (x ↦ χ(σ)^w • σ x)        -- ρ(σ) ⊗ χ^w σ
def PrintHTSpace ρ w : Submodule E ((Fin n → E) ⊗[ℚ_[p]] ℂ_[p]) := {t | ∀ σ, twistAct ρ w σ t = t}
def PrintHTMult ρ w : ℕ := finrank E (PrintHTSpace ρ w)                     -- dim_E (V ⊗_{ℚ_p} ℂ_p(w))^{G_{ℚ_p}}
def PrintHasHTWeights ρ S := ∀ w, PrintHTMult ρ w = S.count w              -- cyclotomic weight −1
def PrintHasHTWeightsPos ρ S := ∀ w, PrintHTMult ρ (-w) = S.count w        -- cyclotomic weight +1

-- the new leaf (ModularHTCoeff.lean §4)
def HTNewAssembly.ModularHTCoeff : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) [NeZero N] (k : ℤ) (f : HeckeRing.GL2.Newform N k), 2 ≤ k →
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (_ : FiniteDimensional ℚ_[ℓ] E)
      (ρ : GQ →* GL (Fin 2) E), Continuous ρ ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ∀ v : ValuationSubring Qbar, LiesOver v p →
        ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : GQ) = 1) ∧
      (((∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ∀ α : Qbar, ιC α = coeff (f.toCuspForm : CF N k) p →
            ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
              (((ρ σ : Matrix (Fin 2) (Fin 2) E).trace : E) : PadicAlgCl ℓ) = ιL α) ∧
          PrintHasHTWeightsPos ℓ E (ρ.comp (decomp ℓ)) {0, k - 1}) ∨
        ((∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ∀ α : Qbar, ιC α = coeff (f.toCuspForm : CF N k) p →
            ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
              (((ρ σ⁻¹ : Matrix (Fin 2) (Fin 2) E).trace : E) : PadicAlgCl ℓ) = ιL α) ∧
          PrintHasHTWeights ℓ E (ρ.comp (decomp ℓ)) {0, k - 1}))
```

All objects are genuine definitions: Mathlib's `TensorProduct`, `IntermediateField`, `Module.finrank`, Mathlib's
cyclotomic character (`cycPow`), the kernel's `cpAct` (the action of `G_{ℚ_ℓ}` on `ℂ_ℓ`), `decomp`, `IsArithFrob`,
`LiesOver`, `coeff`, Tau Ceti's `Newform`. No structure was invented. `autoImplicit false`.

**Sign check (VERIFIED by computation from the definitions).** For `V = ℚ_ℓ(1)`, `twistAct` sends `v ⊗ c` to
`v ⊗ χ^{w+1} σ(c)`, so `(V ⊗ ℂ_ℓ(w))^G ≠ 0` iff `w = −1` (Tate): `PrintHasHTWeights` is the convention "cyclotomic
weight `−1`" (the kernel's), `PrintHasHTWeightsPos` the convention "cyclotomic weight `+1`". The same follows from
the assembly lemma: print multiplicity of `w` for `ℚ_ℓ(1)` = `htMult(ℚ_ℓ(−1), −w)`, nonzero iff `−w = 1`.

**The four printed readings (VERIFIED, `reading_arith`, `reading_geom`).** A print states the Frobenius normalization
(arithmetic `σ` or geometric `σ⁻¹` has trace `a_p`) and the weights in one sign convention. True statements:
arithmetic ↔ `{0, k − 1}` with cyclotomic weight `+1` ↔ `{0, 1 − k}` with cyclotomic weight `−1`; geometric ↔
`{0, k − 1}` with weight `−1` ↔ `{0, 1 − k}` with weight `+1` (STANDARD: `V_ℓ(E)` has weights `{0, −1}`, `H¹` has
`{0, 1}` in the weight `−1` convention). Lean proves `PrintHasHTWeights ρ {0, 1 − k} ↔ PrintHasHTWeightsPos ρ {0, k − 1}`
and `PrintHasHTWeightsPos ρ {0, 1 − k} ↔ PrintHasHTWeights ρ {0, k − 1}`, so each of the four wordings is one disjunct.

## 2. The Lean (all VERIFIED: compiled, `[propext, Classical.choice, Quot.sound]`)

| § | theorem | statement |
|---|---|---|
| §1 | `twistAct_smul`, `PrintHTSpace` | `ρ(σ) ⊗ χ^w σ` is `E`-linear; its fixed tensors form an `E`-subspace |
| §1 | `printHasHTWeightsPos_iff` | the two sign conventions differ by `S ↦ −S` |
| §2 | `trPair_injective`, `trEquiv` | the trace pairing `Eⁿ ≅ Hom_{ℚ_ℓ}(Eⁿ, ℚ_ℓ)`, `v ↦ (u ↦ Tr_{E/ℚ_ℓ}(u·v))` (injective since `Tr(1) = [E:ℚ_ℓ] ≠ 0`) |
| §2 | `psi`, `psi_tmul` | `V ⊗_{ℚ_ℓ} ℂ_ℓ ≅ Hom_{ℚ_ℓ}(Eⁿ, ℂ_ℓ)`, `v ⊗ c ↦ (u ↦ Tr(u·v) c)` (`TensorProduct.congr` + Mathlib's `dualTensorHomEquiv`) |
| §2 | `psi_twistAct` | `psi(ρ(σ) ⊗ χ^w σ · t)(u) = χ(σ)^w σ(psi(t)(ρ(σ)ᵀ u))` |
| §2 | `psi_mem_iff` | `psi t ∈ htSpace(ρ^∨, w) ↔ t ∈ (V ⊗ ℂ_ℓ(w))^G`, `ρ^∨(σ) = ρ(σ⁻¹)ᵀ` (`dualE`) |
| §2 | **`printHTMult_eq`** | **assembly lemma**: `PrintHTMult ρ w = htMult (dualE ρ) (−w)` (tower law `finrank_ℚ = [E:ℚ_ℓ]·finrank_E`, no finiteness needed) |
| §3 | `toGR`, `toGR_mat` | `ρ : G_ℚ → GL_n(E)` with coefficients extended to `ℚ̄_ℓ` |
| §3 | **`kernel_of_print`** | print-side weights `S` (card `n`) of `ρ|_{G_{ℚ_ℓ}}` ⇒ `(toGR ρ).HasHTWeightsAtSelf ℓ S` (kernel weights `−S` for `ρ^∨` over the same `E`, then htnew-print's `HTDual` and `ρ^∨^∨ = ρ`) |
| §5 | `reading_arith`, `reading_geom` | the four readings (§1) |
| §5 | `trace_toGR` | traces commute with `E ⊆ ℚ̄_ℓ` |
| §5 | **`modularHTPrinted_of_coeff`** | `ModularHTCoeff → EigenformHTPrinted.ModularHTPrinted` (**the discharge**) |
| §5 | `eigenformHTNew_of_coeff` | `ModularHTCoeff → EigenformCoeffFieldFinite → EigenformHTNew` (the consumer chain through htnew-print's `eigenformHTNew_of_printed`; the consumer's statement unchanged) |

The proof of `kernel_of_print` is where R1 lived: the kernel's `htMult` counts `G_{ℚ_ℓ}`-equivariant `ℚ_ℓ`-linear maps
`Eⁿ → ℂ_ℓ(i)` (the dual side), a print counts fixed vectors of `V ⊗ ℂ_ℓ(w)`. The trace form identifies
`V ⊗_{ℚ_ℓ} ℂ_ℓ` with `Hom_{ℚ_ℓ}(Eⁿ, ℂ_ℓ)` equivariantly for `ρ` on the left and `ρ^∨` on the right, so the print's
multiplicities of `ρ` are the kernel's of `ρ^∨` with the sign flipped; `HTDual` (proved in htnew-print from Tate's two
theorems, both proved on main) flips back. Nothing in the proof needs `E` Galois or a change of coefficient field.

## 3. Rating of the new leaf

**Proposed: kind `published`, flag `unread: new printed leaf (existence form over the print's coefficient field
K_{f,λ} / F_λ, Hodge–Tate weights 0, k−1 in the print's tensor-product definition, every level; the four
normalization/sign readings reduce to the two disjuncts in Lean; trace clause only); locator UNVERIFIED` (counts
LEAF).** Reasons:

- *Printed form.* Content: Deligne (Sém. Bourbaki 355, 1969/1971) constructs `ρ_{f,λ} : G_ℚ → GL₂(K_{f,λ})` with
  the Frobenius characteristic polynomial (UNVERIFIED wording; Diamond–Shurman 9.6.5 prints the same over `K_{f,λ}`,
  the kernel's `DSThm965Printed`); Faltings (Math. Ann. 278, 1987) Hodge–Tate for `ℓ ∤ N`; Saito (Invent. Math. 129,
  1997) and Kato (Astérisque 295, 2004, §§9.2-9.4, (9.2.2), pp. 187-188, read by the locator audit, row R13) every
  level, for Kato's `V_{F_λ}(f)`, a 2-dimensional `F_λ`-vector space with continuous `G_ℚ`-action, de Rham at `ℓ`
  with Hodge filtration jumps `0, k − 1` (§11.3, UNVERIFIED). Existence form in the surveys Taylor (Ann. Fac. Sci.
  Toulouse 2004) and Gee (ENT 2022 §2) (UNVERIFIED). With `F = K_f`, `λ` the place cut out by `ιL ∘ ιC⁻¹`, `E` the
  image of `F_λ` under the continuous extension `τ̂` of `ιL ∘ ιC⁻¹` (the kernel builds it: `DSCoeffExt.τhat`, image in
  `DSCoeffExt.tgt`), and `ρ` the matrix of `V_{F_λ}(f)` in a basis, the leaf is the print by ∃-introduction.
- *Never stronger than the print.* Coefficient field: ∃-introduction (the leaf asks for some finite `E`, not for
  `K_{f,λ}` itself). Hodge–Tate clause: literally the definition (`dim_E (V ⊗_{ℚ_ℓ} ℂ_ℓ(w))^{G}`), in either sign
  convention by or-introduction. Frobenius: trace only, at every Frobenius element of every place over `p ∤ Nℓ`,
  weaker than the characteristic polynomial (`trace_of_charpoly`); no algebraicity of `a_p` asserted ("if `ιC α = a_p`
  then ..."); no semisimplicity or determinant. Restriction to `G_{ℚ_ℓ}`: the kernel's `decomp` is one choice of
  decomposition group; a print's "`ρ|_{G_{ℚ_ℓ}}`" holds for every choice (the restrictions are conjugate).
- *What remains for a reader (the `unread` flag):* (i) that a refereed print states the existence form **at every
  level** (`ℓ ∣ N` included) — Kato's (9.2.2) as read in R13 covers it; (ii) that the print's "Hodge–Tate weights
  `0, k − 1`" is the Hodge–Tate decomposition multiplicities (Faltings' form) or follows from the de Rham statement
  with filtration jumps `0, k − 1` (de Rham ⇒ Hodge–Tate with `dim gr^i D_dR = dim (V ⊗ ℂ_ℓ(−i))^G`, Fontaine,
  STANDARD); (iii) transport of structure along `τ̂ : F_λ ≅ E` (R4 residue, not a mathematical step).
- *The other reading (R5).* If the only accepted print is Gee's over `ℚ̄_ℓ`, the leaf is that print plus finite-`E`
  descent (Baire: a continuous `G_ℚ → GL₂(ℚ̄_ℓ)` takes values in `GL₂(E)` for a finite `E`) and base change of
  Hodge–Tate multiplicities; then kind `consequence`, GLUE, count-neutral. The descent is not in Lean. Krasner's lemma is in Mathlib v4.35
  (`Mathlib/Analysis/Normed/Field/Krasner.lean`, `IsKrasner.of_completeSpace`, VERIFIED read), but the descent would
  also need the density of `ιL(ℚ̄)` in `ℚ̄_ℓ` (so that `ℚ̄_ℓ` is a countable union of finite extensions), Baire on
  `G_ℚ`, and base change of Hodge–Tate multiplicities from `E` to `ℚ̄_ℓ` for a `ℚ̄_ℓ`-coefficient definition.

**Proposed `locators.md` row** (not added: shared file):
`R13' (printed existence form over K_{f,λ}/F_λ, htnew-assembly) | Deligne 1971; Faltings 1987; Saito 1997; Kato 2004
(9.2.2) pp. 187-188; surveys Taylor 2004, Gee 2022 §2 | — | (9.2.2) read; others UNVERIFIED | there are a finite
E/Q_l in Qbar_l and a continuous rho : G_Q -> GL_2(E) attached to a newform (either Frobenius normalization),
unramified outside N l, Hodge-Tate at l with weights {0, k-1} as dim_E (V ⊗_{Q_l} C_l(±w))^{G}, every level`.

## 4. Compile log, `#discharges`, dry-run fold (VERIFIED, 2026-11-17, Lean 4.35.0 / Mathlib v4.35.0)

One Lean process at a time; load 35-57 (below the host's 150), at least 120 GB available.

| what | command | outcome |
|---|---|---|
| base build | `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.EigenformHTPrinted` | success, 16073 jobs, 54 min |
| contribution | `lake env lean ZInQKernel/Contrib/OneProof/ModularHTCoeff.lean`; `lake build +ZInQKernel.Contrib.OneProof.ModularHTCoeff` | success (~21 s), warnings only |
| axioms | `lake env lean scratch/htnew-assembly/Axioms.lean` | `modularHTPrinted_of_coeff`, `eigenformHTNew_of_coeff`, `printHTMult_eq`, `kernel_of_print`, `reading_arith`, `reading_geom`: `[propext, Classical.choice, Quot.sound]` (`axioms.txt`) |
| `#discharges` | `lake env lean scratch/htnew-assembly/Discharges.lean` | `Discharges-output.txt` (below) |
| fold (top TailZ67) | `python3 scripts/one_proof/autofold.py scratch/htnew-assembly/autofold.json --dry-run`; line 1 stripped → `FoldDryRun.lean`; `lake env lean` | `strict count: 12/22 on 34 -> 13/21 on 34; strictest 11/23 -> 12/22`; `sixContactMin_of_open61` compiles, standard axioms |
| rebuild after merging `origin/wip/leaf-fold33b` beafc63d | `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ModularHTCoeff` | success, 16094 jobs, 3.6 min; axioms re-run: unchanged |
| `#discharges` (top TailZ71) | as above | `DISCHARGES [OpenResearchLeaves45.modularHTPrinted] by HTNewAssembly.modularHTPrinted_of_coeff`, still assumes `[HTNewAssembly.ModularHTCoeff]`, standard axioms; `39 open hypotheses, 14068 theorems checked, 30 discharge one` |
| fold (top TailZ71) | same spec, dry run (kept as `FoldDryRun.lean.txt`, output `FoldDryRun-output.txt`) | `strict count: 10/24 on 34 -> 11/23 on 34; strictest 10/24 -> 11/23`; `HDec.HSyn.sixContactMin_of_open65` compiles, `[propext, Classical.choice, Quot.sound]` |

```
DISCHARGES [OpenResearchLeaves45.modularHTPrinted] by HTNewAssembly.modularHTPrinted_of_coeff
  still assumes: [HTNewAssembly.ModularHTCoeff]
  axioms: [propext, Classical.choice, Quot.sound]
...
#discharges: 39 open hypotheses, 14068 theorems checked, 30 discharge one
```
(On the earlier top TailZ67 the same entry read `OpenResearchLeaves42.modularHTPrinted`; footer `13436 theorems
checked, 26 discharge one`.)

**Autofold spec** (`scratch/htnew-assembly/autofold.json`): discharges `modularHTPrinted` with proof
`_root_.HTNewAssembly.modularHTPrinted_of_coeff {n}.modularHTCoeff`; new leaf `modularHTCoeff :
_root_.HTNewAssembly.ModularHTCoeff`, kind `published`, flag `unread: ...; locator UNVERIFIED`, source as in §3. The
fold itself (autofold without `--dry-run`, the build, the hash guard, OpenStatements, render_open, kinds.tsv,
locators.md) is the integrator's.

## 5. Files

- `ZInQKernel/Contrib/OneProof/ModularHTCoeff.lean` (25 KB): imports only `ZInQKernel.Contrib.OneProof.EigenformHTPrinted`
  (not `OneProof.Main`). Its three helper instances are `local instance` (no global instance added). No `#eval`,
  `run_cmd`, `initialize`, `syntax`, `notation`, macro, elaborator, `axiom` or `sorry` (VERIFIED by grep).
- `scratch/htnew-assembly/`: `ModularHTCoeff.lean` (copy), `ModularHTPrinted-copy.lean.txt` (verbatim copy of the
  target Prop), `Axioms.lean` + `axioms.txt`, `Discharges.lean` + `Discharges-output.txt`, `autofold.json`,
  `autofold-dryrun.txt`, `FoldDryRun.lean.txt` + `FoldDryRun-output.txt`, `build1.log`, `log.md`.

## 6. What remains

- R5 (only for a `ℚ̄_ℓ`-coefficient reading of the print): Baire descent to a finite `E` and base change of
  Hodge–Tate multiplicities. Not attempted.
- No converse: `ModularHTCoeff` asks for a global representation over a finite `E`, which `ModularHTPrinted` does not
  give without the same Baire descent; the leaf is justified by the print, not by the field it replaces.
- The `F_λ ≅ E` transport (R4 residue) is a statement about which object the print names, not a Lean step; a Lean
  version would need a `ℚ_ℓ`-algebra structure on `HeightOneSpectrum.adicCompletion`, which the kernel does not have.
