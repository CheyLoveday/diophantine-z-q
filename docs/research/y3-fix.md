# y3-fix: both leaves of y3abu-print restated in printed form; the field proved from them

Task y3-fix (2026-11-17). Base: fork main 222c98bf (leaf-fold33, top `sixContactMin_of_open48`, TailZ55), with
y3abu-print (579a89bb) merged. Contributor file: `ZInQKernel/Contrib/OneProof/ShimuraY3PrintedLeaves.lean`,
namespace `Y3Fix`. It imports `ShimuraY3Print` (which imports `RayClassShimura`, where the field is defined),
`ShimuraGoodReductionNoGuard` and `UniformizationLeafAll`, never `Main`. It has no `sorry`.
Scratch: `scratch/y3-fix/` (log `log.md`; `Y3Fix.lean` is the same file with `#print axioms` lines added).
Marks used below:
* VERIFIED: compiled, or read in the tree.
* STANDARD: published, exact reference.
* UNVERIFIED: a locator recalled from memory; there is no network on this host.

## 1. Result

**The research field `RayClassCFT.ShimuraMainThmIDeligneY3AbU` (GLUE) is proved in Lean from two new leaves in
printed form, plus the existing textbook field `mumfordTorsionAlgClosed`. The two leaves together are equivalent
to the field (VERIFIED, standard axioms):**

```
Y3Fix.shimuraMainThmIDeligneY3AbU_of_print :
  AvSplit.MumfordTorsionAlgClosed → Y3Fix.Y3FineModuliAbP → Y3Fix.DeligneCanonicalModelY3EveryH →
    RayClassCFT.ShimuraMainThmIDeligneY3AbU
Y3Fix.print_iff_field (hM : AvSplit.MumfordTorsionAlgClosed) :
  (Y3FineModuliAbP ∧ DeligneCanonicalModelY3EveryH) ↔ ShimuraMainThmIDeligneY3AbU
```

The review gave three reasons for rating y3abu-print's two leaves GLUE. Each one is removed:

| review objection | fix | Lean |
|---|---|---|
| (1) `Y3FineModuliAb` asserts `Nonempty (fieldPt Qbar ⟶ Y)`, which no representability print contains | The clause is **dropped** from the leaf. The field's `ℚ̄`-point is **proved** from `Ψ(i, 1) ∈ Y(ℂ)`, which the canonical-model leaf supplies (`Sh_K(ℂ)` is nonempty in the print). | `nonempty_qbar_of_cpt`: a proper `ℚ`-scheme with a `ℂ`-point has a `ℚ̄`-point (a closed point exists by compactness and T0; `HDec.ModelGlue.exists_qbarPt`) |
| (2) the level structure is the kernel's pointwise form | The level structure is **restated in the print's form**, `LevelPrint`: Mumford, *GIT* Def. 7.1 (UNVERIFIED), in `𝒪`-linear form. It is stated over `S`. At every geometric point `s : Spec k → S` the sections `η(a)`, `a ∈ 𝒪/3𝒪`, are distinct and are all of `A_s(k)[3]`. Here `A_s` is the pulled-back fibre with the group law of the pulled-back group object. The comparison with the chain's form is **proved in both directions** over `ℚ`-schemes. | `toKer : QMAbSchemeP S → QMAbScheme S` (`Spec K̄ → Spec K` is an epimorphism); `ofKer : QMAbScheme S.left → QMAbSchemeP S.left` (the fibre object, copied from SGRSplit's `qmAbFieldFibre_of`, then `Level3.onto`, using `TorsionStructure = torsionStructure_of_mumford t.mumfordTorsionAlgClosed`) |
| (3) the moduli clause of `DeligneCanonicalModelY3Every` is in lattice form, and no dictionary to the print's Hodge/H₁ form exists | The clause is **restated in H₁/Hodge form**, `IsHodgeH1 P τ`, and the dictionary is **proved in both directions** | `lattice_of_hodge`, `hodge_of_lattice`, `hodge_iff_lattice` |

**Count** (autofold `--dry-run`, VERIFIED): strict and strictest go from **11/18 on 29 to 13/17 on 30**, which is
**−1 GLUE and +2 LEAF** against the current kinds.tsv. y3abu-print's fold, with both of its leaves rated GLUE, would
go to 11/19 (+1 GLUE). Against that fold this one is **−2 GLUE**, which is the target. `FoldCheck.lean` compiles
(§5).

## 2. What the chain reads (VERIFIED; y3abu-print §2, re-read)

The field's three consumers are in TailZ34: `shimuraFamilyAb_of_U`, `rayClassCMAb_of_leaves` and
`y3Connected_of_leaves`. Two more read it on other branches: grx6ab-print's `x6ModuliWitness_of_coarse` and
elkies-print. Together they read:
* the whole of `R1fpPropsAb`, including the `ℚ̄`-point, which is carried into `ShimuraFamilyAb`, `RayClassCMAb` and
  `Y3ConnectedAb`;
* the lattice-form moduli clause at `g = 1` and at every `u ∈ 𝒪̂^×` (`obj_at`, `shimuraFamilyAb_of_mainThmI`).

Neither can be restricted, so no consumer is re-versioned. Instead, the new leaves prove the field **exactly**:
* the `ℚ̄`-point is reconstructed;
* the kernel's level form is recovered by `toKer`;
* the universal property for kernel-form families is recovered through `ofKer`;
* the lattice form is recovered by `lattice_of_hodge`.

The field's type is unchanged, so no consumer needs a new version.

## 3. The Lean (VERIFIED: every theorem uses only `[propext, Classical.choice, Quot.sound]`)

* §1 `nonempty_qbar_of_cpt`.
* §2 Level structure:
  * `QMAbSchemeNL`: `QMAbScheme` minus `eta_ker`; its other clauses are verbatim.
  * `LevelPrint`, the printed level condition.
  * `QMAbSchemeP`, which extends `QMAbSchemeNL` by `LevelPrint`.
  * `toKer`, `fibre_level`, `charZero_of_pt`, `levelPrint_of_ker`, `ofKer`.
* §3 Clause lists:
  * `R1univAbPropsP` and `R1famAbPropsP`: the same as the kernel's lists, but over `QMAbSchemeP`.
  * `R1fpPropsAbP`: the printed list, **without** the `ℚ̄`-point clause.
  * `R1fpPropsAbNP`: the kernel's list without the point.
  * Conversions between them: `np_of_P` and `P_of_np` (these need `TorsionStructure`), `np_of_ab`, `ab_of_np`.
* §4 `phi_part_np` and `compare_iso_np`. These are elkies-print's pinning, which never used the point.
* §6 `Jmat τ = h_τ(i)`, `IsHodgeH1`, and `ℓ_τ` (`ellE`, `M ↦ M(τ,1)ᵀ`, an `ℝ`-isomorphism `M₂(ℝ) ≅ ℂ²`).
  `ellE_J` gives `ℓ_τ(M J_τ) = i ℓ_τ(M)`. `ellE_iota` gives `ℓ_τ(ι(a)M) = ι(a)ℓ_τ(M)`.
  `Tlin = β ∘ ℓ_τ⁻¹` is `ℂ`-linear. `lattice_of_hodge` takes `Φ = φ ∘ proj ∘ Tlin` and uses the kernel's
  `isUniformization_of_bp`.
* §8 `hodge_of_lattice`, the converse dictionary. Given a lattice-form uniformization `Φu` of `Λ_τ`:
  1. Take bp-analytic's uniformization `(Λ, φ)` from `uniformizationLeafAll_proof` (proved in the tree).
  2. `f = φ⁻¹ ∘ Φu` is continuous, by the open-map clause of `φ` and the differentiability of `Φu`.
  3. `f` factors through `ℂ²/Λ_τ` and lifts to an `ℝ`-linear `T` (`BPAnalytic.exists_realLinear_lift`).
  4. `T` is `ℂ`-linear, by the local-inverse argument of `IsUniformization.exists_complexLinear`.
  5. `T` is injective, because `Λ_τ` is discrete.
  6. `T` is surjective: otherwise a nonzero real functional killing its image would map the countable `Λ` onto
     `ℝ`.
  7. Set `β = T ∘ ℓ_τ`.
* §7 Final assembly:
  * `DeligneBodyAtH` and `ModuliAtUnitsH`: the field's clauses verbatim, with the moduli clause replaced by
    `IsHodgeH1`.
  * `DeligneCanonicalModelY3EveryH`.
  * `body_of_H`, `units_of_H`, `body_H_of`, `units_H_of`, `deligneH_iff_P`.
  * The discharge and `print_iff_field`.

## 4. The new leaves and their ratings

### 4.1 `y3FineModuliAbP`: printed form

```lean
def Y3FineModuliAbP : Prop := ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpPropsAbP Y Φ
```

* **Rating: printed form (LEAF).** It is a consequence of representability:
  * The universal property is used only for proper smooth curves over `ℚ` and is read on field points.
  * The base is `ℚ` instead of `ℤ[1/6]`.
* **Level structure.** The level structure is Mumford's Def. 7.1 form: sections whose values at every geometric
  point form exactly `A_s[3]`. It is stated over the base `S`.
  * The equivalence with an isomorphism of group schemes `(𝒪/3𝒪)_S ≅ A[3]` is Mumford's own remark (the print).
    It is not glue (UNVERIFIED locator).
  * The equivalence with the chain's pointwise form is proved over `ℚ`-schemes (`toKer`, `ofKer`).
* **No `ℚ̄`-point clause.**
* **Sources** (UNVERIFIED): Buzzard, Duke Math. J. 87 (1997) §1; Boutot–Carayol, Astérisque 196-197 Ch. III;
  Milne 1979; Mumford, *GIT*, Def. 7.1 and Thm 7.9.
* **Reading risk.** The moduli problem has no polarization (Lemma P). This is the same for every `R1fpPropsAb` in
  the chain.
* **One object:** `Y₃` with its universal family.
* **Never stronger than the field:** `y3FineModuliAbP_of_field` (it needs `TorsionStructure`).

### 4.2 `deligneCanonicalModelY3EveryH`: printed form, with reading risk

```lean
def DeligneCanonicalModelY3EveryH : Prop :=
  ∀ Y Φ, R1fpPropsAbP Y Φ → ∃ Ψ, DeligneBodyAtH Y Φ Ψ ∧ ModuliAtUnitsH Y Φ Ψ
```

* **Rating: printed form (LEAF), with reading risk.**
* **The moduli clause** is the print's description of `[τ, u]`, `u ∈ 𝒪̂^×`, where `L_u = 𝒪`:
  * `(H₁(A, ℤ), h_A) ≅ (𝒪, h_τ)` as an `𝒪`-module with Hodge structure.
  * `H₁(A, ℤ)` is the lattice `Λ` of an analytic uniformization `A(ℂ) = Lie A / Λ` (bp-analytic's
    `IsUniformization`, the strong, biholomorphic notion).
  * `H₁(A, ℝ) = Lie A`, with its complex structure `i`.
  * This is Mumford, *Abelian varieties*, §1, `H₁(V/Λ, ℤ) = Λ` (STANDARD).
* **The dictionary to the kernel's lattice form is proved both ways** (`hodge_iff_lattice`). So the leaf is
  equivalent to y3abu-print's leaf over the same witnesses, and the identification that locators.md R1 calls
  "qualified" is now a Lean theorem, not an assumption.
* **Other clauses** are verbatim from y3abu-print's leaf, with its consequence weakenings (rayclass-cft §2,
  gt-rayclass §3).
* **Sources** (UNVERIFIED): Deligne, Sém. Bourbaki 389, §4 (moduli interpretation via `H₁` with Hodge
  structure) and §5 (Cor. 5.7 / Ex. 5.8); Milne, ISV, §§8 and 14.
* **Reading risks**, stated in the flag:
  1. locators.md R1: the print treats the polarized PEL problem over `E(G, X) = ℚ`.
  2. The sign convention `h_τ(i) = J_τ` versus `−J_τ` in Deligne's normalization of `h` is unchecked. y3abu-print's
     lattice form already took the `+` convention.
  3. Milne §8 and §14 are read as one statement.
* **One object:** `Y₃ = Sh_{K₃}`.
* **No existence claim.** The leaf now also guarantees that `Y(ℂ)` is nonempty, through `Ψ`. That is part of the
  print, since `Sh_K(ℂ) ≠ ∅`.
* **Never stronger than the field:** `print_iff_field` (it uses `deligneP_of_field`, `compare_iso_np` and
  `hodge_of_lattice`).

### 4.3 The textbook input

`mumfordTorsionAlgClosed` is already a LEAF field of the textbook bundle, and the proof reads it as
`{t}.mumfordTorsionAlgClosed`. It is not a new leaf.

## 5. Checks (VERIFIED)

* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ShimuraY3PrintedLeaves`:
  success, 14229 jobs (`scratch/y3-fix/build1.txt`). `frozenTarget` uses only the standard axioms.
* `#discharges` (`scratch/y3-fix/discharges.txt`):
  ```
  DISCHARGES [OpenResearchLeaves31.shimuraMainThmIDeligneY3AbU] by Y3Fix.shimuraMainThmIDeligneY3AbU_of_print
    still assumes: [AvSplit.MumfordTorsionAlgClosed, Y3Fix.Y3FineModuliAbP, Y3Fix.DeligneCanonicalModelY3EveryH]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 35 open hypotheses, 9889 theorems checked, 36 discharge one
  ```
  (The intermediate `Y3Fix.field_of_printP` also discharges the field.)
* Autofold spec: `scratch/y3-fix/autofold.json`.
  * It discharges `shimuraMainThmIDeligneY3AbU` by
    `_root_.Y3Fix.shimuraMainThmIDeligneY3AbU_of_print {t}.mumfordTorsionAlgClosed {n}.y3FineModuliAbP {n}.deligneCanonicalModelY3EveryH`.
  * The new leaves `y3FineModuliAbP` and `deligneCanonicalModelY3EveryH` are kind `published`, flagged
    "locator UNVERIFIED; reading risk: …".
  * `--dry-run` (`autofold-dryrun.txt`): **11/18 on 29 → 13/17 on 30** (strict and strictest).
  * `FoldCheck.lean` (the dry-run output minus line 1) compiles. `HDec.HSyn.sixContactMin_of_open49` uses only the
    standard axioms (`foldcheck.txt`).
* **For the integrator:**
  * This spec supersedes y3abu-print's. Fold this one instead.
  * The grx6ab-print and elkies-print specs read `{n}.shimuraMainThmIDeligneY3AbU`. Patch them as y3abu-print §6
    did, with the argument
    `(_root_.Y3Fix.shimuraMainThmIDeligneY3AbU_of_print {t}.mumfordTorsionAlgClosed {n}.y3FineModuliAbP {n}.deligneCanonicalModelY3EveryH)`.
    The combined fold was not run here.
  * New rows for locators.md:
    * R1 "fine moduli of QM abelian surfaces, level 3, Mumford level form": Buzzard 1997 §1; Mumford GIT Def. 7.1
      and Thm 7.9; unread.
    * R1 "canonical model and PEL moduli, H₁ form": the existing row.

## 6. Status

* **Done and compiled:**
  * the contributor file;
  * both dictionaries (the level structure; lattice and H₁);
  * the discharge and its converse;
  * `#discharges`;
  * the solo fold check.
* **Not done:**
  * locator readings (no network);
  * the combined fold with grx6ab-print and elkies-print (spec patch described above, not run);
  * a check of the sign convention of `h_τ`.
