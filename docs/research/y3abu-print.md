# y3abu-print: `shimuraMainThmIDeligneY3AbU` from two printed statements, one object each

Task y3abu-print (2026-11-16/17). Base: fork main c1e4ed1b (leaf-fold32, top `sixContactMin_of_open38`, TailZ45). For
the combined fold (§6), origin/wip/grx6ab-print b047ce25 is merged; it already contains elkies-print and gr-dict.
Contributor file: `ZInQKernel/Contrib/OneProof/ShimuraY3Print.lean`, namespace `Y3ABUPrint`. It imports only
`…RayClassShimura`, the module that defines the field, never `Main`, and has no `sorry`. Scratch: `scratch/y3abu-print/`
(log: `log.md`). Marks: VERIFIED (compiled, or read in the tree), STANDARD (published, exact reference), SPECULATIVE,
UNVERIFIED (theorem numbers recalled; no network on this host).

## 1. Result

**The composite research field `shimuraMainThmIDeligneY3AbU` (GLUE) is proved in Lean from two new printed-form
leaves. Each leaf is about one object, and together they are equivalent to the field:**

```
Y3ABUPrint.shimuraMainThmIDeligneY3AbU_of_print :
  Y3ABUPrint.Y3FineModuliAb → Y3ABUPrint.DeligneCanonicalModelY3Every → RayClassCFT.ShimuraMainThmIDeligneY3AbU
Y3ABUPrint.print_iff_field :
  (Y3FineModuliAb ∧ DeligneCanonicalModelY3Every) ↔ RayClassCFT.ShimuraMainThmIDeligneY3AbU
```

| new leaf | statement | object | printed form? |
|---|---|---|---|
| `y3FineModuliAb` | `∃ Y Φ, R1fpPropsAb Y Φ` | the fine moduli scheme `Y₃/ℚ` with its universal family | **yes, a consequence of representability** (§4.1); locator UNVERIFIED; reading risk: no polarization |
| `deligneCanonicalModelY3Every` | `∀ Y Φ, R1fpPropsAb Y Φ → ∃ Ψ, DeligneBodyAt Y Φ Ψ ∧ ModuliAtUnits Y Φ Ψ` (the field's body, verbatim, on **every** witness; no existence claim) | `Y₃ = Sh_{K₃}(B^×, ℍ^±)`, the canonical model | **yes, with reading risk** (§4.2); locator UNVERIFIED |

**Count** (autofold `--dry-run`, VERIFIED): strict **16/21 on 37 → 18/20 on 38**; strictest 16/21 → 18/20.
That is **−1 GLUE**, provided both leaves count as published (they are flagged "locator UNVERIFIED; reading risk",
which autofold counts LEAF). If a reviewer instead rates `deligneCanonicalModelY3Every` composite (moduli
interpretation plus canonical-model property, §4.2), the fold is count-neutral.

Combined with grx6ab-print and elkies-print (§6): **16/21 on 37 → 21/18 on 39 (−3 GLUE)**. FoldCheckCombined
compiles (§6).

## 2. What the field asserts, and what the chain reads (VERIFIED, read at c1e4ed1b)

`ShimuraMainThmIDeligneY3AbU := ∃ Y Φ, R1fpPropsAb Y Φ ∧ ∃ Ψ, DeligneBodyAt Y Φ Ψ ∧ ModuliAtUnits Y Φ Ψ`
(`RayClassShimura.lean:1152`). It is read by three consumers, all in TailZ34; TailZ35-45 only pass it on:
* L81 `RayClassCFT.shimuraFamilyAb_of_U`;
* L101 `rayClassCMAb_of_leaves`;
* L148 `DCY3Used.y3Connected_of_leaves`.

It is also read on the pending branch wip/grx6ab-print, by `GRX6AbPrint.x6ModuliWitness_of_coarse`, which takes
only `(Y, Φ, R1fpPropsAb)`.

| clause | content | read by |
|---|---|---|
| (R) `R1fpPropsAb Y Φ` | proper smooth curve with a `ℚ̄`-point; natural moduli bijections `Φ`; universal QM abelian scheme with level 3; classifying maps over proper smooth curves | carried into the conclusions `ShimuraFamilyAb`, `RayClassCMAb`, `Y3ConnectedAb` (each `∃ Y Φ, R1fpPropsAb ∧ …`); naturality read by `obj_at`; all of it read by `x6ModuliWitness_of_coarse` |
| 1a | `Ψ` onto | `embed_core` (RayClassShimura L1377), `connected_of_body` |
| 1b⇐ | `DCRel τ g τ' g' → Ψ τ g = Ψ τ' g'` | `embed_core` L1380, L1439; `connected_of_body` (DCY3Used L634) |
| 1b⇒ | `Ψ τ g = Ψ τ' g' → DCRel …` (injectivity modulo the double coset) | **unread** (only `.2` of the iff is ever applied) |
| 2 | `τ ↦ Ψ(τ, g)` holomorphic, every `g` | only the open-preimage half `(hhol g).1` (`connected_of_body`); the analytic half is unread for `g ≠ 1` |
| 3 | `IsShimuraHolFamily Y Φ (Ψ · 1)` (moduli clause and full holomorphy at `g = 1`) | `shimuraFamilyAb_of_mainThmI` |
| 4 | Shimura's reciprocity law at CM points | `embed_core`, `connected_of_body` |
| U | `ModuliAtUnits` (the QM torus at every `u ∈ 𝒪̂^×`) | `obj_at` |

**Narrowing not done.** Two parts are unread: 1b⇒ and the analytic half of 2 for `g ≠ 1`. A narrowed field without
them is a weaker consequence of the same printed theorem, so it would not change any rating. Folding it would take
autofold's weaker-leaf bypass: the field's three consumers sit in TailZ34, eleven generations below the top, so the
chain would have to be regenerated as raynaud-narrow did. That costs a lot and gains no count, so the full clause
list is kept. The new leaves prove the field exactly.

## 3. The decomposition and the Lean (VERIFIED, standard axioms)

`ShimuraY3Print.lean` (≈ 240 lines):
* `Y3FineModuliAb`, `DeligneCanonicalModelY3Every`: the two leaves, with docstrings giving source, form and reading
  risk.
* `shimuraMainThmIDeligneY3AbU_of_print`: the discharge. Take the witness from the first leaf, apply the second
  leaf to it.
* `y3FineModuliAb_of_field`: the first leaf is a projection of the field.
* `deligneCanonicalModelY3Every_of_field`: **the every-witness leaf is no stronger than the field.** Two witnesses
  of `R1fpPropsAb` are isomorphic compatibly with `Φ` (`compare_iso_ab`, elkies-print's proof copied verbatim, with
  `phi_part_ab`; it uses `R1univAbProps`, `R1famAbProps`, properness, smoothness and the kernel's
  `eq_id_of_fieldPts`). Each clause transports along such an iso `k` with `Ψ' = Ψ ≫ k⁻¹` (`body_transport`):
  * surjectivity and fibres (`k` is an iso);
  * the moduli clauses (`Φ'(y ≫ k⁻¹) = Φ y`);
  * reciprocity (`galPt σ` is precomposition, so it commutes with `≫ k⁻¹`);
  * holomorphy, through the new lemmas `ptC_comp`, `regVal_comp` (`f(h ∘ y) = (h^* f)(y)`, from the kernel's
    `specToEquivOfField_comp_right` and Mathlib's `Scheme.evaluation_naturality_apply`) and `isHolFamily_comp` (a
    holomorphic family composed with any morphism of schemes is holomorphic).
* `print_iff_field`: the two leaves together are equivalent to the field.

Checks (VERIFIED):
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ShimuraY3Print`
  succeeds (14102 jobs, `build-summary.txt`), with `frozenTarget` on the standard axioms.
* All four theorems depend on `[propext, Classical.choice, Quot.sound]`.

## 4. The new leaves and their ratings

### 4.1 `y3FineModuliAb` — printed form (consequence of representability)

```lean
def Y3FineModuliAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ
```

* *The print*: the moduli functor of abelian surfaces `A/S` with `ι : 𝒪 → End_S(A)` and an `𝒪`-linear full
  level-3 structure `(𝒪/3𝒪)_S ≅ A[3]` is represented by a smooth projective curve (proper since `B` is a division
  algebra). Sources: Buzzard, *Integral models of certain Shimura curves*, Duke Math. J. 87 (1997) §1, over
  `ℤ[1/ND]`; Boutot–Carayol, Astérisque 196-197 (1991) Ch. III; Milne 1979 (Corvallis); Mumford GIT Thm 7.9 for
  level `≥ 3`. Numbers and pages UNVERIFIED (no network).
* *Why it is a consequence, not stronger*:
  * `Φ` is the representing bijection on field points, and natural in the field;
  * `R1famAbProps` is the universal object;
  * `R1univAbProps` is the universal property, used only for bases that are proper smooth curves over `ℚ`, and
    read on field points;
  * the `ℚ̄`-point exists because `Y₃` is nonempty;
  * the base is `ℚ` instead of `ℤ[1/6]`.
* *One object*: `Y₃` and its universal family. The leaf asserts nothing about the complex uniformization or Galois
  action.
* *Over genuine definitions*: Mathlib schemes and the kernel's `QMAbScheme`, `QML3`, `IsFibreOf`, the same objects
  as every existing `R1fpPropsAb` use.
* *Reading risk*: the kernel's moduli problem has no polarization (Lemma P, `QML3` docstring). Buzzard is recalled
  as stating the polarization-free problem, while Milne 1979 and Boutot–Carayol include it (UNVERIFIED). This is the
  same reading every `R1fpPropsAb` clause list in the chain already uses.
* *Never stronger than the field*: `y3FineModuliAb_of_field`.

### 4.2 `deligneCanonicalModelY3Every` — printed form, with reading risk

```lean
def DeligneCanonicalModelY3Every : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ →
    ∃ Ψ, DeligneBodyAt Y Φ Ψ ∧ ModuliAtUnits Y Φ Ψ
```

* *The print*: Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), §§4-5, states that the PEL moduli scheme,
  with the moduli interpretation of its complex points, is the canonical model of `Sh_K(G, X)` over the reflex
  field. locators.md row R1 records Cor. 5.7 / Ex. 5.8 as read by the audit, as a "qualified consequence". Here
  `G = B^×`, `E = ℚ`, `K = K₃`. Also Milne, *Introduction to Shimura varieties*, §8 (moduli interpretation) and §14
  (the PEL moduli variety is the canonical model); Shimura, Ann. of Math. 85 (1967), Main Theorem I. Numbers
  UNVERIFIED.
* *Why it is a consequence*: these are rayclass-cft's and gt-rayclass's reasons, unchanged:
  * the biholomorphism is weakened to "bijective, holomorphic in `τ`";
  * the moduli clause is kept only at `g ∈ 𝒪̂^×`, where `L_u = B ∩ 𝒪̂u⁻¹ = 𝒪`, and describes only the QM pair;
  * the conventions `ε`, `δ` are existential;
  * `ℍ` with `B^×_+` replaces `ℍ^±` with `B^×`;
  * the field-of-moduli clause is dropped.
* *Every-witness form*: this form is a consequence of the print on the moduli scheme. Any `(Y, Φ)` with
  `R1fpPropsAb` is isomorphic to it compatibly with `Φ`, and the clauses transport. Both steps are proved in Lean:
  `deligneCanonicalModelY3Every_of_field` derives the leaf from the field, so the leaf is **never stronger than the
  field it replaces**.
* *One object*: `Y₃ = Sh_{K₃}` with its identification `Y₃(ℂ) = Sh_{K₃}(ℂ)` and the canonical-model property. There
  is no existence claim: the witness comes from `y3FineModuliAb`.
* *Reading risks*: the flag says these explicitly.
  1. **R1 qualifications** (locators.md). The print is for the polarized PEL problem with polarization-compatible
     level structure. Lemma P bridges the gap to the polarization-free moduli. `E(G, X) = ℚ`, and two geometric
     components over `ℚ`.
  2. **One theorem or two.** Milne separates the moduli interpretation of `Sh_K(ℂ)` (§8) from the canonical-model
     theorem (§14). The leaf reads §14 as a statement about the moduli scheme *with* the §8 identification, which is
     how §14 is formulated. A reviewer who counts §8 and §14 as two theorems rates the leaf composite, and the fold
     is then count-neutral.
* *Why a three-leaf split is not offered*: the split would be "moduli interpretation ∃Ψ" plus "reciprocity for
  every such Ψ". gt-rayclass §3 gave a counterexample: a right translation `Ψ'(τ, g) = Ψ(τ, g k)` applied on one
  geometric component only keeps clauses 1-3 and U, but breaks 4. Re-checked here (SPECULATIVE, standard): `K₃` is
  normal in `𝒪̂^×` and `DCRel` preserves `nrd g mod 3`. A reciprocity leaf over every `Ψ` would therefore need the
  moduli clause to pin the **level structure** at `Ψ(τ, u)`. In Deligne's normalization that is
  `η_u(a) = (1/3) ι(a u⁻¹)(τ, 1)ᵀ mod Λ_τ`; the inverse is forced by consistency with `DCRel` at units `γ ∈ 𝒪^×_+`
  (the `u` convention fails that check). Writing this needs `u mod 3` for adelic units, and it would make the leaf
  depend on a convention choice that cannot be checked without the print. Proving that such a leaf is never
  stronger would also need the uniqueness of the pinned `Ψ` (analytic). Left as a proposal; not folded.

## 5. `#discharges` (VERIFIED, `scratch/y3abu-print/discharges.txt`)

```
DISCHARGES [OpenResearchLeaves28.shimuraMainThmIDeligneY3AbU] by Y3ABUPrint.shimuraMainThmIDeligneY3AbU_of_print
  still assumes: [Y3ABUPrint.Y3FineModuliAb, Y3ABUPrint.DeligneCanonicalModelY3Every]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 45 open hypotheses, 6687 theorems checked, 14 discharge one
```

## 6. Autofold

* **Solo** (`scratch/y3abu-print/autofold.json`):
  * discharges `shimuraMainThmIDeligneY3AbU` by
    `_root_.Y3ABUPrint.shimuraMainThmIDeligneY3AbU_of_print {n}.y3FineModuliAb {n}.deligneCanonicalModelY3Every`;
  * adds the leaves `y3FineModuliAb` and `deligneCanonicalModelY3Every`, kind `published`, flags
    "locator UNVERIFIED; reading risk: …";
  * `--dry-run` (`autofold-dryrun.txt`): strict 16/21 on 37 → 18/20 on 38, strictest the same (−1 GLUE);
  * `FoldCheck.lean` (the dry-run output minus line 1) compiles: `sixContactMin_of_open39` uses the standard axioms
    (`foldcheck.txt`).
* **Combined with grx6ab-print and elkies-print** (`autofold-combined.json`; origin/wip/grx6ab-print merged):
  * Their two specs read `{n}.shimuraMainThmIDeligneY3AbU`, which this fold removes. Here that argument is replaced
    by `(Y3ABUPrint.shimuraMainThmIDeligneY3AbU_of_print {n}.y3FineModuliAb {n}.deligneCanonicalModelY3Every)`.
  * `x6ModuliWitness_of_coarse` reads only the `R1fpPropsAb` witness, so `y3FineModuliAb` is the single source of
    `Y₃` for all three folds.
  * `--dry-run`: **16/21 on 37 → 21/18 on 39 (−3 GLUE)**.
  * After `lake build` of `GRX6AbPrint`, `ElkiesX6StarEvery` and `ShimuraY3Print` (13023 jobs, success),
    `FoldCheckCombined.lean` compiles: `sixContactMin_of_open39` uses the standard axioms
    (`foldcheck-combined.txt`, VERIFIED).
* **For the integrator**: use the combined spec, or land this fold first and patch the other two specs the same
  way. Rows for `docs/research/locators.md` (two new leaves): R1 "fine moduli of QM abelian surfaces, level 3"
  (Buzzard 1997 §1; unread) and R1 "canonical model and PEL moduli" (existing row; this leaf is its every-witness
  form).

## 7. Status

* Compiled and checked (VERIFIED): the contributor file; `#discharges`; the solo fold check; the combined fold
  check with grx6ab-print and elkies-print.
* Not done: locator reading (no network). The three-leaf split with a pinned level structure (§4.2) is a proposal
  only.
