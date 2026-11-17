# y3-hodge: `deligneCanonicalModelY3EveryH` restated as its print; the review's gaps closed in Lean

Task y3-hodge (2026-11-17). Base: wip/leaf-fold33b 6b97a5c7 (top `sixContactMin_of_open60`, TailZ67).
Contributor file (new; no existing file edited): `ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean`, namespace `Y3Hodge`.
It imports `ShimuraY3PrintedLeaves` (y3-fix) and `CloudB3W17Hodge.Bridge`, never `Main`, and has no `sorry`. It is
byte-identical to `scratch/y3-hodge/Hodge.lean`. Log: `scratch/y3-hodge/log.md`.

Marks used below:
* VERIFIED: compiled, or read in the tree.
* STANDARD: published, exact reference.
* UNVERIFIED: a locator recalled from memory (there is no network on this host).

## 1. Result

**The review's three gaps (queue11 verdict: consequence, GLUE) and the sign check are all closed by Lean proofs. The
leaf is restated as its print, `Y3Hodge.DeligneCanonicalModelY3EveryPrint`, and the new leaf is proved *equivalent*
to the old one (VERIFIED, standard axioms):**

```
Y3Hodge.deligneH_of_print   : DeligneCanonicalModelY3EveryPrint → Y3Fix.DeligneCanonicalModelY3EveryH
Y3Hodge.print_iff_deligneH  : DeligneCanonicalModelY3EveryPrint ↔ Y3Fix.DeligneCanonicalModelY3EveryH
Y3Hodge.printPM_iff_field (hM : AvSplit.MumfordTorsionAlgClosed) :
  (Y3Fix.Y3FineModuliAbP ∧ DeligneCanonicalModelY3EveryPrint) ↔ RayClassCFT.ShimuraMainThmIDeligneY3AbU
```

| review item | what is proved (Lean, §3) |
|---|---|
| (1) the print's `H₁(A, ℤ)` reaches `IsHodgeH1` | `print_iff_hodge : IsHodgeH1Print P τ ↔ Y3Fix.IsHodgeH1 P τ`. Here `IsHodgeH1Print` is the moduli clause over genuine `H₁(A(ℂ), ℤ) = π₁(A(ℂ), 0)ᵃᵇ`, with `Lie A` given through `exp_A` and the `𝒪`-action on `H₁` by functoriality. |
| (2) Lemma P beyond the lattice-only form | `lemmaP_H1`: on the genuine `H₁(A(ℂ), ℤ)` there is **exactly one** principal Riemann form of type `μ` (with the genuine `ι_A`-action and the genuine complex structure), and it is `E₀` under the print's identification. |
| (3) `ℍ^±` with `B^×` versus `ℍ` with `B^×_+` | `dcRelPM_iff` (on `ℍ` the print's relation is `DCRel`), `exists_upper` (`ℍ⁻` is moved to `ℍ` by `μ = 1+i`), and the retraction lemmas `rel_rPM` and `dcRelPM_left/right`. |
| sign of `h`, `B` versus `B^op` | `F0_iff`, `iota_mul_Jmat`, `adjugate_Jmat`, `Jmat_sq`. **The leaf's sign is correct; no statement change.** |

**Count.** autofold `--dry-run` (VERIFIED): strict **11/23 on 34 → 11/23 on 34**, strictest **10/24 → 10/24**.
* The new leaf has kind `consequence` and the flag "pending review (new leaf, GLUE until a reviewer rates it) …", so
  autofold scores it GLUE, the same as the row it replaces.
* The target **−1 strict GLUE** is reached when a reviewer re-rates the new row LEAF. The gaps the reviewer named are
  now Lean theorems; what remains is listed in §4.2.

## 2. The statements (VERIFIED, read in the compiled file)

* `H1 A := Abelianization (FundamentalGroup (A.Pt ℂ) 1)`. The topology is `CloudB3W17Hodge.classicalTopology`, which
  `CloudB3W17Hodge.classicalTopology_eq` identifies with the ported analytic topology of the complex manifold `X(ℂ)`.
* `loopClass ℓ` is the class of a loop. `pushLoop f ℓ = [t ↦ f(ℓ(t))]`. `h1Act f : H1 A →* H1 A` is the
  functoriality of `π₁` (Mathlib's `FundamentalGroup.mapOfEq`) and of the abelianization; `h1Act_loopClass` computes
  it on loops.
* **`IsHodgeH1Print P τ`** asks for data `(n, e, β, c)` (`HodgeData`) such that:
  * `e : ℂⁿ → A(ℂ)` is a holomorphic homomorphism (`IsAnalyticHom`), i.e. `e = exp_A ∘ L`;
  * `β : M₂(ℝ) ≃ₗ[ℝ] ℂⁿ`;
  * `c b = [t ↦ e(t β(ι b))]`, and `b ↦ loopClass (c b)` is a bijection `𝒪 → H₁(A(ℂ), ℤ)`;
  * `ι_A(a)_* c(b) = c(ab)`;
  * `β(M J_τ) = i β(M)`.

  Together these say "`(H₁(A, ℤ), ι_*, h_A) ≅ (𝒪, left multiplication, h_τ)`".
* **`DCRelPM z g z' g'`** on `ℍ^± × (B ⊗ 𝔸_f)^×`, with `ℍ^± = {z : ℂ // z.im ≠ 0}`: there are `γ ∈ B` with
  `nrd γ ≠ 0` (either sign) and `k ∈ K₃` such that `z' = ι(γ)·z` (Möbius) and `g' = γ g k`. This is the print's
  `B^× \ (ℍ^± × G(𝔸_f) / K₃)`.
* **`DeligneCanonicalModelY3EveryPrint`**: for every `(Y, Φ)` with `Y3Fix.R1fpPropsAbP Y Φ` there is
  `Ψ : ℍ^± → (B ⊗ 𝔸_f)^× → Y(ℂ)` with these clauses:
  1. `Ψ` is onto;
  2. `Ψ z g = Ψ z' g' ↔ DCRelPM z g z' g'`;
  3. `τ ↦ Ψ(τ, g)` is holomorphic on `ℍ` for every `g`;
  4. at `g = 1`, the fibre is `IsHodgeH1Print`;
  5. reciprocity at CM points of `ℍ` (y3-fix's clause, verbatim);
  6. at `[τ, u]`, `u ∈ 𝒪̂^×`, the fibre is `IsHodgeH1Print P τ`.

  The only changes from the old leaf are the domain `ℍ^±` with `DCRelPM`, and `IsHodgeH1Print` in place of
  `IsHodgeH1`.
* **`IsPrincipalRiemannMu β c E`**, for `E : H₁ → H₁ → ℤ`:
  * `E` is biadditive and alternating;
  * `E(ι_A(a)_* x, y) = E(x, ι_A(a†)_* y)`, with `a† = μ⁻¹ā μ` (`dagO`);
  * its Gram determinant on the `ℤ`-basis `c(1), c(i), c((1+j)/2), c((i+k)/2)` is `1`;
  * there is an `ℝ`-bilinear `F` on `ℂⁿ = Lie A` that extends `E` through `β`, `c`, satisfies `F(iv, iw) = F(v, w)`,
    and has `F(iv, v) > 0` for `v ≠ 0` (Mumford's sign convention for Riemann forms).

## 3. The proofs, by item (VERIFIED: compiled; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`)

### 3.1 Item (1): `H₁(A(ℂ), ℤ)` and the period lattice

* **Port.** pel-hodge's `h1Form_iff` (`origin/wip/pel-hodge`, not on this base) is ported onto the base's
  `CloudB3W17Hodge` copies of unif-printed's definitions.
  * The uniformization is a homeomorphism for the classical topology (`phiHomeo`).
  * `φ ∘ proj` is a quotient covering map (`isCov`).
  * Mathlib's monodromy `IsAddQuotientCoveringMap.fundamentalGroupToMulOpposite` is injective, and a rank count
    finishes the argument.
* **New: `continuous_postcomp`.** A morphism of `ℂ`-schemes is continuous on `ℂ`-points, by `Scheme.Hom.comp_appLE`.
  This gives `pushLoop` and `h1Act`.
* **New: `continuous_of_isAnalyticHom`.**
* **`lattice_of_print`.**
  1. Set `Φu = e ∘ T`, with `T = β ∘ ℓ_τ⁻¹`, which is `ℂ`-linear (y3-fix's `Tlin`).
  2. `𝒪 ≅ Λ_τ` (`bOf_bijective`, using `RayClassCFT.iota_eig_inj`) combined with `𝒪 ≅ H₁` gives
     `IsUniformization Λ_τ Φu`, through `isUniformization_of_H1`.
  3. The `𝒪`-linearity on `H₁` gives `ι`-compatibility:
     * `z ↦ Φu(ι(a) z)` and `z ↦ ι_A(a)(Φu z)` are analytic homomorphisms (`isAnalyticHom_lin`, `isAnalyticHom_comp`),
       so they equal `pmap φ ∘ D₁` and `pmap φ ∘ D₂` with `D₁`, `D₂` `ℂ`-linear;
     * the monodromies of `c(ab)` and of `ι_A(a)_* c(b)` are `D₁ v` and `D₂ v`;
     * so `D₁ = D₂` on the full lattice `Λ_τ`, hence everywhere (`LinearMap.ext_on`).
* **`print_of_lattice`** is the converse: take `β = ℓ_τ`, and `ι_A(a)_* c(b) = c(ab)` holds already as loops.
* **`print_iff_hodge`** combines these with y3-fix's `hodge_iff_lattice`.

### 3.2 Item (2): Lemma P on the genuine `H₁`

* **What was there before.** y3abu-strict's `lemmaP_lattice_unique` and `lemmaP_qmTorus` live on `(B, ·j)` and on
  `ℂ²/Λ_τ` in lattice coordinates (`origin/wip/y3abu-strict`). Its helpers `ι_ℝ` and `j_τ` are copied verbatim into
  namespace `Y3Hodge.LP`.
* **Uniqueness: `eq_E0_of_principalRiemann`.**
  1. `c` is additive (`cl_add`): straight loops add, because monodromy is an injective homomorphism (`loopClass_add`).
  2. The argument of `RvQMPolar.eq_smul_E0` is run on `𝒪`:
     * `E(x, y) = f(x†y)`;
     * alternation at `1, 1+i, 1+j ∈ 𝒪` gives `f(1) = f(i) = f(j) + f(k) = 0`;
     * `f(z) = (z_j − z_k) f(j)` on `𝒪`, via `2z ∈ ℤ⟨1, i, j, k⟩`;
     * so `E = r E₀`.
  3. Principal: `det(r · gram) = r⁴ = 1`, so `r = ±1`.
  4. The real extension `F ∘ β ∘ ι_ℝ` is `r · E₀ ⊗ ℝ`. The two agree on `basisOneIJK`, whose vectors `1, i, j, k` lie
     in `𝒪` (`LinearMap.BilinForm.ext_basis`).
  5. Positivity at `x = 1` reads `F(i v, v) = r E₀(j_τ, 1) > 0`. `RvQMPolar.riemann_sign` with `imJ(j_τ) > 0` then
     gives `r = 1`.
* **Existence: `exists_principalRiemann`.**
  * `E := E₀ ∘ c⁻¹`, which is `ℤ`-valued (`E0_int`).
  * `F := E₀ ⊗ ℝ ∘ ι_ℝ⁻¹ ∘ β⁻¹`, where `ι_ℝ : B_ℝ ≅ M₂(ℝ)` (`iotaRE`, by `iotaR_injective` and dimension 4).
  * `F` is `i`-invariant by `RvQMPolar.E0R_mul_j`, and positive by `riemann_sign`.
* **`lemmaP_H1` / `lemmaP_of_isHodgeH1Print`: `∃!` together with "it is `E₀`".**
* **Consequence for the print** (argument, not Lean).
  * The print parametrizes polarized points `(A, ι, λ, η)`. By Riemann's theorem, polarizations of `A` are Riemann
    forms on `H₁(A, ℤ)` (Mumford, *Abelian varieties*, §§2–3, STANDARD; not statable in Mathlib, which has no dual
    abelian variety).
  * So at every complex point with the print's `H₁` description, the polarization of type `μ` exists, is unique, and
    is `ψ = E₀`. The forgetful map from the print's points to the leaf's polarization-free points is a bijection over
    `ℂ`.
  * The PEL compatibility of the level structure is automatic: y3abu-strict's `eq_smul_E0K` (alternating `†`-forms
    are multiples of `E₀`). It is not copied here.

### 3.3 Item (3): `ℍ^±` with `B^×` versus `ℍ` with `B^×_+`

* `im_num_div_denom`: `Im((az + b)/(cz + d)) = det · Im z / |cz + d|²`.
* `dcRelPM_iff`: if `γz ∈ ℍ` for some `z ∈ ℍ`, then `nrd γ > 0`, since `det ι(γ) = nrd γ` (`RayClassCFT.det_iota`).
  Conversely `DCRel ⊆ DCRelPM` (`coe_smul_of_det_pos`).
* `exists_upper`: `μ = 1 + i ∈ 𝒪^×` has `nrd μ = −1` and swaps the half planes.
* For the converse:
  * `mobPM_mul` (Möbius composition on `ℍ^±`) and `iotaGL_mul`;
  * `dcRelPM_left/right` (moving either point by a unit does not change the relation);
  * the retraction `rPM` (`(z, g) ↦ (μz, μg)` on `ℍ⁻`) with `rel_rPM`.

  No subgroup property of `K₃` is needed.

### 3.4 The sign of `h`, and `B` versus `B^op`

* **`F0_iff`.** `{M ∈ M₂(ℂ) : M J_τ = −i M} = {M : M (τ, 1)ᵀ = 0}`.
  * In Deligne's convention, where `h(z)` acts on `V^{p,q}` by `z^{-p} z̄^{-q}` (Deligne, *Variétés de Shimura*, 1.1.1,
    UNVERIFIED locator), this space is `F⁰ = V^{0,-1}` for `h_τ(i)` = right multiplication by `J_τ`.
  * It depends holomorphically on `τ`.
  * `V_ℂ/F⁰ ≅ ℂ²` via `M ↦ M(τ, 1)ᵀ`, which restricts to `ℓ_τ` on `V_ℝ`. So `Lie A = V_ℂ/F⁰`, with lattice
    `ℓ_τ(𝒪) = Λ_τ`.
  * Hence the leaf's sign `β(M J_τ) = i β(M)` is exactly the one for which `τ ↦ [h_τ]` is holomorphic, i.e. the
    complex structure the print puts on `X⁺`. The opposite sign would make the family antiholomorphic and contradict
    the holomorphy clause.
* **`iota_mul_Jmat`.** `ι(γ) J_τ = J_{γτ} ι(γ)` for `nrd γ > 0`. Right multiplication by `ι(γ)⁻¹` therefore carries
  the Hodge datum at `(τ, g)` to the one at `(γτ, γg)` (`L_{γg} = L_g γ⁻¹`), which is consistent with `DCRel`.
* **`adjugate_Jmat`.** `J̄_τ = −J_τ`.
* **The `B` versus `B^op` dictionary.** The leaf lets `𝒪` act on the left of `V = B` and `h` act by right
  multiplication. That is `G = GL_B(B)`, identified with `B^×` by `b ↦ (v ↦ v b⁻¹)`, which gives `L_g = B ∩ 𝒪̂ g⁻¹`
  (as y3abu-strict found). With Deligne's/Milne's `G = B^×` acting by left multiplication and `𝒪` on the right,
  transport by the canonical involution turns right multiplication by `J_τ` into left multiplication by
  `J̄_τ = −J_τ`. So `h_x(i) = −J_τ` in that convention, and y3-fix's docstring phrase "`h_τ(i) = J_τ`" refers to the
  right-multiplication normalization.
* **Verdict.** The *statement* is correct in either convention (VERIFIED as Lean facts plus the STANDARD convention);
  no corrected statement is needed.

## 4. The new leaf and its rating

### 4.1 `deligneCanonicalModelY3EveryPrint`

* **Kind:** `consequence`.
* **Flag:** "pending review (new leaf, GLUE until a reviewer rates it): …". autofold scores it GLUE.
* **Sources** (UNVERIFIED locators):
  * Shimura, Ann. of Math. 85 (1967), Main Theorem I;
  * Deligne, *Travaux de Shimura*, Sém. Bourbaki 389, §4 (`Sh_K(ℂ) = G(ℚ)\X × G(𝔸_f)/K` with the `H₁` moduli
    description) and §5 (Cor. 5.7 / Ex. 5.8);
  * Milne, *Introduction to Shimura varieties*, §§5–8 and 12–14.
* **It is the print, except for these consequence weakenings, which are unchanged from y3-fix:**
  * bijective and holomorphic in place of the biholomorphism;
  * the moduli clause only at `𝒪̂^×`, without polarization and level structure (the polarization exists and is unique
    by `lemmaP_H1`);
  * reciprocity only at CM points of `ℍ`;
  * conventions `ε`, `δ` existential.
* **It is not stronger than the old leaf:** `print_iff_deligneH`.

### 4.2 What remains for a reviewer (reading risks; none is a Lean gap of this leaf)

1. **locators.md R1: the print treats the polarized PEL problem.** The leaf quantifies over polarization-free
   witnesses `(Y, Φ)` of `R1fpPropsAbP`. Passing from the print's `M_PEL` to `Y` needs three things:
   * the forgetful morphism `M_PEL → Y`, which comes from `Y`'s universal property applied to the PEL universal family
     (a `QMAbSchemeP` over a proper smooth curve over `ℚ`; the PEL level structure is `LevelPrint` by `eq_smul_E0K`);
   * that this morphism is bijective on `ℂ`-points, which is Lemma P over `ℂ` (`lemmaP_H1` plus Riemann's theorem,
     STANDARD);
   * that holomorphy and the Galois action transfer along a `ℚ`-morphism.

   The relative Lemma P (over bases) concerns `y3FineModuliAbP`, not this leaf.
2. Milne §8 (moduli interpretation) and §14 (canonical model) are still read as one statement. y3abu-strict's split
   (`DeligneModuliY3Every` / `DeligneReciprocityY3Every`) is on another branch and not combined here.
3. The locators are unread (no network).

## 5. Checks (VERIFIED)

* **Scratch compile.** `lake env lean scratch/y3-hodge/Hodge.lean`: no errors. The build tree was copied with reflinks
  from `~/dzq-wt/h21-gchar`, whose tree is this base plus two unrelated files.
* **Module build.** `lake build ZInQKernel.Contrib.OneProof.Y3HodgePrint` succeeds (12983 jobs).
  `lake build ZInQKernel.OneProof.Discharges ZInQKernel.OneProof.Main` succeeds (16073 jobs); `frozenTarget` uses only
  the standard axioms.
* **`#discharges`** (`scratch/y3-hodge/Discharges.lean`, output in `discharges.txt`):
  ```
  DISCHARGES [OpenResearchLeaves42.deligneCanonicalModelY3EveryH] by Y3Hodge.deligneH_of_print
    still assumes: [Y3Hodge.DeligneCanonicalModelY3EveryPrint]
  #discharges: 39 open hypotheses, 13528 theorems checked, 26 discharge one
  ```
  It also prints the axioms of 17 `Y3Hodge` theorems (among them `print_iff_hodge`, `lemmaP_H1`, `dcRelPM_iff`,
  `exists_upper`, `F0_iff`, `iota_mul_Jmat`, `print_iff_deligneH` and `printPM_iff_field`). All are
  `[propext, Classical.choice, Quot.sound]`.
* **Autofold.**
  * Spec: `scratch/y3-hodge/autofold.json`. It sets field `deligneCanonicalModelY3EveryH` to
    `_root_.Y3Hodge.deligneH_of_print {n}.deligneCanonicalModelY3EveryPrint` and adds leaf
    `deligneCanonicalModelY3EveryPrint`, type `_root_.Y3Hodge.DeligneCanonicalModelY3EveryPrint`, kind
    `consequence`, with the pending-review flag.
  * `--dry-run`: `strict count: 11/23 on 34 -> 11/23 on 34; strictest 10/24 -> 10/24` (`autofold-dryrun.txt`).
  * `FoldCheck.lean.txt` is the dry-run output minus line 1. It compiles, and
    `HDec.HSyn.sixContactMin_of_open61` uses only the standard axioms (`foldcheck.txt`).
* **Name clashes.** `Y3Hodge` (with `Y3Hodge.LP` and `Y3Hodge.UP`) is a new namespace in the tree.

## 6. For the integrator

* Fold `scratch/y3-hodge/autofold.json`. It needs the new module `ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean` (in
  this branch).
* When the reviewer re-rates the new row (LEAF if §4.2 is accepted), the strict count drops by 1.
* If pel-hodge or y3abu-strict are merged later, their copies of `h1Form_iff`, `iotaR` and `jτ` here live in
  `Y3Hodge`/`Y3Hodge.LP` and do not clash.

## 7. Status

* **Done and compiled:**
  * item (1) (`print_iff_hodge`);
  * item (2) (`lemmaP_H1`, existence and uniqueness, on the genuine `H₁`);
  * item (3) (`dcRelPM_iff`, `exists_upper`, retraction);
  * the sign check (`F0_iff`; no change needed);
  * the restated leaf, with both directions to the old leaf and the equivalence with the field;
  * the module build, `#discharges`, the dry run and the fold check.
* **Not done:**
  * locator readings (no network);
  * a combined fold with other pending specs;
  * Riemann's theorem (polarizations ↔ Riemann forms) and the relative Lemma P, which cannot be stated over Mathlib
    today.
