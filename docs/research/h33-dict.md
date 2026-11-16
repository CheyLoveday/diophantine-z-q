# h33-dict: the top hypothesis `h33` (TYZ Theorem 3.3) made printed

Task h33-dict, 2026-11-16. Base origin/main `2880fef1`. Target: `h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33`,
a plain argument of `ZInQ.OneProof.frozenTarget` (row `h33` of `docs/one-proof/kinds.tsv`). Scratch:
`scratch/h33-dict/` (log `log.md`). Contribution: `ZInQKernel/Contrib/OneProof/TYZThm33.lean`.

## Verdict

**`h33` is discharged.** It is replaced by one new leaf, `H33Dict.TYZThm33Printed`. That leaf is Tian–Yuan–Zhang
Theorem 3.3 for TYZ's own identification `i₀ : (X₀(32), ∞) ≅ (A, O)`, with `ε` chosen after `Φ`, as printed.
Every dictionary step between the leaf and the old statement is now a Lean proof:

```lean
theorem ZInQ.Contrib.TYZGenus.H33Dict.tyzThm33_of_printed
    (hCM : T5Glue.ShimuraMainCM) (h : TYZThm33Printed) : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33
```

`hCM` (the printed main theorem of CM) is already an argument of `frozenTarget`, so the fold adds no hypothesis
besides the leaf. Both objections of the 11-16 dictionary pass are resolved:

1. **`phiC` vs `i₀` (fixed by a Lean proof).** The leaf quantifies over every identification `i₀`. Each one is
   given by its pullbacks `X = x∘i₀`, `Y = y∘i₀` in `ℚ(X₀(32))` (`IsX0Identification`). The leaf assumes nothing
   about the eta model. Lean proves that x0-32's eta model `(x, y)` is such an identification
   (`isX0Identification_eta`). The new part of that proof is the pole structure of `x` at the eight cusps.
2. **`ε` before `Φ` (fixed by a Lean proof; no new leaf).** TYZ Prop. 3.2(4), in the form the uniformization
   uses (`TYZProp324Used`), is proved from the CM inputs that `hCM` provides (`tyzProp324Used_of`). The leaf
   keeps the printed quantifier order, with `ε` after `Φ` and `χ`, and `tyzThm33_of_epsAfter` moves `ε` in
   front.

The new leaf is rated **printed form** (reasons in §3). Caveats, all recorded in its docstring:

* The readings are of arXiv v1. **The journal version (Asian J. Math. 21 (2017) 721–774) has not been checked.**
* The TYZ source `~/tyz-src/Period7.tex` was missing from this host on 11-16, so h33-dict did not re-read it. The
  readings used are those of tyz-split and h33-sign, who read Period7.tex. h33-dict changes no reading; it changes
  only how `i₀` and `ε` are encoded.
* Two parts of the old dictionary stay readings and are not Lean: TYZ's curve `X_U` against `X₀(32)_{ℚ(i)}`, with
  `P_n` as the fixed point `τ_n` (checked by h33-sign's `Iso.lean`), and `f₀∘[i]` as `[i]∘f₀` on the component of
  `P_n` (the sign of `[i]`, settled by h33-sign).

## 1. Old and new

| | old (`TYZSplit.TYZThm33`) | new (`H33Dict.TYZThm33Printed`) |
|---|---|---|
| CM points | `TYZ35.basePt`, Heegner points of the eta model `X0.phiC` | `zOfLift w`, with `toC (w n) = i₀(τ_n)` for an arbitrary identification `i₀` (`IsX0Identification X Y`, `ptOf X Y`) |
| `i₀` | implicit: "phiC = [M]∘i₀ by the q-expansion principle" (docstring, statement review v2 M1) | explicit, universally quantified, encoded by its pullbacks over Mathlib's `ℍ` and the kernel's `IsRatModFn` |
| `ε(d₀,d₁)` | chosen before `n, Φ, χ` | chosen after `Φ, χ` (`TYZThm33EpsAfter`); TYZ fix `Φ` before stating the theorem (L1279) |
| everything else | as printed, with the documented weakenings (`𝒫` existential, `n ≡ 5, 7`, `ℓ` sign choice) | identical (verbatim copy of the display, `basePt` replaced by `z`) |

Lean names (all in namespace `ZInQ.Contrib.TYZGenus.H33Dict`, file `ZInQKernel/Contrib/OneProof/TYZThm33.lean`):

| step | kind | Lean | line |
|---|---|---|---|
| the leaf | LEAF (printed form) | `TYZThm33Printed` (with `TYZThm33EpsAfter`, `EpsClass`, `PchiGWith`, `ptOf`, `IsX0Identification`, `zOfLift`) | 53–166 |
| CM inputs from `hCM` | glue, proved | `cmInputs`, `kerFix` | 174–183 |
| restriction of Artin symbols to `H_n` | glue, proved | `picToMax_eq_one_of_fix`, `picToMax_eq_one`, `restricts_inv_mul`, `restricts_agree` | 192–245 |
| TYZ Prop. 3.2(4), used form | glue, proved | `TYZProp324Used`, `tyzProp324Used_of` | 261–289 |
| `ε` before `Φ` | glue, proved | `pchi_sub_tors`, `tyzThm33_of_epsAfter` | 294–360 |
| pole orders of `x` at the cusps | glue, proved | `exists_smul_decomp_exact`, `etaD_norm_exact`, `Hinv_exact`, `xC_sub_two_bound`, `expS_nonneg`, `xC_bigO_atImInfty`, `xC_bounded_cusp`, `etaCuspBounds` | 370–707 |
| eta model is an identification | glue, proved | `not_bounded_xC`, `isX0Identification_eta` | 710–731 |
| the contribution | — | `tyzThm33_of_printed` | 736 |
| non-vacuity of the leaf's hypotheses | — | `tyzThm33Printed_hyps_satisfiable` | 758 |

## 2. The proofs

### 2.1 Fix (1): the eta model is an identification (VERIFIED, compiled)

`IsX0Identification X Y` requires:
* `IsRatModFn 32 X` and `IsRatModFn 32 Y`;
* `Y² = X³ + 4X`;
* `X` unbounded at `∞`;
* `X = O(e^{4π Im τ})` at `∞`;
* `X ∘ γ` bounded at `∞` for every `γ ∈ SL₂(ℤ)` with `32 ∤ c`.

For the eta model the first three were already in the tree: `X0ModuliUsed.isRatModFn_x`, `isRatModFn_y`,
`Shimura.etaModelEquation`, and x0-32's `tendsto_norm_xC_atTop` (giving `not_bounded_xC`). The last two are new:

* `exists_smul_decomp_exact` is tyz-cm's Hermite decomposition `δ·γτ = γ'w` with the imaginary part made exact:
  `δ·Im w = gcd(δ, c)²·Im τ`. The `gcd` comes from `p g = δa`, `s g = c` and `gcd(p, s) = 1`.
* `Hinv_exact` uses `H(w) = |η(w)|⁴ Im w = e^{−π Im w/3}·P(w)·Im w`, with `m ≤ P ≤ M` for `Im w ≥ 1`.
* Together these give `xC_sub_two_bound`: for `Im τ ≥ 32`, uniformly in `γ`,
  `|x(γτ) − 2|⁴ ≤ K·e^{−π Im τ·S(γ)/96}`, where `S = 32g₂² + 2g₁₆² − 8g₄² − 2g₃₂²` and `g_δ = gcd(δ, c)`. This is
  Ligozat's order formula for `x − 2 = η₂²η₁₆/(η₄η₃₂²)`.
* `S(γ)` depends only on `c mod 32`. A kernel `decide` over the 31 residues gives `S ≥ 0` when `32 ∤ c`
  (`expS_nonneg`), hence `xC_bounded_cusp`. At `γ = 1` we get `S = −1536`, so `|x − 2| = O(e^{4π Im τ})`
  (`xC_bigO_atImInfty`).

Why `IsX0Identification` is exactly TYZ's normalization (argued in the docstring, STANDARD):
* By the q-expansion principle, `X` and `Y` are elements of `ℚ(X₀(32))` that are regular on `ℍ`.
* With the curve equation they define a ℚ-morphism `i₀ : X₀(32) → A`, and `i₀(∞) = O` because `X` has a pole at `∞`.
* The cusps `γ∞` with `32 ∣ c` are exactly the `Γ₀(32)`-orbit of `∞`, and `∞` has width 1. So `X` has a single pole,
  at `∞`, of order 1 or 2.
* `deg X = deg i₀ · deg x = 2 deg i₀`, so `deg X = 2` and `deg i₀ = 1`: `i₀` is an isomorphism.
* Conversely, for an isomorphism, `x∘i₀` has its only pole, a double one, at `∞`. So it is regular on `ℍ` and at
  the other cusps.
* There are exactly two identifications, `±i₀` (`Aut_ℚ(A, O) = ±1`, L1174), and Lean proves that `phiC` is one of
  them.

### 2.2 Fix (2): Prop. 3.2(4) from `hCM` (VERIFIED, compiled)

`TYZProp324Used` says: if `ρ, ρ' ∈ Gal(ℚ̄/ℚ)` both restrict to `t ∈ Cl_n` on `H_n`, then
`ρ(z_n) − ρ'(z_n)` is torsion. The proof:

* **`n ≡ 5`.**
  * `σ = ρ'⁻¹ρ` is trivial on `H_n` and fixes `√−n`, so it acts on `H_{n,4}` as `Art(a)` for some
    `a ∈ Pic(𝒪_{n,4})` (`T321.exists_acts4_of_fix`).
  * `a ↦ 1` in `Cl(K_n)` (`picToMax_eq_one`, from ring-class's `restrict_ringClassArtinEquiv`). This is stated
    for a general `K`, because the rewrite at `K = ℚ(√−n)` times out in the kernel (the known pitfall).
  * The kernel's glue KER (`T321.kerFixesZnMod`) then gives `σ z_n = z_n + jτ(1)`.
  * The inputs of KER are `TYZSigmaFixesZn`, `TYZThm36OneFive` and `ZnOverH4`, all from
    `X0ModuliUsed.CMInputs = cmInputs_of (srAt_x …) (srAt_y …)`. That is, they come from `hCM` and theta-wp8's
    proved `xEtaWeierstrass`.
* **`n ≡ 7`.** `z_n ∈ A(H_n)` (`cmFieldOfDefinition7_of`, from the same inputs), so `ρ z_n = ρ' z_n`.

`tyzThm33_of_epsAfter` then proceeds as follows:
* For each pair `(d₀, d₁)` it fixes one family of lifts `φ₀`, the unique character `χ_{d₀,d₁}`
  (`isExtChar_unique`), and the `ε` that the printed statement gives for them.
* For any other `Φ`, `P_χ(Φ) − P_χ(φ₀)` is torsion by `TYZProp324Used`.

### 2.3 CM points

`basePt = zOfLift w` with `w n = tyzHeegnerPt n` for `n ≡ 5` and `tyzZ7 n` otherwise, by unfolding. Also
`toC (heegnerPt Q) = phiC τ_Q = ptOf x y τ_Q` (`toC_heegnerPt`, with `CMAlgebraic` from `hCM`; `ptOf_eta` is `rfl`).

## 3. Rating of the new leaf

**`TYZThm33Printed`: printed form (kind published, strict LEAF).** Reasons:
* It is TYZ's display L1299–1311 with the set-up of §3.1, for the identification TYZ fix. The predicate
  `IsX0Identification` is equivalent to "isomorphism `(X₀(32), ∞) ≅ (A, O)` over ℚ" (§2.1), and a statement for both
  isomorphisms is the printed one.
* The quantifier order is the printed one: `Φ` is fixed first, then `ε(d₀, d₁)`.
* All definitions are genuine: Mathlib's `ℍ`, `IsBoundedAtImInfty`, Weierstrass points and `Gal(ℚ̄/ℚ)`; the
  kernel's `IsRatModFn`, Heegner forms and ring class fields. No structure was invented for the purpose.
* The weakenings are those of the old leaf: `𝒫` existential, `n ≡ 5, 7` only, `ℓ` any sign choice. The hypothesis
  on `w` makes the leaf vacuous, never false, for a non-algebraic family.

Non-vacuity: `tyzThm33Printed_hyps_satisfiable` (given `hCM`). The `ℓ`-hypothesis needs TYZ Thm 1.1, as before.

What it still rests on as reading, not Lean (unchanged from tyz-split and h33-sign):
* `X_U ≅ X₀(32)_{ℚ(i)}` with `P_n ↦ τ_n`;
* `f_n = f₀ − f₀∘[i]` read as `(1 − [i])∘i₀` on the component of `P_n`;
* `A : 2y² = x³ + x ≅ y² = x³ + 4x`;
* the choice of `δ` in `tyzForm7` (one admissible choice).

The row should keep the flag that there is no human review of the paper, and add the journal check.

### 3.1 Independent statement review (model, 11-16)

A separate model agent reviewed the leaf without access to the TeX, using the notes. It did not run Lean.
* **`IsX0Identification`: faithful.** It is exactly the class of pullbacks of ℚ-isomorphisms `(X₀(32), ∞) ≅ (A, O)`.
  The cusp conditions, the width of `∞`, the degree argument and the converse all check out. No spurious pairs:
  the only pairs are `(x, ±y)`.
* **`TYZThm33Printed`: weaker than the print, and not vacuous.**
  * `Q` and `m` are chosen after `ℓ` and before `n`; `ε` after `Φ` and `χ`.
  * It does not depend on the eta model.
  * Mathematically it is equivalent to `TYZThm33EpsAfter basePt`.
* **Inherited, not regressions:** the `P_n`/`[i]`/`δ` dictionary.
* **Docstring:** the reviewer asked to restore four items of the old docstring:
  * the warning that the other sign of `[i]` makes the leaf false;
  * the `ℓ` vacuity remark;
  * classes 6 and 2 kept as printed, and `h₂` reused at L2354;
  * `A ⊗ ℚ` equality as torsion.

  They are restored, and "degree 2" now reads "degree at most 2". The file was rebuilt and `#discharges` re-run with
  the same result.
* Unrelated stale remark: the docstring of `CM.tyzForm` (CM.lean:426) says "source not on this host".

## 4. Lean results (VERIFIED, compiled)

* `lake build +ZInQKernel.Contrib.OneProof.TYZThm33 +ZInQKernel.OneProof.Discharges`: success (the module in 39 s;
  `scratch/h33-dict/build1.txt`, `build2.txt`).
* `#discharges` (`scratch/h33-dict/Discharges.lean`, output `discharges-output.txt`):

  ```
  DISCHARGES [h33] by ZInQ.Contrib.TYZGenus.H33Dict.tyzThm33_of_epsAfter
    still assumes: [ZInQ.Contrib.TYZGenus.H33Dict.TYZProp324Used,
   ZInQ.Contrib.TYZGenus.H33Dict.TYZThm33EpsAfter ZInQ.Contrib.TYZGenus.TYZ35.basePt]
  DISCHARGES [h33] by ZInQ.Contrib.TYZGenus.H33Dict.tyzThm33_of_printed
    still assumes: [T5Glue.ShimuraMainCM, ZInQ.Contrib.TYZGenus.H33Dict.TYZThm33Printed]
  ```
  Axioms of `tyzThm33_of_printed`, `tyzProp324Used_of`, `isX0Identification_eta` and `etaCuspBounds`:
  `[propext, Classical.choice, Quot.sound]`.
* Manual fold checked (`scratch/h33-dict/FoldCheck.lean`): `frozenTarget_h33Printed` has the binders of
  `frozenTarget` with `h33` replaced by `h33p : TYZThm33Printed`. It compiles with standard axioms and is `rfl`-equal
  to `frozenTarget … (tyzThm33_of_printed hCM h33p) …`.
* The contribution's type is the constant `TYZSplit.TYZThm33`, matched by `#discharges`, so the statement is
  unchanged.

## 5. Fold (for the integrator)

`h33` is not a bundle field, so `autofold.py` refuses it (`not a field of the current bundles: ['h33']`, dry run
recorded). The spec and the manual-fold instructions are in `scratch/h33-dict/autofold.json`:
1. In `Main.lean`, import `ZInQKernel.Contrib.OneProof.TYZThm33`.
2. Replace the binder `h33` by `(h33p : ZInQ.Contrib.TYZGenus.H33Dict.TYZThm33Printed)`.
3. Pass `(ZInQ.Contrib.TYZGenus.H33Dict.tyzThm33_of_printed hCM h33p)` to `ThetaWP8.tyzThm35ReadingA_noHX`.
4. In `kinds.tsv`, row `h33` becomes `h33p`: published / LEAF / LEAF, with the flag "unread: journal version not
   checked; arXiv v1 read by tyz-split and h33-sign (sign of [i] verified)". The GLUE counts do not change.

Proposed `docs/research/locators.md` row: TYZ Thm 3.3 — arXiv:1411.4728v1, Period7.tex L1299–1311 (display), set-up
L1173–1174 (`A ≅ (X₀(32), ∞)`), L1195–1198 (`f_n`), L1203–1205 and L1245–1252 (`P_n`), L1263–1284 (`Cl_n`, `Φ`,
`P_χ`), L1288–1295 (`𝒫`), L992 (`h₂`); journal page UNVERIFIED.

## 6. What remains

* A check of Theorem 3.3 and §3.1 against the journal version.
* A human reading of TYZ's §3.1 for the `X_U`/`X₀(32)` dictionary (`P_n ↦ τ_n`, the component, `f₀∘[i]`). The
  computations and the Lean sign pin of h33-sign support it.
* Not needed for the fold: an algebraic statement of `X₀(32)` (as a scheme), which would make `i₀` a morphism
  instead of a pair of modular functions.
