# charpoly-port: `DegHomogPoly` proved in every characteristic; `charPolyIndepOfEllAlgClosed` closes with no new leaf

Task charpoly-port, 2026-11-17. Base: main `bf737bfe7`, with origin/wip/degpoly-proof (`0a9e6698`, for
deg-det's statement) and origin/wip/charpoly-p (`68e5fd34`, for the assembly) merged in.
Scratch: `scratch/charpoly-port/` (results log `log.md`). Lean:
`ZInQKernel/Contrib/OneProof/DegHomogPolyFLT.lean`, `ZInQKernel/Contrib/OneProof/CharPolyPort/FinrankGeneric.lean`
and the vendor directory `ZInQKernel/Contrib/OneProof/CharPolyPort/Vendor/AnthropicFLT/` (59 modules).

Marks: VERIFIED = read in a source, computed or compiled; STANDARD = published with an exact reference;
SPECULATIVE = unchecked. No network: theorem numbers recalled from memory are UNVERIFIED.

## 1. Main result

**deg-det's leaf `DegDet.DegHomogPoly` is a theorem, in every characteristic, with no hypothesis**
(VERIFIED: compiles; axioms `propext`, `Classical.choice`, `Quot.sound`):

```lean
theorem ZInQ.Contrib.OneProof.DegPolyFLT.degHomogPoly : DegDet.DegHomogPoly
```

For `k` algebraically closed of any characteristic, `A : PkgI3.AbVar k` and `e₁, …, e_r ∈ End(A)`,
`x ↦ degEnd(∑ xᵢ eᵢ)` is a homogeneous rational polynomial of degree `2 dim A`, where `degEnd` is the
function-field degree (`0` for non-isogenies).

With charpoly-p's `CharPolyCharP.charPolyIndepOfEllAlgClosed_of_degHomogPoly'` (field from `DegHomogPoly`
alone), **the open field `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` (Mumford §19 Thm 4) is proved with no
new leaf**. The composition `charPolyIndepOfEllAlgClosed_proof` is in `scratch/charpoly-port/DischargesCheck.lean`,
and the fold spec is `scratch/charpoly-port/autofold.json`. One published LEAF row leaves; nothing is added.
`#discharges`: §6.

Both findings-note gaps are closed:
- Gap 1 (`degEnd` vs `endDegree`) is proved (§3).
- Gap 2 (`HomFreeFiniteAlgClosedNoEmb`) is not needed: charpoly-p's assembly takes `DegHomogPoly` only
  (VERIFIED, its theorem's signature).

## 2. The proof

| step | Lean | source |
| --- | --- | --- |
| degree polynomial for FLT's `endDegree` (kernel rank) | `RelativeGroupLaw.exists_isHomogeneous_eval_eq_endDegree_of_abelianSchemePropertyBundle` | Anthropic FLT, vendored with its whole proof (§4) |
| transport to `PkgI3.AbVar` | `degHomogPolyEndDegree` | `CloudB3W16Torsion/RelativeBridges.lean` (relative group law, abelian-scheme bundle, smoothness of relative dimension `g`) plus `toPt_sum`, `toPt_hom` here |
| a finite endomorphism is flat | `flat_of_isFinite` | FLT's miracle-flatness proof for `[n]` (`flat_schemeNsmul_of_isFinite_of_field`), run for any finite endomorphism (regular stalks, equal dimension, zero-dimensional fibre) |
| a finite endomorphism is surjective | `finiteEndSurjective` | flat + FLT `surjective_and_endDegree_eq_finrank_of_isFinite_of_flat` |
| rank at the generic point = function-field degree | `CharPolyPort.finrank_genericPoint`, `finrankGenericPoint` | new, from Mathlib (§3) |
| `degEnd = endDegree` | `degEnd_eq_endDegree`, `degEndEqEndDegree` | isogeny: Mathlib `Scheme.Hom.finrank` via FLT + the previous line; non-isogeny: FLT `isFinite_of_isFinite_endKerStr` (finite kernel ⇒ finite) + surjectivity ⇒ isogeny |
| `DegHomogPoly` | `degHomogPoly` | — |

All in `DegHomogPolyFLT.lean`, except `finrank_genericPoint`, which is in `CharPolyPort/FinrankGeneric.lean`.

## 3. The comparison of the two degrees (all proved)

The findings note left three items for `degEnd ψ = endDegree ψ`. All are now proved:

1. **Isogenies are flat.** This was already in the tree (`MilneQuasiInverse.finite_surjective_abVarHom_flat`).
   `flat_of_isFinite` proves it for every finite endomorphism.
2. **`Scheme.Hom.finrank` at the generic point equals the stalk `finrank` used by `degEnd`.**
   `CharPolyPort.finrank_genericPoint`: for `f : X ⟶ Y` finite, flat and surjective, `X` and `Y` integral,
   `Scheme.Hom.finrank f (f η_X) = finrank_{𝒪_{Y,f η_X}} 𝒪_{X,η_X}`. Proof outline:
   - take an affine `V ∋ f η_X`;
   - the square `Spec Γ(f⁻¹V) → Spec Γ(V)` over `f` is a pullback (`IsOpenImmersion.isPullback`), so
     `Scheme.Hom.finrank_of_isPullback` and `finrank_SpecMap_eq_finrank` turn the rank into
     `RingHom.finrank` of `f.app V` at `hV.primeIdealOf (f η_X)`;
   - that prime is `⊥` (`primeIdealOf_genericPoint`), and the stalks are the fraction fields
     (`isLocalization_stalk` at `⊥`);
   - the algebra core `rankAtStalk_bot_eq_finrank`: `Frac S` is the localization of `S` at `R ∖ 0`, because a
     nonzero `b ∈ S` divides a nonzero element of `R` (`Ideal.under_ne_bot_of_integral_mem`). Hence
     `Frac S = Frac R ⊗_R S` (`Algebra.isLocalization_iff_isPushout`), and `Module.rankAtStalk_isBaseChange`
     finishes.
3. **The two `0` cases agree.** If the kernel is finite, `ψ` is finite (FLT), hence flat and surjective,
   hence an isogeny.

## 4. The port (VERIFIED)

- **Source.** There is no checkout of anthropics/fermats-last-theorem on the host. The theorem and its closure
  exist on `origin/cloud-b3/w13-recovery` (3360b4789), `ZInQKernel/Contrib/CloudB3W13/Source/` (FLT @ `6e837e75`,
  Apache-2.0). They are already ported to Lean 4.35 there, but namespace-wrapped
  (`namespace ZInQ.Contrib.CloudW03NeronSurj.FLT`). That branch is not in main.
- **Closure** (COUNTED, `tools/closure_w13.py`, `tools/missing_w13.py`). The theorem's closure there is 1,586
  modules. Stopping the descent at modules main's `CloudB3W16Torsion` vendor already has (1,315 FLT modules
  and 48 reused), 63 remain: 59 FLT modules and 4 Worker-13 port shims, which are dropped. This agrees with the
  findings note's "about 60".
- **Conversion** (`tools/convert.py`):
  - unwrap the namespace; drop the `r2nos_*` shim commands; rename `w03_*` to `p2m_*`;
  - relocate imports to the W16 vendor or the new directory;
  - apply the FLT-suffix renames of `CloudB3W16Torsion/NOTICE.md` (`tensorPow*`, `pullbackSection*`,
    `preserves*_opensMap`, `isInvertible_unit/top`, `fltMonoidalCategory`, `IdealSheafData.IsCartierFLT`, …);
  - use W16's `respectTransparency false`.

  Each file carries the FLT provenance, the Worker-13 port notice and a "Modified for the Z-in-Q kernel
  (charpoly-port, 2026-11-17)" notice. LICENSE, NOTICE.upstream and ATTRIBUTION.upstream.md are copied to the
  vendor root.
- **Manual repairs** (5 files; no statement changed):
  - two `rfl` became `try rfl`, and one `simp only …; exact` became `<;>`/`first` (simp closes more goals in
    Mathlib 4.35);
  - in two MvPolynomial files, W13's `respectTransparency.types false` and `.instanceSearchTypes false` are
    restored, because W16's global option makes `Module ℚ≥0 (MvPolynomial ι R)` synthesis time out.

  Details are in `log.md`.
- **Builds:** the theorem module 10,647 jobs OK (`build3.log`); `DegHomogPolyFLT` 10,797 jobs OK (`build8.log`).

## 5. Leaves

**No new leaf.** Every statement introduced on the way was proved:
- `FinrankGenericPoint` (glue);
- `FinrankGenericEqDegEnd` (glue);
- `FiniteEndSurjective` (glue);
- `DegEndEqEndDegree` (glue).

The FLT theorem is used as a Lean proof, not as a leaf.

## 6. Checks

- Axioms (VERIFIED, `Axioms-output.txt`): `degHomogPoly`, `degEndEqEndDegree`, `finiteEndSurjective`,
  `finrankGenericPoint`, `CharPolyPort.finrank_genericPoint`, `degHomogPolyEndDegree` and the conditional
  forms all use only `[propext, Classical.choice, Quot.sound]`.
- `#discharges` (VERIFIED, `scratch/charpoly-port/Discharges-output.txt`, after
  `lake build +Main +Discharges +DegHomogPolyFLT +CharPolyCharP`, 16,118 jobs):

  ```
  DISCHARGES [OpenTextbookLeaves17.charPolyIndepOfEllAlgClosed] by charPolyIndepOfEllAlgClosed_proof
    still assumes: []
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 36 open hypotheses, 13237 theorems checked, 37 discharge one
  ```
- Autofold: `scratch/charpoly-port/autofold.json` discharges `charPolyIndepOfEllAlgClosed` with proof
  `CharPolyCharP.charPolyIndepOfEllAlgClosed_of_degHomogPoly' DegPolyFLT.degHomogPoly` and no leaves. It
  imports charpoly-p's `CharPolyCharP` (the assembly is that task's). `autofold.py --dry-run`: strict
  15/16 on 31 → 14/16 on 30, strictest 15/16 → 14/16, and `OpenTextbookLeaves18` has no fields. The
  compile of the dry-run module is recorded in the log.

## 7. State

- Compiles: the 59 vendored modules, `CharPolyPort/FinrankGeneric.lean`, `DegHomogPolyFLT.lean`.
- Nothing open in this task's scope.
- For integration: fold with charpoly-p's `CharPolyCharP.lean` (the spec above). The FLT vendor directory
  depends on main's `CloudB3W16Torsion` vendor. Olean name clashes with Main's closure were not scanned beyond
  the `DischargesCheck` compile, which imports Main together with this file.

Written by Claude Code, at Jack's request.
