# charpoly-port: `DegHomogPoly` in every characteristic from Anthropic's FLT library, up to one commutative-algebra glue statement

Task charpoly-port, 2026-11-17. Base: main `bf737bfe7`, with origin/wip/degpoly-proof (`0a9e6698`, for
deg-det's statement) and origin/wip/charpoly-p (`68e5fd34`, for the assembly) merged in.
Scratch: `scratch/charpoly-port/` (results log `log.md`). Lean: `ZInQKernel/Contrib/OneProof/DegHomogPolyFLT.lean`
and the vendor directory `ZInQKernel/Contrib/OneProof/CharPolyPort/Vendor/AnthropicFLT/`.

Marks: VERIFIED = read in a source, computed or compiled; STANDARD = published with an exact reference;
SPECULATIVE = unchecked. No network: theorem numbers recalled from memory are UNVERIFIED.

## 1. Main result

**`DegDet.DegHomogPoly` is proved in every characteristic from one glue statement of commutative algebra**
(VERIFIED: compiles, standard axioms):

```lean
theorem ZInQ.Contrib.OneProof.DegPolyFLT.degHomogPoly_of_finrankGenericPoint
    (h : DegPolyFLT.FinrankGenericPoint) : DegDet.DegHomogPoly
```

`FinrankGenericPoint` (GLUE, open; §4) says: for `f : X ⟶ Y` finite, flat and surjective between integral
schemes, Mathlib's rank `Scheme.Hom.finrank f` at the generic point is the degree `[K(X) : K(Y)]` of the
function-field extension. It has no abelian-variety content.

With charpoly-p's `CharPolyCharP.charPolyIndepOfEllAlgClosed_of_degHomogPoly'` (which needs `DegHomogPoly`
alone, no `homFreeFiniteAlgClosed`), this gives the open field `charPolyIndepOfEllAlgClosed`
(Mumford §19 Thm 4, a published LEAF) from `FinrankGenericPoint` (GLUE). `#discharges` result: §6.

What is new in Lean (all VERIFIED compiled, standard axioms):

1. **Anthropic's degree polynomial on Lean 4.35 in the tree.** The 59 modules of the closure of
   `GoodReductionJacobian.RelativeGroupLaw.exists_isHomogeneous_eval_eq_endDegree_of_abelianSchemePropertyBundle`
   that main's `CloudB3W16Torsion` vendor did not have are vendored (§2); the theorem builds.
2. **`degHomogPolyEndDegree`** (no hypothesis): the theorem transported to `PkgI3.AbVar` through
   `CloudB3W16Torsion/RelativeBridges.lean`: for `k` algebraically closed, `x ↦ endDegree(∑ xᵢ eᵢ)` is a
   homogeneous rational polynomial of degree `2 dim A`, where `endDegree` is FLT's kernel rank.
3. **`flat_of_isFinite`** (no hypothesis): a finite endomorphism of an abelian variety (any field) is flat.
   The proof is FLT's miracle-flatness argument for `[n]` (`flat_schemeNsmul_of_isFinite_of_field`), run for
   an arbitrary finite endomorphism.
4. **`finiteEndSurjective`** (no hypothesis): a finite endomorphism is surjective (flat + FLT's
   `surjective_and_endDegree_eq_finrank_of_isFinite_of_flat`).
5. **`degEnd_eq_endDegree`**: `degEnd ψ = endDegree ψ` for every `ψ`, from `FinrankGenericEqDegEnd` and
   `FiniteEndSurjective` (the non-isogeny case uses FLT's `isFinite_of_isFinite_endKerStr`: a finite kernel
   makes `ψ` finite, hence surjective by 4, hence an isogeny).
6. `degHomogPoly_of_degEndEq`, `degHomogPoly_of_glue`, `degHomogPoly_of_finrankGeneric`,
   `finrankGenericEqDegEnd_of_finrankGenericPoint`, `degHomogPoly_of_finrankGenericPoint`: the chain.

Gap 2 of the findings note (`HomFreeFiniteAlgClosedNoEmb`) is **not needed**: charpoly-p removed the use of
`homFreeFiniteAlgClosed` from deg-det's route (VERIFIED: its theorem takes `DegHomogPoly` only).

## 2. The port (VERIFIED)

- **Source.** There is no checkout of anthropics/fermats-last-theorem on the host. The target and its closure
  exist, already ported to Lean 4.35 but namespace-wrapped (`namespace ZInQ.Contrib.CloudW03NeronSurj.FLT`), on
  `origin/cloud-b3/w13-recovery` (3360b4789), `ZInQKernel/Contrib/CloudB3W13/Source/` (FLT @ `6e837e75`,
  Apache-2.0). That branch was reverted out of main.
- **Closure** (COUNTED, `tools/closure_w13.py`, `tools/missing_w13.py`). The theorem's closure on that branch is
  1,586 modules. Stopping the descent at modules main's `CloudB3W16Torsion` vendor already has (1,315 FLT
  modules + 48 reused), 63 remain: 59 FLT modules and 4 Worker-13 port shims (dropped). This matches the
  findings note's "about 60".
- **Conversion** (`tools/convert.py`): unwrap the namespace; drop `r2nos_*` shim commands; `w03_*` →
  `p2m_*`; relocate imports to the W16 vendor or the new directory; apply the FLT-suffix renames of
  `CloudB3W16Torsion/NOTICE.md` (`tensorPow*`, `pullbackSection*`, `preserves*_opensMap`,
  `isInvertible_unit/top`, `fltMonoidalCategory`, `IdealSheafData.IsCartierFLT`, …); W16's
  `respectTransparency false`. Each file carries the FLT provenance, the Worker-13 port notice and a
  "Modified for the Z-in-Q kernel (charpoly-port, 2026-11-17)" notice; LICENSE, NOTICE.upstream and
  ATTRIBUTION.upstream.md are copied to the vendor root.
- **Manual repairs** (5 files; no statement changed): two `rfl` → `try rfl` and one `simp only …; exact` →
  `<;>`/`first` (Mathlib's simp closes more goals), and in two MvPolynomial files W13's
  `respectTransparency.types false` + `.instanceSearchTypes false` restored (W16's global option makes
  `Module ℚ≥0 (MvPolynomial ι R)` synthesis time out). Details in `log.md`.
- **Build**: `lake build` of the theorem module: 10,647 jobs, OK (`build3.log`).

## 3. The bridge between the two degrees

The findings note listed three owed lemmas for `degEnd = endDegree`. Status:

| item | status |
| --- | --- |
| isogenies are flat | already in the tree (`MilneQuasiInverse.finite_surjective_abVarHom_flat`); also `flat_of_isFinite` here, for every finite endomorphism |
| finite kernel ⇒ isogeny (the two `0` cases agree) | **proved**: FLT `isFinite_of_isFinite_endKerStr` + `finiteEndSurjective` |
| `Scheme.Hom.finrank` at the generic point = the stalk `finrank` of `degEnd` | **open**: `FinrankGenericPoint` (GLUE) |

## 4. The remaining statement

```lean
def ZInQ.Contrib.OneProof.DegPolyFLT.FinrankGenericPoint : Prop :=
  ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsFinite f] [Flat f],
    Function.Surjective f →
      letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
      Scheme.Hom.finrank f (f (genericPoint X)) =
        Module.finrank (Y.presheaf.stalk (f (genericPoint X))) (X.presheaf.stalk (genericPoint X))
```

- **Rating: GLUE, not a printed-form leaf.** It is standard commutative algebra, not a literature theorem:
  on an affine chart `Spec S → Spec R` with `R ⊆ S` domains and `S` finite flat over `R`, the rank of `S` at
  the prime `(0)` is `dim_{Frac R} (Frac R ⊗_R S)`, and `Frac R ⊗_R S = Frac S` because it is a domain finite
  over a field. Over genuine Mathlib definitions only (`Scheme.Hom.finrank`, `genericPoint`, `stalkMap`).
- **Proof plan** (SPECULATIVE, not attempted in Lean): choose an affine `V ∋ η_Y`; `U = f⁻¹V` is affine;
  `Scheme.Hom.finrank_of_isPullback` with `isPullback_morphismRestrict` moves to `f ∣_ V`;
  `Scheme.isoSpec_hom_naturality`, `finrank_comp_left_of_isIso` and `finrank_SpecMap_eq_finrank` move to
  `RingHom.finrank` of `Γ(V) → Γ(U)` at the generic prime; `Module.rankAtStalk_eq_finrank_tensorProduct`;
  `IsAffineOpen.isLocalization_stalk` identifies the stalks with localizations at the generic primes; and
  `Frac R ⊗_R S ≅ Frac S` (Mathlib's `IsIntegralClosure.isFractionRing_of_algebraic`-type lemmas).
- The narrower form actually consumed is `FinrankGenericEqDegEnd` (abelian varieties only; proved from
  `FinrankGenericPoint` by `finrankGenericEqDegEnd_of_finrankGenericPoint`).

## 5. Count

The fold replaces the published LEAF row `charPolyIndepOfEllAlgClosed` (Mumford §19 Thm 4) by one GLUE row
`finrankGenericPoint`. Strict GLUE count +1, LEAF −1, so `autofold.py` needs `--allow-rise`. The literature
input disappears; what remains is a commutative-algebra lemma for the project.

## 6. Checks

See `scratch/charpoly-port/log.md` for each compile. `#discharges` output: `scratch/charpoly-port/Discharges-output.txt`
(filled in below once run). Autofold spec: `scratch/charpoly-port/autofold.json`.

## 7. State

- Compiles: the 59 vendored modules, `DegHomogPolyFLT.lean` (all theorems standard axioms).
- Open: `FinrankGenericPoint` (GLUE).
- Assembly with charpoly-p's theorem: done only in the scratch discharges file and the autofold spec, as asked.

Written by Claude Code, at Jack's request.
