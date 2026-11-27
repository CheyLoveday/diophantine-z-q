# Conductor-one parametrization values

Scoped stop: the rational modular parametrization at the **fixed analytic
scale** is missing. The reduction from the approved CM field-of-definition
statement is `preparedParamValues`, and the two existing consumers take it
through `genusParamValues` and `missingParamValues`. The new rough-companion
assembly supplies the genus argument itself. The remaining geometric
input is a canonical model of `X₀(N)` with its complex comparison, together
with `AlgebraicParametrizationAtScale` on that model. No unconditional
`PreparedParamValue` is claimed.

The proof evaluates the actual rational morphism at the `H`-valued point
provided by the CM statement. In Lean the morphism is composed with
`Spec H → X₀(N)`. On the `Z ≠ 0` Weierstrass chart, the map on coordinate
rings produces two coordinates over `H`; the coordinate-ring relation and
ellipticity give a nonsingular point. On the complementary chart the
value is the point at infinity. The same chart is used after precomposing
with `Spec ℂ → Spec H`. Naturality of the affine chart lift and of the global
section map proves that evaluating there agrees with `Affine.Point.map`.
The scale equality then gives the required complex image at the exact
form chosen by `StageSelector.formAtLevel`. This scheme calculation and the
selector wiring are on-the-spot (c).

All four files pass serial `lake env lean -j1`. The eleven theorem
audits report exactly `propext`, `Classical.choice` and `Quot.sound`.

## Statements and consumers

Declarations are in `ZInQ.Manuscript.RC.PreparedParam`.

| Declaration | Statement and consumer |
| --- | --- |
| `mem_affineOpen_of_ne_pointO` (private) | Every projective Weierstrass point other than infinity is on `Z ≠ 0`. Used to select the chart branch. |
| `range_le_affineOpen` (private) | If the image of the unique point of `Spec F` lies on the affine chart, the entire morphism factors through its open immersion. Used in the elliptic point evaluation. |
| `specToAlgHom_map` (private) | The ring map corresponding to `Spec G → Spec F → Spec A` is the one corresponding to `Spec F → Spec A` followed by `F → G`. Used for the same embedding as in the CM print. |
| `projectiveValue_map` | For a field embedding `ι : F →ₐ[ℚ] G` and a scheme point `u : Spec F → E_proj`, the `Affine.Point.map ι` of its value equals the value at `Spec.map ι ≫ u`. Both branches include the point at infinity. |
| `value_of_cmFieldOfDefinition` | For an imaginary quadratic field, order of discriminant `d < 0` prime to the level, and primitive Heegner form `[A,B,C]`, the approved CM statement and the fixed scale comparison give `∃ ι : H →ₐ[ℚ] ℂ, ∃ y : E(H), ι(y) = phiAn E f Lat κ (cmPoint A B d)` for the ring class field of that order. |
| `discr_conductorOne`, `coprime_level` (private) | The conductor-one order has the field discriminant. The local unit squares at the primes of twice the level imply `IsCoprime d (N : ℤ)`. These check the print's hypotheses at a prepared parameter. |
| `preparedParamValues` | For one model, the CM statement and the fixed scale comparison, `∀ D (hp : Prepared E hstar D), StageSelector.PreparedParamValue E f Lat κ hN hgp hp` using precisely the selector's field and form. No rank premise. |
| `genusParamValues` | The preceding family for `Ecurve ℓ`, with `curve_form` and `genusPartner_of_support`. Pass this as `halgG` to `instanceOfParamValues`, `gz34CompAt_of_paramValues` or `gz34Target_of_paramValues`. The remaining `hjg` must refer to that selection. |
| `gz34CompAt_of_scaledParametrization` | Installs that genus family in the existing rough-companion assembly and gives `Gz34CompAt W 0`, conditional on the CM and fixed scale inputs and the remaining rough inputs. There is no independent `halgG`. |
| `missingParamValues` | For `s : StageKummer.Setup I L`, use its original `f,Lat,κ` and prepared-filter bridge. The conclusion is `StageKummer.MissingParamValues s`; pass it to its existing selector adapter. |

Each new hypothesis supplies a proper part of the argument for the
elliptic-value assertion. `X0Model N` supplies the source scheme and the
complex comparison in tex 1781–1786 and 2915–2919. Its function field and
section expansions pin the chart to the rational model through
`ℚ(j,j_N)`; it contains no CM descent, target elliptic curve, or
parametrization. `CMFieldOfDefinition X` is the one approved print in
`Prints.lean`: it descends the source point without any map or elliptic
value. `AlgebraicParametrizationAtScale E X f Lat κ` asks for one rational
dominant morphism and the equality with `phiAn` on the upper half plane.
It is the missing modular realization and comparison (tex 1781–1788,
2836–2838, 9347–9350). It supplies no number field, CM point or point over a
class field. In particular it can be addressed once at this level and
scale before considering any `D`.

## Remaining hypotheses

| Input | Manuscript | Owner and size |
| --- | --- | --- |
| `X : X0Model (newformLevel E)` | 1781–1786, 2837–2838, 2915–2919 | Missing theory, large: construct the proper smooth model with the identified rational function field and verify its complex comparison. Existing work on modular function fields is a starting point; the section expansions are the required comparison, not a second print. |
| `CMFieldOfDefinition X` | 2915–2919, 8209–8217 | The single approved print, GLUE (unread). Exact field-of-definition locator in Cai–Chen–Liu §2 or Shimura Ch. 6 needs the reviewer. |
| `AlgebraicParametrizationAtScale E X f Lat κ` | 1781–1788, 2836–2838, 2915–2917, 9347–9350 | Missing theory, large: connect the rational elliptic quotient to an actual morphism, and prove its complex evaluation is the Eichler integral followed by Weierstrass uniformization at this same scale. A different scale or existence of an analytic scale alone does not suffice. The genus and Kummer adapters consume the same statement. |
| Actual `ℓ,f,hf,Lat,hLat,κ,hκ`, and `hNC` | 1012–1013, 1092–1093, 1765–1767, 1825–1828, 2430, 2836–2838 | Existing curve data and ELLIOT scale input. `curve_form` and `curve_lattice` supply the form and lattice; identifying algebraic non-CM with the lattice multiplier assertion is missing theory, medium to large. Positive level for the new adapters follows from the existing level proofs. |
| `P : Prints`, `hArtin`, `hRN` | 1092–1093, 2346, 2428–2432, 10172–10178 | Existing shared leaves and wiring; no change. |
| Central normalization `N,hN` and `hElkikMD` | 1825–1830, 2404, 7175–7180 | RC11 and ELLIOT input respectively, large period rationality and normalization comparisons; outside this task. |
| `hpartner,hlevel0,hS,hprepared,hstarS,hpreparedLoc` | 1974–1979, 2344–2353, 2404–2410, 2460–2462 | Existing nonvanishing and stage support. The stage support field is owned by the reviewer. |
| `halgR` at the chosen conductor-`|h|` companion | 2413–2416, 2428–2431, 9347–9350 | Outside the conductor-one task. The same general morphism evaluation applies once the correct order discriminant and coprimality are supplied there. |
| `hjg,hjr`; final companion `hk0,hksq,hk4,hk2N,hkcop` | 2411–2416, 2595–2603, 2692–2693 | Integrator data choice for the two index identifications, small; final companion lane supplies the final-`k` fields for the full target. |
| Stage Kummer `Setup`, existing witness choice, two reference CM equations, orbit and local weight inputs, comparison geometry and coefficient reading | 2460–2498, 8247–8259, 8340–8405, 9105–9113, 9195–9295, 9347–9350 | Existing setup and witness, ELLIOT reference-point identification, and sibling stage join, stage identification, intertwining, theta and (O.7) work. The new value does not identify the chosen orientation with the reference point used there. See `docs/research/rc-stage-kummer.md` for the individual comparison inputs. |

## Known issues

- Tex 2915 uses its subscript for a **conductor**. The print's `d` is an
  **order discriminant**. In the prepared case the conductor is one and the
  discriminant is `D*hstar`. The source is cited first at tex 2915–2919 and
  Cai–Chen–Liu §2. The archived audit identifies Theorem 2.15, p. 3730 as
  the trace relation; it does not verify the field-of-definition statement's
  own locator. The pinned offprint is absent. Shimura (1971), Ch. 6 is the
  fallback (theorem and page UNVERIFIED).
- The existing CST height print assumes the elliptic value over the specific
  ring class field, as does the fixed witness datum's `hy` field. Algebraicity
  over `ℚ` does not supply that field. Neither this height print nor the
  witness supplies the missing comparison. No new file imports a TYZ
  module directly. The mandated existing selector already imports
  `TYZGenus.RingClassTwo` through its character module; the CM print and
  morphism evaluation do not use that dependency.
- `HasWeakWeilParametrization` and `NewformPeriodsRational` supply analytic
  periods and a scale. `NewformS13.modularPointFieldHom` and the analytic
  differential calculation start from rational function-field coordinates.
  They do not construct the canonical comparison or identify the map on
  complex points with the fixed `phiAn`. No extra print is used for either
  of those steps.
- No manuscript error was found in the steps used here; the external CM
  passage remains unread.

## Manuscript check

- 1781–1788, 2836–2838 — unverified: rational parametrization with complex compatibility at the recorded scale; the exact missing statement is named.
- 2839–2844, 2915–2919 — unverified: the manuscript places the enhanced CM point over the ring class field; the primary source's separate field-of-definition clause has not been read.
- 2915–2917 — gap filled: evaluate the rational morphism on the `H`-point and prove that the resulting Weierstrass point commutes with the chosen complex embedding.
- 8209–8212 — OK: the prepared data give the negative odd fundamental discriminant and splitting at the level. The print's level coprimality follows from the unit clauses.
- 2411–2416, 8213–8217 — gap filled: specialize the value theorem at conductor one, with the exact field and chosen form used by both Lean consumers.
- 9272–9285 — unverified: identifying this chosen form and embedding with the same oriented reference point in the geometric comparison is outside scope.
- 9347–9350 — OK for the use of rationality: evaluation of a morphism over `ℚ` commutes with field extension. Construction of the morphism with the fixed comparison is the scoped stop.
