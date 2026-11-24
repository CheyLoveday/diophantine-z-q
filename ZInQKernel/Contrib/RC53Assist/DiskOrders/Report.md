# Disk orders of the calibration: report

Target: the three fields of `DiskArith G tA shaA` (the disk orders of the Kummer block of
Proposition `ex:arith-central-calibration`, tex 3987–4141; proof at tex 4007–4018 and
(5.7a)–(5.7b) at tex 5280–5302) for the genuine finite central Kummer Selmer complexes
`G.selH i n` of Kummer data `G`.

Write `t = |E^{(h)}(K)[2^∞]|` for the order of the rational `2`-primary torsion of the central
twist (`Nat.card (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2)`), and
`C_K = compactCentralComplex G` for the integral compact Kummer complex of the central twist.

## Status of the three fields

| field | status | theorem |
|---|---|---|
| `arith0`: `\|H⁰\| = 2^{i v₂ tA}` | PROVED for `tA = t` (finite torsion as instance, or from Mordell–Weil) | `arith0_central`, `arith0_of_mordellWeil` |
| `arith3`: `\|H³\| = 2^{i v₂ tA}` | PROVED for `tA = t` from integral self-duality | `arith3_central` |
| `arith2`: `\|H²\| = 2^{i(i + v₂ shaA + v₂ tA)}` | PROVED for `shaA = \|H²(C_K)_tors\|`; at the address curves PROVED for `shaA = \|Ш(E_ℓ/K)[2^∞]\|` from the Kummer sequence | `diskArith_central_actual`, `diskArith_address_sha` |

Inputs of `arith3_central` and `arith2_central`: integral Kummer self-duality of the retained
model (`IntegralCentralKummerDuality`), the Milne finiteness and dimension statements, `K`
totally complex, the places above `2` in the support, rank one of `H¹(C_K)`, finite rational
`2`-primary torsion; for a declared `shaA` also `hsha : |H²(C_K)_tors| = 2^{v₂ shaA}`.

Assembled statements:

* `diskArith_central_actual`: `DiskArith G t |H²(C_K)_tors|`.
* `diskArith_central_of_literature`: the same, with integral self-duality, finite generation and
  finite torsion derived from the nine Milne/Nekovář PRINT statements of the literature route and
  `MordellWeilNumberFieldPrint`.
* `diskArith_central`, `diskArith_central_of_literature_sha`, `diskArith_of_declared_orders`:
  `DiskArith G tA shaA` for declared orders whose `2`-parts are `t` and `|H²(C_K)_tors|`.
* `diskArith_central_selmer`, `diskArith_arithmetic`, `diskArith_address`: at the address
  curves (`K = ℚ(√k)`, central twist the base change of `E_ℓ`, `hcurve`), with `hsha` replaced by
  the order of the genuine Selmer group `Sel_{2^∞}(E_ℓ/K)` modulo the image of the integral free
  part; rank one derived from Selmer corank one over `K` and the coefficient comparison `I`;
  `K` totally complex and `k` not a square derived from `k < 0`.
* **`diskArith_address_sha`**: `DiskArith G t |Ш(E_ℓ/K)[2^∞]|` from eleven PRINT statements
  (the nine of the literature route, Mordell–Weil, and the Kummer sequence
  `KummerSequenceTwoPowerPrint`), `k < 0`, the places above `2` in the support, finiteness of
  `Ш(E_ℓ/K)[2^∞]`, the coefficient comparison `I`, Selmer corank one over `K` and `hcurve`.

## Proved mathematics (bridges)

1. `card_selH0`, `card_selH_zero`: for Kummer local conditions (all `0`-cochains in degree zero,
   injective in degree one), `H⁰(C_f(M_i)) ≅ M_i^{G_{K,S}}` (Nekovář 6.1.3).
2. `finiteCentralTensorEquiv_galois`, `card_central_invariants`, `card_lev_invariants`: the
   twist identification `A_i ⊗ E^{(h)}(K_S)[2^i] ≅ M_i` is Galois equivariant, `A_i` is free of
   rank `i` over `ℤ/2^i`, and Galois descent along `K_S/K` gives
   `|M_i^{G_{K,S}}| = |E^{(h)}(K)[2^i]|^i`.
3. `card_primaryComponent_two`, `torsionBy_eq_primaryComponent`: a finite `2`-primary component
   has order `2^a` and equals the `2^i`-torsion for `i ≥ a`.
4. `card_dual_H3`, `disk3_valuation_eq_disk1`: `H³` of the termwise dual `Hom(P, ℤ₂)[−3]` of the
   Smith resolution model `P` of `C_K` is the cokernel of the transposed degree-zero
   differential, i.e. `H¹(C_K)_tors`; integral self-duality `P ≃ Hom(P, ℤ₂)[−3]` therefore gives
   `v₂ δ₃ = v₂ δ₁` for the constructed Smith disks (the order form of (5.7b)).
5. `card_diskCokernel`, `card_of_coreRank_zero`, `card_torsion_eq_diskCokernel`,
   `card_torsion_two`: `|ℤ₂^r / diag(c)| = 2^{v₂ ∏ c_j}`, `|H³(C_K)| = 2^{v₂ δ₃}`,
   `|H²(C_K)_tors| = 2^{v₂ δ₂}`; with the order tie `DiskTie` of the constructed disks these give
   the finite-level orders.
6. `card_torsion_two_eq_selmer`: `|H²(C_K)_tors|` is the order of `Sel_{2^∞}(E_ℓ/K)` modulo the
   image of the integral free part (tex 4010–4014), given `I`.
7. `card_quot_eq_of_kummer`, `card_selmer_quot_eq_sha`: a divisible image with finite cokernel
   against a divisible kernel with finite image; with the Kummer sequence, the Selmer group modulo
   the image of the free part is `Ш(E_ℓ/K)[2^∞]` when the latter is finite.

## What remains

1. **PRINT statements** (no inhabitants): the nine of the literature route (Milne,
   *Arithmetic Duality Theorems*, 2nd ed., I.3.4, I.2.3 twice, I.2.1, I.4.15, I.4.10(c), I.2.3;
   Nekovář, *Selmer complexes*, 5.4.1, 5.4.3(ii)); `MordellWeilNumberFieldPrint` (Silverman,
   *The Arithmetic of Elliptic Curves*, 2nd ed., Theorem VIII.6.7: "Let `K` be a number field,
   and let `E/K` be an elliptic curve. Then the group `E(K)` is finitely generated.");
   `KummerSequenceTwoPowerPrint` (Silverman X.4.2 for the isogenies `[2^n]`, in the direct limit:
   `0 → E(K) ⊗ ℚ₂/ℤ₂ → Sel_{2^∞}(E/K) → Ш(E/K)[2^∞] → 0`). Page locators of the two Silverman
   statements were not verified here.
2. **Arithmetic hypotheses at the address**: finiteness of `Ш(E_ℓ/K)[2^∞]` (tex 4003–4004, from
   the analytic hypotheses), Selmer corank one over `K` (tex 2616–2626), `k < 0`, the places
   above `2` in the support.
3. **The coefficient comparison `I`** (`KummerCoefficientComparison`: the coefficient-quotient
   complex of `C_K` against the discrete Selmer complex), an existing unconstructed input of the
   central universal-coefficient interface; it is used for rank one and for the Selmer form of the
   degree-two disk. Without it, the general theorems keep rank one and `hsha` as inputs.
4. **Curve binding** `hcurve`: for the calibration's positive addresses it is the existing
   theorem identifying the central twist of `E_ℓ` by `h > 0` with the base change of `E_{ℓh}`.
5. **Binding of the declared orders** of the calibration model (free numbers there): `tA` with
   `v₂ tA = v₂ t` (the meaning `tA = |𝒜(ℚ)_tors[2^∞]|`, `𝒜(ℚ) = E^{(h)}(K)`) and `shaA` with
   `v₂ shaA = v₂ |Ш(E^{(h)}/K)[2^∞]|`; `diskArith_congr_valuation` transfers `DiskArith` along
   such identities.

## Files

| file | content |
|---|---|
| `DegreeZero.lean` | `H⁰` of Selmer cones, central invariants, descent, primary components, Mordell–Weil PRINT and bridge, `arith0_central` |
| `DualityOrders.lean` | disk cokernels, dual top cohomology, `disk3_valuation_eq_disk1`, `arith3_central`, `arith2_central`, `DiskArith` assemblies, non-vacuity examples |
| `Literature.lean` | `DiskArith` from the cited statements |
| `SelmerBridge.lean` | the Selmer-group form of the degree-two disk at the address curves |
| `ShaBridge.lean` | the Kummer-sequence PRINT, the cokernel lemma, `diskArith_address_sha` |
| `AxiomAudit.txt` | elaborated types and axiom dependencies of the principal declarations |

## Verification

* `lake build +ZInQKernel.Contrib.RC53Assist.DiskOrders.ShaBridge` builds all five modules,
  with no warnings in these files.
* The Lean sources contain no `sorry`, `admit`, new axioms, `native_decide`, `implemented_by`,
  notation, macros, syntax, evaluation commands or inspection directives; the default heartbeat
  limit is used; every Lean source line has at most 100 characters.
* Thirty-four audited declarations depend exactly on `[propext, Classical.choice, Quot.sound]`.
