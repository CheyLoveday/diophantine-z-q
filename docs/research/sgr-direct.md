# sgr-direct: removing `shimuraIntegralModelRep` by proving its consumer directly

Task sgr-direct, 2026-11-15. Base `43513d87` (leaf-fold25, 56 H fields). Lean:
`ZInQKernel/Contrib/OneProof/SGRDirectNV.lean` (new, namespace `SGRDirect`). Scratch: `scratch/sgr-direct/`
(`log.md`; `NV.lean` = the Contrib file plus `#print axioms`; `Ram.lean`, `Vert.lean`, `Branch.lean` = the three
proofs as first compiled; `Discharges.lean` with `Discharges-output.txt`; `autofold.json`). Marks: **VERIFIED**
(read, compiled or computed), **STANDARD** (published, reference given), **SPECULATIVE**. No network, so every
theorem number recalled from memory is **UNVERIFIED**.

## 1. Result

**Not every step is proved yet, but the integral model is gone.** The field's consumer is proved from bundle fields
plus two named GLUE Props, and neither Prop mentions an integral model or a moduli problem over a base. Removing
the field outright from existing fields alone, with every step proved, is not reached.

1. **The consumer is a statement about function fields** (§2, VERIFIED by reading the chain).
   - The field enters the H chain at exactly one place, `HDec.HeckeRestNV.HeckeVertWitness`.
   - That statement is about the Hecke cover `E/ℚ(X)`: the Galois function-field extension that carries the
     normalization chart of the R1fp/R2fp curve. It says `E` has an unramified vertical prime at every `p > 324`.
   - It mentions no abelian scheme.
   - The added-bundle GLUE field `quotientP1Coordinate` has the same single consumer, so a proof of
     `HeckeVertWitness` removes both rows.
2. **The direct abelian-variety route does not close** (§3, argued; SPECULATIVE as an impossibility claim).
   - Good reduction of the QM surfaces at the points used follows from bundle fields: NOS `r7a`, Raynaud, SGA 7 IX.
   - It does not give the consumer's statement. Excluding `𝒪`-linear automorphisms of the reduction needs one of
     three inputs:
     - characteristic-`p` moduli;
     - the integral model (the field itself);
     - the local tame-cover analysis of h-b1's Lemma NV.
3. **Route NV, compiled** (§4, VERIFIED: `lake build`, standard axioms):

   ```lean
   theorem SGRDirect.heckeVertWitness_of_nvSqrt (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure)
       (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
       (hL : NVLocalInertia) (hQ : HeckeSqrtBranch) : HDec.HeckeRestNV.HeckeVertWitness
   ```

   - The first five hypotheses are exactly what the chain already passes to the consumer
     (`HeckeRestAll.coverModelOfHecke_of_heckeRest`). They come from the bundle fields `r1r2`, `t5`, `qmAutCard`,
     `serreRigidity3`, `alFixedPoints`.
   - The two remaining named Props, both GLUE:
     - `NVLocalInertia`: local algebra of tame covers, h-b1 Lemma NV step 3.
     - `HeckeSqrtBranch`: `E` contains `√(a(27X + 16))` with `a` prime to `p > 324`, from Elkies' model of `X₆`.
4. **Three further named Props are proved in Lean** (VERIFIED, standard axioms). Route NV started with five; these
   three are now theorems:
   - `ramifiedSqrtInertia`: Hilbert theory over `ℚ[X]`, with the fixing group of a sub-ring of integers and Mathlib's
     `card_inertia_eq_ramificationIdxIn`;
   - `vertInertiaTrivial`: Hilbert theory over the DVR `ℤ[X]_{(p)}`. Its residue extensions are separable because
     the degree is `< p` (new lemma `isSeparable_of_finrank_lt`). It closes with the chain's local-ring witness;
   - `heckeBranchFibreUnram`: residue fields over `−16/27` are unramified. It is proved from `R1R2fp` (its
     reciprocity clause, via the kernel's `residue_unramified_over_branch`) and T5 (`MobiusGlue`), which transfers
     residue fields between triples.
5. **A simplification of Lemma NV** (VERIFIED: it is the compiled proof). Step 4 of h-b1's Lemma NV used two branch
   points and the Atkin–Lehner group `W ≅ (ℤ/2)²`. One branch point and one square root are enough: `−16/27` (index
   `2`) and `√(−(27X + 16)) ∈ ℚ(X₆)`.
   - A vertical inertia element fixes the square root, which is unramified at the Gauss prime since `p ∤ 6`.
   - A conjugate of it lies in an inertia group over `−16/27` (step 3).
   - That group has order at most 2, and its nontrivial element moves the square root, which is ramified there.

**Counts.** The bypass fold (§5) would replace `shimuraIntegralModelRep` and `quotientP1Coordinate` (GLUE, GLUE) by
`nvLocalInertia` and `heckeSqrtBranch` (GLUE, GLUE). That is a net change of 0. What it buys:
- **Removed:** the integral model of the Shimura curve, with its pending reading of Kottwitz/Lan, Lemma P and the
  level comparison.
- **Removed:** the tame-quotient scheme theory of mcr-quot.
- **Added:** one commutative-algebra Prop with no Shimura content, whose two hardest inputs the chain already proves
  (purity in dimension 2, Abhyankar over a DVR).
- **Added:** one Prop about the function field of `X₆`, from an existing field.

Proving either remaining Prop makes the fold a strict gain (−1).

## 2. The consumer map (VERIFIED, read in `ZInQKernel/OneProof/H/`)

| step | where | what flows |
|---|---|---|
| `shimuraIntegralModelRep` | TailZ34 `openAddedLeaves16_of_OpenAddedLeaves17` | the only use: `shimuraGoodReductionNoGuard := SGRSplit.shimuraGoodReductionNoGuard_of_printed _` |
| `shimuraGoodReductionNoGuard` | TailX l.266 | `shimuraGoodReduction := CurveSplitGR.shimuraGoodReduction_of_noGuard (R1R2fp_of_rep r.r1r2) _` |
| `quotientP1Coordinate` | TailX l.272 | `modelCoordinateResidue := MCRGlue.modelCoordinateResidue_of_quotient' _` (its only use) |
| `shimuraGoodReduction`, `modelCoordinateResidue` | TailN l.255 (= TailO l.2910) | `heckeVertWitness := heckeVertWitness_of_leaves5 l.shimuraGoodReduction r.r1r2 (torsionStructure_ofK5 t.t5) g.modelCoordinateResidue l.curveBijIso` (their only use) |
| `heckeVertWitness` | TailK l.318 | `propTSAll_of_pieces3 … g.heckeVertWitness` (TailI l.77) → `HeckeRestAll.coverModelOfHecke_of_heckeRest` → `heckeNoVertRam_of_witness` |
| `HeckeNoVertRam` | TailG | → `CoverModelOfHecke` (Beckmann's hypothesis (d)) → `PropTSAll` → `FibreUnramified` → `fibreCoverExists_of_propTSAll'` → `modularConstituent` |

- The needed range is every prime `p > 324`.
- The points used downstream are the `ℚ̄`-points of `Y₃` over `t = J(u)`, for all `u ∈ ℚ ∖ 𝒞`. These are infinitely
  many fibres, including fibres that meet a branch point mod `p` (with Beckmann's divisibility conditions).
- So the consumer needs the full no-vertical-ramification statement, not finitely many points.

## 3. Why good reduction of the QM surfaces does not suffice

Take `σ` in an inertia group at `p`. Either `σ` acts on `E` at the Gauss prime, or it acts on `ℚ̄` at a prime over
`p`, for a point `y` over `t`.

- The fibre over `t ∈ ℚ` is a single Hecke orbit, so `σ` maps the object `(A, ι, η)` at `y` to a Hecke translate
  `(A, ι∘α, η∘u)`.
- `A` has good reduction (STANDARD):
  - potentially good, since the toric rank `t ≤ 2` and `B` cannot act on `ℚ^t`;
  - `η` makes `A[3]` rational, so Raynaud gives semistable reduction;
  - semistable plus potentially good is good;
  - then NOS applies.
- The isomorphism `σ*A ≅ A'` extends to Néron models and reduces to an `𝒪`-linear automorphism of `Ā` that moves
  `η̄` by `u`.
- Concluding `σ = 1` needs the `𝒪`-commutant of `Ā` to have units `{±1}`. In characteristic `p` that commutant is
  an imaginary quadratic or definite quaternion order. Excluding extra units says the reduced point is not
  elliptic, which is a statement about the special fibre of the moduli problem, i.e. the integral model.
- At the Gauss prime the same issue is non-isotriviality of `Ā`.

SPECULATIVE (argued, not a proof of impossibility): no bundle field supplies characteristic-`p` moduli, and none
supplies the integral model except the field itself. Route NV replaces both with commutative algebra.

## 4. Route NV in Lean (`ZInQKernel/Contrib/OneProof/SGRDirectNV.lean`)

**Definitions.**
- `InertiaQ E Q` and `InertiaZ E q`: the `σ ∈ Gal(E/ℚ(X))` with `σ b ∈ B` and `σ b ≡ b mod Q` for every `b` in the
  integral closure `B` of `ℚ[X]`, respectively of `ℤ[X]` (through `ℚ[X]`, the chain's `intPolyAlg`).
- These are Mathlib's inertia subgroups, written as sets.
- Everything else is the chain's own: `BranchData`, `vertPrime`, `nY3`, `UnramifiedAt`, `NormalizationModel`,
  `VertUnramWitness`, `HeckeVertWitness`.

**The named Props.** Each statement and docstring is in the file.

| Prop | content | status | rating, reason |
|---|---|---|---|
| `NVLocalInertia` | `E/ℚ(X)` finite Galois of degree `< p`, branch data in `S ∪ {∞}` with `S` `p`-integral and distinct mod `p`, `b ∈ S` with all residue fields over `X = b` unramified at `p`. Then every vertical inertia element has a conjugate in an inertia set over `X − b`. | **open, GLUE** (project, commutative algebra) | **not printed form.** h-b1 §3 step 3, which rv-h-b1 §3 found "holds as stated". It is a consequence of Abhyankar's lemma (SGA 1 XIII 5.3; Grothendieck–Murre, LNM 208) and Zariski–Nagata purity (SGA 1 X 3.1). Purity is **proved** in the chain for 2-dimensional regular local rings (`PropTSGlue.PurityGlobalDim2`). Locators UNVERIFIED. |
| `HeckeSqrtBranch` | for the Hecke cover, `E` contains `s` with `s² = a(27X + 16)`, `a ∈ ℤ` prime to every `p > 324` | **open, GLUE** (from the field `elkiesX6StarPrinted`) | **not printed form.** Elkies' coordinate `t` (`t = 0, 1, ∞` at discriminants `−24, −4, −3`) equals `(27X + 16)/16` in R2fp's coordinate (branch values `−16/27, 0, ∞`, same CM types). Elkies' chart `s² = −t` then gives `a = −1`, and `Y₃ → X₆` is dominant. The same comparison is in the chain's `X6Kummer.ConicModel` docstring (`j = 16(t − 1)/27`). |
| `RamifiedSqrtInertia` | over a prime above `X − b` with `e ∣ 2`, an inertia element fixing `√(c(X − b))` is `1` | **proved** (`ramifiedSqrtInertia`) | textbook |
| `VertInertiaTrivial` | degree `< p`, trivial inertia at every vertical prime ⇒ `VertUnramWitness E p` | **proved** (`vertInertiaTrivial`) | textbook |
| `HeckeBranchFibreUnram` | residue fields of the Hecke cover over `−16/27` are unramified at `p > 324` | **proved** from `R1R2fp` and T5 (`heckeBranchFibreUnram`) | — |

Neither open Prop is a published statement in printed form. Each is project glue with a named proof route, so
neither is proposed as a LEAF.

**Truth checks** (paper):
- `NVLocalInertia` with `b` a non-branch point says that one unramified good fibre forces no vertical ramification.
  That is the homotopy-sequence form of Grothendieck's tame specialization (h-b1 §1.2).
- Test cases (checked by hand; `p` a large prime):

  | cover | data used | `NVLocalInertia` | composite |
  |---|---|---|---|
  | `ℚ(X)(√(pX))` | residue field over `0` is `ℚ`; `I_V = I_{Q_0} = ℤ/2` | true | — |
  | `ℚ(√p)(X)` | residue fields over `b` ramified at `p` | hypothesis fails | — |
  | h-b1's F1, `y² = p·j(27j+16)` | residue fields over `0` and `−16/27` are `ℚ`; vertical inertia `ℤ/2` (rv-h-b1 R5) | only asserts `I_V ⊆ I_{Q_0}`: true | F1 fails `HeckeSqrtBranch` (its only quadratic subfield has constant `p`), so the composite does not wrongly prove F1 unramified |

**The compiled composite** (`vertUnramWitness_of_nv`, `heckeVertWitness_of_nv`):
- `HeckeBranch` and `HeckeDegree` come from the chain's `TSHecke.heckeBranch_of'` and `heckeDegree_of_torsion`.
- `VertInertiaTrivial` reduces the goal to: every `τ` in the inertia set of every vertical prime `q` is `1`.
- For such `τ`:
  - `τ` fixes `s` (`vert_fix`). Otherwise `2s ∈ q`, so `4a(27X + 16) ∈ q ∩ ℤ[X] = pℤ[X]`, so `p ∣ 64a`.
  - `NVLocalInertia` at `b = −16/27` (residue fields there unramified by `HeckeBranchFibreUnram`) gives `Q` and `g`
    with `gτg⁻¹ ∈ InertiaQ E Q`.
  - `gτg⁻¹` fixes `s`, since `g(s) = ±s` (`conj_fix`).
  - `BranchData` gives `e_Q ∣ nY3(−16/27) = 2`, so `RamifiedSqrtInertia` gives `gτg⁻¹ = 1`, hence `τ = 1`.

**The three proofs.**
- `ramifiedSqrtInertia`. Suppose `σ ≠ 1`.
  - Let `A'` be the integral closure of `ℚ[X]` in the fixed field of `⟨σ⟩` (Dedekind).
  - Let `H'` be its fixing group, a Galois group for `B/A'` (`IsGaloisGroup.of_isScalarTower`). Then `σ ∈ H'`.
  - `σ` lies in the inertia of `Q` in `H'`, so `e(Q|A') = |I_{H'}(Q)| ≥ 2`.
  - The tower and `e(Q | X − b) ∣ 2` give `e(Q ∩ A' | X − b) = 1`.
  - But `s ∈ A'` lies in `Q ∩ A'`, and `X − b = c⁻¹s²`, so `e(Q ∩ A' | X − b) ≥ 2` (`ramificationIdx'` as a
    supremum). Contradiction.
- `vertInertiaTrivial`.
  - `R₀ = ℤ[X]_{(p)}` is a DVR: Noetherian, integrally closed, one nonzero prime, by the chain's `eq_vertPrime`.
  - Let `S₀` be its integral closure in `E`, and `q₂` a prime of `S₀` over the maximal ideal.
  - The residue extensions over `R₀` are separable. They have degree `≤ |G| < p`, by Mathlib's
    `sum_ramification_inertia_eq_card`, so `isSeparable_of_finrank_lt` applies.
  - The inertia of `q₂` lies in the inertia set of `q₂ ∩ B_ℤ`, which is trivial. So `e(q₂ | R₀) = 1`.
  - Hence `p` generates the maximal ideal of `(S₀)_{q₂}`, a local-ring witness. The chain's
    `vertUnramWitness_of_local` concludes.
- `heckeBranchFibreUnram`.
  - A prime over `X + 16/27` and an embedding `φ` give a `ℚ̄`-point `y` of the curve with `π(y) = −16/27` and residue
    field `ℚ(range φ)`, via the chain's `residueImage_comp_openImmersion` and `residueImage_specMap`.
  - `sameTripleMor_of_mobius` (`MobiusGlue` from T5) maps `y` to the witness triple of `R1R2fp`, keeping the residue
    field (`residueImage_comp_eq_of_pt`) and the value of `π`.
  - There the kernel's `residue_unramified_over_branch` gives `p ∤ disc`.
  - `GlueB3Unram.unramifiedAt_of_not_dvd_discr` concludes.

**Checks (VERIFIED).**
- `lake build +ZInQKernel.Contrib.OneProof.SGRDirectNV` succeeds.
- `#print axioms` gives `propext, Classical.choice, Quot.sound` for each of: `heckeVertWitness_of_nv`,
  `vertUnramWitness_of_nv`, `ramifiedSqrtInertia`, `vertInertiaTrivial`, `heckeBranchFibreUnram`,
  `heckeVertWitness_of_nvLocal`, `heckeVertWitness_of_nvSqrt`.
- The file has no code that runs at build time. It only uses `set_option` for heartbeats.
- `#discharges` (`scratch/sgr-direct/Discharges-output.txt`): "63 open hypotheses, 1853 theorems checked,
  7 discharge one". None of the seven is from this file, as expected: `HeckeVertWitness` is not itself an open
  field.

## 5. Fold plan (not executed; `scratch/sgr-direct/autofold.json`)

`autofold.py` cannot express this fold, for three reasons:
- The new theorem proves `HeckeVertWitness`, not `shimuraGoodReductionNoGuard` or `modelCoordinateResidue`.
- `HeckeVertWitness` is a field only at generation `OpenGlue4` (TailK).
- Every generation from TailN up carries `shimuraGoodReduction` (later `NoGuard`, then `IntegralModelRep`) and
  `modelCoordinateResidue` (later `quotientP1Coordinate`) as fields.

So a bypass has to rethread the conversions from the top bundle down to TailN. At the TailN conversion it sets:

```lean
heckeVertWitness := SGRDirect.heckeVertWitness_of_nvSqrt (LeafAdopt.R1R2fp_of_rep r.r1r2)
  (ObjBridge.torsionStructure_iff.mpr t.t5) l.qmAutCard l.serreRigidity3 l.alFixedPoints
  n.nvLocalInertia n.heckeSqrtBranch
```

The names are those of the then-current bundles; check them against TailI/TailK. The strict count does not change
(−2 + 2). The fold is worth doing when the integrator wants the integral model out of the trust base, or once one
of the two Props is proved (−1).

## 6. What remains

1. `NVLocalInertia`. Commutative algebra with no Shimura content. The chain proves its two hardest inputs: purity in
   dimension 2 and Abhyankar over a DVR (T2). Missing is the local step at the closed point `(p, X − b)`. Proof
   route:
   - Adjoin `(X − b)^{1/m}` and `p^{1/m}` with `m` prime to `p`. This gives a 2-dimensional regular local ring.
   - The cover becomes unramified in codimension 1 (T2 at both divisors). Then purity makes it étale.
   - Read off `I_𝔓 = I_{Q_b}` from the unramified residue fields over `b`.

   A good target for a commutative-algebra contributor.
2. `HeckeSqrtBranch`. Take the section `s = φU(eS)` of Elkies' chart (`ElkiesCharts`, field
   `elkiesX6StarPrinted`). Then:
   - identify `t = 1 + 27π₆/16` by a Möbius argument on `X₆/W`;
   - pull `s` back to `Spec B_ℚ` along `h`, the comparison morphism and `fY`;
   - check `(4s)² = −(27X + 16)` on `ℚ̄`-points, and conclude by Jacobson density in the reduced, finitely
     generated `ℚ`-algebra `B_ℚ`.

   Scheme glue, estimated at one to three days.
3. The bypass fold (§5).

sir-printed's alternative, the weaker leaf `ShimuraIntegralModelUsed` (wip/sir-printed), keeps the integral model.
It reduces the reading task, not the GLUE count. Route NV removes the integral model and the tame quotient from the
consumer's proof.
