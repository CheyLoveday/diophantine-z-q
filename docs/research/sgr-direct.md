# sgr-direct: removing `shimuraIntegralModelRep` by proving its consumer directly

Task sgr-direct, 2026-11-15. Base `43513d87` (leaf-fold25, 56 H fields). Lean:
`ZInQKernel/Contrib/OneProof/SGRDirectNV.lean` (new, namespace `SGRDirect`). Scratch: `scratch/sgr-direct/`
(`log.md`, `NV.lean` = the Contrib file plus `#print axioms`, `Discharges.lean` with `Discharges-output.txt`,
`autofold.json`). Marks: **VERIFIED** (read, compiled or computed), **STANDARD** (published, reference given),
**SPECULATIVE**. No network, so every theorem number recalled from memory is **UNVERIFIED**.

## 1. Result

**The field cannot be removed today using only fields already in the bundles, with every step proved.** What
this task did instead:

1. **The consumer is a statement about function fields.** The field enters the H chain at exactly one place,
   `HDec.HeckeRestNV.HeckeVertWitness` (§2, VERIFIED by reading the chain). That statement says that the Hecke
   cover `E/ℚ(X)` (the Galois function-field extension that carries the normalization chart of the R1fp/R2fp
   curve) has an unramified vertical prime at every `p > 324`. It mentions no abelian scheme and no integral model.
   - The added-bundle field `quotientP1Coordinate` (GLUE) has the same single consumer.
   - So a proof of `HeckeVertWitness` removes **both** GLUE rows.
2. **The direct abelian-variety route does not close** (§3). Good reduction of the QM surfaces at the points used
   follows from fields already in the bundles: `r7a` (NOS), `raynaudSemistableSH`, the SGA 7 IX leaves, CM via
   `shimuraMainThmIDeligneY3AbU`. It does not give the consumer's statement. An inertia element at `p` acts on the
   reduction through `𝒪`-linear automorphisms, and excluding those needs one of three inputs:
   - the integral model (the field itself);
   - the moduli of QM surfaces in characteristic `p`;
   - the local tame-cover analysis of h-b1's Lemma NV.

   None of these is a bundle field.
3. **Route NV compiled, with no integral model** (§4, VERIFIED: compiled, standard axioms). It uses the bundle
   fields `r1r2`, `t5`, `qmAutCard`, `serreRigidity3`, `alFixedPoints` and five new named Props, all GLUE:

   ```lean
   theorem SGRDirect.heckeVertWitness_of_nv (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure)
       (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
       (hL : NVLocalInertia) (hR : RamifiedSqrtInertia) (hV : VertInertiaTrivial)
       (hF : HeckeBranchFibreUnram) (hQ : HeckeSqrtBranch) : HeckeVertWitness
   ```

   The five Props split into two kinds:
   - **No Shimura-curve content (commutative algebra).** `NVLocalInertia` has a proof route from the chain's
     *proved* Zariski–Nagata purity in dimension 2 (`PropTSGlue.PurityGlobalDim2`, t-purity3) and Abhyankar's
     lemma. `RamifiedSqrtInertia` and `VertInertiaTrivial` are textbook Hilbert ramification theory.
   - **From existing fields.** `HeckeBranchFibreUnram` comes from `shimuraMainThmIDeligneY3AbU` (Shimura
     reciprocity at CM points). `HeckeSqrtBranch` comes from `elkiesX6StarPrinted` (Elkies' chart `s² = −t`).
4. **A simplification of Lemma NV** (VERIFIED: it is the compiled proof). Step 4 of h-b1's Lemma NV used two
   branch points and the Atkin–Lehner group `W ≅ (ℤ/2)²`. One branch point is enough: `−16/27`, with index `2`,
   together with one square root `√(−(27X + 16)) ∈ ℚ(X₆)`:
   - a vertical inertia element fixes that square root (it is unramified at the Gauss prime, `p ∤ 6`);
   - a conjugate of it lies in an inertia group over `−16/27` (Lemma NV step 3);
   - that inertia group has order at most 2, and its nontrivial element moves the square root, which is ramified
     there.

**Counts.** No fold is proposed now. Folding route NV today would replace two GLUE rows
(`shimuraIntegralModelRep`, `quotientP1Coordinate`) by five, a net rise of three. The fold becomes a gain once the
three algebra Props are proved, which needs no new literature: the result is then −2 + 2 = 0 rows, and both rows
that need a Shimura-curve integral model or tame-quotient scheme theory are gone. Proving the two moduli Props from
their fields as well gives −2.

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

Take `σ` in an inertia group at `p`. Either `σ` acts on the function field `E` at the Gauss prime, or it acts on
`ℚ̄` at a prime over `p`, for a point `y` over `t`.

- The fibre over `t ∈ ℚ` is a single Hecke orbit, so `σ` maps the object `(A, ι, η)` at `y` to a Hecke translate
  `(A, ι∘α, η∘u)`.
- `A` has good reduction (STANDARD, and statable from the bundle fields):
  - it has potentially good reduction, since the toric rank `t ≤ 2` and `B` cannot act on `ℚ^t`;
  - `η` makes `A[3]` rational, so Raynaud's criterion gives semistable reduction;
  - semistable plus potentially good is good;
  - then NOS applies.
- The isomorphism `σ*A ≅ A'` extends to Néron models and reduces to an automorphism of `Ā` that commutes with
  `𝒪` and moves `η̄` by `u`.
- Concluding `σ = 1` needs the `𝒪`-commutant of `Ā` to have unit group `{±1}`. In characteristic `p` that
  commutant is an imaginary quadratic order (ordinary reduction) or a definite quaternion order (supersingular).
  Excluding extra units is exactly the statement that the reduced point is not elliptic. That is a theorem about
  the special fibre of the moduli problem, i.e. the integral model.
- At the Gauss prime the same issue appears as non-isotriviality of `Ā`.

SPECULATIVE (argued, not a proof of impossibility): no bundle field supplies characteristic-`p` moduli or the
integral model, apart from the field under study. So the direct route needs a new input. Route NV supplies one
that is commutative algebra.

## 4. Route NV in Lean (`ZInQKernel/Contrib/OneProof/SGRDirectNV.lean`)

**Definitions.**
- `InertiaQ E Q` and `InertiaZ E q`: the elements `σ ∈ Gal(E/ℚ(X))` with `σ b ∈ B` and `σ b ≡ b mod Q` for every
  `b` in the integral closure `B` of `ℚ[X]`, respectively of `ℤ[X]` (through `ℚ[X]`, the chain's `intPolyAlg`).
- These are Mathlib's inertia subgroups, written as sets. They use the chain's `BranchData`, `vertPrime`, `nY3`,
  `UnramifiedAt`, `NormalizationModel`, `VertUnramWitness`.

**The five named Props** (statements in the file; each has a docstring naming its step and source):

| Prop | content | kind | rating, reason |
|---|---|---|---|
| `NVLocalInertia` | `E/ℚ(X)` finite Galois of degree `< p`, branch data in `S ∪ {∞}` with `S` `p`-integral and distinct mod `p`, `b ∈ S` with all residue fields over `X = b` unramified at `p`. Then each vertical inertia element has a conjugate in an inertia set over `X − b`. | GLUE (project, commutative algebra) | **not printed form.** It is h-b1 §3 step 3 (reviewed in rv-h-b1 §3: "holds as stated"), a consequence of Abhyankar's lemma (SGA 1 XIII 5.3; Grothendieck–Murre LNM 208) and Zariski–Nagata purity (SGA 1 X 3.1; **proved** in the chain for 2-dimensional regular local rings, `PropTSGlue.PurityGlobalDim2`). Locators UNVERIFIED. |
| `RamifiedSqrtInertia` | over a prime above `X − b` with `e ∣ 2`, an inertia element fixing `√(c(X − b))` is `1` | GLUE (textbook) | **not printed form.** Hilbert theory (`\|I\| = e`, the inertia field is unramified). Serre, *Local Fields*, Ch. I §7 and Ch. IV §1, UNVERIFIED. Mathlib 4.35 has `card_inertia_eq_ramificationIdxIn`. |
| `VertInertiaTrivial` | trivial vertical inertia set gives `ramificationIdx = 1` | GLUE (textbook) | **not printed form.** `\|I_q\| = e_q · [κ(q):κ(p)]_insep` over the DVR `ℤ[X]_{(p)}` (same references). |
| `HeckeBranchFibreUnram` | residue fields of the Hecke cover over `−16/27` are unramified at `p > 324` | GLUE from the field `shimuraMainThmIDeligneY3AbU` | **not printed form.** h-b1 §3 step 2: the fibre consists of CM points by `ℤ[√−6]` (conductor 1, rv-h-b1 R2), and by Shimura reciprocity their fields lie in a ray class field of conductor 3, unramified outside `{2, 3}`. |
| `HeckeSqrtBranch` | `E` contains `s` with `s² = a(27X + 16)`, `a ∈ ℤ` prime to every `p > 324` | GLUE from the field `elkiesX6StarPrinted` | **not printed form.** Elkies' `t` (`t = 0, 1, ∞` at discriminants `−24, −4, −3`) equals `(27X + 16)/16` in R2fp's coordinate (branch values `−16/27, 0, ∞` with the same CM types). Elkies' chart `s² = −t` gives `a = −1`, and `Y₃ → X₆` is dominant. |

None is a published statement in printed form. That is why none is proposed as a LEAF: each is project glue with
a named proof route.

**Truth checks** (paper):
- `NVLocalInertia` with `b` a non-branch point says that one unramified good fibre forces no vertical
  ramification. This is the homotopy-sequence form of Grothendieck's tame specialization, consistent with
  h-b1 §1.2.
- h-b1's counterexample F1 is consistent with `NVLocalInertia`. F1 is `E = ℚ(j)(√(p·j(27j+16)))`. Its residue
  fields over the branch points `0` and `−16/27` are `ℚ`, and it has vertical inertia `ℤ/2` (rv-h-b1 R5).
  `NVLocalInertia` then only asserts `I_V ⊆ I_{Q_0} = ℤ/2`, which is true.
- F1 fails `HeckeSqrtBranch`. Its only quadratic subfield is `E` itself, and the constant `p` is not a unit at
  `p`. So the composite does not wrongly prove F1 unramified.
- Both checks are by reasoning from rv-h-b1's data, not recomputed.

**The compiled proof** (`vertUnramWitness_of_nv`, `heckeVertWitness_of_nv`):
- `HeckeBranch` and `HeckeDegree` come from the chain's own `TSHecke.heckeBranch_of'` and `heckeDegree_of_torsion`,
  using the same inputs as `HeckeRestAll.coverModelOfHecke_of_heckeRest`.
- A vertical prime `q` exists by lying-over (`exists_vertPrime`).
- For `τ` in its inertia set:
  - `τ` fixes `s` (`vert_fix`). Otherwise `2s ∈ q`, so `4a(27X + 16) ∈ q ∩ ℤ[X] = pℤ[X]`, so `p ∣ 64a`.
  - `NVLocalInertia` at `b = −16/27` gives `Q` and `g` with `gτg⁻¹ ∈ InertiaQ E Q`.
  - `gτg⁻¹` fixes `s`, because `g(s) = ±s` (`conj_fix`).
  - `BranchData` gives `e_Q ∣ nY3(−16/27) = 2`, so `RamifiedSqrtInertia` gives `gτg⁻¹ = 1`, hence `τ = 1`.
- `VertInertiaTrivial` then gives `e_q = 1`.

**Checks (VERIFIED).**
- `lake build +ZInQKernel.Contrib.OneProof.SGRDirectNV` succeeds.
- `#print axioms` gives `propext, Classical.choice, Quot.sound` for `heckeVertWitness_of_nv` and
  `vertUnramWitness_of_nv`.
- The file has no code that runs at build time.
- `#discharges` (`scratch/sgr-direct/Discharges-output.txt`): "63 open hypotheses, 1827 theorems checked,
  7 discharge one". None is from this file, as expected: `HeckeVertWitness` is not itself an open field.

## 5. Fold plan (not executed; `scratch/sgr-direct/autofold.json`)

`autofold.py` cannot express this fold.
- The new Props imply `HeckeVertWitness`, not `shimuraGoodReductionNoGuard` or `modelCoordinateResidue`.
- `HeckeVertWitness` was a field only down at generation `OpenGlue4` (TailK). Every generation between TailN and
  TailZ34 carries `shimuraGoodReduction` (or `NoGuard`, or `IntegralModelRep`) and `modelCoordinateResidue` (or
  `quotientP1Coordinate`) as fields.
- A bypass therefore has to rethread every conversion from the top bundle down to TailN, setting
  `heckeVertWitness := SGRDirect.heckeVertWitness_of_nv …` at the TailN conversion. That is mechanical but long, and
  it is worth doing only once the algebra Props are proved, because the count rises until then (§1).

## 6. What remains

1. `NVLocalInertia`: commutative algebra, with no Shimura content. The chain already proves its two hardest
   inputs, purity in dimension 2 and the DVR form of Abhyankar (T2). Missing is the local step: the strictly
   henselian Kummer structure at `(p, X − b)` and the reading-off of `I_𝔓 = I_{Q_b}`. Good target for a
   commutative-algebra contributor.
2. `RamifiedSqrtInertia`, `VertInertiaTrivial`: Mathlib 4.35 Hilbert theory (`card_inertia_eq_ramificationIdxIn`,
   `ramificationIdx_tower`). For `VertInertiaTrivial` there is the extra step of localizing `ℤ[X]` at `pℤ[X]`.
3. `HeckeBranchFibreUnram`: from the reciprocity clause of `shimuraMainThmIDeligneY3AbU` and the conductor-1
   enumeration (rv-h-b1 R2).
4. `HeckeSqrtBranch`: from `elkiesX6StarPrinted` and the coordinate comparison `t = (27X + 16)/16`.
5. The bypass fold (§5).

sir-printed's alternative, the weaker leaf `ShimuraIntegralModelUsed` (wip/sir-printed), keeps the integral model.
It reduces the reading task but not the GLUE count. Route NV removes the integral model altogether.
