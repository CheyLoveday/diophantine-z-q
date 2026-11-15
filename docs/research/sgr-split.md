# sgr-split: `shimuraGoodReductionNoGuard` reduced to the printed integral model of the Shimura curve

## 1. Result

The added field `shimuraGoodReductionNoGuard` (`HDec.CurveSplitGR.ShimuraGoodReductionNoGuard`,
`ZInQKernel/OneProof/H/TailW.lean` line 739; kind composite, strict GLUE) is now proved in Lean from two
statements (compiled, standard axioms):

```lean
theorem SGRSplit.shimuraGoodReductionNoGuard_of_printed (hRep : ShimuraIntegralModelRep)
    (g1 : QMAbFieldFibre) : HDec.CurveSplitGR.ShimuraGoodReductionNoGuard
```

(`ZInQKernel/Contrib/OneProof/ShimuraGoodReductionNoGuard.lean`, the one file this task adds under
`ZInQKernel/`). The two statements are:

| new hypothesis | what it says | kind | strict |
|---|---|---|---|
| `SGRSplit.ShimuraIntegralModelRep` | for every prime `p > 324`, the moduli problem of QM abelian surfaces (order `𝒪` of discriminant 6) with full level-3 structure on locally noetherian `ℤ_(p)`-schemes is representable by a proper smooth curve over `ℤ_(p)` (Kottwitz 1992 §5; Buzzard 1997; Morita 1981) | published, flagged **pending reading** | GLUE until read |
| `SGRSplit.QMAbFieldFibre` | the fibre of a `QMAbScheme` at a characteristic-0 field point is an object `QML3` | project glue | GLUE |

**Verdict on curve-split §3.6** ("not statable in published form today"): no longer true. The printed
theorem, representability of the integral moduli problem, is statable over genuine definitions now that the
kernel has r1univ-rigid's `LeafQM.AV.R1UnivRigid.QMAbScheme S`: an abelian scheme over any scheme `S` (a group
object of `Over S`, proper, smooth of relative dimension 2, geometrically connected) with a unital ring map
`𝒪 → End_S(A)` and a level-3 map `η : 𝒪 → A(S)`. Of the five missing definitions listed in curve-split §3.6,
four now exist or have a faithful encoding (§3 below); the fifth, polarizations over a base, is not needed for
the polarization-free form (it enters only the comparison with Kottwitz's PEL form).

**The other routes named in the task do not give the field.** The Néron–Ogg–Shafarevich leaf `r7a`
(`PkgI2.NeronOggShafarevich`) and the Néron/BLR leaves are statements about models of *abelian varieties*
over a DVR (or a Dedekind base). The field's core content is a smooth proper model of the *curve* `Y₃` over
`ℤ_(p)` carrying the family; NOS cannot produce the model of the curve, and even given one, extending the
universal abelian surface over the 2-dimensional regular base `𝒴` needs purity for abelian schemes
(Faltings–Chai V.6.8, Vasiu–Zink; UNVERIFIED), which is not in the bundle. So these routes would replace one
composite by a larger one. Representability is the printed statement (and is how Morita, Carayol and Buzzard
prove good reduction: from the moduli interpretation). SPECULATIVE in its last clause; the first two are
VERIFIED by reading the Lean statements (`ZInQKernel/HDecomp/Objects.lean` lines 861 and 1377).

Everything else the reduction needs is proved here: the clause-by-clause glue (`shimuraGoodReductionNoGuard_of_rep`),
uniqueness of fibres up to isomorphism (`fibreClassUnique`), objects over a field as abelian schemes over
`Spec K` (`qml3AsQMAb_of`), and the relative dimension of an abelian surface (`abVarSurfaceRelDim`, from the
kernel's smooth dimension theory).

The fold that discharges the field (autofold spec `scratch/sgr-split/autofold.json`) moves the strict counts
from 46 LEAF / 13 GLUE on 59 fields to 46 / 14 on 60 (strictest 45/14 to 45/15): the composite GLUE row is
replaced by the printed leaf, which counts GLUE while it is flagged pending reading, and the glue G1. So
`autofold.py` needs `--allow-rise`. If a reading clears the flag on `shimuraIntegralModelRep` (§2.2), the strict
GLUE count returns to 13; if G1 is also proved (§4), it drops to 12.

## 2. The printed leaf

### 2.1 Statement (`ZInQKernel/Contrib/OneProof/ShimuraGoodReductionNoGuard.lean`)

```lean
def QMFamFibre {S T : Scheme.{0}} (𝒜 : QMFamily T) (g : S ⟶ T) (𝒜' : QMFamily S) : Prop :=
  ∃ h : 𝒜'.F.left ⟶ 𝒜.F.left, IsPullback h 𝒜'.F.hom 𝒜.F.hom g ∧
    (∀ a : O, 𝒜'.iota a ≫ h = h ≫ 𝒜.iota a) ∧ (∀ a : O, 𝒜'.eta a ≫ h = g ≫ 𝒜.eta a)

def ShimuraIntegralModelRepAt (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMAbScheme 𝒴.left),
    IsProper 𝒴.hom ∧ SmoothOfRelativeDimension 1 𝒴.hom ∧
    ∀ (S : Over (Spec (CommRingCat.of (Zloc p)))), IsLocallyNoetherian S.left →
      ∀ 𝒜' : QMAbScheme S.left, ∃! g : S ⟶ 𝒴, QMFamFibre 𝒜.toQMFamily g.left 𝒜'.toQMFamily

def ShimuraIntegralModelRep : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p → ShimuraIntegralModelRepAt p
```

`QMFamFibre 𝒜 g 𝒜'` says `𝒜' ≅ g^*𝒜` compatibly with `ι` and `η` (it is the kernel's `IsFibreOf` over an
arbitrary base). For abelian schemes it is the isomorphism relation of the moduli problem: the isomorphism
carries `η'(0)` (the identity) to `η(0)`, so it is a homomorphism by rigidity (Mumford, *GIT*, Cor. 6.4;
UNVERIFIED number). So `ShimuraIntegralModelRepAt p` says: every object over a locally noetherian
`ℤ_(p)`-scheme `S` is the pullback of the universal object along exactly one `ℤ_(p)`-morphism `S → 𝒴`.

### 2.2 Sources and form (locators UNVERIFIED; no network)

* R. Kottwitz, *Points on some Shimura varieties over finite fields*, J. AMS 5 (1992), 373–444, §5: the PEL
  moduli problem with neat `K^p` and hyperspecial `K_p` is representable by a smooth quasi-projective scheme
  over `𝒪_E ⊗ ℤ_(p)`, proper when `B` is a division algebra. Here `E = ℚ`, `p ∤ 6`, `K_p = 𝒪_p^× ≅ GL₂(ℤ_p)`,
  `K^p = K₃ × ∏ 𝒪_ℓ^×` with `K₃` the full level-3 subgroup at `3 ∣ D` (allowed: `3 ≠ p`). The bibliographic
  identity is established in `docs/research/locators.md` row R1; §5 is unread.
* K. Buzzard, *Integral models of certain Shimura curves*, Duke Math. J. 87 (1997), 591–612, §§1–4: the
  polarization-free problem `(A, ι, level)` is representable by a smooth proper curve away from `D·level`.
* Y. Morita, *Reduction modulo 𝔓 of Shimura curves*, Hokkaido Math. J. 10 (1981), 209–238: good reduction of
  the curve and its QM abelian surfaces at `p ∤ D·level`.
* H. Carayol, Compositio Math. 59 (1986), 151–230: its construction is for totally real `F ≠ ℚ`; secondary.

The Lean statement is a consequence of these, never stronger:

1. only `p > 324` (printed: `p ∤ 6`), only locally noetherian `S` in universe 0;
2. `QMAbScheme`'s `η` (with `eta_three`, `eta_ker`) is the same datum as an `𝒪`-linear isomorphism
   `(𝒪/3𝒪)_S ≅ A[3]` when `3` is invertible on `S`: a fibrewise injective map of finite étale group schemes of
   degree 81 is an isomorphism (STANDARD);
3. the determinant condition of the PEL problem is automatic since `𝒪 ⊗ ℤ_p ≅ M₂(ℤ_p)` (STANDARD);
4. polarizations: Kottwitz's objects carry a polarization; by the relative Lemma P (for the fixed Rosati type
   the principal polarization of `(A, ι)` exists and is unique; Boutot–Carayol, Astérisque 196–197 (1991),
   III §1, UNVERIFIED) the two functors agree; Buzzard's form has no polarization.

Flag (pending reading): whether Buzzard's or Morita's printed level structures include a prime dividing `D`
(Kottwitz's do: only `K_p` must be hyperspecial), and the comparison 4 for Kottwitz's PEL form, including the
passage from Kottwitz's `K^p`-orbits of rational level structures to integral ones. This is the human check
curve-split §3.6 already asked for.

### 2.3 Not vacuous, not stronger

The leaf asserts an object `𝒴` with a universal property over all objects; objects exist (e.g. the CM objects
over `ℚ̄` from `R1R2fp`, converted by `qml3AsQMAb_of`), so `𝒴` has `ℚ̄`-points. It quantifies over genuine
abelian schemes (`QMAbScheme`, group law included), not over `QMFamily` (curve-split's objection to a
`QMFamily` universal property, which would assert more than the printed functor, does not apply).

## 3. Status of curve-split's five missing definitions

| curve-split §3.6 item | now |
|---|---|
| 1. abelian schemes over `S` | `QMAbScheme S`: `GrpObj F`, proper, smooth of relative dimension 2, `GeometricallyConnected` |
| 2. `𝒪 → End_S(A)` | `iota_hom`, `iota_one`, `iota_mul`, `iota_add` |
| 3. `A[3] ≅ (𝒪/3𝒪)_S` | encoded by `η : 𝒪 → A(S)` with `eta_three`, `eta_ker` (equivalent when `3 ∈ 𝒪_S^×`, §2.2 item 2) |
| 4. polarizations over `S` | not defined; not needed for the polarization-free form; enters the form argument only |
| 5. moduli functor, representability | `QMFamFibre` + `∃!` (`ShimuraIntegralModelRepAt`) |

## 4. The Lean reduction

All in `ZInQKernel/Contrib/OneProof/ShimuraGoodReductionNoGuard.lean` (namespace `SGRSplit`), also in
`scratch/sgr-split/SGR.lean` (namespace `HDec.SGRSplit`).

* `shimuraGoodReductionNoGuard_of_rep : ShimuraIntegralModelRep → QMAbFieldFibre → QML3AsQMAb →
  FibreClassUnique → ShimuraGoodReductionNoGuard`. Clause by clause, with `(𝒴, 𝒜)` from the leaf and the
  family `𝒜.toQMFamily`:
  - proper, smooth: from the leaf;
  - fibre clause: G1 (`QMAbFieldFibre`);
  - injectivity on `ℚ̄`-points: convert `P` to a `QMAbScheme` over `Spec ℚ̄` (G2); both `y` and `y'` classify it
    (`isFibreOf_of_iso` transports `IsFibreOf` along `P ≅ P'`; `spec_to_Zloc_ext`: maps `Spec R → Spec ℤ_(p)`
    are unique), so `y = y'` by uniqueness;
  - surjectivity: existence for the `QMAbScheme` of `P` over `Spec ℚ̄` (structure map `zlocTo`);
  - Hecke clauses (Yoneda): `twistAb 𝒜 α` (`ι ∘ α`, `η ∘ α`) and `rightMulAb 𝒜 u` (`η(· u)`) are
    `QMAbScheme`s over `𝒴`; their classifying maps `g_α`, `g_{α⁻¹}` are inverse (uniqueness against the
    identity, `qmFamFibre_comp`, `qmFamFibre_id`), and pasting pullback squares shows the fibre at `y ≫ g_α` is
    `P.twist α` (resp. `P.rightMul u`); G3 identifies it with the given `P'`.
* `fibreClassUnique : FibreClassUnique` (G3, proved): the pullback isomorphism of two fibres is
  `𝒪`-equivariant and respects `η` (pullback uniqueness), carries the identity to the identity
  (`eta_left_comp`, after r1univ-rigid's `isGrpFibre_of_rigidity`), so it is a homomorphism by
  `G0FibreSimple.rigidityHom` (proved in the kernel from Mathlib).
* `qml3AsQMAb_of : AbVarSurfaceRelDim → QML3AsQMAb` (G2, proved): `P.A.X` with `ι`, `η` is a `QMAbScheme` over
  `Spec K`; `GeometricallyConnected` from `GeometricallyIrreducible`; the ring and level identities from
  `QMStr`, `Level3`; `eta_ker` at an arbitrary field point `Spec K' → Spec K` because that map is an
  epimorphism (`epi_spec_field`, from Mathlib's `Flat.epi_of_flat_of_surjective`); the relative dimension from
  `AbVarSurfaceRelDim` (`QML3` records `A.dim = 2`, the Krull dimension; `QMAbScheme` needs
  `SmoothOfRelativeDimension 2`).
* `abVarSurfaceRelDim : AbVarSurfaceRelDim` (proved): at `x`, Mathlib's `Smooth.exists_isStandardSmooth` gives a
  standard smooth chart of some relative dimension `d`; the chart has a closed point `z` (`A` is Jacobson);
  `d = dim 𝒪_{A,z}` (`ZInQ.Contrib.Dim.ringKrullDim_stalk_of_chart`) `= dim A`
  (`topologicalKrullDim_eq_ringKrullDim_stalk_of_smooth`, `A` irreducible) `= 2`.
* `shimuraGoodReductionNoGuard_of_printed`, the discharge: `_of_rep` with G2 from
  `qml3AsQMAb_of abVarSurfaceRelDim` and G3 from `fibreClassUnique`.

### What remains

* **G1 `QMAbFieldFibre`** (project glue, not compiled). Outline: the base change `A_y = (Over.pullback y).obj A`
  is a group object (Mathlib's `Functor.grpObjObj`, as in r1univ-rigid's `isGrpFibre_of_rigidity`), proper and
  smooth of relative dimension 2 over `K` (base change); `dim A_y = 2` by the argument of `abVarSurfaceRelDim`
  read backwards (`ringKrullDim_stalk_of_smoothOfRelativeDimension` at a closed point); `ι` restricts to a unital
  ring map `𝒪 → End_K(A_y)` (`Over.pullback y` is monoidal, so it maps `IsMonHom` maps, products and `1` to the
  same); `η` restricts to `𝒪 → A_y(K)` with kernel `3𝒪` (`eta_ker` at `y`); `IsFibreOf` with `pullback.fst`.
  Two inputs are not in Mathlib v4.35 or the kernel:
  1. *geometric integrality*: a smooth, geometrically connected scheme over a field is geometrically integral
     (smooth ⇒ normal; connected + normal + locally noetherian ⇒ integral; Stacks, tags UNVERIFIED). The kernel
     has most of it: `ZInQ.Contrib.Dim.isRegularLocalRing_stalk_of_smooth` (regular at closed points),
     `LeafQM.AV.R1UnivRigid.isReduced_of_smooth`, and Tau Ceti's
     `irreducibleSpace_of_connected_of_isDomain_stalk` (`ZInQKernel/Contrib/TauCeti/AlgebraicGeometry/
     IrreducibleOfConnectedDomainStalk.lean`); missing is the passage from closed points to all points
     (stalks at non-closed points are localizations of stalks at closed specializations);
  2. *injectivity of `ι` on the fibre* (`QMStr.injective`): the kernel of `𝒪 → End(A_y)` is a two-sided ideal;
     a nonzero one contains a nonzero integer `n` (reduced norm), and `[n] ≠ 0` on `A_y ≠ 0` needs `End(A_y)`
     torsion-free, i.e. `[n]` an isogeny (Mumford, *Abelian varieties*, §4 (iv); UNVERIFIED), which the kernel
     does not prove. The level structure alone does not give it.
  So the smallest faithful split of G1 is two textbook leaves (1 and `[n]` surjective) plus Lean transport
  (about 300 lines by the estimate of this task; not attempted for lack of time).
* The reading flagged in §2.2.

## 5. What compiles (all VERIFIED by compiling)

| file | contents | result |
|---|---|---|
| `ZInQKernel/Contrib/OneProof/ShimuraGoodReductionNoGuard.lean` | the deliverable | `lake build +ZInQKernel.Contrib.OneProof.ShimuraGoodReductionNoGuard`: success |
| `scratch/sgr-split/SGR.lean` | same development in `HDec.SGRSplit` | `lake env lean`: no errors |
| `scratch/sgr-split/StatementCopy.lean` | verbatim copy of the field's statement, checked `Iff.rfl` against the chain's | no errors |
| `scratch/sgr-split/Discharges.lean` | `#discharges` | output below |
| `scratch/sgr-split/AutofoldDryRun.lean` | `autofold.py --dry-run --allow-rise` output, line 1 stripped | `sixContactMin_of_open26`, standard axioms |

`#discharges` (`scratch/sgr-split/discharges.out`; the other lines are other contributions already in the tree):

```
DISCHARGES [OpenAddedLeaves16.shimuraGoodReductionNoGuard] by SGRSplit.shimuraGoodReductionNoGuard_of_printed
  still assumes: [SGRSplit.ShimuraIntegralModelRep, SGRSplit.QMAbFieldFibre]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenAddedLeaves16.shimuraGoodReductionNoGuard] by SGRSplit.shimuraGoodReductionNoGuard_of_rep
  still assumes: [SGRSplit.ShimuraIntegralModelRep,
 SGRSplit.QMAbFieldFibre,
 SGRSplit.QML3AsQMAb,
 SGRSplit.FibreClassUnique]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 66 open hypotheses, 1245 theorems checked, 5 discharge one
```

Autofold: `scratch/sgr-split/autofold.json` discharges `shimuraGoodReductionNoGuard` with proof
`_root_.SGRSplit.shimuraGoodReductionNoGuard_of_printed {n}.shimuraIntegralModelRep {n}.qmAbFieldFibre` and two
new rows: `shimuraIntegralModelRep` (published, flag "pending reading: ..."), `qmAbFieldFibre` (project glue).
`--dry-run` reports `strict count: 46/13 on 59 -> 46/14 on 60; strictest 45/14 -> 45/15` and refuses without
`--allow-rise`.

Build note: the worktree reused the prebuilt tree of `~/dzq-check2` (same commit `6edf020d`), then built
`ZInQKernel.OneProof.Main`, `ZInQKernel.OneProof.Discharges` (up to date except `TailZ28`–`TailZ31`, `Main`)
and the new module (59 to 86 s).
