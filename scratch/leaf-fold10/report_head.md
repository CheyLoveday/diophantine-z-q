# leaf-fold10: dimjac-glue (`dimJacobianEqGenus` proved) and shimura-glue (`y3Connected` from Deligne's printed theorem) folded into the single proof; 62 fields, strict GLUE 19 (was 21 of 63)

Task leaf-fold10, 2026-11-14. Base 28b41fb3 (fork main after w60, with leaf-fold9 inside OneProof). Merged:
`origin/wip/dimjac-glue`, `origin/wip/shimura-glue`. New Lean:
- `ZInQKernel/OneProof/H/TailZ10.lean` (dimjac-glue's `DimJacGlue.lean`) and `TailZ11.lean` (the bundle
  `OpenTextbookLeaves10`, `sixContactMin_of_open10`);
- `TailZ12.lean` (shimura-glue's `Deligne.lean`) and `TailZ13.lean` (the bundle `OpenAddedLeaves9`,
  `sixContactMin_of_open11`, the new top);
- the switch of `ZInQKernel/OneProof/Main.lean`.

Each new module is under 150 KB. Checks and tools are in `scratch/leaf-fold10/`; the results log is `log.md`. No
existing OneProof module was edited. No other file under `ZInQKernel/`, `blueprint/`, or another task's files was
edited either. This is model work with no human review.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference. **SPECULATIVE** = a
judgement. **UNVERIFIED** = a theorem number or locator recalled without a source. There is no network on this host,
so every locator is the source report's. It is UNVERIFIED unless the audit `locators.md` read it.

## 1. Main result

```lean
theorem ZInQ.OneProof.frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves9) (t : HDec.HSyn.OpenTextbookLeaves10) (l : HDec.HSyn.OpenAddedLeaves9)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) (hS : Shimura.ShimuraReciprocityModFn)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget
```

The H half goes through the new top of the H assembly (`OneProof/H/TailZ13.lean`):

```lean
theorem HDec.HSyn.sixContactMin_of_open11 (r : OpenResearchLeaves9) (t : OpenTextbookLeaves10)
    (l : OpenAddedLeaves9) (g : OpenGlue7) : ZInQ.SixContactMin
```

Two folds were taken. Each lowers the strict GLUE count by one, and neither raises any count.

1. **dimjac-glue (fold (1)).** `ModularSplit.DimJac.dimJacobianEqGenus : ZInQ.Contrib.CurvesG.DimJacobianEqGenus`,
   with no hypotheses, fills the textbook field `dimJacobianEqGenus` (a composite: Milne's Jacobian varieties
   Prop. 2.1 with Serre duality). The field is dropped and nothing is added.
   - The proof is dimjac-glue's: it identifies `H⁰(X, Ω¹_{X/ℚ})` with the holomorphic differentials of the
     function field. It uses Mathlib (Kähler differentials, the valuative criterion, Jacobson spaces, the DVR
     TFAE, sheaf gluing), the vendored Jacobian library `Contrib/CloudW07JacobiansCurves/` and the kernel's
     `Contrib/Dim/`.
   - `ZInQ.Contrib.CurvesG.DimJacobianEqGenus` is a kernel Prop, so the theorem plugs into the field directly.
2. **shimura-glue (fold (2)).** The added field `y3Connected` (`TSHecke.Y3Connected`, a composite: Deligne's
   description of `π₀` plus an orbit computation) is replaced by `deligneComponentsY3Printed :
   ShimuraGlue.DeligneComponentsY3Printed`. That is Deligne's theorem on the connected components of a Shimura
   variety in printed form, for `G = B^×`, `B = (2, −3 | ℚ)`, at level `K₃`, on one fine witness `Y₃`. It is
   stated over Mathlib's `FiniteAdeleRing ℤ ℚ`, `QuaternionAlgebra`, `cyclotomicCharacter` and
   `ConnectedComponents`.
   - The proof is `ShimuraSplit.y3Connected_of_deligne (ShimuraGlue.deligneComponentsY3_of_printed _)`.
     shimura-glue computes in Lean that `ℚ^×_{>0}\𝔸_f^×/nrd(K₃) ≅ (ℤ/3)^×` and that the cyclotomic idele maps
     to the mod-3 character. shimura-split's orbit computation then gives connectedness.
   - The new field carries the witness clause list `R1fpProps` (Lemma QP and R1's "qualified consequence"
     caveat), as `r1r2` and `gonzalezRotgerCountX6` do. Under the stricter reading it is a consequence, and the
     fold is strict 0 (comp → c), lenient −1. No count rises under either reading.

<!--CHECKS-->

**Counts.** The forms are leaf-fold9's. A removed field takes its form with it. The table is printed by
`mk_fields10.py shimura` (`counts10.md`).

<!--COUNTS-->

**Bundles.**
- `OpenResearchLeaves9` (30): leaf-fold9's, unchanged.
- `OpenTextbookLeaves10`: 17 fields (18 in leaf-fold9).
- `OpenAddedLeaves9`: 14 fields (leaf-fold8's 14, with one replaced).
- `OpenGlue7` (1, `QuotientP1Coordinate`): leaf-fold7's, unchanged.

**TYZ side.** Unchanged: `h11`, `h29`, `hS`, `h33`, `hL2`, `hL3`.

**Module layout.**
- `TailZ10` imports `TailZ9` and holds dimjac-glue's `DimJacGlue.lean` verbatim, after its five import lines (four
  kernel `Contrib` modules: `CurvesG.GenusSplit`, two CloudW07 modules, `Dim.SmoothStalk`, `Dim.Basic`). It imports
  only kernel modules besides `TailZ9`, and could move to `ZInQKernel/Contrib/` unchanged.
- `TailZ11` imports `TailZ10` and holds `OpenTextbookLeaves10`, `textbookLeaves9_of_open10` and
  `sixContactMin_of_open10`.
- `TailZ12` imports `TailZ11` and holds shimura-glue's `Deligne.lean` verbatim after its import lines (the kernel's
  `HDecomp.QM.Leaves` and nine Mathlib files), with its three `#print axioms` lines dropped. Besides `TailZ11` it
  imports only kernel and Mathlib modules.
- `TailZ13` imports `TailZ12` and holds `OpenAddedLeaves9`, `addedLeaves8_of_open9` and `sixContactMin_of_open11`.
- `Main` imports `TailZ13` in place of `TailZ9`. The chain from `LPrefix` to `TailZ9` is untouched.
