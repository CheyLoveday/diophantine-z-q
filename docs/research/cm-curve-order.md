# cm-curve-order: the original CM order statement is proved; the CM fold loses one GLUE

**VERIFIED.** The verbatim `CMCurveOrder` body at `324f0655a` is proved from the existing
T6 input. `CMFibreSplit` is supplied from inputs already available in the height proof.
The open78 CM fold and the `frozenTarget` dry run compile with only `propext`,
`Classical.choice`, and `Quot.sound`. No new leaf or GLUE is introduced.

- Before: **H strict LEAF/GLUE 5/28 on 33** (cm-fold-rebase, open77 CM).
- After: **H strict LEAF/GLUE 5/27 on 32** (open78 CM).

The research bundle loses exactly `cmFibreSplit` (31 fields to 30). The textbook bundle
has zero fields; the added bundle retains its two fields. The H count excludes pole
completeness. The five strict LEAF ratings and the four other CM rows are unchanged.

## Exact Lean statement

The base is cm-fold-rebase `664e00417`. Merge `471bbc0da` brings in the refreshed
`origin/wip/cm-fibre-split` at `fe5ad6a96`, including the requested `324f0655a`.
`origin/main` at `15c9e93d3` had no CMFoldRebase in its history, so the target is open77 CM.

There are two versions of the statement. At `324f0655a`, the binder for `A` has no
dimension condition, despite the docstring discussing a surface. The later
fibre-split branch inserted `A.dim = 2` and proved that specialization. This task proves
the original body, under the name `CMCurveOrder324` to coexist with the merged definition.
Both the production and scratch copies match the original body byte for byte. The scratch
file checks definitional equality and applies the proof. The dependencies are the original
`Kd` (the `AdjoinRoot` of `X² − d`), `cmp` (composition), `IsImagQuadOrder`
(totally complex quadratic field, integral subring, nonzero conductor), and `IsCMBy`
(a ring isomorphism with the full geometric endomorphism ring). They are imported from
the original tree. No consumer changes: `cmCurveOrder_of_324` specializes the original
statement by ignoring the extra surface condition.

`ZInQKernel/Contrib/OneProof/CMCurveOrder.lean` exports
`HDec.CMBranch.FibreSplit.cmCurveOrder324_of` from
`ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC` (T6). It also exports
`cmFibreSplit_of_curveOrder324` with conclusion exactly `HDec.CMBranch.CMFibreSplit`.
The latter takes T27 (Yu's dichotomy), T6, G2 (`FibreCoverExists`), Néron–Ogg–Shafarevich,
Raynaud, and torsion structure. At open4 these are `hYu`, `t.t6`, the existing G2
construction from the moduli row, `r.r7a`, `r.r6`, and `t.t5`, respectively.

## Manuscript check and proof

**VERIFIED against the 11/5 TeX.** The passage in the proof of `thm:height`, L582–587,
is correct as written. L582 uses the imaginary quadratic field from L575–577.
At L583–586 the scaled matrix units produce an elliptic factor with rational geometric
endomorphism algebra `k`; its integral geometric endomorphism ring is a full order of
that field, so its discriminant is defined and negative. This is the manuscript's own
step (ELLIOT). The standard fact used there is the corner description of the endomorphism
algebra of an isogeny factor together with the order property of its integral endomorphism
ring. It is uncited at that point. The class number sentence at L586–587 uses the separate
classical degree formula for a singular modulus, also uncited there. Fowler is cited at
L588 for the effective bound, after the order and its class number have been supplied.

**On-the-spot, proper corner.** Over the algebraic closure `Ω` in the statement, write
`i : E → A`, `h : A → E`, and `h ∘ i = [n]`. Then `ε = (1/n) i ∘ h` is idempotent
in `End⁰(A)`. It is nonzero: if `i ∘ h = 0`, composing with `h` and `i` gives
`[n²] = 0` on the positive-dimensional `E`, contradicting torsion-freeness and
`1 ≠ 0`. If `ε = 1`, then `i ∘ h = [n]` on `A`, and
`g ↦ h ∘ g ∘ i` embeds `End(A)` in `End(E)`: composing back gives `n²g`, so the
kernel is zero. The former has ℤ-rank 8 by rationalization and the given matrix algebra;
the latter has rank at most 4 by T6, using an embedding `Ω → ℂ`. This is the new
argument that avoids assuming `A.dim = 2`. A nonzero proper idempotent in `M₂(k)` has
rank one. Its corner consists of scalar multiples of `ε`, with the scalar given by trace.

**On-the-spot, the full integral order.** Embed `End(E_Ω)` into that corner by
`g ↦ (1/n) i ∘ g ∘ h`, then take the trace. The resulting injection into
`k = ℚ(√d)` has integral image by finite generation over ℤ (T6). Clearing a
denominator for the scalar matrix `√d · 1` and applying `h` and `i` produces a
nonzero integer multiple of `√d` in the image. The suborder it generates has finite
index in `𝓞_k` (the existing Lean conductor argument), so the whole image has finite
index too. The negative square rules out a real embedding of `k`. Finally, the
`L`-isomorphism between `Ω` and Mathlib's `AlgebraicClosure L` transports the
base changed schemes and their group laws, and hence their endomorphism rings. This
uses the merged fibre-split helpers and proves the order property without a CM
classification theorem. T6 is the existing chain's Hom rank and finiteness statement;
its tree locator is Mumford, *Abelian Varieties*, §19 Thm. 3
(`h-trust.md`, step A8; the locator is UNVERIFIED here).

There are **no new leaves to rate**. For tracking, these are the inherited CM inputs:

| Inherited row | Printed form? | Reason and existing flag |
|---|---|---|
| `fowlerProp27` | Yes, per the cm-fold-rebase rating | Prop. 2.7 via the order discriminant and class-number dictionary; upstream audit read, pending review. Manuscript L588–590. |
| `cmjDegree` | No | Only the consequence `#Pic(R) ≤ [L:ℚ]`; ELLIOT-literature, uncited at L586–587, locator UNVERIFIED. |
| `cmPotentialGood` | No | Formulated as existence of a group model after a finite extension; ELLIOT-literature, uncited at L596–597, locators UNVERIFIED. |
| `cmHeight62` | No | Good-reduction case and upper half of the formula; cited consequence, pending review. Manuscript L600–605. |

## Fold and checks

The hand spec is `scratch/cm-curve-order/autofold.json`. Its generated module
`ZInQKernel/Contrib/OneProof/CMCurveOrder/Fold.lean` exposes
`HDec.HSyn.sixContactMin_of_open78_cm` on `OpenResearchLeaves59CMFS`,
`OpenTextbookLeaves18`, and `OpenAddedLeaves27`. It supplies the CM split at open4
and reuses the open77 reductions, including the GR §9 route. The new proposition
bundle and theorem chain are new declarations. Main and all existing Lean files
are unchanged.

- **VERIFIED:** both new Lean modules and the scratch files compiled with sequential
  `lake env lean` runs; the existing imports used the two merged worktrees' cached
  build artifacts. `MainDryRun.txt` records the standard axioms on the order proof,
  its specialization, the split provider, open78, and the frozen target.
- **VERIFIED:** `Closure.lean` checks that the open78 theorem reads every one of its
  30 research fields and uses the proof of the original order statement. It does not
  read the old split projection or the removed González–Rotger or R5 rows.
- **VERIFIED:** stock `#discharges` against Main/open76 does not have a CM field to
  match (`Discharges.txt`). The checker also only flattens bundles declared under
  `ZInQKernel.OneProof`. `CMDischarges.lean` therefore runs the same checker on the
  pre-fold open77 telescope with the CM field curried out and reinserted at the old
  call site. Its transcript reports `DISCHARGES [cmFibreSplit]` for the new provider
  with the six existing inputs above and just the standard axioms.

## Known issues

1. No gap or mismatched citation was found in the assigned implication at L582–586.
   The difference between the two Lean versions is resolved by proving the original
   and specializing it. The class-number and potential-good-reduction rows remain as
   rated above; this task did not reread the adjacent published CM bounds.
2. The inherited chain obtains the matrix-algebra dichotomy via its existing Yu
   input, whereas the manuscript derives it using the Hodge centralizer at L564–577,
   citing Milne there. This is the pre-existing difference recorded in
   `cm-fibre-split.md`; the order proof starts at L582 with the matrix algebra in hand.
   No Gross–Zagier or Tian–Yuan–Zhang argument is used.

The remaining integration step is to switch Main to the new bundle and top using
the hand spec and regenerate the open-row documentation.
