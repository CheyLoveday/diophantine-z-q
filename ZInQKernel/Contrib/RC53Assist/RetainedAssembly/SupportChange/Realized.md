# Actual-stage realization of the retained inner limit

The new entry point is
`ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange.assemble_from_support_change_realized`.
It has the same arithmetic assumptions as the support-change assembler and adds
no realization hypothesis. All earlier files are unchanged.

The conclusion produces the six-coordinate residual control `T` and one
`AssembledLimit L`, with the chosen stages equal to the existing
`producedStages`, together with `L.Realized`.

`L.Realized` states, on one ultrafilter-large set of positive stages, that the
same retained complex `L.C` and pairing `L.D` are realized on a bounded finite
free model of `F.globalCx i`. Each stage witness has:

```lean
model : GCx (StageA i)
retract : GRetract (F.globalCx i) model
coordinate : ∀ n : ℤ,
  model.X n ≃ₗ[StageA i] (Fin (L.C.rank n) → StageA i)
```

The normalized retract gives actual inclusion, projection and contraction,
with `pi = 1`, `1 - ip = dh + hd`, `h² = hi = ph = 0`. It therefore gives an
actual homotopy equivalence. Coordinates prove finite freeness of every term;
the retained rank window proves boundedness.

Let `j` denote `retract.i`, `e` denote `coordinate`, and put
`Qᵢ := (L.stages i).pairing`, `trᵢ := (L.stages i).trace`, and
`pᵢ := (L.stages i).projection`. For **all model cochains**, the identities are:

```lean
e b (model.d a b hab x) =
  (L.C.d i a b hab).map (stageMap i) *ᵥ e a x

lCoordR (StageA i) n
  ((ghomComp (ghomComp (projG (F.datum i)) (F.restriction i)) pᵢ).f
    n n rfl (j.f n n rfl x)) =
  (L.D.res n i).map (stageMap i) *ᵥ e n x

stageGlobMap Qᵢ trᵢ a b hab
  (j.f a a rfl x) (j.f b b rfl y) =
  e a x ⬝ᵥ ((L.D.glob a b hab i).map (stageMap i) *ᵥ e b y)
```

The first identity has `hab : a + 1 = b`; the third has `hab : a + b = 3`.
They are not merely cohomology, rank or cycle identities. The same inclusion
occurs in localization and global trace.

## Construction

`exists_stageDiagram_of_inputs_realized` repeats the existing graded-model
construction while retaining the normalized retract and the localization/global
trace identities supplied by the stage pairing transport.

`exists_retained_of_stageInputs_realized` calls
`exists_retained_of_stageDiagrams` on those exact stage diagrams and keeps its
matrix-lift identities. It transports the actual model coordinates along the
same rank equality. It does not call a second retained constructor or attempt to
recover discarded witnesses from an arbitrary existential retained output.

`assemble_inner_limit_realized` constructs all fields of `AssembledLimit`,
including the existing conditional fibre certificates, from this one retained
construction. `assemble_from_support_change_realized` derives `T` by the
existing support-change route and calls that strengthened assembler.

The result is a joint existence theorem for a retained diagram and its actual
stage realizations. It does not assert that an arbitrary earlier selected
retained diagram is realized, or that all varying stages have the same rank.
The ultrafilter-large-set qualification is essential.

The exact original arithmetic obligations remain unchanged: support and local
cochain presentation, old-term flatness, original cups/isotropy and duality
comparison, unmatched original complement cases, derivative action, fixed roots
and local dimensions. The concrete local-form normalization, original retained
local trace-cup normalization, label matching and side-to-stage identities are
not supplied by this realization export.

`RealizedAudit.txt` contains all 26 new statement, constructor/projection and
axiom reports. The scratch consumer checks verify the exact differential,
actual composite localization and `stageGlobMap` formulas, finite freeness,
boundedness and homotopy equivalence.

Source and audit checks passed without warnings. Every axiom report contains
only `propext`, `Classical.choice`, and `Quot.sound`. Manuscript locators:
`diophantine_zq.tex`, lines 4385–4451 and 4976–5135.
