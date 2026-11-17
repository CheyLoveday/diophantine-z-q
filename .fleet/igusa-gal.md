# igusa-gal (11-17)

**Result.** I addressed review queue14's objection to `igusaGL2DS`: lifting σ₀ from `Gal(ℚ(j, E_j[N])/ℚ(j))` to
`Aut(\overline{ℚ(j)}/ℚ(j))` is now a Lean proof.
* New leaf `X1Igusa.IgusaGL2DSGal`: Diamond–Shurman Thm 7.6.3 with σ₀ in `Gal(L_N/ℚ(j))`, where
  `L_N = LDS N = ℚ(j, E_j[N])` (the adjoin of the x and y coordinates of `E_j[N]` inside `\overline{ℚ(j)}`) and
  `1 < N`.
* `igusaGL2DS_of_igusaGL2DSGal : IgusaGL2DSGal → IgusaGL2DS` uses liftNormal, liftNormal_commutes and
  IsAlgClosure.normal (`ZInQKernel/Contrib/OneProof/IgusaGL2DSGal.lean`).
* The one-basis form `IgusaGL2DSGalSome` and its proof of the every-basis form are in
  `ZInQKernel/Contrib/OneProof/IgusaGL2DSGalSome.lean`.
* No consumer of `IgusaGL2DS` loses anything: they all take it as a hypothesis.

**Page check.** Diamond–Shurman, read in the 2005 and 2016 printings. Every answer is favourable:
* Thm 7.6.3 is on p. 290 / p. 294;
* ρ is the action on `E_j[N]` in the one basis `(P_τ, Q_τ)`, p. 287 / p. 291, so the every-basis form is a
  consequence, now proved in Lean;
* `N > 1` (§7.5 opening, p. 279 / p. 283);
* `E_j[N]` lies in the algebraic closure of `ℚ(j)`, with `j` transcendental (p. 282 / p. 286 and
  p. 287 / p. 291);
* the group law is chord–tangent (§7.1, pp. 253–254 / pp. 257–258).

**What compiles** (all on standard axioms):
* both new files;
* `#discharges`: `OpenResearchLeaves45.igusaGL2DS` is discharged by either theorem;
* the Main build;
* the autofold dry-run module (`scratch/igusa-gal/DryRunFold.lean`).

**Autofold.**
* `scratch/igusa-gal/autofold.json` folds `IgusaGL2DSGal`; `autofold-some.json` folds `IgusaGL2DSGalSome`.
  I recommend the second, since it is closer to the print.
* Both dry runs give strict 9/25 → 10/24 and strictest 9/25 → 10/24: one GLUE fewer, new row LEAF/LEAF with
  flag_class unread.
* The exact row is in `scratch/igusa-gal/kinds-row.tsv`.

**Remaining.** Both new rows still need a reviewer, and no human has read the pages. Report:
`docs/research/igusa-gal.md`.
