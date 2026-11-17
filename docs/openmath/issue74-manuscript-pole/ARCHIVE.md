# Route K archive and retirement

The pre-transition revision is
`bf691da2236b494bb429caabc2f907d4ea428c4d` on Deicyde/main.
It is retained in Git; no Route K source files are deleted by this contribution.
The changed `Main` modules no longer expose the old certified-rank assemblies.
`RETIREMENT.json` lists assemblies excluded from the active import targets and
the lower Route K helpers still required by H and density.

The project's `scratch/leaf-fold33/log.md`, item 41 at that revision, reports a
complete build of Main and Discharges, 16,215 jobs, with standard axioms and 36
extracted hypotheses. This is a **project-reported historical result**. This
contribution has not independently reproduced that build or recovered its full
logs. It must not call the revision independently verified.

Before closing #77, the fork integrator must attach the historical build log
and axiom output to this exact revision, or arrange a reproduction, then create
an annotated `route-k-last-built-2026-11-17` tag in Deicyde/diophantine-z-q at the
last revision actually supported by that evidence. The tag must name the
checked SHA and evidence link. Do not tag a source-only snapshot as verified.

This target-fork archival tag remains a merge gate. Publishing a contribution
branch in Chey's fork does not create a tag in Deicyde's repository.
