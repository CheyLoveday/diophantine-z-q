# x6-fold results log

## Step 0 (11-14 17:45 PST): setup
- Merged origin/wip/x6-glue (685a56e1). lean/.lake reflink-copied from the x6-glue worktree (identical lean/ZInQ).
- Base check: `lake build --no-build +ZInQKernel.OneProof.Main` reports only two unrelated modules out of date
  (Compiler.Exponential.AlphaEquations, Multiplication.Certificate.Parity).
- Of X6Glue.lean, the base chain already has shimura-split Count.lean (TailZ8) and shimura-glue Deligne.lean
  (Adelic, Y3Conn, DeligneComponentsX6, DeligneNew; TailZ12). Dump1.lean = X6Glue.lean + a dump of its constants
  (name, type hash, line range) to find exact-name duplicates against TailZ19.
