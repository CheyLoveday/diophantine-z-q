# x6-fold results log

## Step 0 (11-14 17:45 PST): setup
- Merged origin/wip/x6-glue (685a56e1). lean/.lake reflink-copied from the x6-glue worktree (identical lean/ZInQ).
- Base check: `lake build --no-build +ZInQKernel.OneProof.Main` reports only two unrelated modules out of date
  (Compiler.Exponential.AlphaEquations, Multiplication.Certificate.Parity).
- Of X6Glue.lean, the base chain already has shimura-split Count.lean (TailZ8) and shimura-glue Deligne.lean
  (Adelic, Y3Conn, DeligneComponentsX6, DeligneNew; TailZ12). Dump1.lean = X6Glue.lean + a dump of its constants
  (name, type hash, line range) to find exact-name duplicates against TailZ19.

## Step 1 (18:25): what the base lacks; trimmed body compiles over TailZ19
- Dump1.lean / Dump3.lean = `cat ../x6-glue/X6Glue.lean Dump{1,3}.tail.lean` (not committed): compiled over TailK
  (3 min each, 0 errors) they write x6names.tsv (constant, type hash, line range) and x6edges.tsv (local
  dependency graph). Dump2.lean (over TailZ19) writes x6dups.tsv: 394 NEW, 258 same (same name and same type
  hash): 37 in TailU (qm-split ModuliSplit), 53 in TailR (ModelGlue, CurveSplit), 165 in TailZ12 (shimura-glue
  Deligne/Adelic, shimura-split Y3Conn), 3 in TailZ8 (Count).
- mk_tail.py: keeps the declarations reachable from r1r2_of_published, x6ConicModel_of_published, X6Leaves,
  x6Rows_of_leaves, ElkiesEquationsX6 without passing through a "same" declaration (plus textual safety); drops
  every example and #print. Also: twelve CoarseFactorAG lemmas are verbatim copies (text after the docstring) of
  TailR's CurveSplit lemmas; they are dropped and `open _root_.CurveSplit (...)` added (a thirteenth,
  isDedekindDomain_sections, has different section variables in TailR (IsAlgClosed) and is kept).
- Result x6body.lean: 240 declarations kept, 3434 lines, 167 KB. Test1.lean (TailZ19 + X6Glue's imports + body):
  0 errors, 1 min; r1r2_of_published, x6ConicModel_of_published axioms standard. VERIFIED.
