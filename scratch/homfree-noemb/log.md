# homfree-noemb log

## Setup
- Merged origin/main (c1e4ed1b8, top `sixContactMin_of_open38`, TailZ45) into wip/homfree-noemb: c9ddaeda0.
- Build: reflink copy of leaf-fold33b's .lake/build and lean/.lake/build; `lake build +ZInQKernel.OneProof.Main`
  OK (14100 jobs), frozenTarget standard axioms. VERIFIED.

## Taint analysis (scratch/homfree-noemb/Taint.lean -> taint_out.txt), VERIFIED
- Closure of `ZInQ.OneProof.frozenTarget`: 268,654 constants.
- Seeds: projections `*.t6`, `*.homFreeFiniteAlgClosed`. Carriers (structures with such a field):
  TextbookLeaves, OpenTextbookLeaves2,3,4,6,7,8,9,10,11,12,13.
- Constants whose value depends transitively on a seed: 60 (lines `T`). These are: the projections; the
  conversions that copy/produce the field; the top wrappers `sixContactMin_of_open4..38`; `frozenTarget`;
  the readers `gluePieces_of_open4`, `fibreSimple_of_leaves`, `g8_g12_of_leaves3`, `afterG7_of3`;
  SGRFold.added12_of_open29 / heckeSqrtBranchAny_of_open29 and openGlue7_of_OpenGlue8 (through
  openTextbookLeaves10_of_OpenTextbookLeaves11).
- `sixContactMin_of_leavesR3` is NOT tainted (does not read t.t6), but takes a carrier.
- Untainted constants whose type mentions a carrier (lines `S`, excluding mk/projections): 29.
