# Results log

- VERIFIED: starting base `7c092f8c3753f783037df1d31a7253feb70fa323`, clean worktree.
- VERIFIED (source): the active top uses `OpenResearchLeaves67`, `OpenTextbookLeaves18` and
  `OpenAddedLeaves28`; the Faltings fold reconstructs `FaltingsSemistableHeightBC` at `TailZ93`.
- VERIFIED (Lean): the narrowed universal statement follows from the old row alone, using
  `exists_jacBar` and packaging the model over `K`. Both declarations use only the three
  standard axioms; see `CheckJacK.txt`.
- VERIFIED (build): the initial cache predates the base; imports used here were recovered
  from local artifacts whose Lean sources match byte for byte. The old top will be
  rebuilt explicitly from the checked-in `TailZ93.lean` and `Main.lean`.
- VERIFIED (Lean): `javanpeykarBound_of_jacK` reads the narrowed row directly. The
  old geometric-Jacobian model is absent from this reader's proof. Its axiom output
  is in `CheckReader.txt`.
- VERIFIED (process): a superseded cache rebuild survived its first stop attempt and
  overlapped with the next Lean checks. This violated the single-process limit. The
  old job was terminated; the remaining checks ran with an exclusive process lock.
- VERIFIED (Lean): the existential row has a reader and is equivalent to the
  universal form with the existing witness existence and uniqueness inputs.
  `javanpeykarThm111JacKEx_of_an` uses the already present Raynaud and Néron fields.
  Both group-iso and Pic⁰ representative invariance compile; all ten declarations
  checked in `CheckJacKEx.txt` use only the standard axioms.
- VERIFIED (Lean): the generated composite and both dry-run tops report only
  `propext`, `Classical.choice`, and `Quot.sound`. The old row occurs only in the
  original top's closure; the existential row and reader occur only in the new
  top's closure. The Faltings comparison is in both; neither reaches `sorryAx`.
  See `ClosureCheck.txt`.
- VERIFIED (computed): the generator and count output reproduce exactly. The
  in-memory swap preserves 29 H hypotheses (5 LEAF / 24 GLUE) and four other
  hypotheses under both ratings; see `Counts.txt`.
