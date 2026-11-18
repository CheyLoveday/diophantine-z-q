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
