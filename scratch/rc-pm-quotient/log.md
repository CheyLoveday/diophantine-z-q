# Results

- Base merge: 164fadfa60c0f3fee3eb1866a0dd5bf23e5679fc and 77255b723c39631f737224bb96e3393b79b6bc7c.
- Citation verdict: tex 1784–1788 (Milne) and 8468–8474 (Jetchev–Kane), recorded and committed.
- No new print. At the base pins, the reviewed Manin–Drinfeld source transcript is in `RC/PrintsArith/Heegner.lean`.
- Model: Néron extension of fixed `π`, actual residue point reading, additive degree-zero quotient and Frobenius compatibility.
- Operators: normalized cusp, generic signed and Hecke identities specialized on the same quotient.
- CM: contracted place and exact detector residue embedding, source and target diagram, `hπ` through `GoodReduction.hpi_of_integralDiagram`.
- Cusps: actual rational moved cusp image, Manin–Drinfeld, fixed annihilator, additive reduction.
- Assembly: total selector, pinned newform, actual row and focused dependent `#discharges` audit.
- Verification: serial builds under 60 GB user scopes, host load/memory gate. Source-matched dependencies available. Automatic review rejected a build while another lane's Lean process was active; later build attempts were guarded on host process exit.
- Initial `lake build`, Model: FAIL (Frobenius rewrite and model field elaboration in the first draft). Source edits applied; no revised module ran before handoff.
- Operators, Cusps, CM, Assembly, focused `#discharges`: NOT RUN (Lean process gate; no Model artifact).
- Axiom audit: NOT VERIFIED. Static source check: no `sorry`, `admit`, axiom declaration, local notation, or import of `OneProof.Main`; whitespace check passed.
