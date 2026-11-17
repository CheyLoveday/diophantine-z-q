# y3-fix (fleet summary)

**Result.** `RayClassCFT.ShimuraMainThmIDeligneY3AbU` is proved in Lean from two new printed-form leaves plus the
existing textbook field `mumfordTorsionAlgClosed`. The file is `ZInQKernel/Contrib/OneProof/ShimuraY3PrintedLeaves.lean`
(namespace `Y3Fix`). The two leaves together are equivalent to the field (`print_iff_field`). They replace
y3abu-print's two leaves, which were rated GLUE.

- `y3FineModuliAbP`: representability with Mumford's GIT Def. 7.1 level structure (𝒪-linear, over S, checked at
  geometric fibres), and **without** the ℚ̄-point clause.
  - The ℚ̄-point is proved from Ψ(i,1) (`nonempty_qbar_of_cpt`).
  - The printed and kernel level forms are proved equivalent over ℚ-schemes (`toKer`, `ofKer`; the second uses
    TorsionStructure and `Level3.onto` on the fibre object).
- `deligneCanonicalModelY3EveryH`: the moduli clause is in the print's H₁/Hodge form, `IsHodgeH1`:
  (H₁(A,ℤ), h_A) ≅ (𝒪, h_τ), via a bp-analytic uniformization.
  - The uniformization dictionary is proved both ways: `hodge_iff_lattice`. The converse direction uses
    `uniformizationLeafAll_proof`, a ℂ-linear lift, and arguments from discreteness and countability.

**Compiles (VERIFIED).**
- `lake build +Main +Discharges +ShimuraY3PrintedLeaves` succeeds (14229 jobs). All theorems use only the
  standard axioms.
- `#discharges`: DISCHARGES `OpenResearchLeaves31.shimuraMainThmIDeligneY3AbU`. It still assumes
  [MumfordTorsionAlgClosed (an existing textbook leaf), Y3FineModuliAbP, DeligneCanonicalModelY3EveryH].
- `scratch/y3-fix/autofold.json` dry-run gives strict and strictest 11/18 → 13/17. That is −1 GLUE against the
  current kinds.tsv, and −2 GLUE against y3abu-print's fold as rated now (11/19).
- `FoldCheck.lean` compiles: `sixContactMin_of_open49` uses only the standard axioms.

**Remains.**
- Locator readings (no network). Reading risks are flagged:
  - polarization (locators.md R1);
  - the sign convention h_τ(i) = J_τ;
  - Milne §8 and §14 counted as one theorem.
- The combined fold with grx6ab-print and elkies-print was not run. Their specs need the argument patch given in
  the report §5.

Report: docs/research/y3-fix.md.
