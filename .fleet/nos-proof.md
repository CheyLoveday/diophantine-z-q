# nos-proof (fleet summary)

**Result.** `r7a : PkgI2.NeronOggShafarevich.{0}` (Serre–Tate 1968 Thm 1) is proved in Lean from one new leaf,
`NOSProof.NOSConverseSep`: only the direction (c) ⇒ (a) (infinitely many `m` with inertia trivial on `A(K_s)[m]` ⇒
good reduction), over a separable closure as printed. Rated printed form (one implication of the printed
equivalence; locator UNVERIFIED). The directions (a) ⇒ (b) ⇒ (c) are proved outright: (a) ⇒ (b) from the proved
row `ReductionTorsionBijective` (MulEtale, fork PR #19) over `K̄`, and again over any field `Ω ⊇ K` by copying
av-split's injectivity of reduction; (b) ⇒ (c) from infinitely many integer units of `O`. Standard axioms only.
The target of −1 with no new leaf is **not** reached. The count is unchanged at 34/11 (strict and strictest), with
a strictly weaker leaf.

**Why.** The converse is live: one consumer (LPrefix l. 856, QM surfaces over number fields) goes from 3-adic
triviality to good reduction and then to `ℓ`-adic triviality for every `ℓ`. That independence of `ℓ` is the converse's
content, and no open field supplies it. A proof from the open fields (raynaudSemistableSH, Néron fields) would also
need the criterion "`N⁰_s` abelian ⇒ `N⁰` abelian scheme", which is a new leaf, plus weeks of glue (torsion count of
semi-abelian special fibres, `[m]` étale on smooth group schemes, descent from `O^sh`).

**Compiles (VERIFIED).** `ZInQKernel/Contrib/OneProof/NeronOggShafarevich.lean` (lake build).
`#discharges`: `DISCHARGES [OpenResearchLeaves26.r7a] by NOSProof.neronOggShafarevich_of_converse; still assumes
[NOSProof.NOSConverseSep]`. The autofold dry run (`scratch/nos-proof/autofold.json`) compiles, giving
`sixContactMin_of_open36` with standard axioms. `scratch/nos-proof/SepCompat.lean` proves dict-galois's
`NeronOggShafarevichSep` (verbatim copy) from the same leaf, in case that fold lands first.

**Remains.** `NOSConverseSep` itself, plus a reading of Serre–Tate §1 to confirm that (c) is in the displayed
theorem. Report: docs/research/nos-proof.md.
