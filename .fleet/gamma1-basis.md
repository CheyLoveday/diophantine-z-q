# gamma1-basis (2026-11-17)

**Result.** The research field `gamma1IntegralSpan : CoeffFieldFinite.Gamma1IntegralSpan` (rated LEAF strict, GLUE
strictest because "basis ⇒ span" sat inside the statement) is proved from a new leaf in the printed form,
`Gamma1Basis.Gamma1IntegralBasis`: for every N ≥ 1 and k ≥ 2, Mathlib's `CuspForm ((Gamma1 N).map (mapGL ℝ)) k` has a
`Module.Basis` whose members all have integer `qExpansion 1` coefficients (Shimura 1971 §3.5 Thm 3.52, number
UNVERIFIED; Diamond–Im §12.3). Bridge `gamma1IntegralSpan_of_basis` (= `old_of_basis`) is proved, and so is the converse
`gamma1IntegralBasis_of_span`, so the two are equivalent: either printed wording ("has a basis", "is spanned by") gives
the leaf. Rated printed form: LEAF/LEAF, flagged unread, locator UNVERIFIED. Autofold dry run: strictest 11/24 → 12/23
(GLUE −1), strict unchanged, no new glue.

**Checks.** Mathlib's `Gamma1 N` is c ≡ 0, a ≡ d ≡ 1 mod N (Γ₁(N), not Γ¹(N)), contains T, so period 1 is right.
The consumer `DSCoeffExt.EigenformCoeffFieldFinite` quantifies over every k ≥ 2 and every χ, so the leaf has to cover
odd k too. The print covers every k ≥ 2.

**Compiles (VERIFIED).** `ZInQKernel/Contrib/OneProof/Gamma1IntegralBasis.lean` (imports EigenformCoeffFieldFinite only);
`lake build +…Gamma1IntegralBasis +OneProof.Main +OneProof.Discharges` ok; `#discharges`: DISCHARGES
[OpenResearchLeaves41.gamma1IntegralSpan], still assumes [Gamma1Basis.Gamma1IntegralBasis], standard axioms
(scratch/gamma1-basis/discharges-output.txt); dry-run TailZ module (`sixContactMin_of_open60`) compiles with standard
axioms. Spec: scratch/gamma1-basis/autofold.json.

**Remains.** A statement check of the leaf against Shimura's book: the theorem number, the Γ₁(N) convention and the
weight range. A row for `docs/research/locators.md` is proposed in the report (not edited here). Report:
docs/research/gamma1-basis.md.
