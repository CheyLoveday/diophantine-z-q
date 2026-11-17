# x6-coarse (fleet summary)

**Result.** The Atkin–Lehner reading risk of the research leaf `x6CoarseModuli` is removed. The new file
`ZInQKernel/Contrib/OneProof/X6AtkinLehnerIdeal.lean` (namespace `X6ALIdeal`) does three things:
* it states the printed (ideal-quotient) form: `w_m(A, ι) = (A/A[I_m], ι_m)`, with `I_m = {a ∈ 𝒪 : m ∣ nrd a}`
  and the quotient read as an `𝒪`-equivariant isogeny with scheme-theoretic kernel `A[I_m]`;
* it proves `I_m = 𝒪μ_m` and that `ι(μ_m)` realizes the quotient as `(A, ι ∘ Ad μ_m)`;
* it proves **printed ⇒ twist with no hypothesis**, and **twist ⇒ printed** from the bundle's existing textbook
  fields `gagaMorphism` and `mumfordTorsionAlgClosed`. The missing fact "A/A[I] ≅ (A, ι ∘ Ad μ) for principal `I`"
  is proved through the lattice model (`iso_of_quotient_lat`), so no new textbook leaf is needed.

The Galois clause is proved to be exactly the naturality square of the coarse map at `Spec σ`
(`galoisClause_iff_natural`, no hypothesis; it constructs the base change of a QM pair along `σ`). New leaf
`X6CoarseModuliIdeal` (printed form; replaces `x6CoarseModuli`, proof `x6CoarseModuli_of_ideal`).

Elkies (1) step (b) is done: `ElkiesX6StarEveryIdeal` uses Elkies' isogeny-form `W`. On the coarse witness the two
`W`'s coincide (`atkinLehnerW_eq_of_clause`, via `hom_ext_qbar`), and `elkiesX6StarEvery_of_ideal'` discharges
`elkiesX6StarEvery`. Steps (a) and (c), and GR's transport step T1, are analysed but not proved
(docs/research/x6-coarse.md §4). GR's T2 is covered by `x6CoarseModuli` plus the proved coarse comparison.

**Compiles (VERIFIED).** The contribution builds; all 52 theorems use the standard axioms. `#discharges` shows
`x6CoarseModuli` and `elkiesX6StarEvery` discharged. The autofold dry run (`scratch/x6-coarse/autofold.json`) gives
16/18 → 16/18, since the new leaves are flagged GLUE until review; if `X6CoarseModuliIdeal` is rated printed, −1.
The fold module `sixContactMin_of_open56` compiles with the standard axioms.

**Remains.** A reviewer rating for `X6CoarseModuliIdeal`. Elkies (a) needs a quotient curve; (c) needs exactness of
`HasCM*` and the closed facts for `ℚ(√−6)`, not `h(−24)`. GR's T1 needs Shimura's moduli interpretation of `Γ∖ℍ` (a
new printed input). The docstring corrections for GRDict and ElkiesX6StarEvery are written out in the report.
