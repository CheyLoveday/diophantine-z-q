# shimura-glue (2026-11-14): summary

**Main result.** Both Deligne leaves of shimura-split are now theorems from Deligne's theorem on `π₀` in
printed form, plus a compiled exact computation. VERIFIED: compiled, standard axioms.
* **The printed form** (`DelignePi0`). A bijection `π₀(Y ×_ℚ ℚ̄) ≃ ℚ^×_{>0}\𝔸_f^×/nrd(K)` under which
  `σ ∈ Aut(ℚ̄/ℚ)` acts by `[u]^{±1}`, where `u = (χ_p(σ))_p` is the cyclotomic idele. It is stated over
  Mathlib's `FiniteAdeleRing ℤ ℚ`, `QuaternionAlgebra 𝔸_f 2 0 (−3)`, `cyclotomicCharacter` and
  `ConnectedComponents`.
* **The computation** (`Adelic.lean`, Mathlib only):
  * `nrd(𝒪̂^×) = ℤ̂^×` and `nrd(K₃) = ℤ̂^× ∩ (1 + 3ℤ̂)`, by Hensel's lemma at every prime;
  * `𝔸_f^× = ℚ^×_{>0} ℤ̂^×` with unique factors;
  * hence `Pi0(𝒪̂^×) = 1` and `Pi0(K₃) ≅ (ℤ/3)^×`, with `σ` acting by `χ₃`.
* **Converses** are proved, so each printed leaf is equivalent to the old leaf.

**Two further results.** VERIFIED: compiled, standard axioms.
* **The Möbius glue is proved.** `MobiusCompose` (`mobiusCompose`): postcompose the kernel's `ToP1` with any
  `g ∈ GL₂(ℚ)`; the translation chart is glued with `objSupIsoProdEqLocus`. With it:
  * `BabaGranathRational` (Baba–Granath Thm 2.1 and Lemma 3.1, without the `j`-values `0, ∞, −16/27`, which the
    audit had not located) gives `BabaGranathX6'`;
  * `ElkiesConicT` (Elkies §3 in his own coordinate `t`) gives `ElkiesConicX6`.

  Both converses are proved too.
* **`ReciprocityCanonical` is a theorem from `RayClassCM`.** `RayClassCM` says CM residue fields embed into
  the ray class field of conductor 3, using the vendored Tau Ceti's `rayClassField`. The glue is proved:
  * ray class fields are unramified away from 3;
  * `ℚ(i)`, `ℚ(ζ₃)`, `ℚ(√−6) ⊆ ℚ(ζ₂₄)` are unramified above 5;
  * towers and discriminants.

**What compiles** (`lake env lean`, one process at a time; all `#print axioms` lines are
`[propext, Classical.choice, Quot.sound]`):
* `Local.lean` and `Adelic.lean` (Mathlib only);
* `Deligne.lean`, `Mobius.lean`, `RayClass.lean` (kernel imports);
* `RowsGlue.lean` (over `TailK`, 73 axiom lines). It contains the bundle `ShimuraGlueLeaves3` (9 fields) and
  `rows_of_shimuraGlueLeaves3`, which gives shimura-split's six rows.

Counts:

| | published form | consequences |
|---|---|---|
| shimura-split | 3 | 5 |
| now | 6 | 2 (`RayClassCM`, `ElkiesConicT`) |

`ShimuraHolFamily` is unchanged.

**Reviews.** Two model reviews (read-only, no human review) found no false or vacuous leaf. They found one
provenance error, now corrected: the Baba–Granath §3.1 table is graded NO in `locators.md`, so the CM
assignment is an UNVERIFIED reading.

**What remains:**
* The adelic subgroup computation from the printed reciprocity law to `RayClassCM`. It needs CM points in
  adelic form.
* Elkies' function-field form, which needs the comparison of points with places.
* `ShimuraHolFamily`, whose printed form needs the canonical model of one component over `ℚ(ζ₃)`.
* `r3`. Its missing definitions are a principal polarization (dual abelian variety) on `PkgI3.AbVar`, and the
  coarse moduli bijection on `ℂ`-points (`X6Props` is over `ℚ̄` only).

Report: `docs/research/shimura-glue.md`. Log: `scratch/shimura-glue/log.md`.
