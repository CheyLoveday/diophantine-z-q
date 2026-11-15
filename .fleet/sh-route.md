# sh-route (2026-11-14): summary

**Result.** Over fields of characteristic 0 whose DVR has a perfect residue field, reduct-glue's three
strict-henselization leaves are now Lean theorems. They follow from one Néron leaf, and the commutative algebra
needs no other leaf:
- `StrictHenselizationNeron0`, `StrictHenselizationPair0`, `StrictHenselizationInside0`: reduct-glue's statements
  word for word, plus `[CharZero K]` and `[PerfectField κ(O)]`;
- the one leaf is `NeronBaseChangeSH` (BLR §7.2 Thm 1 / §1.2 Prop 2, UNVERIFIED): Néron models base change along
  `O → O₁` with `O₁` a strictly henselian DVR, `e = 1`, separable residue extension and `K₁/K` algebraic.

In characteristic 0 those hypotheses force `O₁ ≅ O^sh` (report §3). So the leaf is the printed
strict-henselization statement, and Lean checks that it is a specialization of reduct-glue's
`NeronBaseChangeUnramifiedDVR`.

**Commutative algebra, proved from Mathlib.**
- The valuation ring of the inertia field of `w` in `Ω = K̄` is a strictly henselian DVR. A uniformizer of `O`
  stays a uniformizer, and the residue extension is algebraic and separable. The inertia group fixes the field.
- These rings nest along finite `K'/K`, with `[E' : E]` finite.
- Key step: Mathlib's `card_inertia_eq_ramificationIdxIn`, applied twice, gives `e = 1` for finite inertia fields.

**Route.** `route_final` proves `RaynaudSemistable0`, `SemistablePersistsDVR0` and `SemistableUnipotent0` from four
leaves and no glue:
- the printed strictly-henselian SGA 7 IX leaves;
- `MulEtaleAbelianScheme`;
- `NeronBaseChangeSH`.

**What compiles.** `scratch/sh-route/ShRoute.lean`, built by `mk.sh` from reduct-glue's verbatim Base/Body plus
Top, CA1–3 and Final. `chk.sh` runs it in 68 s with no errors. It has no sorry or axiom, and its 58 `#print axioms`
lines are all standard.

**What remains.**
1. The kernel rows (`PkgI2.RaynaudCriterion`, `ReductLeaves`) quantify over every field. Using this route means
   restricting them to characteristic-0 fields with perfect residue fields (number fields and their completions),
   or extending the route in two ways:
   - characteristic `p`: use `T ∩ K^sep`, and treat defect;
   - imperfect residue fields: Mathlib's `card_inertia` needs separable residue fields.
2. The BLR and SGA 7 locators are unverified (no network).
