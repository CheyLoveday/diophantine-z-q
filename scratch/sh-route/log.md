# sh-route results log

Base e38375b3 (wip/w62). Lean 4.35 / Mathlib v4.35.0.

## Setup
- Base.lean, Body.lean: verbatim copies of scratch/reduct-glue/{Base,Body}.lean. olean/ShRG.lean = their
  concatenation (diff with scratch/reduct-glue/ReductGlue.lean empty, VERIFIED); compiled to olean/ShRG.olean
  (110 s, 7.6 GB, no errors, VERIFIED 17:20).

## Top.lean (namespace ShRoute) — compiles over ShRG (VERIFIED 17:40, no errors)
- `IsSHUnram O O₁ hO` := SH DVR ∧ K₁/K algebraic ∧ uniformizer ↦ uniformizer ∧ κ₁/κ separable.
- LEAF `NeronBaseChangeSH` (BLR 7.2/1, 1.2/2; UNVERIFIED): char 0, IsSHUnram ⇒ Néron base change.
- `isSHNeronExt_of : NeronBaseChangeSH → IsSHUnram → IsSHNeronExt`.
- GLUE (commutative algebra) `SHExists0`, `SHInside0`, `SHPair0`.
- `StrictHenselization{Neron,Pair,Inside}0` = reduct-glue statements + `[CharZero K] [PerfectField κ(O)]`;
  each proved from NeronBaseChangeSH + the matching CA Prop.
- `RaynaudSemistable0`, `SemistablePersistsDVR0`, `SemistableUnipotent0` (char-0 forms) proved from the printed
  SH leaves (reduct-glue's proofs replayed).

## CA1.lean (Mathlib only) — compiles, no sorry (VERIFIED 19:05, 18 s)
- `exists_of_mem`: valuation subring W ⊇ R (Dedekind) of Frac R with nonzero center: x ∈ W ⇒ x = a/s, s ∉ center.
- `unit_mul_pow_of_div`: from 𝔮·j ⊆ ϖR (j ∉ 𝔮) every nonzero a/s (s ∉ 𝔮) is ϖⁿ·unit of W (induction on 𝔮-adic order).
- `key_finite`: M/K finite Galois, A ⊆ K DVR with perfect residue field, W over A; x ∈ W∖0 fixed by every σ ∈ Gal(M/K)
  acting trivially mod 𝔪_W ⇒ x = ϖⁿ·unit(W). Proof: S = integralClosure A M, P = S ∩ 𝔪_W, H = Ideal.inertia P,
  E = Fix(H), R = integralClosure A E, 𝔮 = P ∩ R; Mathlib `Ideal.card_inertia_eq_ramificationIdxIn` over A and over R
  (group H, inertia of P in H is ⊤) + `ramificationIdx_tower` ⇒ e(𝔮|p) = 1; `ramificationIdx_eq_multiplicity` ⇒
  p𝓞_E = 𝔮·J, J ⊄ 𝔮; inertia elements act trivially mod 𝔪_W on W (via exists_of_mem) so x ∈ E.
