# gz-fh: hL2 = `ZInQ.GZDecomp.FHNonvanishing`, split

**Result.** `FHNonvanishing` is proved from two printed leaves, with all glue in Lean (standard axioms):
`ZInQ.GZFH.fhNonvanishing_of_printed : FriedbergHoffsteinB → TwistNewformRootNumber → FHNonvanishing`
in `ZInQKernel/Contrib/OneProof/FHNonvanishing.lean`.

* `FriedbergHoffsteinB` (LEAF, research): Friedberg–Hoffstein, Ann. of Math. 142 (1995), Thm B, specialized to
  weight-2 newforms of trivial nebentypus, `χ₀ = χ_{D₀}` unramified at `S ⊇ {p ∣ 2N}`; local conditions as
  `D/D₀ ∈ (ℚ_p^×)²` (Mathlib `ℚ_[p]`), `ε(½, π⊗χ₀) = 1` as Tau Ceti's root number of the twisted newform.
  Rated: printed form up to a stated dictionary, never stronger. Statement recalled from memory (UNVERIFIED).
* `TwistNewformRootNumber` (LEAF, textbook): Iwaniec–Kowalski Prop. 14.20 / Atkin–Li 1978. The twist by `χ_D`,
  `(D, N) = 1`, is a newform of level `N D²` with root number `χ_D(−N) ε(f)`. Rated: a consequence of the
  printed proposition (Gauss sum evaluated). UNVERIFIED numbers.
* Glue proved: Dirichlet (Mathlib) gives `D₀ = −q`, `q ≡ −1 mod 8N`; the root-number computation
  `χ_{D₀}(−N) ε(f) = (−1)(−1) = +1` is in Lean; reducing `ℤ_p → ℤ/p` and `ℤ_2 → ℤ/8` turns local squares into
  the Heegner hypothesis.
* Variant (`FHNonvanishing/FE.lean`): `FriedbergHoffsteinB_FE` (root number as the sign of the FE) plus
  `TwistFunctionalEquation` (GLUE, implied by `TwistNewformRootNumber`, provable from Tau Ceti's twist and
  Fricke FE without newform theory, not done) also give hL2.

**Compiles.** Both Contrib files build. `#discharges` reports `DISCHARGES [hL2]` for both reductions
(`scratch/gz-fh/Discharges-output.txt`). The proposed Main.lean edit (`hL2` → `hFH hTw`) is checked in scratch
(`gzfh_frozenTarget`), and so is the `FHNonvanishingCd` corollary.

**Cd form.** It doesn't make this split easier, since the same leaves imply it. It would let the project prove
the twisted root number itself: `f ⊗ χ_D` is the newform of `C_{d|D|}`, `d|D| ≡ 3 mod 8`. That needs
HeckeThetaNewform and the Hecke FE extended to `n ≡ 3 mod 8`.

**Remains.** Human checks of FH Thm B (gz-statements §6 H1) and IK 14.20 (H2); the integrator's Main.lean
edit and kinds/locators rows (docs/research/gz-fh.md §4); `TwistFunctionalEquation` unproved.
