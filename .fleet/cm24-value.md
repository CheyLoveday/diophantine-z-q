# cm24-value — the field `igusaCMValue24` is proved in Lean, with no leaf

**Verdict.** `HDec.LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24` is a theorem: `CM24.igusaCMValue24_field`.
VERIFIED: compiled, no `sorry`, axioms `[propext, Classical.choice, Quot.sound]`.

The same proof also gives:
* qm-split's glue `ThetaQuotientValue24` (`CM24.thetaQuotientValue24_field`);
* the closed statement `ThetaValueAtOmega24`, i.e. `jDen Ω₂₄ ≠ 0 ∧ jNum/jDen = −16/27`.

So the published-form leaf (Lin–Yang (2), (14) at the Baba–Granath CM value) is no longer needed, and row H-88
loses one leaf.

**How.** No CM theory is used. The steps:
1. `W = −Ω₂₄⁻¹ = [[1+i√6/2, ½], [½, ½+i√6/4]]`, and `2W` is `diag(i√6, i√6/2)` up to an integral translation.
   This comes from an extra involution in the Sp₄(ℤ)-stabilizer.
2. Genus-2 theta inversion: two partial inversions, each from Mathlib's `jacobiTheta₂_functional_equation`.
3. Duplication and translation write the ten θ_m(Ω₂₄)² through genus-1 theta constants at the two discriminant
   −24 CM points.
4. Landen and Jacobi's quartic identity follow from the 1D duplication formula.
5. The cubic modular equation `θ₃(τ)θ₃(3τ) = θ₂(τ)θ₂(3τ) + θ₄(τ)θ₄(3τ)` is proved by a lattice
   rearrangement. Used at `i√6/3` with the S-transformation, it gives `m(k) = 0` for
   `k = θ₁₀(i√6)²/θ₀₀(i√6)²`, where `m(k) = k⁴+12k³+2k²−12k+1`. Positivity on the imaginary axis gives
   `0 < k < 1`, which excludes the spurious factor.
6. `3779136P² + (16/27)S⁵ ≡ 0 mod m(k)`, and `S ≠ 0` follows from a Bezout certificate.

**What compiles.**
* `scratch/cm24-value/CM24Value.lean`: imports Mathlib only; contains a verbatim copy of qm-glue's
  `ThetaValue24.lean` plus the proof; about 15 s.
* `scratch/cm24-value/CM24Kernel.lean`: imports `ZInQKernel.OneProof.H.TailZ3` and proves the build's own field
  type. Checked with the oleans of `~/dzq-check2`, whose 527 closure sources are byte-identical to this base.

Both are assembled by `mk.py` / `mk_kernel.py` from `T1.lean`, `Alg.lean` and `P3.lean`; run them with `chk.sh`.
Every step is also checked numerically in `py/`. Report: `docs/research/cm24-value.md`.

**What remains.** Nothing for this field. Optional, not needed by the field: the exact radical value
`k = (2−√3)(√3−√2)`. `CM24Kernel.lean` is ready to become a `ZInQKernel/Contrib/` module.
