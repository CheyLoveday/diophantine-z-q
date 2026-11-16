# coeff-field results log

Base: wip/coeff-fix 496c1f75, merged origin/main 0caafe66 (STATUS.md only) → ae975643.

## Survey (VERIFIED, read in the tree)
- Vendored Tau Ceti (ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/) has: finite-dimensionality of
  `CuspForm 𝒢 k` (SturmBound.lean:150 `finiteDimensional_cuspForm_finiteIndex`), the Sturm bound,
  the coefficient formula for `T_n` on `cuspFormCharSpace k χ`
  (HeckeSlash/Nebentypus/CoefficientFormula.lean:115), full eigenforms (Newforms/Eigenform.lean),
  complex conjugation of forms (Conjugate.lean).
- No rational structure anywhere: grep for IsAlgebraic / IsIntegral ℤ / FiniteDimensional ℚ / NumberField
  in Tau Ceti ModularForms: no hits. No Eichler–Shimura, no modular symbols, no q-expansion principle,
  no Galois action Aut(ℂ) on forms. Mathlib 4.35: level-one only (E4, E6 graded ring).
- Conclusion: an outright proof needs a rational structure on `S_k(N, χ)`, which is not in the tree.

## Plan
- Glue (to prove): abstract linear algebra — `V` finite-dim over `K`, coordinate functionals `c_i` with
  zero joint kernel, `W = {v | c_i v ∈ F}` spanning `V` over `K`; then eigenvalues of operators
  preserving `W` at a common eigenvector `f ≠ 0` generate a finite-dim `F`-algebra.
- Leaf: `S_k(N, χ)` is spanned over `ℂ` by forms with coefficients in `ℚ(χ)`.

## Abstract.lean (VERIFIED: compiles, lake env lean, 10 s)
- `CoeffField.finiteDimensional_adjoin_eigenvalues`: V f.d. over K, c : ι → V →ₗ[K] K with zero joint kernel,
  span K {v | ∀ i, c i v ∈ F} = ⊤, f ≠ 0, every μ ∈ s an eigenvalue at f of a K-linear T preserving the
  F-rational vectors ⇒ FiniteDimensional F (Algebra.adjoin F s).
