import Mathlib.NumberTheory.Height.MvPolynomial

/-!
# The `x`-coordinate map of a 2-isogeny doubles heights

Let `K` be a field with an admissible family of absolute values (so that the logarithmic heights
`Height.logHeight₁` and `Height.logHeight` are defined), and let `a b : K` with `b ≠ 0`.
The 2-isogeny of the curve `y² = x (x² + a x + b)` with kernel `{O, (0,0)}` acts on
`x`-coordinates by the rational map `x ↦ (x² + a x + b) / x` of degree two. We prove that this
map doubles heights up to a bounded error:

* `ZInQ.Manuscript.RC.Height.abs_logHeight₁_velu_sub_le`: there is a constant `C` such that
  `|logHeight₁ ((x ^ 2 + a * x + b) / x) - 2 * logHeight₁ x| ≤ C` for all `x ≠ 0`.

We also record
* the projective form `abs_logHeight_velu_sub_le`: the morphism of the projective line
  `(u : v) ↦ (u² + a u v + b v² : u v)` doubles `logHeight` up to a bounded error,
  together with its one-sided bounds `logHeight_velu_le` (valid for all `a b`) and
  `logHeight_velu_ge`;
* the affine one-sided bounds `logHeight₁_velu_le` (valid for all `a b`) and `logHeight₁_velu_ge`,
  and the two-sided bound `abs_logHeight₁_velu_sub_le'` for all `x` (at `x = 0` both heights
  vanish).

Proof: `(x² + a x + b) / x` is the quotient of the binary quadratic forms
`F = X₀² + a X₀ X₁ + b X₁²` and `G = X₀ X₁` evaluated at `(x, 1)`, so its height is the height
of the pair `(F, G)(x, 1)`. The upper bound is `Height.logHeight_eval_le'`; the lower bound is
`Height.logHeight_eval_ge'` applied to the identities
`X₀⁴ = X₀² F + (-a X₀² - b X₀ X₁) G` and `X₁⁴ = b⁻¹ X₁² F + (-a b⁻¹ X₁² - b⁻¹ X₀ X₁) G`,
which express that `F` and `G` have no common zero on the projective line when `b ≠ 0`.
-/

open Height MvPolynomial

namespace ZInQ.Manuscript.RC.Height

/-- Upper bound for the degree-two morphism `(u : v) ↦ (u² + a u v + b v² : u v)` of the
projective line: `h(u² + a u v + b v², u v) ≤ C + 2 h(u, v)`. This direction needs no hypothesis
on `a` and `b`. PROVED. -/
theorem logHeight_velu_le {K : Type*} [Field K] [AdmissibleAbsValues K] (a b : K) :
    ∃ C : ℝ, ∀ u v : K,
      logHeight ![u ^ 2 + a * u * v + b * v ^ 2, u * v] ≤ C + 2 * logHeight ![u, v] := by
  let p : Fin 2 → MvPolynomial (Fin 2) K :=
    ![X 0 ^ 2 + C a * X 0 * X 1 + C b * X 1 ^ 2, X 0 * X 1]
  have hp (i : Fin 2) : (p i).IsHomogeneous 2 := by
    fin_cases i
    · exact ((isHomogeneous_X_pow 0 2).add
        ((isHomogeneous_C_mul_X a 0).mul (isHomogeneous_X K 1))).add
        (isHomogeneous_C_mul_X_pow b 1 2)
    · exact (isHomogeneous_X K 0).mul (isHomogeneous_X K 1)
  obtain ⟨C₁, hC₁⟩ := logHeight_eval_le' hp
  refine ⟨C₁, fun u v ↦ ?_⟩
  have hpx : (fun j ↦ (p j).eval ![u, v]) = ![u ^ 2 + a * u * v + b * v ^ 2, u * v] := by
    ext j
    fin_cases j <;> simp [p]
  have h := hC₁ ![u, v]
  rw [hpx] at h
  exact_mod_cast h

/-- Lower bound for the degree-two morphism `(u : v) ↦ (u² + a u v + b v² : u v)` of the
projective line: `C + 2 h(u, v) ≤ h(u² + a u v + b v², u v)`, provided `b ≠ 0`. PROVED. -/
theorem logHeight_velu_ge {K : Type*} [Field K] [AdmissibleAbsValues K] (a b : K)
    (hb : b ≠ 0) :
    ∃ C : ℝ, ∀ u v : K,
      C + 2 * logHeight ![u, v] ≤ logHeight ![u ^ 2 + a * u * v + b * v ^ 2, u * v] := by
  let p : Fin 2 → MvPolynomial (Fin 2) K :=
    ![X 0 ^ 2 + C a * X 0 * X 1 + C b * X 1 ^ 2, X 0 * X 1]
  -- certificates: `∑ j, q (k, j) * p j = X k ^ 4` for `k = 0, 1`
  let q : Fin 2 × Fin 2 → MvPolynomial (Fin 2) K :=
    ![![X 0 ^ 2, -(C a * X 0 ^ 2) - C b * X 0 * X 1],
      ![C b⁻¹ * X 1 ^ 2, -(C (a * b⁻¹) * X 1 ^ 2) - C b⁻¹ * X 0 * X 1]].uncurry
  have hq (ij : Fin 2 × Fin 2) : (q ij).IsHomogeneous 2 := by
    fin_cases ij
    · exact isHomogeneous_X_pow 0 2
    · exact (isHomogeneous_C_mul_X_pow a 0 2).neg.sub
        ((isHomogeneous_C_mul_X b 0).mul (isHomogeneous_X K 1))
    · exact isHomogeneous_C_mul_X_pow b⁻¹ 1 2
    · exact (isHomogeneous_C_mul_X_pow (a * b⁻¹) 1 2).neg.sub
        ((isHomogeneous_C_mul_X b⁻¹ 0).mul (isHomogeneous_X K 1))
  obtain ⟨C₂, hC₂⟩ := logHeight_eval_ge' (N := 2) hq
  refine ⟨C₂, fun u v ↦ ?_⟩
  have hcert (k : Fin 2) :
      ∑ j, (q (k, j)).eval ![u, v] * (p j).eval ![u, v] = (![u, v] k) ^ (2 + 2) := by
    fin_cases k
    · simp [p, q, Fin.sum_univ_two]
      ring
    · simp [p, q, Fin.sum_univ_two]
      linear_combination v ^ 4 * inv_mul_cancel₀ hb
  have h := hC₂ p hcert
  have hpx : (fun j ↦ (p j).eval ![u, v]) = ![u ^ 2 + a * u * v + b * v ^ 2, u * v] := by
    ext j
    fin_cases j <;> simp [p]
  rw [hpx] at h
  exact_mod_cast h

/-- The degree-two morphism `(u : v) ↦ (u² + a u v + b v² : u v)` of the projective line
doubles heights up to a bounded error, provided `b ≠ 0`. PROVED. -/
theorem abs_logHeight_velu_sub_le {K : Type*} [Field K] [AdmissibleAbsValues K] (a b : K)
    (hb : b ≠ 0) :
    ∃ C : ℝ, ∀ u v : K,
      |logHeight ![u ^ 2 + a * u * v + b * v ^ 2, u * v] - 2 * logHeight ![u, v]| ≤ C := by
  obtain ⟨C₁, h₁⟩ := logHeight_velu_le a b
  obtain ⟨C₂, h₂⟩ := logHeight_velu_ge a b hb
  refine ⟨max C₁ (-C₂), fun u v ↦ abs_sub_le_iff.mpr ⟨?_, ?_⟩⟩
  · linarith [h₁ u v, le_max_left C₁ (-C₂)]
  · linarith [h₂ u v, le_max_right C₁ (-C₂)]

/-- Upper bound for the `x`-coordinate map of the 2-isogeny: `h((x² + a x + b) / x) ≤ C + 2 h(x)`
for all `x`. This direction needs no hypothesis on `a` and `b`. PROVED. -/
theorem logHeight₁_velu_le {K : Type*} [Field K] [AdmissibleAbsValues K] (a b : K) :
    ∃ C : ℝ, ∀ x : K, logHeight₁ ((x ^ 2 + a * x + b) / x) ≤ C + 2 * logHeight₁ x := by
  obtain ⟨C, hC⟩ := logHeight_velu_le a b
  refine ⟨C, fun x ↦ ?_⟩
  have h := hC x 1
  simp only [mul_one, one_pow] at h
  rwa [logHeight₁_div_eq_logHeight, logHeight₁_eq_logHeight]

/-- Lower bound for the `x`-coordinate map of the 2-isogeny: `C + 2 h(x) ≤ h((x² + a x + b) / x)`
for all `x`, provided `b ≠ 0`. PROVED. -/
theorem logHeight₁_velu_ge {K : Type*} [Field K] [AdmissibleAbsValues K] (a b : K)
    (hb : b ≠ 0) :
    ∃ C : ℝ, ∀ x : K, C + 2 * logHeight₁ x ≤ logHeight₁ ((x ^ 2 + a * x + b) / x) := by
  obtain ⟨C, hC⟩ := logHeight_velu_ge a b hb
  refine ⟨C, fun x ↦ ?_⟩
  have h := hC x 1
  simp only [mul_one, one_pow] at h
  rwa [logHeight₁_div_eq_logHeight, logHeight₁_eq_logHeight]

/-- The `x`-coordinate map `x ↦ (x² + a x + b) / x` of the 2-isogeny of `y² = x (x² + a x + b)`
doubles heights up to a bounded error, for all `x` (at `x = 0` both heights are `0`). PROVED. -/
theorem abs_logHeight₁_velu_sub_le' {K : Type*} [Field K] [AdmissibleAbsValues K]
    (a b : K) (hb : b ≠ 0) :
    ∃ C : ℝ, ∀ x : K, |logHeight₁ ((x ^ 2 + a * x + b) / x) - 2 * logHeight₁ x| ≤ C := by
  obtain ⟨C, hC⟩ := abs_logHeight_velu_sub_le a b hb
  refine ⟨C, fun x ↦ ?_⟩
  have h := hC x 1
  simp only [mul_one, one_pow] at h
  rwa [logHeight₁_div_eq_logHeight, logHeight₁_eq_logHeight]

/-- The `x`-coordinate map `x ↦ (x² + a x + b) / x` of the 2-isogeny of `y² = x (x² + a x + b)`
with kernel `{O, (0,0)}` (a rational map of degree two) doubles heights up to a bounded error:
`|h((x² + a x + b) / x) - 2 h(x)| ≤ C` for all `x ≠ 0`. PROVED. -/
theorem abs_logHeight₁_velu_sub_le {K : Type*} [Field K] [Height.AdmissibleAbsValues K]
    (a b : K) (hb : b ≠ 0) :
    ∃ C : ℝ, ∀ x : K, x ≠ 0 →
      |Height.logHeight₁ ((x ^ 2 + a * x + b) / x) - 2 * Height.logHeight₁ x| ≤ C := by
  obtain ⟨C, hC⟩ := abs_logHeight₁_velu_sub_le' a b hb
  exact ⟨C, fun x _ ↦ hC x⟩

end ZInQ.Manuscript.RC.Height
