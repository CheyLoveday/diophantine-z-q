import Mathlib.NumberTheory.Height.MvPolynomial
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Heights under a rational map of `ℙ¹`

Let `K` be a field with an admissible family of absolute values, and let `f g : K[X]` be coprime
polynomials of degree at most `d > 0`, one of them of degree exactly `d`. Then the map
`x ↦ [f(x) : g(x)]` is a morphism `ℙ¹ → ℙ¹` of degree `d`, and we prove
```
  |logHeight ![f.eval x, g.eval x] - d * logHeight₁ x| ≤ C
```
for a constant `C` independent of `x : K` (the height bound for a morphism of projective space:
Hindry–Silverman, *Diophantine Geometry: An Introduction*, Part B, §B.2; Silverman, *The Arithmetic
of Elliptic Curves*, 2nd ed., §VIII.5; in the case of `ℙ¹`; locators UNVERIFIED). As a corollary,
the same bound holds for `logHeight₁ (f.eval x / g.eval x)`.

The proof homogenizes `f` and `g` to binary forms of degree `d` and combines the upper bound
`Height.logHeight_eval_le'` with the lower bound `Height.logHeight_eval_ge'`. The certificates
needed for the lower bound are homogenizations of polynomials `a, b` of degree `≤ d - 1` with
`a * f + b * g = 1` and `a * f + b * g = X ^ (2 * d - 1)`; these are obtained from a Bézout
identity for `f` and `g` by division with remainder.
-/

namespace ZInQ.Manuscript.RC.Height

open Polynomial

section Certificate

variable {K : Type*} [Field K]

/-- A Bézout identity with degree bounds: if `f` has degree exactly `d > 0`, `g` has degree
at most `d` and `f, g` are coprime, then every polynomial `T` of degree at most `(d - 1) + d`
can be written as `a * f + b * g` with `a` and `b` of degree at most `d - 1`. PROVED. -/
theorem exists_mul_add_mul_eq_of_natDegree_eq {f g : K[X]} {d : ℕ} (hd : 0 < d)
    (hf : f.natDegree = d) (hg : g.natDegree ≤ d) (hcop : IsCoprime f g) (T : K[X])
    (hT : T.natDegree ≤ d - 1 + d) :
    ∃ a b : K[X], a.natDegree ≤ d - 1 ∧ b.natDegree ≤ d - 1 ∧ a * f + b * g = T := by
  obtain ⟨u, v, huv⟩ := hcop
  have hdiv := EuclideanDomain.div_add_mod (T * v) f
  set c := T * v / f
  set b := T * v % f
  have hbd : b.natDegree < d := hf ▸ natDegree_mod_lt (T * v) (by omega)
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hf
    omega
  refine ⟨T * u + c * g, b, ?_, by omega, by linear_combination T * huv + g * hdiv⟩
  set a := T * u + c * g
  have hab : a * f = T - b * g := by linear_combination T * huv + g * hdiv
  rcases eq_or_ne a 0 with ha0 | ha0
  · simp [ha0]
  have h1 : (a * f).natDegree = a.natDegree + d := by rw [natDegree_mul ha0 hf0, hf]
  have h2 : (T - b * g).natDegree ≤ d - 1 + d := by
    refine (natDegree_sub_le _ _).trans (max_le hT ?_)
    refine natDegree_mul_le.trans ?_
    omega
  rw [hab] at h1
  omega

/-- A Bézout identity with degree bounds: if `f` and `g` are coprime of degree at most `d > 0`
and one of them has degree exactly `d`, then every polynomial `T` of degree at most `(d - 1) + d`
can be written as `a * f + b * g` with `a` and `b` of degree at most `d - 1`. PROVED. -/
theorem exists_mul_add_mul_eq {f g : K[X]} {d : ℕ} (hd : 0 < d) (hf : f.natDegree ≤ d)
    (hg : g.natDegree ≤ d) (hdeg : f.natDegree = d ∨ g.natDegree = d) (hcop : IsCoprime f g)
    (T : K[X]) (hT : T.natDegree ≤ d - 1 + d) :
    ∃ a b : K[X], a.natDegree ≤ d - 1 ∧ b.natDegree ≤ d - 1 ∧ a * f + b * g = T := by
  rcases hdeg with h | h
  · exact exists_mul_add_mul_eq_of_natDegree_eq hd h hg hcop T hT
  · obtain ⟨a, b, ha, hb, e⟩ := exists_mul_add_mul_eq_of_natDegree_eq hd h hf hcop.symm T hT
    exact ⟨b, a, hb, ha, by rw [← e]; ring⟩

end Certificate

/-- The homogenization of `r` to degree `n ≥ deg r`, evaluated at `![x, 1]`, is `r.eval x`.
PROVED. -/
theorem eval_homogenize_vec_one {K : Type*} [Field K] {r : K[X]} {n : ℕ}
    (hn : r.natDegree ≤ n) (x : K) :
    MvPolynomial.eval ![x, 1] (r.homogenize n) = r.eval x := by
  rw [eval_homogenize hn _ (by simp)]
  simp

/-- **Height under a rational map of `ℙ¹`.** Let `f, g` be coprime polynomials of degree at
most `d > 0`, one of them of degree exactly `d`. Then the logarithmic height of `[f(x) : g(x)]`
is `d` times the logarithmic height of `x`, up to a bounded error. PROVED. -/
theorem abs_logHeight_eval_sub_le {K : Type*} [Field K] [Height.AdmissibleAbsValues K]
    (f g : Polynomial K) (d : ℕ) (hd : 0 < d) (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d)
    (hdeg : f.natDegree = d ∨ g.natDegree = d) (hcop : IsCoprime f g) :
    ∃ C : ℝ, ∀ x : K,
      |Height.logHeight ![f.eval x, g.eval x] - d * Height.logHeight₁ x| ≤ C := by
  -- the binary forms of degree `d` defining the map
  let p : Fin 2 → MvPolynomial (Fin 2) K := ![f.homogenize d, g.homogenize d]
  have hp : ∀ j, (p j).IsHomogeneous d := by
    intro j
    fin_cases j <;> simp [p]
  -- the certificates of degree `d - 1` for the lower bound
  obtain ⟨a₀, b₀, ha₀, hb₀, e₀⟩ :=
    exists_mul_add_mul_eq hd hf hg hdeg hcop (X ^ (d - 1 + d)) (by simp)
  obtain ⟨a₁, b₁, ha₁, hb₁, e₁⟩ := exists_mul_add_mul_eq hd hf hg hdeg hcop 1 (by simp)
  let q : Fin 2 × Fin 2 → MvPolynomial (Fin 2) K :=
    fun kj ↦ (![![a₀, b₀], ![a₁, b₁]] kj.1 kj.2).homogenize (d - 1)
  have hq : ∀ kj, (q kj).IsHomogeneous (d - 1) := fun kj ↦ isHomogeneous_homogenize _
  obtain ⟨C₁, hC₁⟩ := Height.logHeight_eval_le' hp
  obtain ⟨C₂, hC₂⟩ := Height.logHeight_eval_ge' (N := d) hq
  refine ⟨max C₁ (-C₂), fun x ↦ ?_⟩
  have hpx : (fun j ↦ MvPolynomial.eval ![x, 1] (p j)) = ![f.eval x, g.eval x] := by
    funext j
    fin_cases j <;> simp [p, eval_homogenize_vec_one hf, eval_homogenize_vec_one hg]
  have hcond : ∀ k, ∑ j, MvPolynomial.eval ![x, 1] (q (k, j)) * MvPolynomial.eval ![x, 1] (p j) =
      (![x, 1] k) ^ (d - 1 + d) := by
    intro k
    fin_cases k
    · simpa [q, p, Fin.sum_univ_two, eval_homogenize_vec_one ha₀, eval_homogenize_vec_one hb₀,
        eval_homogenize_vec_one hf, eval_homogenize_vec_one hg] using congrArg (eval x) e₀
    · simpa [q, p, Fin.sum_univ_two, eval_homogenize_vec_one ha₁, eval_homogenize_vec_one hb₁,
        eval_homogenize_vec_one hf, eval_homogenize_vec_one hg] using congrArg (eval x) e₁
  have h₁ := hC₁ ![x, 1]
  have h₂ := hC₂ p hcond
  rw [hpx] at h₁ h₂
  rw [Height.logHeight₁_eq_logHeight, abs_le]
  constructor <;> linarith [le_max_left C₁ (-C₂), le_max_right C₁ (-C₂)]

/-- **Height under a rational map of `ℙ¹`, affine form.** Under the hypotheses of
`abs_logHeight_eval_sub_le`, the height of `f(x) / g(x)` is `d` times the height of `x`, up to a
bounded error. (No hypothesis `g.eval x ≠ 0` is needed: with the convention `y / 0 = 0` the
statement remains true, since `logHeight₁ (y / z) = logHeight ![y, z]` for all `y, z`.)
PROVED. -/
theorem abs_logHeight₁_eval_div_sub_le {K : Type*} [Field K] [Height.AdmissibleAbsValues K]
    (f g : Polynomial K) (d : ℕ) (hd : 0 < d) (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d)
    (hdeg : f.natDegree = d ∨ g.natDegree = d) (hcop : IsCoprime f g) :
    ∃ C : ℝ, ∀ x : K,
      |Height.logHeight₁ (f.eval x / g.eval x) - d * Height.logHeight₁ x| ≤ C := by
  obtain ⟨C, hC⟩ := abs_logHeight_eval_sub_le f g d hd hf hg hdeg hcop
  exact ⟨C, fun x ↦ by rw [Height.logHeight₁_div_eq_logHeight]; exact hC x⟩

/-- **Height under a rational map of `ℙ¹`, affine form at points where `g` does not vanish.**
PROVED. -/
theorem abs_logHeight₁_eval_div_sub_le_of_ne_zero {K : Type*} [Field K]
    [Height.AdmissibleAbsValues K]
    (f g : Polynomial K) (d : ℕ) (hd : 0 < d) (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d)
    (hdeg : f.natDegree = d ∨ g.natDegree = d) (hcop : IsCoprime f g) :
    ∃ C : ℝ, ∀ x : K, g.eval x ≠ 0 →
      |Height.logHeight₁ (f.eval x / g.eval x) - d * Height.logHeight₁ x| ≤ C := by
  obtain ⟨C, hC⟩ := abs_logHeight₁_eval_div_sub_le f g d hd hf hg hdeg hcop
  exact ⟨C, fun x _ ↦ hC x⟩

end ZInQ.Manuscript.RC.Height
