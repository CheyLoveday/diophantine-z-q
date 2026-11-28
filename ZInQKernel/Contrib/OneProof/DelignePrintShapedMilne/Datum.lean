import ZInQKernel.Contrib.OneProof.Y3HodgePrint

set_option autoImplicit false

/-!
# The PEL datum `(B, *, V = B, ψ)`

Elementary facts about the PEL datum attached to the indefinite quaternion algebra
`B = (2, -3)_ℚ` (`i² = 2`, `j² = -3`, `k = ij`), its real embedding
`ι : B → M₂(ℝ)`, `ι(i) = diag(√2, -√2)`, `ι(j) = !![0, -3; 1, 0]`, and the positive involution
`x* = μ⁻¹ x̄ μ` with `μ = 2j + ij`, `μ² = -6`.

* **Reflex field.** The trace of `ι(b)` is the reduced trace `2 re(b) ∈ ℚ`; hence the reflex field
  of the datum, generated over `ℚ` by these traces, is `ℚ`.
* **Type C.** With `S = J ι(μ) = diag(2 - √2, 6 + 3√2)` (`J = !![0, 1; -1, 0]`), a symmetric
  positive definite matrix, one has `S ι(x*) = ι(x)ᵀ S` for all `x ∈ B`: under `ι`, `*` becomes the
  adjoint involution of the positive definite symmetric form `S`, so
  `(B ⊗ ℝ, *) ≅ (M₂(ℝ), transpose)`.
* **Positivity.** `trd(x* x) > 0` for `x ≠ 0`.
-/

noncomputable section

namespace DelignePSMilne.Datum

open Matrix

/-- The entries of `ι(x)` for `x = a + b i + c j + d k`:
`ι(x) = !![a + b√2, -3c - 3d√2; c - d√2, a - b√2]`. -/
theorem iota_eq (x : LeafQM.B) : BPAnalytic.QM.iota x =
    !![(x.re : ℝ) + x.imI * √2, -3 * (x.imJ : ℝ) - 3 * x.imK * √2;
      (x.imJ : ℝ) - x.imK * √2, (x.re : ℝ) - x.imI * √2] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [BPAnalytic.QM.iota, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj] <;> ring

/-- **The trace of `ι(b)` is the reduced trace `2 re(b)`.**

Milne, *Introduction to Shimura varieties*, Clay Math. Proc. 4 (2005), Example 12.4(c), p. 344:
"If (G, X) is a simple PEL datum of type (A) or (C), then E(G, X) is the field generated over Q by
{TrX(b) | b ∈ B}", and Remark 8.18(b): "Tr(i(b)|Tgt₀A) = Tr_X(b)". Here `Tgt₀ A = ℂ²` with `b`
acting by `ι(b)`, so the traces are `2 re(b)`. -/
theorem trace_iota (x : LeafQM.B) :
    Matrix.trace (BPAnalytic.QM.iota x) = 2 * (x.re : ℝ) := by
  rw [iota_eq, Matrix.trace_fin_two]
  simp
  ring

/-- **The traces `Tr ι(b)` are rational**, so the field they generate over `ℚ` is `ℚ`: by
Milne, Clay Math. Proc. 4 (2005), Example 12.4(c), p. 344, and Remark 8.18(b), the reflex field of
the datum is `E(G, X) = ℚ`. -/
theorem exists_rat_trace_iota (x : LeafQM.B) :
    ∃ r : ℚ, Matrix.trace (BPAnalytic.QM.iota x) = (r : ℝ) :=
  ⟨2 * x.re, by rw [trace_iota]; push_cast; ring⟩

/-- The symmetric matrix `S = diag(2 - √2, 6 + 3√2) = J ι(μ)`, `J = !![0, 1; -1, 0]`. -/
def Sd : Matrix (Fin 2) (Fin 2) ℝ := !![2 - √2, 0; 0, 6 + 3 * √2]

/-- `S` is symmetric. -/
theorem Sd_transpose : Sd.transpose = Sd := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Sd]

/-- The first diagonal entry of `S` is positive. -/
theorem Sd_pos_left : (0 : ℝ) < 2 - √2 := by
  have h : √2 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- The second diagonal entry of `S` is positive. -/
theorem Sd_pos_right : (0 : ℝ) < 6 + 3 * √2 := by positivity

/-- `S = J ι(μ)` with `J = !![0, 1; -1, 0]` and `μ = 2j + ij`. -/
theorem Sd_eq_J_mul_iota_mu :
    Sd = !![0, 1; -1, 0] * BPAnalytic.QM.iota RvQMPolar.mu := by
  rw [iota_eq]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Sd, RvQMPolar.mu, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- **`*` is the adjoint involution of the positive definite symmetric form `S` (type C).**
For every `x ∈ B`, `S ι(x*) = ι(x)ᵀ S`, where `x* = μ⁻¹ x̄ μ`. Hence `ι` identifies
`(B ⊗ ℝ, *)` with `(M₂(ℝ), transpose)` (conjugating by `S^{1/2}`), so the PEL datum is of type C.

Milne, Clay Math. Proc. 4 (2005), Definition 8.15, p. 327, and Example 8.6, p. 325. The proof uses
`ι(x̄) = adj ι(x) = J ι(x)ᵀ J⁻¹` and `S = J ι(μ)`. -/
theorem Sd_mul_iota_dag (x : LeafQM.B) :
    Sd * BPAnalytic.QM.iota (RvQMPolar.dag x) = (BPAnalytic.QM.iota x).transpose * Sd := by
  have h2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [iota_eq, iota_eq]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Sd, RvQMPolar.dag, RvQMPolar.muInv, RvQMPolar.mu, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring_nf <;> (try simp only [h2]) <;> ring_nf

/-- `S` is diagonal. -/
theorem Sd_eq_diagonal : Sd = Matrix.diagonal ![2 - √2, 6 + 3 * √2] := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [Sd]

/-- `S` is positive definite. -/
theorem Sd_posDef : Sd.PosDef := by
  rw [Sd_eq_diagonal, Matrix.posDef_diagonal_iff]
  intro i; fin_cases i
  · exact Sd_pos_left
  · exact Sd_pos_right

/-- **The type C identity on `𝒪`**: for every `a ∈ 𝒪`, `S ι(a†) = ι(a)ᵀ S`, with `a† = μ⁻¹ ā μ`
the involution of the polarization (Milne, Clay Math. Proc. 4 (2005), Definition 8.15, p. 327,
and Example 8.6, p. 325). -/
theorem Sd_mul_iota_dagO (a : LeafQM.O) :
    Sd * BPAnalytic.QM.iota (Y3Hodge.dagO a : LeafQM.B) =
      (BPAnalytic.QM.iota (a : LeafQM.B)).transpose * Sd :=
  Sd_mul_iota_dag (a : LeafQM.B)

/-- The type C identity with the involution written out: `S ι(μ⁻¹ x̄ μ) = ι(x)ᵀ S`. -/
theorem Sd_mul_iota_conj (x : LeafQM.B) :
    Sd * BPAnalytic.QM.iota (RvQMPolar.muInv * star x * RvQMPolar.mu) =
      (BPAnalytic.QM.iota x).transpose * Sd :=
  Sd_mul_iota_dag x

/-- **The real part of `x* x`.** For `x = a + b i + c j + d k`,
`re(x* x) = a² + 2b² + (3c - 4d)² + 2d²`. -/
theorem dag_mul_self_re (x : LeafQM.B) :
    (RvQMPolar.dag x * x).re =
      x.re ^ 2 + 2 * x.imI ^ 2 + (3 * x.imJ - 4 * x.imK) ^ 2 + 2 * x.imK ^ 2 := by
  simp [RvQMPolar.dag, RvQMPolar.muInv, RvQMPolar.mu]
  ring

/-- **Positivity of `*`**: `re(x* x) > 0` for `x ≠ 0`, i.e. the reduced trace
`trd(x* x) = 2 re(x* x)` is positive (Milne, Clay Math. Proc. 4 (2005), §8: `*` is a positive involution). -/
theorem dag_mul_self_re_pos (x : LeafQM.B) (hx : x ≠ 0) : 0 < (RvQMPolar.dag x * x).re := by
  rw [dag_mul_self_re]
  by_contra h
  apply hx
  have h' := not_lt.mp h
  have h1 : x.re ^ 2 = 0 := by
    nlinarith [sq_nonneg x.re, sq_nonneg x.imI, sq_nonneg (3 * x.imJ - 4 * x.imK), sq_nonneg x.imK]
  have h2 : x.imI ^ 2 = 0 := by
    nlinarith [sq_nonneg x.re, sq_nonneg x.imI, sq_nonneg (3 * x.imJ - 4 * x.imK), sq_nonneg x.imK]
  have h3 : (3 * x.imJ - 4 * x.imK) ^ 2 = 0 := by
    nlinarith [sq_nonneg x.re, sq_nonneg x.imI, sq_nonneg (3 * x.imJ - 4 * x.imK), sq_nonneg x.imK]
  have h4 : x.imK ^ 2 = 0 := by
    nlinarith [sq_nonneg x.re, sq_nonneg x.imI, sq_nonneg (3 * x.imJ - 4 * x.imK), sq_nonneg x.imK]
  have e1 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp h1
  have e2 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp h2
  have e3 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp h3
  have e4 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp h4
  ext <;> simp <;> linarith

/-- **Positivity of `*` in terms of the reduced trace**: `trd(x* x) > 0` for `x ≠ 0`
(Milne, Clay Math. Proc. 4 (2005), §8: `*` is a positive involution). -/
theorem trd_dag_mul_self_pos (x : LeafQM.B) (hx : x ≠ 0) :
    0 < RvQMPolar.trd (RvQMPolar.dag x * x) := by
  have := dag_mul_self_re_pos x hx
  simp only [RvQMPolar.trd]
  linarith

/-- **Positivity of `*` through `ι`**: `Tr ι(x* x) > 0` for `x ≠ 0`. -/
theorem trace_iota_dag_mul_self_pos (x : LeafQM.B) (hx : x ≠ 0) :
    0 < Matrix.trace (BPAnalytic.QM.iota (RvQMPolar.dag x * x)) := by
  rw [trace_iota]
  have := dag_mul_self_re_pos x hx
  have h : (0 : ℝ) < ((RvQMPolar.dag x * x).re : ℝ) := by exact_mod_cast this
  linarith

end DelignePSMilne.Datum
