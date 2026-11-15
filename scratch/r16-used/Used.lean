import ZInQKernel.Contrib.OneProof.R16Split

noncomputable section

set_option linter.unusedSectionVars false

namespace R16Used

open Module PkgI3 PkgI3.AbVar LeafModCurves
open scoped TensorProduct

/-! ## 1. `ℚ_ℓ ⊗ F` acting through a ring homomorphism -/

section Lift

variable {k F S : Type*} [Field k] [Algebra ℚ k] [Field F] [Algebra ℚ F] [Ring S] [Algebra k S]

/-- `x ⊗ a ↦ x · ψ(a)` on `k ⊗_ℚ F`, additively. -/
def liftAdd (ψ : F →+* S) : k ⊗[ℚ] F →+ S :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun x : k => AddMonoidHom.mk' (fun a : F => algebraMap k S x * ψ a)
        (by intro a b; rw [map_add, mul_add]))
      (by intro x y; ext a; simp [add_mul]))
    (by
      intro q x a
      simp only [AddMonoidHom.mk'_apply]
      have hq : ψ (algebraMap ℚ F q) = algebraMap k S (algebraMap ℚ k q) := by
        have : ψ.comp (algebraMap ℚ F) = (algebraMap k S).comp (algebraMap ℚ k) :=
          RingHom.ext_rat _ _
        exact RingHom.congr_fun this q
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, hq]
      simp only [← mul_assoc]
      rw [show algebraMap k S (algebraMap ℚ k q) * algebraMap k S x =
        algebraMap k S x * algebraMap k S (algebraMap ℚ k q) by rw [← map_mul, ← map_mul, mul_comm]])

theorem liftAdd_tmul (ψ : F →+* S) (x : k) (a : F) :
    liftAdd ψ (x ⊗ₜ a) = algebraMap k S x * ψ a := by
  simp [liftAdd]

/-- `x ⊗ a ↦ x · ψ(a)` on `k ⊗_ℚ F`, a ring homomorphism. -/
def liftHom (ψ : F →+* S) : k ⊗[ℚ] F →+* S where
  toFun := liftAdd ψ
  map_one' := by
    rw [Algebra.TensorProduct.one_def, liftAdd_tmul, map_one, map_one, one_mul]
  map_mul' x y := by
    induction x using TensorProduct.inductionOn with
    | tmul x a =>
      induction y using TensorProduct.inductionOn with
      | tmul y b =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, liftAdd_tmul, liftAdd_tmul, liftAdd_tmul,
          map_mul, map_mul, mul_assoc, mul_assoc, ← mul_assoc (ψ a), ← Algebra.commutes y,
          mul_assoc]
      | add y y' hy hy' => rw [mul_add, map_add, map_add, hy, hy', mul_add]
    | add x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]
  map_zero' := map_zero _
  map_add' := map_add _

theorem liftHom_tmul (ψ : F →+* S) (x : k) (a : F) :
    liftHom ψ (x ⊗ₜ a) = algebraMap k S x * ψ a := liftAdd_tmul ψ x a

end Lift

/-! ## 2. The `ℚ_ℓ ⊗ K_f`-module structure on `V_ℓ(A)` -/

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `ℚ_ℓ ⊗_ℚ F` acting on `V_ℓ(A)` through `θ : F → End⁰(A)`: `x ⊗ a ↦ x · V_ℓ(θ a)`. -/
def tensorAct (A : AbVar ℚ) {F : Type} [Field F] [Algebra ℚ F] (θ : F →+* A.End0) :
    ℚ_[ℓ] ⊗[ℚ] F →+* Module.End ℚ_[ℓ] (A.V ℓ) :=
  liftHom (R16Split.rhoV ℓ A θ)

/-- **`V_ℓ(A)` as a `ℚ_ℓ ⊗_ℚ F`-module** through `θ` (DS §9.5: `V_ℓ(A_f)` as a
`K_f ⊗ ℚ_ℓ`-module). -/
def tensorModule (A : AbVar ℚ) {F : Type} [Field F] [Algebra ℚ F] (θ : F →+* A.End0) :
    Module (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ) :=
  Module.compHom (A.V ℓ) (tensorAct ℓ A θ)

/-- The matrix of `σ ∈ G_ℚ` on `V_ℓ(A)` in an `ℚ_ℓ ⊗ F`-basis `b`: `σ(b j) = Σ_i M i j • b i`
(`σ` is `ℚ_ℓ ⊗ F`-linear, `frob_linear` below). -/
def frobMat (A : AbVar ℚ) {F : Type} [Field F] [Algebra ℚ F] (θ : F →+* A.End0)
    (b : letI := tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ))
    (σ : PkgI4.GQ) : Matrix (Fin 2) (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) :=
  letI := tensorModule ℓ A θ
  Matrix.of fun i j => b.repr (A.galRep ℓ σ (b j)) i

/-- `X² − (1 ⊗ a) X + (1 ⊗ d)` over `ℚ_ℓ ⊗_ℚ F`. -/
def esPoly {F : Type} [Field F] [Algebra ℚ F] (a d : F) : Polynomial (ℚ_[ℓ] ⊗[ℚ] F) :=
  Polynomial.X ^ 2 - Polynomial.C ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] a) * Polynomial.X +
    Polynomial.C ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] d)

section Statement

open scoped MatrixGroups ModularForm
open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff HasNebentypus IsNormalizedEigenform scaleH
  oldSpace IsNewform)

/-- **Leaf (existence form of Diamond–Shurman Lemma 9.5.3 + Theorem 9.5.4).** -/
def AfTateCharPoly : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (J : AbVar ℚ),
    0 < N → IsNewform f χ → IsJ1 N J →
    ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0),
      Function.Surjective π.hom.left ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime],
        ∃ b : (letI := tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] coeffField f) (A.V ℓ)),
          ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
            ∃ c : coeffField f, (c : ℂ) = χ (p : ZMod N) ∧
              (frobMat ℓ A θ b σ).charpoly =
                esPoly ℓ (⟨coeff f p, coeff_mem_coeffField f p⟩ : coeffField f) (c * (p : coeffField f))

end Statement

end R16Used
