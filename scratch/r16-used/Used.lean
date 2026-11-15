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


/-! ## 2. A free rank-two `k ⊗ F`-module: the `ι`-eigenfunctionals, trace and determinant -/

section Generic

variable {k F V Ω : Type*} [Field k] [Algebra ℚ k] [Field F] [Algebra ℚ F]
  [AddCommGroup V] [Module k V] [Field Ω] [Algebra k Ω]

/-- `V` as a `k ⊗_ℚ F`-module through `ρ : F → End_k(V)`. -/
@[instance_reducible]
def tModule (ρ : F →+* Module.End k V) : Module (k ⊗[ℚ] F) V :=
  Module.compHom V (liftHom ρ)

theorem tsmul_def (ρ : F →+* Module.End k V) (r : k ⊗[ℚ] F) (v : V) :
    (letI := tModule ρ; r • v) = liftHom ρ r v := rfl

theorem tsmul_left (ρ : F →+* Module.End k V) (x : k) (v : V) :
    (letI := tModule ρ; ((x ⊗ₜ (1 : F) : k ⊗[ℚ] F) • v)) = x • v := by
  rw [tsmul_def, liftHom_tmul, map_one, mul_one, Module.algebraMap_end_apply]

theorem tsmul_right (ρ : F →+* Module.End k V) (a : F) (v : V) :
    (letI := tModule ρ; (((1 : k) ⊗ₜ a : k ⊗[ℚ] F) • v)) = ρ a v := by
  rw [tsmul_def, liftHom_tmul, map_one, one_mul]

theorem liftHom_one_tmul (emb : F →+* Ω) (a : F) :
    liftHom emb ((1 : k) ⊗ₜ a : k ⊗[ℚ] F) = emb a := by
  rw [liftHom_tmul, map_one, one_mul]

theorem liftHom_tmul_one (emb : F →+* Ω) (x : k) :
    liftHom emb (x ⊗ₜ (1 : F) : k ⊗[ℚ] F) = algebraMap k Ω x := by
  rw [liftHom_tmul, map_one, mul_one]

variable (ρ : F →+* Module.End k V) (emb : F →+* Ω) (E : Submodule Ω (V →ₗ[k] Ω))
  (hE : ∀ φ, φ ∈ E ↔ ∀ a, φ ∘ₗ ρ a = emb a • φ)

include hE in
/-- An `ι`-eigenfunctional is semilinear along `ι_R : k ⊗ F → Ω`. -/
theorem semilin {φ : V →ₗ[k] Ω} (hφ : φ ∈ E) (r : k ⊗[ℚ] F) (v : V) :
    φ (liftHom ρ r v) = liftHom emb r * φ v := by
  induction r using TensorProduct.inductionOn with
  | tmul x a =>
    have h1 := LinearMap.congr_fun ((hE φ).1 hφ a) v
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h1
    rw [liftHom_tmul, liftHom_tmul, Module.End.mul_apply, Module.algebraMap_end_apply,
      LinearMap.map_smul, h1, smul_eq_mul, Algebra.smul_def, mul_assoc]
  | add r s hr hs => rw [map_add, LinearMap.add_apply, map_add, hr, hs, map_add, add_mul]

include hE in
/-- An `ι`-eigenfunctional is determined by its values on an `k ⊗ F`-basis. -/
theorem eval_eq (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V)
    {φ : V →ₗ[k] Ω} (hφ : φ ∈ E) (v : V) :
    (letI := tModule ρ; φ v = ∑ i, liftHom emb (b.repr v i) * φ (b i)) := by
  let _ := tModule ρ
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tsmul_def, semilin ρ emb E hE hφ]

/-- The inverse of the coordinate map: `w ↦ (v ↦ Σ_i ι_R(b^*_i(v)) w_i)`. -/
def coordInv (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V) (w : Fin 2 → Ω) :
    V →ₗ[k] Ω :=
  letI := tModule ρ
  { toFun := fun v => ∑ i, liftHom emb (b.repr v i) * w i
    map_add' := fun u v => by
      simp only [map_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]
    map_smul' := fun x v => by
      rw [RingHom.id_apply, ← tsmul_left ρ x v, LinearEquiv.map_smul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finsupp.smul_apply, smul_eq_mul, map_mul, liftHom_tmul_one, Algebra.smul_def,
        mul_assoc] }

include hE in
theorem coordInv_mem (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V)
    (w : Fin 2 → Ω) : coordInv ρ emb b w ∈ E := by
  letI := tModule ρ
  rw [hE]
  intro a
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, coordInv, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [← tsmul_right ρ a v, LinearEquiv.map_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, map_mul, liftHom_one_tmul, mul_assoc]

theorem coordInv_apply_basis (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V)
    (w : Fin 2 → Ω) (j : Fin 2) : (letI := tModule ρ; coordInv ρ emb b w (b j) = w j) := by
  letI := tModule ρ
  simp only [coordInv, LinearMap.coe_mk, AddHom.coe_mk, Module.Basis.repr_self]
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [Finsupp.single_eq_of_ne hij, map_zero,
    zero_mul]) (fun h => absurd (Finset.mem_univ j) h), Finsupp.single_eq_same, map_one, one_mul]

/-- The coordinate map `E → Ω²`, `φ ↦ (φ(b 0), φ(b 1))`. -/
def coordL (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V) : E →ₗ[Ω] (Fin 2 → Ω) where
  toFun φ i := (φ : V →ₗ[k] Ω) (b i)
  map_add' _ _ := by ext i; simp
  map_smul' _ _ := by ext i; simp

include hE in
theorem coordL_bijective (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V) :
    Function.Bijective (coordL ρ E b) := by
  constructor
  · intro φ ψ h
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    have hi : ∀ i, (φ : V →ₗ[k] Ω) (b i) = (ψ : V →ₗ[k] Ω) (b i) := fun i => congrFun h i
    rw [eval_eq ρ emb E hE b φ.2, eval_eq ρ emb E hE b ψ.2]
    simp only [hi]
  · intro w
    exact ⟨⟨coordInv ρ emb b w, coordInv_mem ρ emb E hE b w⟩,
      funext fun j => coordInv_apply_basis ρ emb b w j⟩

/-- The coordinate isomorphism `E ≃ Ω²`. -/
def coordEquiv (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V) :
    E ≃ₗ[Ω] (Fin 2 → Ω) :=
  LinearEquiv.ofBijective (coordL ρ E b) (coordL_bijective ρ emb E hE b)

include hE in
theorem finrank_eq_two (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V) :
    Module.finrank Ω E = 2 := by
  rw [(coordEquiv ρ emb E hE b).finrank_eq, Module.finrank_fin_fun]

/-- The matrix of `g` in the basis `b`, `g(b j) = Σ_i M i j • b i`. -/
def matOf (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V) (g : V →ₗ[k] V) :
    Matrix (Fin 2) (Fin 2) (k ⊗[ℚ] F) :=
  letI := tModule ρ
  Matrix.of fun i j => b.repr (g (b j)) i

include hE in
/-- Precomposition by `g` on `E`, in coordinates: the transpose of `ι_R(M)`. -/
theorem coord_conj (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V)
    (g : V →ₗ[k] V) (T : E →ₗ[Ω] E) (hT : ∀ φ, (T φ : V →ₗ[k] Ω) = (φ : V →ₗ[k] Ω) ∘ₗ g) :
    (coordEquiv ρ emb E hE b).conj T =
      Matrix.toLin' ((matOf ρ b g).map (liftHom emb)).transpose := by
  apply LinearMap.ext
  intro w
  obtain ⟨φ, rfl⟩ := (coordEquiv ρ emb E hE b).surjective w
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  funext j
  change ((T φ : E) : V →ₗ[k] Ω) (b j) = _
  rw [hT, LinearMap.comp_apply, eval_eq ρ emb E hE b φ.2, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rfl

include hE in
theorem trace_det_of_basis (b : letI := tModule ρ; Module.Basis (Fin 2) (k ⊗[ℚ] F) V)
    (g : V →ₗ[k] V) (T : E →ₗ[Ω] E) (hT : ∀ φ, (T φ : V →ₗ[k] Ω) = (φ : V →ₗ[k] Ω) ∘ₗ g) :
    LinearMap.trace Ω E T = liftHom emb (matOf ρ b g).trace ∧
      @LinearMap.det E _ Ω _ _ T = liftHom emb (matOf ρ b g).det := by
  have h := coord_conj ρ emb E hE b g T hT
  constructor
  · have h1 := LinearMap.trace_conj' (R := Ω) (M := E) (N := Fin 2 → Ω) T (coordEquiv ρ emb E hE b)
    rw [h, Matrix.trace_toLin'_eq, Matrix.trace_transpose] at h1
    rw [← h1, AddMonoidHom.map_trace]
  · have h1 := LinearMap.det_conj (A := Ω) (M := E) (N := Fin 2 → Ω) T (coordEquiv ρ emb E hE b)
    rw [LinearEquiv.conj_apply, LinearMap.comp_assoc] at h
    rw [h, LinearMap.det_toLin', Matrix.det_transpose] at h1
    rw [← h1, RingHom.map_det]
    rfl

end Generic

/-- Trace and determinant of a `2 × 2` matrix from its characteristic polynomial. -/
theorem trace_det_of_charpoly {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) (t d : R)
    (h : M.charpoly = Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C d) :
    M.trace = t ∧ M.det = d := by
  constructor
  · rw [Matrix.trace_eq_neg_charpoly_coeff, h]
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C]
  · rw [Matrix.det_eq_sign_charpoly_coeff, h]
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X]

/-! ## 3. The `ℚ_ℓ ⊗ K_f`-module structure on `V_ℓ(A)` -/

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `ℚ_ℓ ⊗_ℚ F` acting on `V_ℓ(A)` through `θ : F → End⁰(A)`: `x ⊗ a ↦ x · V_ℓ(θ a)`. -/
def tensorAct (A : AbVar ℚ) {F : Type} [Field F] [Algebra ℚ F] (θ : F →+* A.End0) :
    ℚ_[ℓ] ⊗[ℚ] F →+* Module.End ℚ_[ℓ] (A.V ℓ) :=
  liftHom (R16Split.rhoV ℓ A θ)

/-- **`V_ℓ(A)` as a `ℚ_ℓ ⊗_ℚ F`-module** through `θ` (DS §9.5: `V_ℓ(A_f)` as a
`K_f ⊗ ℚ_ℓ`-module). -/
@[instance_reducible]
def tensorModule (A : AbVar ℚ) {F : Type} [Field F] [Algebra ℚ F] (θ : F →+* A.End0) :
    Module (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ) :=
  tModule (R16Split.rhoV ℓ A θ)

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
