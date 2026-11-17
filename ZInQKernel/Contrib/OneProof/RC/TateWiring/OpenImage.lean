import ZInQKernel.Contrib.OneProof.RC.TateWiring.Image
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Annihilator

/-!
# Lane RC17 (Tate wiring): step 1 of the finite Heegner descent over the genuine Tate image

Manuscript (11/5 version), Proposition `ex:arith-finite-heegner`, proof, paragraph "1. One uniform
torsion annihilator", tex 2881–2912:

> By the non-CM open-image theorem [Serre], choose `n ≥ 2` such that
> `1 + 2^n M₂(ℤ₂) ⊂ ρ_T(G_ℚ)`, and choose `g ∈ G_ℚ` with `ρ_T(g) = uI`, `u = 1 + 2^n`. For an
> actual complex conjugation `τ` set `z = g²τg²τ⁻¹`, `e = v₂(u⁴ − 1) = n + 2` (H1). [...] while
> `ρ_T(z) = u⁴I`. [...] For the matrix-span statement used elsewhere, square preimages of
> `I + 2^nE₁₁`, `I + 2^nE₁₂` and `I + 2^nE₂₁`. The squares belong to every quadratic subgroup,
> and their images, together with `I`, are `I, I + (2^{n+1} + 2^{2n})E₁₁, I + 2^{n+1}E₁₂,
> I + 2^{n+1}E₂₁`. Their `ℤ₂`-span contains `2^{n+1}M₂(ℤ₂)`.

Lane RC10 proved the algebra of this paragraph over abstract inputs (`HeegnerAlgebra.Annihilator`:
`H1_padicVal`, `rho_z`, `H2_ringClass`, `matrix_span_Z2`); lane RC9 proved the basis-free forms
`serre_two_adic` and `serre_scalar` from Serre's print.  Here the paragraph is stated over the
genuine image `ρ_T(G_ℚ) ⊂ GL₂(ℤ₂)` (the matrices `tateMatrix E σ` of `ρ_T(σ)` in lane RC9's basis
of `T₂E`), all PROVED from `SerreThm3` (PRINT) and non-CM; no determinant statement is needed:

* `serre_matrix`: `1 + 2^n M₂(ℤ₂) ⊂ ρ_T(G_ℚ)` for some `n ≥ 2` (tex 2882–2883);
* `serre_scalar_matrix`: some `g` with `ρ_T(g) = uI` (tex 2883–2884);
* `serre_z_matrix`: `ρ_T(g²τg²τ⁻¹) = u⁴I` for every `τ` (tex 2885–2892, through lane RC10's
  `rho_z`);
* `serre_scalar_torsion`: `g` acts on every point of `E[2^∞](ℚ̄)` as multiplication by `u`, and
  `g²τg²τ⁻¹` as multiplication by `u⁴` (the form in which (H2), tex 2892–2895, uses it);
* `matrix_span_tate`: the matrix-span statement, tex 2902–2912 (through lane RC10's
  `matrix_span_Z2`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.TateWiring

open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.Moving ZInQ.Manuscript.RC.HeegnerAlgebra
open scoped WeierstrassCurve MatrixGroups

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- `det(1 + 2^c X)` is a unit of `ℤ₂` for `c ≥ 1` (it is `≡ 1 (mod 2)`). -/
theorem isUnit_det_one_add_two_pow_smul {c : ℕ} (hc : 1 ≤ c) (X : Matrix (Fin 2) (Fin 2) ℤ_[2]) :
    IsUnit (1 + (2 : ℤ_[2]) ^ c • X).det := by
  apply isUnit_of_two_dvd_sub_one
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
  rw [Matrix.det_fin_two, Matrix.one_fin_two]
  refine ⟨2 ^ k * (X 0 0 + X 1 1) + 2 ^ (2 * k + 1) * (X 0 0 * X 1 1 - X 0 1 * X 1 0), ?_⟩
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    smul_eq_mul]
  ring

/-- **`1 + 2^n M₂(ℤ₂) ⊂ ρ_T(G_ℚ)`** (tex 2882–2883; PROVED from `SerreThm3` through lane RC9's
`serre_two_adic`): for some `n ≥ 2`, every matrix `1 + 2^n X` is the matrix of `ρ_T(σ)` for some
`σ ∈ G_ℚ`. -/
theorem serre_matrix (hS : SerreThm3) (hE : HasNoCM E) :
    ∃ n : ℕ, 2 ≤ n ∧ ∀ X : Matrix (Fin 2) (Fin 2) ℤ_[2],
      ∃ σ : GalQ, tateMatrix E σ = 1 + (2 : ℤ_[2]) ^ n • X := by
  obtain ⟨n, hn, h⟩ := serre_two_adic hS E hE
  refine ⟨n, hn, fun X => ?_⟩
  have hA := isUnit_det_one_add_two_pow_smul (c := n) (by omega) X
  obtain ⟨σ, hσ⟩ := h (autOfMatrix E _ _ (Matrix.mul_nonsing_inv _ hA)
    (Matrix.nonsing_inv_mul _ hA))
    (fun x => ⟨Matrix.toLin (tateBasis E) (tateBasis E) X x, by
      rw [autOfMatrix_apply, toLin_one_add_smul]⟩)
  exact ⟨σ, by rw [tateMatrix, hσ, toMatrix_autOfMatrix]⟩

/-- **The scalar element** (tex 2883–2884; PROVED from `SerreThm3`): for some `n ≥ 2` there is
`g ∈ G_ℚ` with `ρ_T(g) = uI`, `u = 1 + 2^n`. -/
theorem serre_scalar_matrix (hS : SerreThm3) (hE : HasNoCM E) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ g : GalQ, tateMatrix E g = (1 + (2 : ℤ_[2]) ^ n) • 1 := by
  obtain ⟨n, hn, h⟩ := serre_matrix E hS hE
  obtain ⟨g, hg⟩ := h 1
  exact ⟨n, hn, g, by rw [hg, add_smul, one_smul]⟩

/-- **`ρ_T(z) = u⁴I` for `z = g²τg²τ⁻¹`** (tex 2885–2892; PROVED from `SerreThm3` and lane RC10's
`rho_z`): with `g` as in `serre_scalar_matrix`, for every `τ ∈ G_ℚ` (in particular an actual
complex conjugation). -/
theorem serre_z_matrix (hS : SerreThm3) (hE : HasNoCM E) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ g : GalQ, tateMatrix E g = (1 + (2 : ℤ_[2]) ^ n) • 1 ∧
      ∀ τ : GalQ, tateMatrix E (g ^ 2 * τ * g ^ 2 * τ⁻¹) = (1 + (2 : ℤ_[2]) ^ n) ^ 4 • 1 := by
  obtain ⟨n, hn, g, hg⟩ := serre_scalar_matrix E hS hE
  refine ⟨n, hn, g, hg, fun τ => ?_⟩
  have hc : ∀ x : GL (Fin 2) ℤ_[2], Commute (rhoGL E g) x := fun x =>
    Units.ext (by
      change tateMatrix E g * (x : Matrix (Fin 2) (Fin 2) ℤ_[2]) = x * tateMatrix E g
      rw [hg, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])
  have h := congrArg (fun A : GL (Fin 2) ℤ_[2] => (A : Matrix (Fin 2) (Fin 2) ℤ_[2]))
    (rho_z (rhoGL E) g τ hc)
  simp only [coe_rhoGL, Units.val_pow_eq_pow_val] at h
  rw [h, hg, smul_pow, one_pow]

/-- The `2^k`-torsion of `E(ℚ̄)` is the `k`-th level of the Tate tower, and every point of it is
the `k`-th component of a point of `T₂E` (vendored Tau Ceti: `#E[2^k] = (2^k)²`). -/
theorem exists_proj_eq (k : ℕ) (P : (E⁄Qbar).toAffine.Point) (hP : 2 ^ k • P = 0) :
    ∃ x : TateMod E 2, (TauCeti.TateModule.proj k x : (E⁄Qbar).toAffine.Point) = P := by
  have hcard : ∀ m : ℕ, Nat.card (TauCeti.TateModuleLevel 2 (E⁄Qbar).toAffine.Point m) =
      (2 ^ m) ^ 2 := fun m => by
    convert (E⁄Qbar).natCard_tateModuleLevel two_ne_zero_qbar m
  obtain ⟨x, hx⟩ := TauCeti.TateModule.proj_surjective
    (TauCeti.TateModule.tateModuleTransition_surjective_of_natCard Nat.prime_two.ne_zero hcard) k
    ⟨P, AddSubgroup.torsionBy.nsmul_iff.2 hP⟩
  exact ⟨x, congrArg Subtype.val hx⟩

/-- If `2^k • P = 0` then `a • P = (a mod 2^k) • P`. -/
theorem nsmul_mod_of_two_pow_nsmul {A : Type*} [AddCommGroup A] {k : ℕ} {P : A}
    (hP : 2 ^ k • P = 0) (a : ℕ) : (a % 2 ^ k) • P = a • P := by
  conv_rhs => rw [← Nat.div_add_mod a (2 ^ k)]
  rw [add_nsmul, mul_nsmul, hP, nsmul_zero, zero_add]

/-- `ρ_T(σ)` acting as a scalar `c ∈ ℕ` on `T₂E` acts as `c` on every point of `E[2^∞](ℚ̄)`. -/
theorem map_eq_nsmul_of_tateRep (σ : GalQ) (c : ℕ) (hσ : ∀ x : TateMod E 2,
    tateRep E 2 σ x = (c : ℤ_[2]) • x) (k : ℕ) (P : (E⁄Qbar).toAffine.Point) (hP : 2 ^ k • P = 0) :
    WeierstrassCurve.Affine.Point.map σ.toAlgHom P = c • P := by
  obtain ⟨x, rfl⟩ := exists_proj_eq E k P hP
  rw [← coe_proj_tateRep, hσ, TauCeti.TateModule.proj_smul, TauCeti.TateModule.coe_zmod_smul,
    map_natCast, ZMod.val_natCast, nsmul_mod_of_two_pow_nsmul hP]

/-- **`g` acts on `E[2^∞](ℚ̄)` as `u`, and `z = g²τg²τ⁻¹` as `u⁴`** (tex 2883–2895; PROVED from
`SerreThm3`): for some `n ≥ 2` and `g ∈ G_ℚ`, every point `P` of `E(ℚ̄)` killed by a power of `2`
satisfies `g P = (1 + 2^n) P` and `z P = (1 + 2^n)⁴ P` for every `τ ∈ G_ℚ`.  This is the scalar
hypothesis of lane RC10's (H2) (`H2_ringClass`, `OpenImageInput.scalar`) for the genuine Galois
action on `E[2^∞](ℚ̄)`. -/
theorem serre_scalar_torsion (hS : SerreThm3) (hE : HasNoCM E) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ g : GalQ,
      (∀ (k : ℕ) (P : (E⁄Qbar).toAffine.Point), 2 ^ k • P = 0 →
        WeierstrassCurve.Affine.Point.map g.toAlgHom P = ((1 : ℤ) + 2 ^ n) • P) ∧
      ∀ τ : GalQ, ∀ (k : ℕ) (P : (E⁄Qbar).toAffine.Point), 2 ^ k • P = 0 →
        WeierstrassCurve.Affine.Point.map (g ^ 2 * τ * g ^ 2 * τ⁻¹).toAlgHom P =
          (((1 : ℤ) + 2 ^ n) ^ 4) • P := by
  obtain ⟨n, hn, g, hg⟩ := serre_scalar hS E hE
  have hcast : ((1 + 2 ^ n : ℕ) : ℤ_[2]) = 1 + 2 ^ n := by push_cast; ring
  have hgT : ∀ x : TateMod E 2, tateRep E 2 g x = ((1 + 2 ^ n : ℕ) : ℤ_[2]) • x := fun x => by
    rw [hcast]; exact hg x
  have hzT : ∀ τ : GalQ, ∀ x : TateMod E 2,
      tateRep E 2 (g ^ 2 * τ * g ^ 2 * τ⁻¹) x = (((1 + 2 ^ n) ^ 4 : ℕ) : ℤ_[2]) • x := by
    intro τ x
    have hτx : tateRep E 2 τ (tateRep E 2 τ⁻¹ x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have e1 : g ^ 2 * τ * g ^ 2 * τ⁻¹ = g * (g * (τ * (g * (g * τ⁻¹)))) := by
      simp only [sq, mul_assoc]
    rw [e1]
    simp only [map_mul, Module.End.mul_apply, hg, map_smul, hτx, smul_smul]
    congr 1
    push_cast
    ring
  refine ⟨n, hn, g, fun k P hP => ?_, fun τ k P hP => ?_⟩
  · rw [map_eq_nsmul_of_tateRep E g _ hgT k P hP, ← natCast_zsmul]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
  · rw [map_eq_nsmul_of_tateRep E _ _ (hzT τ) k P hP, ← natCast_zsmul]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]

/-- **The matrix-span statement** (tex 2902–2912; PROVED from `SerreThm3`, lane RC4's
`sq_mem_of_index_le_two` and lane RC10's `matrix_span_Z2`): for some `n ≥ 2` there are
`σ₁₁, σ₁₂, σ₂₁ ∈ G_ℚ` with `ρ_T(σ_{ij}) = I + 2^n E_{ij}`; their squares lie in every subgroup of
index at most two of `G_ℚ` ("every quadratic subgroup"); and the `ℤ₂`-span of `I` and the matrices
of the three squares contains `2^{n+1} M₂(ℤ₂)`. -/
theorem matrix_span_tate (hS : SerreThm3) (hE : HasNoCM E) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ σ₁₁ σ₁₂ σ₂₁ : GalQ,
      tateMatrix E σ₁₁ = 1 + (2 : ℤ_[2]) ^ n • E11 ℤ_[2] ∧
      tateMatrix E σ₁₂ = 1 + (2 : ℤ_[2]) ^ n • E12 ℤ_[2] ∧
      tateMatrix E σ₂₁ = 1 + (2 : ℤ_[2]) ^ n • E21 ℤ_[2] ∧
      (∀ H : Subgroup GalQ, (H.index = 1 ∨ H.index = 2) →
        σ₁₁ ^ 2 ∈ H ∧ σ₁₂ ^ 2 ∈ H ∧ σ₂₁ ^ 2 ∈ H) ∧
      ∀ M : Matrix (Fin 2) (Fin 2) ℤ_[2], (2 : ℤ_[2]) ^ (n + 1) • M ∈
        Submodule.span ℤ_[2] {1, tateMatrix E (σ₁₁ ^ 2), tateMatrix E (σ₁₂ ^ 2),
          tateMatrix E (σ₂₁ ^ 2)} := by
  obtain ⟨n, hn, h⟩ := serre_matrix E hS hE
  obtain ⟨σ₁₁, h₁₁⟩ := h (E11 ℤ_[2])
  obtain ⟨σ₁₂, h₁₂⟩ := h (E12 ℤ_[2])
  obtain ⟨σ₂₁, h₂₁⟩ := h (E21 ℤ_[2])
  have hsq : ∀ σ : GalQ, tateMatrix E (σ ^ 2) = tateMatrix E σ ^ 2 := fun σ => by
    rw [sq, tateMatrix_mul, sq]
  refine ⟨n, hn, σ₁₁, σ₁₂, σ₂₁, h₁₁, h₁₂, h₂₁, fun H hH =>
    ⟨sq_mem_of_index_le_two hH _, sq_mem_of_index_le_two hH _, sq_mem_of_index_le_two hH _⟩,
    fun M => ?_⟩
  have hset : ({1, tateMatrix E (σ₁₁ ^ 2), tateMatrix E (σ₁₂ ^ 2), tateMatrix E (σ₂₁ ^ 2)} :
      Set (Matrix (Fin 2) (Fin 2) ℤ_[2])) = spanSet ℤ_[2] n := by
    rw [hsq, hsq, hsq, h₁₁, h₁₂, h₂₁, spanSet]
  rw [hset]
  exact matrix_span_Z2 n hn M

end ZInQ.Manuscript.RC.TateWiring
