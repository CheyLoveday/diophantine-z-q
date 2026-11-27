import ZInQKernel.Contrib.CloudB3RC53.Duality.ConjugateWeil

/-!
# Duality area: base change of a perfect pairing on a free `ℤ/m`-module of rank two

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`, tex L2797–2803: the Weil
pairing gives an `R_i`-linear *perfect* pairing on `M_i`. If `T ≃ (ℤ/m)²`, `μ ≃ ℤ/m` and
`e : T × T → μ` is perfect, then for every commutative ring `R` the `R`-bilinear extension
`(R ⊗ T) × (R ⊗ T) → R ⊗ μ` is perfect (`pairingBaseChange_bijective`).

Proof: with the basis `b_k` of `T` and the dual basis `c_k` (`e(b_j, c_k) = δ_{jk} ζ`,
`ζ ↔ 1 ∈ ℤ/m`), the inverse of `v ↦ e_R(v, ·)` is `f ↦ Σ_k (R ⊗ g_k)(f(1 ⊗ c_k))`, where
`g_k : μ → T` sends `ζ` to `b_k`.

**Classification.** GLUE, PROVED.
-/

set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.CloudB3RC53.Duality

open TensorProduct

section Perfect

variable {T μ : Type*} [AddCommGroup T] [AddCommGroup μ] {m : ℕ} [NeZero m]
  (φ : T ≃+ ZMod m × ZMod m) (ψ : μ ≃+ ZMod m) (e : T →+ T →+ μ)

/-- The basis `b₀ = φ⁻¹(1, 0)`, `b₁ = φ⁻¹(0, 1)`. -/
def basisVec (k : Fin 2) : T := φ.symm (if k = 0 then (1, 0) else (0, 1))

/-- The `k`-th coordinate of `φ`. -/
def coordZ (k : Fin 2) (t : T) : ZMod m := if k = 0 then (φ t).1 else (φ t).2

theorem eq_sum_coord (t : T) : t = ∑ k, (coordZ φ k t).val • basisVec φ k := by
  apply φ.injective
  rw [map_sum]
  simp only [map_nsmul, basisVec, AddEquiv.apply_symm_apply, Fin.sum_univ_two, coordZ]
  ext <;> simp

theorem coordZ_basisVec (j k : Fin 2) :
    coordZ φ k (basisVec φ j) = if j = k then 1 else 0 := by
  fin_cases j <;> fin_cases k <;> simp [coordZ, basisVec]

/-- The coordinate functional `T → μ`, `t ↦ ψ⁻¹(t_k)`. -/
def coordFun (k : Fin 2) : T →+ μ where
  toFun t := ψ.symm (coordZ φ k t)
  map_zero' := by simp [coordZ]
  map_add' s t := by
    fin_cases k <;> simp [coordZ, map_add]

theorem m_nsmul_basisVec (k : Fin 2) : m • basisVec φ k = 0 := by
  apply φ.injective
  rw [map_nsmul, map_zero]
  ext <;> simp [basisVec]

theorem val_add_nsmul_basisVec (k : Fin 2) (a b : ZMod m) :
    (a + b).val • basisVec φ k = a.val • basisVec φ k + b.val • basisVec φ k := by
  rw [← add_nsmul, ZMod.val_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) m]
  rw [add_nsmul, mul_nsmul, m_nsmul_basisVec, nsmul_zero, add_zero]

/-- `g_k : μ → T`, `z ↦ ψ(z) · b_k`. -/
def gk (k : Fin 2) : μ →+ T where
  toFun z := (ψ z).val • basisVec φ k
  map_zero' := by simp
  map_add' z z' := by rw [map_add, val_add_nsmul_basisVec]

theorem gk_apply (k : Fin 2) (z : μ) : gk φ ψ k z = (ψ z).val • basisVec φ k := rfl

variable (he' : Function.Bijective e.flip)

/-- The dual basis: `e(·, c_k) = coordFun k`. -/
noncomputable def dualVec (k : Fin 2) : T := (he'.2 (coordFun φ ψ k)).choose

theorem e_dualVec (t : T) (k : Fin 2) : e t (dualVec φ ψ e he' k) = ψ.symm (coordZ φ k t) := by
  have h := (he'.2 (coordFun φ ψ k)).choose_spec
  have := congrArg (fun f : T →+ μ => f t) h
  simpa [dualVec, coordFun] using this

omit [NeZero m] in
include he' in
/-- Right nondegeneracy. -/
theorem eq_of_forall_e_eq {t t' : T}
    (h : ∀ s, e s t = e s t') : t = t' :=
  he'.1 (AddMonoidHom.ext fun s => by simpa using h s)

/-- Identity (I): `Σ_k g_k(e(t, c_k)) = t`. -/
theorem sum_gk_e_dualVec (t : T) : ∑ k, gk φ ψ k (e t (dualVec φ ψ e he' k)) = t := by
  conv_rhs => rw [eq_sum_coord φ t]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [e_dualVec, gk_apply, AddEquiv.apply_symm_apply]

/-- The coefficients of `t` in the dual basis: `n_k = ψ(e(b_k, t))`. -/
theorem eq_sum_dualVec (t : T) :
    t = ∑ k, (ψ (e (basisVec φ k) t)).val • dualVec φ ψ e he' k := by
  have hb : ∀ j, e (basisVec φ j) (∑ k, (ψ (e (basisVec φ k) t)).val • dualVec φ ψ e he' k) =
      e (basisVec φ j) t := by
    intro j
    simp only [map_sum, map_nsmul, e_dualVec, coordZ_basisVec]
    rw [Fin.sum_univ_two]
    apply ψ.injective
    fin_cases j <;> simp
  refine eq_of_forall_e_eq e he' fun s => ?_
  have expand : ∀ X, e s X = ∑ j, (coordZ φ j s).val • e (basisVec φ j) X := by
    intro X
    conv_lhs => rw [eq_sum_coord φ s]
    simp only [map_sum, map_nsmul, AddMonoidHom.finsetSum_apply, AddMonoidHom.nsmul_apply]
  rw [expand, expand]
  simp only [hb]

omit he' in
/-- `e(g_k z, t) = n_k · z`. -/
theorem e_gk (k : Fin 2) (z : μ) (t : T) :
    e (gk φ ψ k z) t = (ψ (e (basisVec φ k) t)).val • z := by
  rw [gk_apply, map_nsmul, AddMonoidHom.nsmul_apply]
  apply ψ.injective
  rw [map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val,
    ZMod.natCast_zmod_val, mul_comm]

variable (R : Type*) [CommRing R]

/-- The inverse of `v ↦ e_R(v, ·)`. -/
noncomputable def invMapBC (f : R ⊗[ℤ] T →ₗ[R] R ⊗[ℤ] μ) : R ⊗[ℤ] T :=
  ∑ k, (gk φ ψ k).toIntLinearMap.baseChange R (f (1 ⊗ₜ dualVec φ ψ e he' k))

theorem invMapBC_left (v : R ⊗[ℤ] T) :
    invMapBC φ ψ e he' R (pairingBaseChange e v) = v := by
  induction v using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [invMapBC, map_add, LinearMap.add_apply, Finset.sum_add_distrib] at hx hy ⊢
    rw [hx, hy]
  | tmul r t =>
    simp only [invMapBC, pairingBaseChange_tmul, mul_one, LinearMap.baseChange_tmul,
      AddMonoidHom.coe_toIntLinearMap]
    rw [← TensorProduct.tmul_sum, sum_gk_e_dualVec]

theorem pairingBaseChange_gk (k : Fin 2) (x : R ⊗[ℤ] μ) (t : T) :
    pairingBaseChange e ((gk φ ψ k).toIntLinearMap.baseChange R x) (1 ⊗ₜ t) =
      (ψ (e (basisVec φ k) t)).val • x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, smul_add]
  | tmul r z =>
    simp only [LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap, pairingBaseChange_tmul,
      mul_one, e_gk φ ψ e k z t]
    exact map_nsmul (TensorProduct.mk ℤ R μ r) _ z

theorem invMapBC_right (f : R ⊗[ℤ] T →ₗ[R] R ⊗[ℤ] μ) :
    pairingBaseChange e (invMapBC φ ψ e he' R f) = f := by
  have key : ∀ t : T, pairingBaseChange e (invMapBC φ ψ e he' R f) (1 ⊗ₜ t) = f (1 ⊗ₜ t) := by
    intro t
    rw [invMapBC, map_sum, LinearMap.sum_apply]
    conv_rhs => rw [eq_sum_dualVec φ ψ e he' t, TensorProduct.tmul_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pairingBaseChange_gk φ ψ e R,
      show (1 : R) ⊗ₜ[ℤ] ((ψ (e (basisVec φ k) t)).val • dualVec φ ψ e he' k) =
        (ψ (e (basisVec φ k) t)).val • ((1 : R) ⊗ₜ[ℤ] dualVec φ ψ e he' k) from
        map_nsmul (TensorProduct.mk ℤ R T 1) _ _, map_nsmul]
  ext t
  exact key t

include φ ψ he' in
/-- **Base change of a perfect pairing on `(ℤ/m)²`** with values in `μ ≃ ℤ/m`: `v ↦ e_R(v, ·)`
is bijective for every commutative ring `R`. -/
theorem pairingBaseChange_bijective : Function.Bijective (pairingBaseChange (R := R) e) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨invMapBC φ ψ e he' R, invMapBC_left φ ψ e he' R, invMapBC_right φ ψ e he' R⟩

end Perfect

theorem pairingBaseChange_flip {T μ : Type*} [AddCommGroup T] [AddCommGroup μ] (R : Type*)
    [CommRing R] (e : T →+ T →+ μ) :
    (pairingBaseChange (R := R) e).flip = pairingBaseChange e.flip := by
  ext t t'
  simp

/-- Both adjoints of the base-changed pairing are bijective. -/
theorem pairingBaseChange_perfect {T μ : Type*} [AddCommGroup T] [AddCommGroup μ] {m : ℕ}
    [NeZero m] (φ : T ≃+ ZMod m × ZMod m) (ψ : μ ≃+ ZMod m) (e : T →+ T →+ μ)
    (he : Function.Bijective e) (he' : Function.Bijective e.flip) (R : Type*) [CommRing R] :
    Function.Bijective (pairingBaseChange (R := R) e) ∧
      Function.Bijective (pairingBaseChange (R := R) e).flip := by
  refine ⟨pairingBaseChange_bijective φ ψ e he' R, ?_⟩
  rw [pairingBaseChange_flip]
  have hff : e.flip.flip = e := by ext; rfl
  exact pairingBaseChange_bijective φ ψ e.flip (hff ▸ he) R

end ZInQ.Contrib.CloudB3RC53.Duality
