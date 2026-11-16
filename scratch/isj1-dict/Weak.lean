import ZInQKernel.Contrib.OneProof.R16Used
import ZInQKernel.Contrib.OneProof.DSThm965Weak

/-! # isj1-dict, part 2: `AfTateCharPoly` under the weak reading of Diamond–Shurman 9.5.4 -/

noncomputable section

set_option linter.unusedSectionVars false

namespace ISJ1Weak

open Polynomial
open PkgI3 PkgI3.AbVar LeafModCurves
open scoped TensorProduct

/-! ## 1. Frobenius in the sense of `GlueC10.IsFrobAt` on roots of unity -/

section RootsOfUnity

open ZInQ.Contrib.G9.PkgI4

/-- At a Frobenius `σ` in the sense of `IsFrobAt` (a prime `𝔓` of `ℤ̄` over `p` with
`σ x ≡ x^p mod 𝔓`), roots of unity of order prime to `p` are raised to the `p`-th power. -/
theorem frobAt_pow_of_rootOfUnity {σ : GQ} {p : ℕ} (hp : p.Prime) (hσ : GlueC10.IsFrobAt σ p)
    {ζ : Qbar} {m : ℕ} (hm : m ≠ 0) (hζ : ζ ^ m = 1) (hpm : ¬ p ∣ m) : σ ζ = ζ ^ p := by
  obtain ⟨P, hP, hPp, hcong⟩ := hσ
  have hint : ∀ x : Qbar, x ^ m = 1 → IsIntegral ℤ x := fun x hx =>
    ⟨Polynomial.X ^ m - 1, monic_X_pow_sub_C 1 hm, by simp [hx]⟩
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp [hm] at hζ
  have hσζm : (σ ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
  set ξ := σ ζ * (ζ ^ p)⁻¹ with hξ
  have hξm : ξ ^ m = 1 := by
    rw [hξ, mul_pow, hσζm, inv_pow, ← pow_mul, mul_comm p m, pow_mul, hζ, one_pow, inv_one, one_mul]
  -- elements of `ℤ̄`
  let z : GlueC10.Zbar := ⟨ζ, hint ζ hζ⟩
  let zi : GlueC10.Zbar := ⟨(ζ ^ p)⁻¹, hint _ (by rw [inv_pow, ← pow_mul, mul_comm p m, pow_mul, hζ,
    one_pow, inv_one])⟩
  let w : GlueC10.Zbar := ⟨ξ, hint ξ hξm⟩
  let d : GlueC10.Zbar := ⟨σ ζ - ζ ^ p, by
    have h1 : IsIntegral ℤ (σ ζ) := hint _ hσζm
    exact h1.sub ((hint ζ hζ).pow p)⟩
  have hd : d ∈ P := hcong z d rfl
  have hw1 : w - 1 ∈ P := by
    have : w - 1 = d * zi := by
      apply Subtype.ext
      change ξ - 1 = (σ ζ - ζ ^ p) * (ζ ^ p)⁻¹
      rw [hξ, sub_mul, mul_inv_cancel₀ (pow_ne_zero _ hζ0)]
    rw [this]
    exact P.mul_mem_right _ hd
  by_contra hne
  have hξne : ξ ≠ 1 := by
    intro h; apply hne
    rw [hξ, mul_inv_eq_one₀ (pow_ne_zero _ hζ0)] at h
    exact h
  have hwne : w ≠ 1 := fun h => hξne (congrArg Subtype.val h)
  have hgeom : ∑ j ∈ Finset.range m, w ^ j = 0 := by
    have := geom_sum_mul w m
    have hwm : w ^ m = 1 := Subtype.ext (by
      change ξ ^ m = 1
      exact hξm)
    rw [hwm, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hwne)
  have hj : ∀ j, w ^ j - 1 ∈ P := by
    intro j
    have : w ^ j - 1 = (w - 1) * ∑ i ∈ Finset.range j, w ^ i := by rw [mul_comm, geom_sum_mul]
    rw [this]
    exact P.mul_mem_right _ hw1
  have hmP : (m : GlueC10.Zbar) ∈ P := by
    have : (m : GlueC10.Zbar) = -∑ j ∈ Finset.range m, (w ^ j - 1) := by
      rw [Finset.sum_sub_distrib, hgeom]; simp
    rw [this]
    exact P.neg_mem (P.sum_mem fun j _ => hj j)
  have hpP : (p : GlueC10.Zbar) ∈ P := by
    have : (p : ℤ) ∈ P.under ℤ := by rw [hPp]; exact Ideal.subset_span rfl
    simpa using this
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * m + b * p = 1 := by
    obtain ⟨a, b, h⟩ := Nat.Coprime.isCoprime hcop.symm
    exact ⟨a, b, by exact_mod_cast h⟩
  have h1 : (1 : GlueC10.Zbar) ∈ P := by
    have : (1 : GlueC10.Zbar) = (a : GlueC10.Zbar) * m + (b : GlueC10.Zbar) * p := by
      exact_mod_cast hab.symm
    rw [this]
    exact P.add_mem (P.mul_mem_left _ hmP) (P.mul_mem_left _ hpP)
  exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1)

/-- The cyclotomic character at a Frobenius (`IsFrobAt`) at `p ≠ ℓ` is `p`. -/
theorem cycQ_frobAt {ℓ : ℕ} [Fact ℓ.Prime] {σ : GQ} {p : ℕ} (hp : p.Prime) (hpl : p ≠ ℓ)
    (hσ : GlueC10.IsFrobAt σ p) :
    ((ZInQ.Contrib.HodgeSplit.G0Galois.cycQ ℓ σ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = (p : PadicAlgCl ℓ) := by
  have hc : ((cyclotomicCharacter Qbar ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = (p : ℤ_[ℓ]) := by
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [cyclotomicCharacter.toZModPow, map_natCast]
    have hl : (ℓ ^ n) ≠ 0 := pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero
    have : NeZero (ℓ ^ n) := ⟨hl⟩
    refine (modularCyclotomicCharacter.unique Qbar _ σ.toRingEquiv fun t ht => ?_).symm
    have htn : (t : Qbar) ^ (ℓ ^ n) = 1 := by
      have := (mem_rootsOfUnity _ _).mp ht
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    have hpm : ¬ p ∣ ℓ ^ n := fun h =>
      hpl ((Nat.prime_dvd_prime_iff_eq hp (Fact.out : ℓ.Prime)).mp (hp.dvd_of_dvd_pow h))
    change σ (t : Qbar) = ((t ^ ((p : ZMod (ℓ ^ n))).val : Qbarˣ) : Qbar)
    rw [frobAt_pow_of_rootOfUnity hp hσ hl htn hpm, Units.val_pow_eq_pow_val, ZMod.val_natCast,
      ← ZInQ.Contrib.HodgeSplit.pow_eq_pow_mod_of htn]
  change algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)
    (((cyclotomicCharacter Qbar ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) = _
  rw [hc]
  simp

/-- `ε₀` at a Frobenius (`IsFrobAt`) at `p ∤ N`. -/
theorem eps0_frobAt {ℓ : ℕ} [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {σ : GQ} {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) (hσ : GlueC10.IsFrobAt σ p) :
    ∃ γ : Qbar, ιC γ = χ (p : ZMod N) ∧
      ((ZInQ.Contrib.HodgeSplit.eps0 ιC ιL χ σ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = ιL γ := by
  obtain ⟨γ, hγ, hval⟩ := ZInQ.Contrib.HodgeSplit.chiL_spec ιC ιL χ
    (ZInQ.Contrib.HodgeSplit.modCycQ σ)
  refine ⟨γ, ?_, hval⟩
  rw [hγ]
  congr 1
  refine (modularCyclotomicCharacter.unique Qbar _ σ.toRingEquiv fun t ht => ?_).symm
  have htn : (t : Qbar) ^ N = 1 := by
    have := (mem_rootsOfUnity _ _).mp ht
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  change σ (t : Qbar) = ((t ^ ((p : ZMod N)).val : Qbarˣ) : Qbar)
  rw [frobAt_pow_of_rootOfUnity hp hσ (NeZero.ne N) htn hpN, Units.val_pow_eq_pow_val,
    ZMod.val_natCast, ← ZInQ.Contrib.HodgeSplit.pow_eq_pow_mod_of htn]

end RootsOfUnity

/-! ## 2. An `ℓ`-adic embedding of `ℚ̄` extending a given embedding of `F ⊆ ℂ` -/

theorem exists_iotaL (ℓ : ℕ) [Fact ℓ.Prime] (F : IntermediateField ℚ ℂ)
    (emb : F →+* PadicAlgCl ℓ) (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ) :
    ∃ ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ,
      ∀ (γ : ZInQ.Contrib.G9.PkgI4.Qbar) (c : F), (c : ℂ) = ιC γ → ιL γ = emb c := by
  let L : IntermediateField ℚ ZInQ.Contrib.G9.PkgI4.Qbar := F.comap ιC
  let g : L →ₐ[ℚ] F :=
    { toFun := fun x => ⟨ιC (x : ZInQ.Contrib.G9.PkgI4.Qbar), x.2⟩
      map_one' := Subtype.ext (map_one ιC)
      map_mul' := fun x y => Subtype.ext (map_mul ιC (x : ZInQ.Contrib.G9.PkgI4.Qbar) y)
      map_zero' := Subtype.ext (map_zero ιC)
      map_add' := fun x y => Subtype.ext (map_add ιC (x : ZInQ.Contrib.G9.PkgI4.Qbar) y)
      commutes' := fun q => Subtype.ext (ιC.commutes q) }
  let f : L →ₐ[ℚ] PadicAlgCl ℓ := (emb.toRatAlgHom).comp g
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits (K := PadicAlgCl ℓ)
    (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) f
  refine ⟨φ, fun γ c hc => ?_⟩
  have hγ : γ ∈ L := by
    change ιC γ ∈ F
    rw [← hc]; exact c.2
  have h1 := congrArg (fun h => h ⟨γ, hγ⟩) hφ
  simp only [AlgHom.coe_comp, Function.comp_apply, IntermediateField.coe_val] at h1
  rw [h1]
  change emb ⟨ιC γ, hγ⟩ = emb c
  congr 1
  exact Subtype.ext hc.symm

/-! ## 3. Complex conjugation -/

/-- Complex conjugations exist in `G_ℚ` (copied from `ZInQ.LeafPush2.exists_isComplexConj`). -/
theorem exists_isComplexConj : ∃ c : ZInQ.Contrib.G9.PkgI4.GQ, ZInQ.Contrib.G9.PkgI4.IsComplexConj c := by
  obtain ⟨emb⟩ : Nonempty (AlgebraicClosure ℚ →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  let _ : Algebra (AlgebraicClosure ℚ) ℂ := emb.toRingHom.toAlgebra
  have : IsScalarTower ℚ (AlgebraicClosure ℚ) ℂ :=
    IsScalarTower.of_algebraMap_eq (fun x => (emb.commutes x).symm)
  let χ : ℂ ≃ₐ[ℚ] ℂ := Complex.conjAe.restrictScalars ℚ
  refine ⟨χ.restrictNormal (AlgebraicClosure ℚ), emb, fun x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes χ (AlgebraicClosure ℚ) x

theorem IsComplexConj.mul_self {c : ZInQ.Contrib.G9.PkgI4.GQ}
    (hc : ZInQ.Contrib.G9.PkgI4.IsComplexConj c) : c * c = 1 := by
  obtain ⟨ι, hι⟩ := hc
  ext x
  apply ι.toRingHom.injective
  change ι (c (c x)) = ι x
  rw [hι, hι, Complex.conj_conj]


/-! ## 4. Matrices of Galois on a free rank-two `ℚ_ℓ ⊗ F`-module and its `ι`-components -/

section Mat

variable (ℓ : ℕ) [Fact ℓ.Prime] (A : AbVar ℚ) {F : Type} [Field F] [Algebra ℚ F]
  (θ : F →+* A.End0)

/-- `frobMat` is multiplicative (`G_ℚ` acts `ℚ_ℓ ⊗ F`-linearly). -/
theorem frobMat_mul
    (b : letI := R16Used.tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ))
    (σ τ : PkgI4.GQ) :
    R16Used.frobMat ℓ A θ b (σ * τ) = R16Used.frobMat ℓ A θ b σ * R16Used.frobMat ℓ A θ b τ := by
  letI := R16Used.tensorModule ℓ A θ
  ext i j
  simp only [R16Used.frobMat, Matrix.of_apply, Matrix.mul_apply]
  have h : A.galRep ℓ (σ * τ) (b j) = A.galRep ℓ σ (A.galRep ℓ τ (b j)) :=
    LinearMap.congr_fun (map_mul (A.galRep ℓ) σ τ) (b j)
  rw [h]
  conv_lhs => rw [← b.sum_repr (A.galRep ℓ τ (b j))]
  rw [map_sum]
  simp_rw [R16Used.galRep_tsmul]
  rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]

theorem frobMat_one
    (b : letI := R16Used.tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ)) :
    R16Used.frobMat ℓ A θ b 1 = 1 := by
  letI := R16Used.tensorModule ℓ A θ
  ext i j
  have h1 : A.galRep ℓ 1 (b j) = b j := LinearMap.congr_fun (map_one (A.galRep ℓ)) (b j)
  simp only [R16Used.frobMat, Matrix.of_apply]
  erw [h1]
  rw [b.repr_self, Matrix.one_apply, Finsupp.single_apply]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Ne.symm hij]

/-- The matrix of `σ` on the `ι`-component: `ι_R` applied to `frobMat`. -/
def compMat
    (b : letI := R16Used.tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ))
    (emb : F →+* PadicAlgCl ℓ) (σ : PkgI4.GQ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ) :=
  (R16Used.frobMat ℓ A θ b σ).map (R16Used.liftHom (k := ℚ_[ℓ]) emb)

theorem compMat_mul
    (b : letI := R16Used.tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ))
    (emb : F →+* PadicAlgCl ℓ) (σ τ : PkgI4.GQ) :
    compMat ℓ A θ b emb (σ * τ) = compMat ℓ A θ b emb σ * compMat ℓ A θ b emb τ := by
  rw [compMat, frobMat_mul, Matrix.map_mul]; rfl

theorem compMat_one
    (b : letI := R16Used.tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ))
    (emb : F →+* PadicAlgCl ℓ) : compMat ℓ A θ b emb 1 = 1 := by
  rw [compMat, frobMat_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem trace_det_frobOn
    (b : letI := R16Used.tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ))
    (emb : F →+* PadicAlgCl ℓ) (σ : PkgI4.GQ) :
    LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) = (compMat ℓ A θ b emb σ).trace ∧
      LinearMap.det (frobOn ℓ A θ emb σ) = (compMat ℓ A θ b emb σ).det := by
  obtain ⟨-, h⟩ := R16Used.iota_component ℓ A θ b emb
  obtain ⟨h1, h2⟩ := h σ
  refine ⟨h1.trans ?_, h2.trans ?_⟩
  · exact AddMonoidHom.map_trace (R16Used.liftHom (k := ℚ_[ℓ]) emb).toAddMonoidHom _
  · exact RingHom.map_det _ _

/-- The weak relation over `ℚ_ℓ ⊗ F` gives the weak relation on each `ι`-component. -/
theorem aeval_compMat
    (b : letI := R16Used.tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ))
    (emb : F →+* PadicAlgCl ℓ) (σ : PkgI4.GQ) (a d : F)
    (h : aeval (R16Used.frobMat ℓ A θ b σ) (R16Used.esPoly ℓ a d) = 0) :
    aeval (compMat ℓ A θ b emb σ) (Polynomial.X ^ 2 - C (emb a) * Polynomial.X + C (emb d)) = 0 := by
  set φ := R16Used.liftHom (k := ℚ_[ℓ]) emb
  have hcomp : φ.mapMatrix.comp (algebraMap (ℚ_[ℓ] ⊗[ℚ] F) (Matrix (Fin 2) (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F))) =
      (algebraMap (PadicAlgCl ℓ) (Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))).comp φ := by
    refine RingHom.ext fun r => ?_
    ext i j
    simp only [RingHom.comp_apply, Matrix.algebraMap_eq_diagonal, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.diagonal_apply, Pi.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
    split_ifs <;> simp
  have key : ∀ P : (ℚ_[ℓ] ⊗[ℚ] F)[X],
      aeval (compMat ℓ A θ b emb σ) (P.map φ) = φ.mapMatrix (aeval (R16Used.frobMat ℓ A θ b σ) P) := by
    intro P
    rw [aeval_def, aeval_def, eval₂_map, hom_eval₂, hcomp]
    rfl
  have hmap : (R16Used.esPoly ℓ a d).map φ = Polynomial.X ^ 2 - C (emb a) * Polynomial.X + C (emb d) := by
    simp [R16Used.esPoly, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, φ, R16Used.liftHom_one_tmul]
  rw [← hmap, key, h, map_zero]

end Mat

end ISJ1Weak
