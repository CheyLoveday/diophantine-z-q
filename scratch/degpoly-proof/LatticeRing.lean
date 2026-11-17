import ZInQKernel.Contrib.OneProof.CharPolyLattice

/-! degpoly-proof scratch, part D: `End(A) → End_ℤ(Λ)` is an injective ring homomorphism; an
endomorphism with `det_ℤ(M_ψ|_Λ) ≠ 0` is an isogeny (Cayley–Hamilton and `[n]` an isogeny). -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

namespace DegPolyScratch

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj Polynomial
open ZInQ.LeafPush2 (CPts IsUniformization)
open ZInQ.Contrib.OneProof.CharPolyLattice

variable {K : Type} [Field K]

/-- (copied from homfree-proof) A homomorphism trivial on `A(ℂ)_σ` is zero. -/
theorem hom_eq_zero_of_cpts (σ : K →+* ℂ) {A B : PkgI3.AbVar K} (f : PkgI3.AbVar.Hom A B)
    (h : ∀ p : CPts A σ, p ≫ f.hom = 1) : f = 0 := by
  letI : Algebra K ℂ := σ.toAlgebra
  have hC : ZInQ.Contrib.AVB1.bcHom ℂ A B f = 0 := by
    apply PkgI3.AbVar.Hom.ext'
    apply ZInQ.HomUnify.hom_ext_of_cpts
    intro q
    rw [PkgI3.AbVar.Hom.hom_zero, MonObj.comp_one]
    have h1 := ZInQ.Contrib.AVB1.bcPt_ptMap (A := A) (B := B) ℂ f q
    have h2 : PkgI3.AbVar.ptMap f (ZInQ.Contrib.AbVarBC.bcPt A ℂ q) = 1 :=
      h (ZInQ.Contrib.AbVarBC.bcPt A ℂ q)
    rw [h2] at h1
    have h3 : PkgI3.AbVar.ptMap (ZInQ.Contrib.AVB1.bcHom ℂ A B f) q = 1 :=
      (MulEquiv.map_eq_one_iff _).1 h1
    exact h3
  apply ZInQ.Contrib.AVB1.bcHom_injective (L := ℂ) A B
  rw [hC, map_zero]

section Lift

variable {σ : K →+* ℂ} {A : PkgI3.AbVar K} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
  [DiscreteTopology Λ] [IsZLattice ℝ Λ] {Φ : (Fin g → ℂ) → CPts A σ}

/-- (copied from homfree-proof) Two linear lifts of the same map agree. -/
theorem lift_unique (hA : IsUniformization σ Λ Φ) (ψ : (Fin g → ℂ) → CPts A σ)
    (M M' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hM : ∀ z, Φ (M z) = ψ z) (hM' : ∀ z, Φ (M' z) = ψ z) : M = M' := by
  have key : ∀ w, M w - M' w ∈ Λ := by
    intro w
    rw [← hA.2.1]
    have e : Φ (M w) = Φ (M w - M' w) * Φ (M' w) := by
      rw [← hA.1, sub_add_cancel]
    rw [hM, hM'] at e
    have := congrArg (fun x => x * (ψ w)⁻¹) e
    simpa using this.symm
  apply LinearMap.ext
  intro z
  apply sub_eq_zero.1
  apply HDec.G0Galois.eq_zero_of_real_smul_mem Λ
  intro t
  have := key ((t : ℂ) • z)
  rwa [map_smul, map_smul, ← smul_sub, Complex.coe_smul] at this

/-- The lattice representation `End(A) → End_ℤ(Λ)` as a ring homomorphism. -/
def latRep (hA : IsUniformization σ Λ Φ) (M : PkgI3.AbVar.End A → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hM : ∀ f z, Φ (M f z) = Φ z ≫ f.hom) (hMlat : ∀ f (lam : Λ), M f lam ∈ Λ) :
    PkgI3.AbVar.End A →+* Module.End ℤ Λ where
  toFun f := latEnd Λ (M f) (hMlat f)
  map_one' := by
    have h1 : M 1 = LinearMap.id := lift_unique hA (fun z => Φ z) _ _
      (fun z => by rw [hM]; exact Category.comp_id _) (fun z => rfl)
    apply LinearMap.ext; intro lam; apply Subtype.ext
    rw [latEnd_apply, h1]; rfl
  map_mul' f f' := by
    have h1 : M (f * f') = M f ∘ₗ M f' := lift_unique hA (fun z => Φ z ≫ (f * f').hom) _ _
      (fun z => hM _ z) (fun z => by
        rw [LinearMap.comp_apply, hM, hM]
        change (Φ z ≫ f'.hom) ≫ f.hom = Φ z ≫ (f'.hom ≫ f.hom)
        rw [Category.assoc])
    apply LinearMap.ext; intro lam; apply Subtype.ext
    rw [latEnd_apply, h1]; rfl
  map_zero' := by
    have h1 : M 0 = 0 := lift_unique hA (fun z => Φ z ≫ (0 : PkgI3.AbVar.End A).hom) _ _
      (fun z => hM _ z) (fun z => by
        rw [LinearMap.zero_apply, PkgI3.AbVar.Hom.hom_zero, MonObj.comp_one]
        exact (hA.2.1 0).2 (zero_mem _))
    apply LinearMap.ext; intro lam; apply Subtype.ext
    rw [latEnd_apply, h1]; rfl
  map_add' f f' := by
    have h1 : M (f + f') = M f + M f' := lift_unique hA (fun z => Φ z ≫ (f + f').hom) _ _
      (fun z => hM _ z) (fun z => by
        rw [LinearMap.add_apply, hA.1, hM, hM, PkgI3.AbVar.Hom.hom_add, MonObj.comp_mul])
    apply LinearMap.ext; intro lam; apply Subtype.ext
    rw [latEnd_apply, h1]; rfl

theorem latRep_apply (hA : IsUniformization σ Λ Φ)
    (M : PkgI3.AbVar.End A → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hM : ∀ f z, Φ (M f z) = Φ z ≫ f.hom) (hMlat : ∀ f (lam : Λ), M f lam ∈ Λ) (f) :
    latRep hA M hM hMlat f = latEnd Λ (M f) (hMlat f) := rfl

theorem latRep_injective (hA : IsUniformization σ Λ Φ)
    (M : PkgI3.AbVar.End A → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hM : ∀ f z, Φ (M f z) = Φ z ≫ f.hom) (hMlat : ∀ f (lam : Λ), M f lam ∈ Λ) :
    Function.Injective (latRep hA M hM hMlat) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have h0 : ∀ lam ∈ Λ, M f lam = 0 := fun lam hlam => by
    have := congrArg Subtype.val (LinearMap.congr_fun hf ⟨lam, hlam⟩)
    exact this
  have hMR : (M f).restrictScalars ℝ = 0 := by
    apply LinearMap.ext_on_range (v := fun lam : Λ => (lam : Fin g → ℂ))
    · rw [Subtype.range_coe_subtype]
      exact IsZLattice.span_top
    · intro lam
      exact h0 lam lam.2
  apply hom_eq_zero_of_cpts σ f
  intro p
  obtain ⟨z, rfl⟩ := hA.2.2.1 p
  rw [← hM]
  have : M f z = 0 := by
    have := LinearMap.congr_fun hMR z
    simpa using this
  rw [this]
  exact (hA.2.1 0).2 (zero_mem _)

/-- **An endomorphism with `det_ℤ(M_ψ|_Λ) ≠ 0` is an isogeny** (characteristic `0`): by
Cayley–Hamilton and injectivity of `latRep`, `ψ q(ψ) = q(ψ) ψ = [n]` with `n = ±det ≠ 0`, and `[n]`
is finite and surjective. -/
theorem isIsogeny_of_det_ne_zero [CharZero K] (hA : IsUniformization σ Λ Φ)
    (M : PkgI3.AbVar.End A → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hM : ∀ f z, Φ (M f z) = Φ z ≫ f.hom) (hMlat : ∀ f (lam : Λ), M f lam ∈ Λ)
    (ψ : PkgI3.AbVar.End A) (hdet : LinearMap.det (latEnd Λ (M ψ) (hMlat ψ)) ≠ 0) :
    PkgI3.AbVar.IsIsogenyMor ψ.hom := by
  classical
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  set U := latRep hA M hM hMlat with hU
  set χ := (U ψ).charpoly with hχ
  have hUχ : U (aeval ψ χ) = 0 := by
    change U.toIntAlgHom (aeval ψ χ) = 0
    rw [← Polynomial.aeval_algHom_apply U.toIntAlgHom]
    exact LinearMap.aeval_self_charpoly (U ψ)
  have hχ0 : aeval ψ χ = 0 := latRep_injective hA M hM hMlat (by rw [hUχ, map_zero])
  have hc : χ.coeff 0 = LinearMap.det (U ψ) := by
    rw [LinearMap.det_eq_sign_charpoly_coeff, finrank_lattice Λ, pow_mul, neg_one_sq, one_pow,
      _root_.one_mul]
  set q := aeval ψ χ.divX with hq
  set n : ℤ := -χ.coeff 0 with hn
  have hn0 : n ≠ 0 := by rw [hn, neg_ne_zero, hc]; exact hdet
  have h1 : ψ * q = (n : PkgI3.AbVar.End A) := by
    have := congrArg (aeval ψ) (X_mul_divX_add χ)
    rw [map_add, map_mul, aeval_X, aeval_C, hχ0] at this
    rw [hn, Int.cast_neg, ← add_eq_zero_iff_eq_neg, ← this, hq]
    simp
  have h2 : q * ψ = (n : PkgI3.AbVar.End A) := by
    have := congrArg (aeval ψ) (divX_mul_X_add χ)
    rw [map_add, map_mul, aeval_X, aeval_C, hχ0] at this
    rw [hn, Int.cast_neg, ← add_eq_zero_iff_eq_neg, ← this, hq]
    simp
  have hiso := HDec.HSyn.mulIsogeny_proved K A n hn0
  obtain ⟨hfin, hsurj⟩ := hiso
  have e1 : (n : PkgI3.AbVar.End A).hom.left = q.hom.left ≫ ψ.hom.left := by
    rw [← h1]; rfl
  have e2 : (n : PkgI3.AbVar.End A).hom.left = ψ.hom.left ≫ q.hom.left := by
    rw [← h2]; rfl
  refine ⟨?_, ?_⟩
  · haveI : IsFinite (ψ.hom.left ≫ q.hom.left) := by rw [← e2]; exact hfin
    haveI : IsSeparated (q.hom.left ≫ A.X.hom) := by
      rw [show q.hom.left ≫ A.X.hom = A.X.hom from Over.w q.hom]; infer_instance
    haveI : IsSeparated q.hom.left := IsSeparated.of_comp q.hom.left A.X.hom
    exact IsFinite.of_comp ψ.hom.left q.hom.left
  · constructor
    intro y
    obtain ⟨x, hx⟩ := hsurj.surj y
    refine ⟨q.hom.left x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← e1, hx]

end Lift

end DegPolyScratch
