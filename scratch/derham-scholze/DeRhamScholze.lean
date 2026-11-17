import ZInQKernel.HDecomp.Textbook.T10Etale
import ZInQKernel.Contrib.OneProof.DeRhamRange
import ZInQKernel.Contrib.OneProof.HodgeTateDecompOrH1

/-!
# derham-scholze: `V_p(A)` is de Rham by Scholze's comparison (manuscript `lem:de-rham-descent`)

Task derham-scholze (2026-11-17). Report `docs/research/derham-scholze.md`.

The manuscript (diophantine_zq.tex, `lem:de-rham-descent`, L10939-11004, step C3) proves that `V_ℓ(A)` is
de Rham by Scholze's comparison (Forum Math. Pi 1 (2013), Cor. 1.8, Thms 9.1, 9.3, corrigendum Forum Math. Pi 4
(2016) e6) for `H¹_ét(A_{F̄}, ℚ_ℓ)`, then Milne, *Abelian varieties* v2.00, Part I, Thm 12.1(a)
(`V_ℓ(A) ≅ H¹_ét(A_{F̄}, ℚ_ℓ)^∨`, Galois-equivariantly), then closure under duals (Brinon–Conrad 5.2.1, 6.3.3).

Here:
* §1 the Galois action on `Hⁱ(X_{F̄}, ℤ_ℓ)` for any `X/F` (Mathlib's pro-étale `ℓ`-adic cohomology, transport of
  t10-etale), equal by `rfl` to t10-etale's `galH` for an abelian variety;
* §2 `D_dR` and its Hodge filtration for a family of operators;
* §3 the leaf `ScholzeDeRhamAlg` (Scholze's Cor. 1.8 for the analytification, with Thms 9.1, 9.3);
* §4-§6 the glue: transport along equivariant isomorphisms, the Milne identification (t10-etale's leaf
  `T10_TateDuality`), duality, and the two research fields.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace DeRhamScholze

open CategoryTheory AlgebraicGeometry Limits
open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open scoped TensorProduct

noncomputable section

/-! ## §1. The Galois action on `Hⁱ(X_{F̄}, ℤ_ℓ)` -/

section Gal

variable {K : Type} [Field K] (X : Over (Spec (CommRingCat.of K)))

/-- `X_{K̄} = X ×_K Spec K̄`. -/
abbrev XKbar : Scheme := pullback X.hom (T10Etale.specAlg K)

/-- `1 × Spec(σ)` on `X_{K̄}`. -/
def galAutX (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) : XKbar X ⟶ XKbar X :=
  pullback.map X.hom (T10Etale.specAlg K) X.hom (T10Etale.specAlg K) (𝟙 _) (T10Etale.specAut σ) (𝟙 _)
    (by simp) (by rw [Category.comp_id, T10Etale.specAut_comp])

lemma galAutX_mul (σ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    galAutX X (σ * τ) = galAutX X σ ≫ galAutX X τ := by
  simp only [galAutX, pullback.map_comp, T10Etale.specAut_mul, Category.comp_id]

lemma galAutX_one : galAutX X 1 = 𝟙 _ := by
  simp only [galAutX, T10Etale.specAut_one]
  exact pullback.map_id

/-- `1 × Spec(σ)` as an automorphism of the scheme `X_{K̄}`. -/
def galIsoX (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) : XKbar X ≅ XKbar X where
  hom := galAutX X σ
  inv := galAutX X σ⁻¹
  hom_inv_id := by rw [← galAutX_mul, mul_inv_cancel, galAutX_one]
  inv_hom_id := by rw [← galAutX_mul, inv_mul_cancel, galAutX_one]

/-- **The Galois action on `Hⁱ(X_{K̄}, ℤ_ℓ)`** (Mathlib's pro-étale `ℓ`-adic cohomology): `σ` acts by
transport along `1 × Spec(σ⁻¹)` (t10-etale's `galH`, for any `X` and any degree). -/
def galHX (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) (σ : Field.absoluteGaloisGroup K) :
    (XKbar X).EllAdicCohomology ℓ i →ₗ[ℤ_[ℓ]] (XKbar X).EllAdicCohomology ℓ i :=
  T10Etale.transportₗ ℓ (galIsoX X (σ⁻¹ : Field.absoluteGaloisGroup K)) i

/-- For an abelian variety and `i = 1` this is t10-etale's action `galH` (by `rfl`). -/
theorem galHX_abVar (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (σ : Field.absoluteGaloisGroup K) :
    galHX A.X ℓ 1 σ = T10Etale.galH A ℓ σ := rfl

/-- The action is by automorphisms (t10-etale's `transport_bijective`). -/
theorem galHX_bijective (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) (σ : Field.absoluteGaloisGroup K) :
    Function.Bijective (galHX X ℓ i σ) :=
  T10Etale.transport_bijective ℓ _ i

/-- `Hⁱ(X_{K̄}, ℚ_ℓ) = ℚ_ℓ ⊗_{ℤ_ℓ} Hⁱ(X_{K̄}, ℤ_ℓ)`. -/
abbrev HQ (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) := ℚ_[ℓ] ⊗[ℤ_[ℓ]] (XKbar X).EllAdicCohomology ℓ i

/-- The Galois action on `Hⁱ(X_{K̄}, ℚ_ℓ)`. -/
def rhoH (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) (σ : Field.absoluteGaloisGroup K) :
    HQ X ℓ i →ₗ[ℚ_[ℓ]] HQ X ℓ i :=
  (galHX X ℓ i σ).baseChange ℚ_[ℓ]

end Gal

/-! ## §2. `D_dR` and its Hodge filtration -/

section DR

attribute [local instance] algPlus

variable (p : ℕ) [Fact p.Prime] {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
variable {W : Type*} [AddCommGroup W] [Module ℚ_[p] W]

/-- `D_dR(W) = (B_dR ⊗_{ℚ_p} W)^{G_F}` for a family of operators `ρ(σ)` (the carrier of `ddrTensorOver`). -/
def ddrFam (ρ : Field.absoluteGaloisGroup F → W →ₗ[ℚ_[p]] W) : Submodule ℚ_[p] (BdR p ⊗[ℚ_[p]] W) where
  carrier := {x | ∀ σ, TensorProduct.map (drAct p (gfToGqp p F σ)) (ρ σ) x = x}
  zero_mem' σ := map_zero _
  add_mem' ha hb σ := by rw [map_add, ha σ, hb σ]
  smul_mem' c x hx σ := by rw [map_smul, hx σ]

theorem ddrFam_rep (ρW : Representation ℚ_[p] (Field.absoluteGaloisGroup F) W) :
    ddrFam p (fun σ => ρW σ) = ddrTensorOver p ρW := rfl

/-- `W` is de Rham: finite-dimensional, `dim_{ℚ_p} D_dR(W) = [F:ℚ_p] · dim_{ℚ_p} W` (`IsDeRhamTensorOver`). -/
def IsDeRhamFam (ρ : Field.absoluteGaloisGroup F → W →ₗ[ℚ_[p]] W) : Prop :=
  FiniteDimensional ℚ_[p] W ∧
    finrank ℚ_[p] (ddrFam p ρ) = finrank ℚ_[p] F * finrank ℚ_[p] W

/-- `Fil^j B_dR = t^j B_dR^+ = 𝔪^j` for `j ≥ 0` (`B_dR^+` is a DVR with uniformizer `ξ`, and `t = ξ · unit`,
`TDict.tt_eq_varpi_mul_unit`), as a `ℚ_p`-subspace of `B_dR`. -/
def filB (j : ℕ) : Submodule ℚ_[p] (BdR p) where
  carrier := {x | ∃ b ∈ IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) ^ j,
    algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) b = x}
  zero_mem' := ⟨0, zero_mem _, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, add_mem ha hb, map_add _ _ _⟩
  smul_mem' := by
    rintro c _ ⟨b, hb, rfl⟩
    refine ⟨qpToPlus p c * b, Ideal.mul_mem_left _ _ hb, ?_⟩
    rw [map_mul, Algebra.smul_def]
    rfl

/-- `Fil^j D_dR(W) = D_dR(W) ∩ (Fil^j B_dR ⊗ W)`. -/
def filD (ρ : Field.absoluteGaloisGroup F → W →ₗ[ℚ_[p]] W) (j : ℕ) : Submodule ℚ_[p] (BdR p ⊗[ℚ_[p]] W) :=
  ddrFam p ρ ⊓ LinearMap.range (TensorProduct.map (filB p j).subtype (LinearMap.id : W →ₗ[ℚ_[p]] W))

/-- **The Hodge filtration of `D_dR(W)` has its jumps in `[0, i]`**: `Fil⁰ D_dR = D_dR` and
`Fil^{i+1} D_dR = 0`. For `W = Hⁱ_ét` this is what the filtered comparison `D_dR(Hⁱ_ét) ≅ Hⁱ_dR(X)` gives,
since the Hodge filtration of `Hⁱ_dR` (by `H^i(Ω^{≥j})`) has `Fil⁰ = Hⁱ_dR` and `Fil^{i+1} = 0`. -/
def HodgeRange (ρ : Field.absoluteGaloisGroup F → W →ₗ[ℚ_[p]] W) (i : ℕ) : Prop :=
  filD p ρ 0 = ddrFam p ρ ∧ filD p ρ (i + 1) = ⊥

end DR

end

end DeRhamScholze
