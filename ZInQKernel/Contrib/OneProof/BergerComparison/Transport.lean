import ZInQKernel.Contrib.OneProof.BergerReroute.BergerReroute

/-!
# Basis transport for the two semistable period rings

Base change along a Galois-equivariant algebra map preserves invariant bases.
The Frobenius map of period rings is isolated from the representation argument.
-/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4
open BergerBst BmaxOne FontaineSt BergerReroute
open PanBergerSplit (bdrLin vAct tensorInv)
open Module
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 700000

variable (p : ℕ) [Fact p.Prime]

private abbrev xi := ZInQ.Contrib.G9.BdrKer.Cp.xi p

/-- Fontaine's embedded semistable ring at the canonical generator of `ker θ`. -/
abbrev FontaineRing {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) :=
  BstFOf p h (xi p) (theta_xi' p)

/-- The induced Galois algebra map on a stable period subalgebra. -/
def periodAct (B : Subalgebra ℚ_[p] (BdR p))
    (hB : ∀ σ : GQp p, ∀ x ∈ B, bdrAct p σ x ∈ B) (σ : GQp p) : B →ₐ[ℚ_[p]] B :=
  (bdrAlg p σ |>.comp B.val).codRestrict B (fun b => hB σ b b.2)

section Tensor

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] {n : ℕ}
variable {B B' : Subalgebra ℚ_[p] (BdR p)}
variable (hB : ∀ σ : GQp p, ∀ x ∈ B, bdrAct p σ x ∈ B)
variable (hB' : ∀ σ : GQp p, ∀ x ∈ B', bdrAct p σ x ∈ B')

private theorem inclT_periodAct (ρ : GQp p →* GL (Fin n) E) (σ : GQp p)
    (x : B ⊗[ℚ_[p]] (Fin n → E)) :
    inclT p B (TensorProduct.map (periodAct p B hB σ).toLinearMap (vAct p ρ σ) x) =
      TensorProduct.map (bdrLin p σ) (vAct p ρ σ) (inclT p B x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b v =>
    rw [TensorProduct.map_tmul, inclT_tmul, inclT_tmul, TensorProduct.map_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Base change of an invariant basis along an equivariant algebra homomorphism.
The map is allowed to differ from the inclusion into the ambient period field. -/
theorem isAdmissibleT_of_equivariant (φ : B →ₐ[ℚ_[p]] B') (H : Subgroup (GQp p))
    (hφ : ∀ σ ∈ H, ∀ b : B, φ (periodAct p B hB σ b) = periodAct p B' hB' σ (φ b))
    (ρ : GQp p →* GL (Fin n) E) (h : IsAdmissibleT p B H ρ) : IsAdmissibleT p B' H ρ := by
  obtain ⟨ι, b, hb⟩ := h
  let : Algebra B B' := φ.toRingHom.toAlgebra
  let : IsScalarTower ℚ_[p] B B' := IsScalarTower.of_algebraMap_eq fun c =>
    (φ.commutes c).symm
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ_[p] B B' B' (Fin n → E)
  let F := TensorProduct.map φ.toLinearMap (LinearMap.id (R := ℚ_[p]) (M := Fin n → E))
  have hbase (x : B ⊗[ℚ_[p]] (Fin n → E)) : e ((1 : B') ⊗ₜ[B] x) = F x := by
    induction x using TensorProduct.inductionOn with
    | tmul c v =>
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
      simp [F, Algebra.smul_def]
      rfl
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  refine ⟨ι, (b.baseChange B').map e, fun i σ hσ => ?_⟩
  rw [Basis.map_apply, Basis.baseChange_apply, hbase, ← inclT_periodAct p hB']
  let A := TensorProduct.map (periodAct p B hB σ).toLinearMap (vAct p ρ σ)
  let A' := TensorProduct.map (periodAct p B' hB' σ).toLinearMap (vAct p ρ σ)
  change inclT p B' (A' (F (b i))) = inclT p B' (F (b i))
  have hcomm (x : B ⊗[ℚ_[p]] (Fin n → E)) : A' (F x) = F (A x) := by
    induction x using TensorProduct.inductionOn with
    | tmul c v => simp [A, A', F, hφ σ hσ c]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hfix : A (b i) = b i := inclT_injective p B <| by
    rw [inclT_periodAct p hB]
    exact hb i σ hσ
  rw [hcomm, hfix]

end Tensor

private theorem fontaineRing_le {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) :
    FontaineRing p h ≤ Bst p :=
  LogPTransc.bstFOf_le_bst p h (theta_xi' p)

/-- Sufficient ring data for basis transport. The expected map is Frobenius; neither its
injectivity nor a presentation of the source as a polynomial ring is needed here. -/
def FrobeniusTransport : Prop :=
  ∀ (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀),
    ∃ φ : Bst p →ₐ[ℚ_[p]] FontaineRing p h,
      ∀ (σ : GQp p) (b : Bst p),
        φ (periodAct p _ (bst_stable p) σ b) =
          periodAct p _ (bstF_stable p h) σ (φ b)

section Representations

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] {n : ℕ}

/-- The two normalized embedded rings give equivalent basis predicates over the same
subgroup, given the ring map in the direction from the maximal to the crystalline ring. -/
theorem isAdmissibleT_fontaine_iff (hφ : FrobeniusTransport p)
    {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀)
    (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) :
    IsAdmissibleT p (FontaineRing p h) H ρ ↔ IsAdmissibleT p (Bst p) H ρ := by
  obtain ⟨φ, heq⟩ := hφ ε₀ h
  exact ⟨isAdmissibleT_mono p (fontaineRing_le p h) H ρ,
    isAdmissibleT_of_equivariant p (bst_stable p) (bstF_stable p h) φ H
      (fun σ _ => heq σ) ρ⟩

/-- Comparison of the basis predicates after identifying the paper's maximal period ring. -/
theorem isAdmissibleT_paper_iff (hφ : FrobeniusTransport p)
    {ell : BdR p} (hell : Algebra.adjoin ℚ_[p] ((Bmax p : Set (BdR p)) ∪ {ell}) = Bst p)
    {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀)
    (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) :
    IsAdmissibleT p (FontaineRing p h) H ρ ↔
      IsAdmissibleT p (Algebra.adjoin ℚ_[p] ((Bmax p : Set (BdR p)) ∪ {ell})) H ρ := by
  rw [hell]
  exact isAdmissibleT_fontaine_iff p hφ h H ρ

/-- The comparison asked for by the draft, from a ring map and the logarithm estimate.
The finite extension and the representation are unchanged. -/
theorem bergerPaperStComparison_of_frobenius (hφ : FrobeniusTransport p)
    {ell : BdR p} (c : ℚ_[p])
    (hell : ((p : ℚ_[p]) - 1) • ell -
      (p : ℚ_[p]) • (algebraMap ℚ_[p] (BdR p) c + toBdR p (logPTilde p)) ∈ BmaxPlus p) :
    BergerPaperStComparison p ell := by
  intro ε₀ h K _ n E _ ρ _ hBasis
  exact isAdmissible_of_pstF p h K.fixingSubgroup ρ
    ((isAdmissibleT_paper_iff p hφ (bmax_adjoin_eq_bst p ell c hell) h K.fixingSubgroup ρ).2 hBasis)

/-- A paper-ring witness supplies the basis conclusion of the existing Fontaine-ring draft. -/
theorem isPstFBasis_of_paper (hφ : FrobeniusTransport p)
    {ell : BdR p} (hell : Algebra.adjoin ℚ_[p] ((Bmax p : Set (BdR p)) ∪ {ell}) = Bst p)
    {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀)
    (ρ : GQp p →* GL (Fin n) E)
    (hpst : ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
      IsAdmissibleT p (Algebra.adjoin ℚ_[p] ((Bmax p : Set (BdR p)) ∪ {ell})) K.fixingSubgroup ρ) :
    IsPstFBasis p h (xi p) (theta_xi' p) ρ := by
  obtain ⟨K, hK, hBasis⟩ := hpst
  exact ⟨K, hK, (isAdmissibleT_paper_iff p hφ hell h K.fixingSubgroup ρ).2 hBasis⟩

end Representations

end ZInQ.Manuscript.BergerComparison
