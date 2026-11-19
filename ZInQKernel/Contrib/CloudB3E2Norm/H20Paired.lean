import ZInQKernel.Contrib.CloudB3E2Norm.H20AmbientS
import ZInQKernel.Contrib.CloudB3E2Norm.PairedNorm

/-!
# The paired side of the norm identity on the ambient module over `S₁`

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:arith-common-coordinate` (tex 4166–4171):
"The generic paired strict lift satisfies `j z_S = e_q^c z_{P⊥}`. Conjugation sends `z` to `z⁻¹`,
so `e_q^c = e_q`."

`PairedNorm.paired_transfer_kummer_norm_of_transversal` gives the transfer-level identity on the
paired side for paired characters `θ'` with the inverse Frobenius value (`hconj`). On the untwisted
ambient module (`H20AmbientS`, ambient points over `S₁`) the paired character is the transfer
character of the same construction with `π` replaced by `π⁻¹`: `θ' = χ_h [π]⁻¹ = (χ_h [π])⁻¹`
(`χ_h = ±1`). This file proves `hconj` for every `σ` and assembles the paired global identity:

* `alphaShap_inv_pi` (PROVED): `χ_h [π⁻¹] = (χ_h [π])⁻¹` on `G_{K,S₀}`; `ker_alphaInfl_inv_pi`
  (PROVED): the two characters have the same kernel, so the same transfer subgroups serve.
* **`thetaH_inv_pi`** (PROVED): `θ'(σ) = θ(σ)⁻¹` for every `σ` (the paired `hconj`);
  **`eq_paired`** (PROVED): the paired point factor is `e_q` (`e_q^c = e_q`).
* **`paired_norm_ambientS`** (PROVED): the paired transfer identity
  `z'_S(g) = e_q z'_{P⊥}(g) + (R'(g) b' − b')` on `ℤ[Δ] ⊗ E(K_{S₁})` for the paired characters
  `θ' = thetaH (π⁻¹)` at `H_P` and `H_R`, with the ORIGINAL point factor `e_q`, from the same norm
  relation (4.1) — the global component (1) of `PairedNorm.hlift_of_components`.

Not here: the identification of lane RC30's orthogonal Selmer data `DPp` and strict conditions
`fS` of a switch (`StepRetention`) with genuine complexes, and the local components (2), (3) of
`hlift_of_components` (the local Kummer cocycles of the paired points in the local conditions).

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open NumberField IsDedekindDomain

attribute [local instance] ptSAction

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [NumberField K] {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h1 : S₁ ⊆ S) (W : WeierstrassCurve K) (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ)

/-- **`χ_h [π⁻¹] = (χ_h [π])⁻¹`** (`χ_h = ±1`). Kind: PROVED. -/
theorem alphaShap_inv_pi (g : GKS K S₀) :
    alphaShap s hs hs0 π⁻¹ g = (alphaShap s hs hs0 π g)⁻¹ := by
  simp only [alphaShap, charMul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, map_inv,
    mul_inv]
  rw [← map_inv (intUnitsTo (MonoidAlgebra ℤ Δ)), Int.units_inv_eq_self]

/-- The two transfer characters have the same kernel. Kind: PROVED. -/
theorem ker_alphaInfl_inv_pi :
    (alphaInfl hS s hs hs0 π⁻¹).ker = (alphaInfl hS s hs hs0 π).ker := by
  ext g
  simp only [MonoidHom.mem_ker, alphaInfl, MonoidHom.comp_apply]
  rw [alphaShap_inv_pi, inv_eq_one]

variable (HP : Subgroup (GKS K S)) [HP.Normal] (hHP : HP ≤ (alphaInfl hS s hs hs0 π).ker)

/-- **The paired `hconj`**: `θ'(σ) = θ(σ)⁻¹` for `θ' = thetaH (π⁻¹)`, `θ = thetaH π`, every `σ`
(PROVED). -/
theorem thetaH_inv_pi (σ : GKS K S) :
    thetaH hS s hs hs0 π⁻¹ HP ((ker_alphaInfl_inv_pi hS s hs hs0 π).symm ▸ hHP)
        (σ : GKS K S ⧸ HP) = (thetaH hS s hs hs0 π HP hHP (σ : GKS K S ⧸ HP))⁻¹ := by
  rw [thetaH_mk, thetaH_mk, alphaShap_inv_pi]

/-- **`e_q^c = e_q`**: the paired point factor is the original one (PROVED). -/
theorem eq_paired (a : ℤ) (σ : GKS K S) :
    eq_ HP (thetaH hS s hs hs0 π⁻¹ HP ((ker_alphaInfl_inv_pi hS s hs hs0 π).symm ▸ hHP)) a σ =
      eq_ HP (thetaH hS s hs hs0 π HP hHP) a σ :=
  eq_conj HP _ _ a σ (thetaH_inv_pi hS s hs hs0 π HP hHP σ)

variable (HR : Subgroup (GKS K S)) [HR.Normal] (hHR : HR ≤ (alphaInfl hS s hs hs0 π).ker)
  [Fintype (GKS K S ⧸ HP)] [Fintype (GKS K S ⧸ HR)]
  (rP : GKS K S ⧸ HP → GKS K S) (hrP : ∀ δ, ((rP δ : GKS K S) : GKS K S ⧸ HP) = δ)
  (rR : GKS K S ⧸ HR → GKS K S) (hrR : ∀ δ, ((rR δ : GKS K S) : GKS K S ⧸ HR) = δ)
  (U : Subgroup HP) (hU : ∀ x : HP, x ∈ U ↔ (x : GKS K S) ∈ HR) [Fintype (HP ⧸ U)]
  (t : HP ⧸ U → HP) (ht : ∀ τ : HP ⧸ U, (QuotientGroup.mk (t τ) : HP ⧸ U) = τ)

include hU ht in
/-- **The paired transfer identity on the ambient module over `S₁`** (PROVED; tex 4166–4171): for
the paired characters `θ' = χ_h [π⁻¹]` at `H_P`, `H_R` and the norm relation (4.1) for points of
`ℤ[Δ] ⊗ E(K_{S₁})`, the paired twisted transfers satisfy `z'_S = e_q z'_{P⊥} + (R' b' − b')` with
the original point factor `e_q = eq_ HP (thetaH π) a σ`, and `b'` is `k`-torsion. -/
theorem paired_norm_ambientS (hle : HR ≤ HP) (k a : ℤ) (σ : GKS K S)
    {yR yP QR QP : ambU h1 W Δ} (hQR : k • QR = yR) (hQP : k • QP = yP)
    (hfixR : ∀ x ∈ HR, ambRhoU h1 W Δ x yR = yR) (hfixP : ∀ x ∈ HP, ambRhoU h1 W Δ x yP = yP)
    (hnorm : ∑ τ : HP ⧸ U, ambRhoU h1 W Δ (t τ : GKS K S) yR =
      a • yP - ambRhoU h1 W Δ σ yP - ambRhoU h1 W Δ σ⁻¹ yP) :
    (∀ g : Fin 1 → GKS K S,
      T HR rR hrR (ambRhoU h1 W Δ)
          (thetaH hS s hs hs0 π⁻¹ HR ((ker_alphaInfl_inv_pi hS s hs hs0 π).symm ▸ hHR)) 1
          (kummerCochain (ambRhoU h1 W Δ) HR QR) g =
        eq_ HP (thetaH hS s hs hs0 π HP hHP) a σ •
          T HP rP hrP (ambRhoU h1 W Δ)
            (thetaH hS s hs hs0 π⁻¹ HP ((ker_alphaInfl_inv_pi hS s hs hs0 π).symm ▸ hHP)) 1
            (kummerCochain (ambRhoU h1 W Δ) HP QP) g +
          (R HR (ambRhoU h1 W Δ)
              (thetaH hS s hs hs0 π⁻¹ HR ((ker_alphaInfl_inv_pi hS s hs hs0 π).symm ▸ hHR)) (g 0)
              (retainedBoundaryT (ambRhoU h1 W Δ) HP HR rP rR
                (thetaH hS s hs hs0 π⁻¹ HP ((ker_alphaInfl_inv_pi hS s hs hs0 π).symm ▸ hHP))
                (thetaH hS s hs hs0 π⁻¹ HR ((ker_alphaInfl_inv_pi hS s hs hs0 π).symm ▸ hHR))
                a σ QR QP) -
            retainedBoundaryT (ambRhoU h1 W Δ) HP HR rP rR
              (thetaH hS s hs hs0 π⁻¹ HP ((ker_alphaInfl_inv_pi hS s hs hs0 π).symm ▸ hHP))
              (thetaH hS s hs hs0 π⁻¹ HR ((ker_alphaInfl_inv_pi hS s hs hs0 π).symm ▸ hHR))
              a σ QR QP)) ∧
      k • retainedBoundaryT (ambRhoU h1 W Δ) HP HR rP rR
          (thetaH hS s hs hs0 π⁻¹ HP ((ker_alphaInfl_inv_pi hS s hs hs0 π).symm ▸ hHP))
          (thetaH hS s hs hs0 π⁻¹ HR ((ker_alphaInfl_inv_pi hS s hs hs0 π).symm ▸ hHR))
          a σ QR QP = 0 :=
  let h := paired_transfer_kummer_norm_of_transversal (ambRhoU h1 W Δ) HP HR rP hrP rR hrR U hU t
    ht hle (thetaH hS s hs hs0 π HP hHP)
    (thetaH hS s hs hs0 π⁻¹ HP ((ker_alphaInfl_inv_pi hS s hs hs0 π).symm ▸ hHP))
    (thetaH hS s hs hs0 π⁻¹ HR ((ker_alphaInfl_inv_pi hS s hs hs0 π).symm ▸ hHR))
    (fun _ => rfl) k a σ (thetaH_inv_pi hS s hs hs0 π HP hHP σ) hQR hQP hfixR hfixP hnorm
  ⟨h.1, h.2.1⟩

end ZInQ.Contrib.CloudB3E2.NormCochain
