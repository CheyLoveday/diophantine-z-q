import ZInQKernel.Contrib.CloudB3E2Norm.PairedNorm
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Characters

/-!
# The character compatibility `hθ` from one global character

Manuscript `diophantine_zq.tex`, tex 3203–3215 (paragraph 7, "The actual coefficient push"): the
class over `K` is obtained by Shapiro followed by `v ⊗ [δ] ↦ θ(δ) v` for "the character `θ` of
`Δ_f`", and (tex 3281–3290) "The weighted sums are transitive finite sums. Thus the two horizontal
Artin terms in (4.1) become `θ(σ_q)` and `θ(σ_q)⁻¹`, giving `a_q − θ(σ_q) − θ(σ_q)⁻¹` on the
class." The family's characters are characters of the ring class group of the ORIGINAL conductor
(tex 2779–2796: `ξ_i : Gal(H_{r_i}/K) → ℤ/2^{n_i}`, `Ψ_i = (1 + t)^{ξ_i}`), inflated to `G_{K,S}`
(the tree's `CoefModules.inflChar`); an unused prime `q` does not change them.

The hypothesis `hθ` of `transfer_kummer_norm_of_transversal` (the character at support `R` is
inflated from the one at support `P`) therefore holds as soon as both are descents of ONE character
`α` of `G` that is trivial on `HP` (hence on `HR ≤ HP`):

* `descendChar α H h` (definition): the character of `G/H` induced by `α`, for `H ≤ ker α`;
  `descendChar_mk` (PROVED): `θ(x mod H) = α(x)`.
* `hθ_of_global` (PROVED): the two descents satisfy `hθ`; `frobValue_descend` (PROVED):
  `z = θP(σ) = α(σ)`.
* **`transfer_kummer_norm_of_global_char`** (PROVED): `transfer_kummer_norm_of_transversal` with
  `θP`, `θR` the descents of a global `α` trivial on `HP`; `hθ` is gone and
  `e_q = pointFactor a α(σ) α(σ)⁻¹`.
* **`paired_transfer_kummer_norm_of_global_char`** (PROVED): the paired twin for a paired global
  character `α'` trivial on `HP` with `α'(σ) = α(σ)⁻¹`, with the same `e_q`.
* `fixS_le_ker_inflChar` (PROVED): the tree's inflated family character `inflChar H ξ` of a
  character `ξ` of `Gal(H/K)` is trivial on `G_{K,S}`-fixing subgroups `fixS L` of every
  intermediate field `L ⊇ H`; so for `H = H_{r_i}` contained in the ring class field `H_P` of the
  support, `inflChar H ξ` is trivial on `HP = fixS H_P` and the results above apply.
* Non-vacuity: `nonVacuity_global`.

**What is still missing in the tree** for a fully unconditional `hθ` at the actual data:
1. the ring class fields `H_T` of the supports as intermediate fields of `K_S/K` (the tree's
   `HeegnerPointData.H` lives in `ℚ̄/ℚ`), and the inclusion `H_{r_i} ⊆ H_P`;
2. the treatment of the quadratic factor `χ_h` of `α_i = χ_h Ψ_i` (tex 2791): it is trivial on
   `G_{H_P}` only if `K(√h) ⊆ H_P`; the manuscript instead absorbs it into the coefficient module
   through the fixed quadratic-twist identification (tex 3264–3268), so the character to which
   these results apply is `Ψ_i` (or `α_i` on the twisted module);
3. for `a`: the trace of `Frob_q` on the Tate module is `a_q` (`Wiring.FrobeniusTrace`, proved
   from the Frobenius-trace dictionary and `LocalGlobalFrobenius` in
   `RC/Wiring/CommonCoordinate7Frobenius.lean`), and (4.1) uses `a = a_q` (`NormRelations`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Manuscript.RC.Central (pointFactor)

variable {G : Type*} [Group G] {A : Type*} [CommRing A]

/-- **The descent of a global character** to `G/H`, for `H` normal and contained in its kernel.
Kind: definition. -/
def descendChar (α : G →* Aˣ) (H : Subgroup G) [H.Normal] (h : H ≤ α.ker) : G ⧸ H →* Aˣ :=
  QuotientGroup.lift H α h

@[simp] theorem descendChar_mk (α : G →* Aˣ) (H : Subgroup G) [H.Normal] (h : H ≤ α.ker)
    (x : G) : descendChar α H h (x : G ⧸ H) = α x :=
  QuotientGroup.lift_mk _ _ _

/-- **`hθ` for two descents of one global character** (PROVED). -/
theorem hθ_of_global (α : G →* Aˣ) (HP HR : Subgroup G) [HP.Normal] [HR.Normal]
    (hP : HP ≤ α.ker) (hR : HR ≤ α.ker) (x : G) :
    ((descendChar α HR hR (x : G ⧸ HR) : Aˣ) : A) = descendChar α HP hP (x : G ⧸ HP) := by
  simp

/-- **The scalar Frobenius value of a descended character** (PROVED): `z = α(σ)`. -/
theorem frobValue_descend (α : G →* Aˣ) (HP : Subgroup G) [HP.Normal] (hP : HP ≤ α.ker)
    (σ : G) : frobValue HP (descendChar α HP hP) σ = α σ ∧
      frobValueInv HP (descendChar α HP hP) σ = ((α σ)⁻¹ : Aˣ) := by
  simp [frobValue, frobValueInv]

section Norm

variable {M : Type*} [AddCommGroup M] [Module A M] (ρ : G →* Module.End A M)
  (HP HR : Subgroup G) [HP.Normal] [HR.Normal] [Fintype (G ⧸ HP)] [Fintype (G ⧸ HR)]
  (rP : G ⧸ HP → G) (hrP : ∀ δ, ((rP δ : G) : G ⧸ HP) = δ)
  (rR : G ⧸ HR → G) (hrR : ∀ δ, ((rR δ : G) : G ⧸ HR) = δ)
  (U : Subgroup HP) (hU : ∀ h : HP, h ∈ U ↔ (h : G) ∈ HR) [Fintype (HP ⧸ U)]
  (t : HP ⧸ U → HP) (ht : ∀ τ : HP ⧸ U, (QuotientGroup.mk (t τ) : HP ⧸ U) = τ)

set_option linter.unusedSectionVars false

include hrP hrR hU ht in
/-- **The norm identity over `G` for the descents of one global character** (PROVED): with
`θP`, `θR` the descents of a character `α` of `G` trivial on `HP`, the conclusion of
`transfer_kummer_norm_of_transversal` holds without `hθ`, with `e_q = eq_ HP θP a σ =
pointFactor a α(σ) α(σ)⁻¹` (`frobValue_descend`). -/
theorem transfer_kummer_norm_of_global_char (hle : HR ≤ HP) (α : G →* Aˣ) (hP : HP ≤ α.ker)
    (k a : ℤ) (σ : G) {yR yP QR QP : M}
    (hQR : k • QR = yR) (hQP : k • QP = yP) (hfixR : ∀ h ∈ HR, ρ h yR = yR)
    (hfixP : ∀ h ∈ HP, ρ h yP = yP)
    (hnorm : ∑ τ : HP ⧸ U, ρ (t τ : G) yR = a • yP - ρ σ yP - ρ σ⁻¹ yP) :
    (∀ g : Fin 1 → G, T HR rR hrR ρ (descendChar α HR (hle.trans hP)) 1 (kummerCochain ρ HR QR) g =
        eq_ HP (descendChar α HP hP) a σ •
          T HP rP hrP ρ (descendChar α HP hP) 1 (kummerCochain ρ HP QP) g +
          (R HR ρ (descendChar α HR (hle.trans hP)) (g 0)
              (retainedBoundaryT ρ HP HR rP rR (descendChar α HP hP)
                (descendChar α HR (hle.trans hP)) a σ QR QP) -
            retainedBoundaryT ρ HP HR rP rR (descendChar α HP hP)
              (descendChar α HR (hle.trans hP)) a σ QR QP)) ∧
      k • retainedBoundaryT ρ HP HR rP rR (descendChar α HP hP)
        (descendChar α HR (hle.trans hP)) a σ QR QP = 0 ∧
      (∀ g : Fin 1 → G, k • T HR rR hrR ρ (descendChar α HR (hle.trans hP)) 1
        (kummerCochain ρ HR QR) g = 0) ∧
      (∀ g : Fin 1 → G, k • T HP rP hrP ρ (descendChar α HP hP) 1
        (kummerCochain ρ HP QP) g = 0) :=
  transfer_kummer_norm_of_transversal ρ HP HR rP hrP rR hrR (descendChar α HP hP)
    (descendChar α HR (hle.trans hP)) U hU t ht hle
    (hθ_of_global α HP HR hP (hle.trans hP)) k a σ hQR hQP hfixR hfixP hnorm

include hrP hrR hU ht in
/-- **The paired twin for the descents of global characters** (PROVED): for a paired global
character `α'` trivial on `HP` with `α'(σ) = α(σ)⁻¹` ("conjugation sends `z` to `z⁻¹`"), the paired
identity holds with the point factor `e_q` of `α`. -/
theorem paired_transfer_kummer_norm_of_global_char (hle : HR ≤ HP) (α α' : G →* Aˣ)
    (hP : HP ≤ α.ker) (hP' : HP ≤ α'.ker) (k a : ℤ) (σ : G) (hconj : α' σ = (α σ)⁻¹)
    {yR yP QR QP : M}
    (hQR : k • QR = yR) (hQP : k • QP = yP) (hfixR : ∀ h ∈ HR, ρ h yR = yR)
    (hfixP : ∀ h ∈ HP, ρ h yP = yP)
    (hnorm : ∑ τ : HP ⧸ U, ρ (t τ : G) yR = a • yP - ρ σ yP - ρ σ⁻¹ yP) :
    (∀ g : Fin 1 → G, T HR rR hrR ρ (descendChar α' HR (hle.trans hP')) 1
        (kummerCochain ρ HR QR) g =
        eq_ HP (descendChar α HP hP) a σ •
          T HP rP hrP ρ (descendChar α' HP hP') 1 (kummerCochain ρ HP QP) g +
          (R HR ρ (descendChar α' HR (hle.trans hP')) (g 0)
              (retainedBoundaryT ρ HP HR rP rR (descendChar α' HP hP')
                (descendChar α' HR (hle.trans hP')) a σ QR QP) -
            retainedBoundaryT ρ HP HR rP rR (descendChar α' HP hP')
              (descendChar α' HR (hle.trans hP')) a σ QR QP)) ∧
      k • retainedBoundaryT ρ HP HR rP rR (descendChar α' HP hP')
        (descendChar α' HR (hle.trans hP')) a σ QR QP = 0 ∧
      (∀ g : Fin 1 → G, k • T HR rR hrR ρ (descendChar α' HR (hle.trans hP')) 1
        (kummerCochain ρ HR QR) g = 0) ∧
      (∀ g : Fin 1 → G, k • T HP rP hrP ρ (descendChar α' HP hP') 1
        (kummerCochain ρ HP QP) g = 0) :=
  paired_transfer_kummer_norm_of_transversal ρ HP HR rP hrP rR hrR U hU t ht hle
    (descendChar α HP hP) (descendChar α' HP hP') (descendChar α' HR (hle.trans hP'))
    (hθ_of_global α' HP HR hP' (hle.trans hP')) k a σ (by simp [hconj]) hQR hQP hfixR hfixP hnorm

end Norm

/-! ### The tree's inflated family characters -/

section Tree

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.SelmerComplex (GKS)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

omit [NumberField K] in
/-- **The tree's inflated family character is trivial on `fixS L` for every `L ⊇ H`** (PROVED):
for a character `ξ` of `Gal(H/K)` (the ring class field of the original conductor, tex 2781) and
an intermediate field `L ⊇ H` of `K_S/K` (the ring class field `H_P` of a support), the inflation
`inflChar H ξ` to `G_{K,S}` kills `fixS L = G_{L,S}`. -/
theorem fixS_le_ker_inflChar (H L : IntermediateField K (KS K S)) [Normal K H] (hHL : H ≤ L)
    {B : Type} [Monoid B] (ξ : (H ≃ₐ[K] H) →* B) : fixS K S L ≤ (inflChar H ξ).ker := by
  intro σ hσ
  rw [MonoidHom.mem_ker]
  change ξ (AlgEquiv.restrictNormalHom (F := K) (K₁ := KS K S) H (galS K S σ)) = 1
  have : AlgEquiv.restrictNormalHom (F := K) (K₁ := KS K S) H (galS K S σ) = 1 := by
    ext x
    have h1 := AlgEquiv.restrictNormal_commutes (galS K S σ) H x
    have h2 : (galS K S σ) (algebraMap H (KS K S) x) = algebraMap H (KS K S) x :=
      (mem_fixS K S).mp hσ _ (hHL x.2)
    rw [h2] at h1
    have h3 := (algebraMap H (KS K S)).injective h1
    exact congrArg (fun y : H => ((y : KS K S) : AlgebraicClosure K)) h3
  exact (congrArg ξ this).trans (map_one ξ)

end Tree

/-! ### Non-vacuity -/

/-- **Non-vacuity of the hypotheses of `transfer_kummer_norm_of_global_char`** (the new ones:
a global character trivial on `HP`, and for the paired version one with the inverse Frobenius
value): the trivial character of `ℤˣ` on `HP = ⊤`; the remaining hypotheses are those of
`transfer_kummer_norm_of_transversal` (`nonVacuity_transversal`). -/
theorem nonVacuity_global :
    ∃ (α α' : ℤˣ →* ℤˣ) (HP : Subgroup ℤˣ), HP ≤ α.ker ∧ HP ≤ α'.ker ∧
      α' (-1) = (α (-1))⁻¹ :=
  ⟨1, 1, ⊤, fun _ _ => rfl, fun _ _ => rfl, by simp⟩

end ZInQ.Contrib.CloudB3E2.NormCochain
