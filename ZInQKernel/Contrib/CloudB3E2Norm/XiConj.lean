import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitFamilyPinGenuine
import ZInQKernel.Contrib.OneProof.RC.CoefModules.ConjStable

/-!
# The anticyclotomy of the genuine moving character

Manuscript `diophantine_zq.tex`, Proposition `ex:arith-moving-character`, tex 2731–2736,
2778–2795 ("the two characters are interchanged by the conjugation"): the family's exponent
`ξ_s = ξ₀ ∘ ringClassRes` is inverted by an actual complex conjugation `c`,
`ξ_s(c σ c⁻¹) = ξ_s(σ)⁻¹` — the field `xiConj` of lane RC32's `StagedPresentation`.

* **`RingClassDihedral f S κ τ`** (definition; PRINT): conjugation by `τ` acts by inversion on
  `Gal(H_f/K)`. This is the generalized dihedral structure of ring class fields:
  D. A. Cox, *Primes of the Form x² + ny²*, §9.A, Lemma 9.3 — for an order `𝒪` of an imaginary
  quadratic field `K`, the ring class field `L` of `𝒪` is Galois over `ℚ` and
  `Gal(L/ℚ) ≅ Gal(L/K) ⋊ ℤ/2ℤ`, the nontrivial element acting on `Gal(L/K)` by inversion (page
  not recorded here). Used at tex 2778–2795.
* `artinClass_bar` (PROVED; lane E1's `artinClass_mul_eq_one`): the Frobenius core of
  `RingClassDihedral`: `Art([𝔭̄]) = Art([𝔭])⁻¹` for `𝔭 𝔭̄ = (p)`. With the transport of
  Frobenius elements along `τ` and Chebotarev density, it gives `RingClassDihedral`; those two
  steps are not formalized here.
* **`genuinePsi_conj`** (PROVED from `RingClassDihedral`): the genuine moving character is
  inverted by the conjugation of `G_{K,S_r}`.
* **`xiConj_genuine`**, **`xiConj_family`** (PROVED): the statement in exactly the shape of
  `StagedPresentation.xiConj`, for the coefficient support `S₀ ⊇ S_r` with an actual complex
  conjugation, under the named hypothesis that `S_r` is `κ`-stable. For lane E1's exact supports
  (the places above `r`) the stability is `isStable_primesAbove`.

Kinds: definitions, PRINT and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.XiConj

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.CoefModules (ActualConj conjGKS KS)
open ZInQ.Contrib.CloudB3E1RingClass (RingClassSetup setupGal ringClassRes ringClassGal
  artinClass artinClass_mul_eq_one ringClassOrder)
open ZInQ.Manuscript.RC.Wiring (genuinePsi GenuineFamilyMovingCharacter)
open TauCeti.GlobalNumberFields

variable {K : Type} [Field K] [NumberField K]

/-- **The generalized dihedral structure of ring class fields** (PRINT: Cox, *Primes of the Form
x² + ny²*, §9.A, Lemma 9.3; tex 2778–2795): conjugation by the complex conjugation `τ` (restricting
to `κ` on `K`) acts on `Gal(H_f/K)` by inversion, read through `G_{K,S} → Gal(H_f/K)`.
Kind: definition (the statement of the printed result). -/
def RingClassDihedral (f : ℕ) (hf : f ≠ 0) (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S) (κ : K ≃+* K)
    (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hτ : ∀ x : K,
      τ (algebraMap K (AlgebraicClosure K) x) = algebraMap K (AlgebraicClosure K) (κ x))
    (hSst : ∀ v w : HeightOneSpectrum (𝓞 K),
      w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K) → (v ∈ S ↔ w ∈ S)) :
    Prop :=
  ∀ σ : GKS K S, ringClassRes f hf S hS (conjGKS K κ τ hτ S hSst σ) = (ringClassRes f hf S hS σ)⁻¹

/-- **The Frobenius core** (PROVED; lane E1's `artinClass_mul_eq_one`): for ideals `𝔭`, `𝔭̄`
prime to the conductor with `𝔭 𝔭̄ = (p)`, `Art([𝔭̄]) = Art([𝔭])⁻¹` in `Gal(H_f/K)`. -/
theorem artinClass_bar (f : ℕ) (hf : f ≠ 0) (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (J J' : integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus) (p : ℤ)
    (hJJ' : (J : Ideal (𝓞 K)) * (J' : Ideal (𝓞 K)) = Ideal.span {(p : 𝓞 K)}) :
    artinClass f hf S hS J' = (artinClass f hf S hS J)⁻¹ :=
  eq_inv_of_mul_eq_one_right (artinClass_mul_eq_one f hf S hS J J' p hJJ')

/-- **The genuine moving character is inverted by the conjugation** (PROVED from
`RingClassDihedral`). -/
theorem genuinePsi_conj {s : ℕ} (C : RingClassSetup K s) (r m : ℕ)
    (ξ₀ : Additive (setupGal C r) →+ ZMod (2 ^ m)) (κ : K ≃+* K)
    (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hτ : ∀ x : K,
      τ (algebraMap K (AlgebraicClosure K) x) = algebraMap K (AlgebraicClosure K) (κ x))
    (hSst : ∀ v w : HeightOneSpectrum (𝓞 K),
      w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K) →
        (v ∈ C.Sr r ↔ w ∈ C.Sr r))
    (hD : RingClassDihedral (max r 1) (ZInQ.Contrib.CloudB3E1RingClass.max_one_ne_zero r)
      (C.Sr r) (C.hSr r) κ τ hτ hSst) (σ : GKS K (C.Sr r)) :
    genuinePsi C r m ξ₀ (conjGKS K κ τ hτ (C.Sr r) hSst σ) = (genuinePsi C r m ξ₀ σ)⁻¹ := by
  change AddMonoidHom.toMultiplicative ξ₀ (ringClassRes (max r 1) _ (C.Sr r) (C.hSr r)
      (conjGKS K κ τ hτ (C.Sr r) hSst σ)) =
    (AddMonoidHom.toMultiplicative ξ₀ (ringClassRes (max r 1) _ (C.Sr r) (C.hSr r) σ))⁻¹
  rw [hD σ]
  exact map_inv (AddMonoidHom.toMultiplicative ξ₀)
    (show Multiplicative (Additive (setupGal C r)) from
      ringClassRes (max r 1) _ (C.Sr r) (C.hSr r) σ)

/-- **`xiConj` for the genuine moving character** (PROVED from `RingClassDihedral`), in the shape
of `StagedPresentation.xiConj`: for a coefficient support `S₀ ⊇ S_r` with an actual complex
conjugation `Cc`, and `S_r` stable under `Cc.κ` (named hypothesis `hSst`; for the places above
`r` it is `isStable_primesAbove`). -/
theorem xiConj_genuine {s : ℕ} (C : RingClassSetup K s) (r m : ℕ)
    (ξ₀ : Additive (setupGal C r) →+ ZMod (2 ^ m)) {S₀ : Set (HeightOneSpectrum (𝓞 K))}
    (hSr : C.Sr r ⊆ S₀) (Cc : ActualConj K S₀)
    (hSst : ∀ v w : HeightOneSpectrum (𝓞 K),
      w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv Cc.κ : 𝓞 K →+* 𝓞 K) →
        (v ∈ C.Sr r ↔ w ∈ C.Sr r))
    (hD : RingClassDihedral (max r 1) (ZInQ.Contrib.CloudB3E1RingClass.max_one_ne_zero r)
      (C.Sr r) (C.hSr r) Cc.κ Cc.τ Cc.hτ hSst) (σ : GKS K S₀) :
    (genuinePsi C r m ξ₀).comp (inflMap K hSr).toMonoidHom (Cc.conj σ) =
      ((genuinePsi C r m ξ₀).comp (inflMap K hSr).toMonoidHom σ)⁻¹ := by
  change genuinePsi C r m ξ₀ (inflMap K hSr (Cc.conj σ)) =
    (genuinePsi C r m ξ₀ (inflMap K hSr σ))⁻¹
  rw [ActualConj.conj_apply, ZInQ.Manuscript.RC.CoefModules.inflMap_conjGKS K Cc.κ Cc.τ Cc.hτ hSr
    hSst Cc.hS σ]
  exact genuinePsi_conj C r m ξ₀ Cc.κ Cc.τ Cc.hτ hSst hD _

/-- **The `κ`-stability of lane E1's exact supports** (PROVED; `isStable_primesAbove`): if the
moving support is the set of places above `r`, it is stable under every automorphism of `K`. -/
theorem sr_stable_of_eq {s : ℕ} (C : RingClassSetup K s) (r : ℕ)
    (hEq : C.Sr r = {u : HeightOneSpectrum (𝓞 K) | ((r : ℤ) : 𝓞 K) ∈ u.asIdeal}) (κ : K ≃+* K) :
    ∀ v w : HeightOneSpectrum (𝓞 K),
      w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K) →
        (v ∈ C.Sr r ↔ w ∈ C.Sr r) := by
  rw [hEq]
  exact ZInQ.Manuscript.RC.CoefModules.isStable_primesAbove (r : ℤ) κ

/-- **`xiConj` for the family's moving character from genuine data** (PROVED from
`RingClassDihedral` at every stage): exactly the field `xiConj` of `StagedPresentation` for
`Ψ = G.toFamily`. -/
theorem xiConj_family {ℓ : ℕ} {Q : Finset ℕ} (G : GenuineFamilyMovingCharacter K ℓ Q)
    {S₀ : ℕ → Set (HeightOneSpectrum (𝓞 K))} (hSr : ∀ s, G.toFamily.Sr s ⊆ S₀ s)
    (Cc : ∀ s, ActualConj K (S₀ s))
    (hSst : ∀ s, ∀ v w : HeightOneSpectrum (𝓞 K),
      w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv (Cc s).κ : 𝓞 K →+* 𝓞 K) →
        (v ∈ G.C.Sr (G.r s) ↔ w ∈ G.C.Sr (G.r s)))
    (hD : ∀ s, RingClassDihedral (max (G.r s) 1)
      (ZInQ.Contrib.CloudB3E1RingClass.max_one_ne_zero (G.r s)) (G.C.Sr (G.r s))
      (G.C.hSr (G.r s)) (Cc s).κ (Cc s).τ (Cc s).hτ (hSst s)) :
    ∀ s σ, (G.toFamily.ψ s).comp (inflMap K (hSr s)).toMonoidHom ((Cc s).conj σ) =
      ((G.toFamily.ψ s).comp (inflMap K (hSr s)).toMonoidHom σ)⁻¹ :=
  fun s σ => xiConj_genuine G.C (G.r s) (2 * s) (G.ξ₀ s) (hSr s) (Cc s) (hSst s) (hD s) σ

end ZInQ.Contrib.CloudB3E2.XiConj
