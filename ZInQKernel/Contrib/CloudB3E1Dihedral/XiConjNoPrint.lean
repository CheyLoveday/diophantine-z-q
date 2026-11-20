import ZInQKernel.Contrib.CloudB3E1Dihedral.Stability
import ZInQKernel.Contrib.CloudB3E1RingClass.CurveDataExact
import ZInQKernel.Contrib.CloudB3E1RingClass.FromPairs

/-!
# `xiConj` without the print, end to end

Manuscript `diophantine_zq.tex`, Proposition `ex:arith-moving-character`, tex 2731–2736 and
2778–2795: "the two characters are interchanged by the conjugation".

Lane E2's `XiConj.xiConj_family` proves the field `xiConj` of lane RC32's `StagedPresentation` for
the family's moving character `G.toFamily`. It takes two inputs: the `κ`-stability `hSst` of the
moving supports, and the dihedral structure `hD : RingClassDihedral …` at every stage. Both are
now discharged:
* `hD`, by `ringClassDihedral` (`Stability.lean`, PROVED: no print). Its hypotheses are
  `[K : ℚ] = 2` and `κ ≠ id`; the latter follows for an actual complex conjugation of a totally
  complex `K` (`complexConj_restrict_ne_refl`).
* `hSst`, by `sr_stable_of_eq` when the moving supports are exactly the places above `r_i`.

Results.
* **`xiConj_family'`** (PROVED): for `G : GenuineFamilyMovingCharacter K ℓ Q` over an imaginary
  quadratic `K` whose moving supports are the places above `r_i`, the field `xiConj` holds for
  every family of actual complex conjugations. No print and no named input remain.
* **`genuinePsi_anticyclotomic`** (PROVED): RC0's family character `G.toFamily.ψ i` is
  anticyclotomic, `ψ_i(τ σ τ⁻¹) = ψ_i(σ)⁻¹` on `G_{K,S_{r_i}}`, for any actual complex
  conjugation.
* **`exists_genuineFamilyMovingCharacter_xiConj`** (PROVED): consistency of the two leaves. The
  family character built by `exists_genuineFamilyMovingCharacter_exactSr` (moving supports exactly
  the places above `r_i`) serves both leaves. It is RC0's `GenuineFamilyMovingCharacter` (the
  moving-character leaf), and it satisfies `xiConj` (the staged-presentation leaf) with no further
  input. The leaves see the same `G`, `ψ_i` and `S_{r_i}`, so one family character can serve both
  with the exact support.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1Dihedral

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.SelmerComplex (GKS inflMap)
open ZInQ.Manuscript.RC.CoefModules (ActualConj conjGKS complexConj_restrict_ne_refl)
open ZInQ.Contrib.CloudB3E1RingClass (RingClassSetup setupGal max_one_ne_zero)
open ZInQ.Contrib.CloudB3E2.XiConj (xiConj_family genuinePsi_conj sr_stable_of_eq)
open ZInQ.Manuscript.RC.PrintsArith (SerreThm3 CMjInteger)
open ZInQ.Contrib.ChebFD.C10 (Qbar)
open ZInQ.Contrib.CloudB3RC53 (Ecurve)
open ZInQ.Contrib.CloudB3RC53.CST (newformLevel)
open ZInQ.Manuscript.RC.TateWiring (FrobeniusTrace)

variable {K : Type} [Field K] [NumberField K]

/-- `κ ≠ id` as a ring map gives `κ ≠ 1` in `Gal(K/ℚ)`. Kind: PROVED. -/
theorem ringEquivAlg_ne_one {κ : K ≃+* K} (h : κ ≠ RingEquiv.refl K) : ringEquivAlg κ ≠ 1 := by
  intro h1
  apply h
  ext x
  have := congrArg (fun g : K ≃ₐ[ℚ] K => g x) h1
  simpa [ringEquivAlg_apply] using this

/-- **For an actual complex conjugation of a totally complex `K`, `κ ≠ 1`** (lane RC's
`complexConj_restrict_ne_refl`). Kind: PROVED. -/
theorem actualConj_ne_one [IsTotallyComplex K] {S : Set (HeightOneSpectrum (𝓞 K))}
    (Cc : ActualConj K S) : ringEquivAlg Cc.κ ≠ 1 :=
  ringEquivAlg_ne_one (K := K) (complexConj_restrict_ne_refl K Cc.ι Cc.τ Cc.hι Cc.κ Cc.hτ)

/-- **RC0's family character is anticyclotomic** (tex 2731–2736, 2778–2795; no print): for an
imaginary quadratic `K`, a moving support `S_{r_i}` that is `κ`-stable, and any actual complex
conjugation `(τ, κ)`, `ψ_i(τ σ τ⁻¹) = ψ_i(σ)⁻¹` on `G_{K,S_{r_i}}`. Kind: PROVED. -/
theorem genuinePsi_anticyclotomic [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2) {ℓ : ℕ}
    {Q : Finset ℕ} (G : GenuineFamilyMovingCharacter K ℓ Q) (i : ℕ)
    {S₀ : Set (HeightOneSpectrum (𝓞 K))} (Cc : ActualConj K S₀)
    (hSst : ∀ v w : HeightOneSpectrum (𝓞 K),
      w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv Cc.κ : 𝓞 K →+* 𝓞 K) →
        (v ∈ G.C.Sr (G.r i) ↔ w ∈ G.C.Sr (G.r i)))
    (σ : GKS K (G.C.Sr (G.r i))) :
    G.toFamily.ψ i (conjGKS K Cc.κ Cc.τ Cc.hτ (G.C.Sr (G.r i)) hSst σ) = (G.toFamily.ψ i σ)⁻¹ :=
  genuinePsi_conj G.C (G.r i) (2 * i) (G.ξ₀ i) Cc.κ Cc.τ Cc.hτ hSst
    (ringClassDihedral (max (G.r i) 1) (max_one_ne_zero (G.r i)) (G.C.Sr (G.r i))
      (G.C.hSr (G.r i)) Cc.κ Cc.τ Cc.hτ hSst hK (actualConj_ne_one Cc)) σ

/-- **`xiConj` for the family's moving character, with no print and no named input** (tex
2731–2736, 2778–2795): for an imaginary quadratic `K` and moving supports exactly the places above
`r_i` (as constructed by `exists_genuineFamilyMovingCharacter_exactSr`), the field `xiConj` of
`StagedPresentation` holds for every family of actual complex conjugations on coefficient supports
`S₀ i ⊇ S_{r_i}`. Kind: PROVED. -/
theorem xiConj_family' [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2) {ℓ : ℕ}
    {Q : Finset ℕ} (G : GenuineFamilyMovingCharacter K ℓ Q)
    (hEq : ∀ i, G.C.Sr (G.r i) = {u : HeightOneSpectrum (𝓞 K) | ((G.r i : ℤ) : 𝓞 K) ∈ u.asIdeal})
    {S₀ : ℕ → Set (HeightOneSpectrum (𝓞 K))} (hSr : ∀ i, G.toFamily.Sr i ⊆ S₀ i)
    (Cc : ∀ i, ActualConj K (S₀ i)) :
    ∀ i σ, (G.toFamily.ψ i).comp (inflMap K (hSr i)).toMonoidHom ((Cc i).conj σ) =
      ((G.toFamily.ψ i).comp (inflMap K (hSr i)).toMonoidHom σ)⁻¹ :=
  xiConj_family G hSr Cc (fun i => sr_stable_of_eq G.C (G.r i) (hEq i) (Cc i).κ)
    (fun i => ringClassDihedral (max (G.r i) 1) (max_one_ne_zero (G.r i)) (G.C.Sr (G.r i))
      (G.C.hSr (G.r i)) (Cc i).κ (Cc i).τ (Cc i).hτ _ hK (actualConj_ne_one (Cc i)))

/-- **One family character serves both leaves, with the exact support** (tex 2716–2736,
2778–2795, 3500–3702): the family character `G` of `exists_genuineFamilyMovingCharacter_exactSr`
(RC0's moving-character leaf, for the final companion and an admissible family) has moving
supports exactly the places above `r_i`, and satisfies `xiConj` (the staged-presentation leaf) for
every family of actual complex conjugations, with no print. Kind: PROVED. -/
theorem exists_genuineFamilyMovingCharacter_xiConj {ℓ : ℕ} {D : RCData ℓ} (St : RCSteps D)
    (hodd : ¬ D.OddEmptyUnit)
    (hS2N : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ D.S)
    {F : Family} (hF : F.Admissible D.S D.kfin) {Q : Finset ℕ} (hQ : Q ⊆ F.Q)
    (hS : SerreThm3) (hcm : CMjInteger) (hℓ : 0 < ℓ) (hT : FrobeniusTrace (Ecurve ℓ)) :
    ∃ (s : Qbar) (_ : s ^ 2 = algebraMap ℚ Qbar D.kfin)
      (G : GenuineFamilyMovingCharacter (ZInQ.Manuscript.RC.TateWiring.quadField s) ℓ Q),
      (∀ i, G.C.Sr (G.r i) = placesOf (ZInQ.Manuscript.RC.TateWiring.quadField s) (G.r i : ℤ)) ∧
      ∀ (S₀ : ℕ → Set (HeightOneSpectrum (𝓞 (ZInQ.Manuscript.RC.TateWiring.quadField s))))
        (hSr : ∀ i, G.toFamily.Sr i ⊆ S₀ i)
        (Cc : ∀ i, ActualConj (ZInQ.Manuscript.RC.TateWiring.quadField s) (S₀ i)),
        ∀ i σ, (G.toFamily.ψ i).comp (inflMap _ (hSr i)).toMonoidHom ((Cc i).conj σ) =
          ((G.toFamily.ψ i).comp (inflMap _ (hSr i)).toMonoidHom σ)⁻¹ := by
  obtain ⟨s, hs, G, -, -, hEx⟩ :=
    ZInQ.Contrib.CloudB3E1RingClass.exists_genuineFamilyMovingCharacter_exactSr St hodd hS2N hF
      hQ hS hcm hℓ hT
  obtain ⟨hk0, -⟩ := St.companion hodd
  have hsD : s ^ 2 = algebraMap ℚ Qbar ((D.kfin : ℤ) : ℚ) := hs
  have hK := ZInQ.Contrib.CloudB3E1RingClass.finrank_quadField_of_neg hsD (by exact_mod_cast hk0)
  have := ZInQ.Contrib.CloudB3E1RingClass.isTotallyComplex_quadField_of_neg hsD
    (by exact_mod_cast hk0)
  refine ⟨s, hs, G, hEx, fun S₀ hSr Cc => xiConj_family' hK G (fun i => hEx i) hSr Cc⟩

end ZInQ.Contrib.CloudB3E1Dihedral
