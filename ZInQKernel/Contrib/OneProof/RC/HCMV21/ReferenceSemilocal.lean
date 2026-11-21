import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceCMEmbedding
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.FiniteAdele
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Integers
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-! Semilocal components of the actual CM ideles in the rational
reference frame. Tex 9150–9169. -/

namespace ZInQ.Manuscript.RC.HCMV21

open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum
open Eichler Adelic TauCeti
open scoped CategoryTheory.MonObj NumberField AdicCompletionExtension Pointwise TensorProduct

noncomputable section

variable {F : Type} [Field F] [NumberField F] {a b : ℚ}

private abbrev basePlace (p : Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (primesEquiv (R := 𝓞 ℚ)).symm p

local instance (v : HeightOneSpectrum (𝓞 ℚ)) : Algebra ℚ (v.adicCompletion ℚ) :=
  instAlgebraAdicCompletion (𝓞 ℚ) ℚ v

private def padicSemilocal (p : Prime) :
    ((basePlace p).adicCompletion ℚ ⊗[ℚ] F) ≃ₐ[ℚ] (ℚ_[p.val] ⊗[ℚ] F) :=
  Algebra.TensorProduct.congr (Padic.adicCompletionEquiv (𝓞 ℚ) p).toAlgEquiv.symm
    (AlgEquiv.refl : F ≃ₐ[ℚ] F)

/-- The semilocal factor of a finite idele at the rational prime. -/
def referenceCMComponents (p : Prime) : 𝔸ᶠ[𝓞 F, F]ˣ →* (ℚ_[p.val] ⊗[ℚ] F)ˣ :=
  (Units.map (padicSemilocal (F := F) p).toMonoidHom).comp
    (finiteIdeleSemilocalHom F (basePlace p))

private theorem padicSemilocal_tmul (p : Prime)
    (x : (basePlace p).adicCompletionIntegers ℚ) (y : 𝓞 F) :
    padicSemilocal p ((x : (basePlace p).adicCompletion ℚ) ⊗ₜ[ℚ] (y : F)) =
      (((PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) p).symm x : ℤ_[p.val]) : ℚ_[p.val]) ⊗ₜ[ℚ]
        (y : F) := by
  rw [padicSemilocal, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  exact congrArg (fun c : ℚ_[p.val] => c ⊗ₜ[ℚ] (y : F))
    (PadicInt.coe_adicCompletionIntegersEquiv_symm_apply (𝓞 ℚ) p x).symm

private theorem integral_of_adic_coordinates (p : Prime) (u : ℚ_[p.val] ⊗[ℚ] F)
    (h : ∀ w : {w : HeightOneSpectrum (𝓞 F) // w.asIdeal.LiesOver (basePlace p).asIdeal},
      semilocalEquiv F (basePlace p) ((padicSemilocal p).symm u) w ∈ w.1.adicCompletionIntegers F) :
    ∃ x : (basePlace p).adicCompletionIntegers ℚ ⊗[𝓞 ℚ] 𝓞 F,
      padicSemilocal p (integralSemilocalToField F (basePlace p) x) = u := by
  let z : (w : {w : HeightOneSpectrum (𝓞 F) // w.asIdeal.LiesOver (basePlace p).asIdeal}) →
      w.1.adicCompletionIntegers F := fun w => ⟨_, h w⟩
  let x := (integralSemilocalEquiv F (basePlace p)).symm z
  refine ⟨x, ?_⟩
  apply (padicSemilocal p).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  apply (semilocalEquiv F (basePlace p)).injective
  rw [integralSemilocalEquiv_fieldCompatibility]
  exact congrArg (fun t : (w : {w : HeightOneSpectrum (𝓞 F) //
      w.asIdeal.LiesOver (basePlace p).asIdeal}) → w.1.adicCompletionIntegers F =>
    fun w : {w : HeightOneSpectrum (𝓞 F) // w.asIdeal.LiesOver (basePlace p).asIdeal} =>
      (t w : w.1.adicCompletion F)) ((integralSemilocalEquiv F (basePlace p)).apply_symm_apply z)

private theorem localOrder_contains_CM_coordinates {k : Type} [Field k] {A : PkgI3.AbVar k}
    (p : Prime) (S : Order a b) (j : A.End ≃+* S.ring) (action : 𝓞 F →+* A.End)
    (C : Subgroup (A.Pt k)) (N : ℕ) (hN : N ≠ 0) (hC : ∀ P ∈ C, P ^ N = 1)
    (hact : ∀ x : 𝓞 F, action x ∈ levelEnd A C)
    (x : (basePlace p).adicCompletionIntegers ℚ ⊗[𝓞 ℚ] 𝓞 F) :
    localCMEmbedding p (referenceCMEmbedding S j action)
      (padicSemilocal p (integralSemilocalToField F (basePlace p) x)) ∈
        (levelOrderOfEndOrder S j C N hN hC).completion p.val := by
  induction x using TensorProduct.inductionOn with
  | tmul c y =>
    rw [integralSemilocalToField_tmul, padicSemilocal_tmul]
    exact localCMEmbedding_integral_tensors p S j action C N hN hC hact _ y
  | add x y hx hy =>
    simpa only [map_add] using ((levelOrderOfEndOrder S j C N hN hC).completion p.val).add_mem hx hy

private theorem adic_coordinates_of_localOrder (p : Prime)
    (R : Order a b) (j : F →ₐ[ℚ] B a b) (u : ℚ_[p.val] ⊗[ℚ] F)
    (hu : localCMEmbedding p j u ∈ R.completion p.val)
    (w : {w : HeightOneSpectrum (𝓞 F) // w.asIdeal.LiesOver (basePlace p).asIdeal}) :
    semilocalEquiv F (basePlace p) ((padicSemilocal p).symm u) w ∈ w.1.adicCompletionIntegers F := by
  let ρ : (ℚ_[p.val] ⊗[ℚ] F) →+* w.1.adicCompletion F :=
    (Pi.evalRingHom _ w).comp
      ((semilocalEquiv F (basePlace p)).toRingHom.comp (padicSemilocal p).symm.toRingHom)
  have hR := localLattice_full p R.full
  rw [← R.completion_toSubmodule] at hR
  let : Module.Finite ℤ_[p.val] (R.completion p.val) := Module.Finite.of_fg hR.fg
  have hy : IsIntegral ℤ_[p.val] (⟨_, hu⟩ : R.completion p.val) :=
    Algebra.IsIntegral.isIntegral _
  have hInt : IsIntegral ℤ_[p.val] (localCMEmbedding p j u) := by
    have h := RingHom.IsIntegralElem.map hy (R.completion p.val).val.toRingHom
    exact h
  let f : (ℚ_[p.val] ⊗[ℚ] F) →ₐ[ℤ_[p.val]] Bp p.val a b :=
    { toRingHom := (localCMEmbedding p j).toRingHom
      commutes' := fun x => (localCMEmbedding p j).commutes (x : ℚ_[p.val]) }
  have ht : IsIntegral ℤ_[p.val] u :=
    (isIntegral_algHom_iff f (localCMEmbedding_injective p j)).mp hInt
  have h := RingHom.IsIntegralElem.map ht ρ
  let e := (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) p).toAlgEquiv
  have hc : ρ.comp (algebraMap ℤ_[p.val] (ℚ_[p.val] ⊗[ℚ] F)) =
      (algebraMap ((basePlace p).adicCompletionIntegers ℚ) (w.1.adicCompletion F)).comp
        e.toRingHom := by
    apply RingHom.ext
    intro x
    let c : (basePlace p).adicCompletionIntegers ℚ := e x
    have hxc : (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) p).symm c = x :=
      e.symm_apply_apply x
    have hx : padicSemilocal p ((c : (basePlace p).adicCompletion ℚ) ⊗ₜ[ℚ] (1 : F)) =
        (x : ℚ_[p.val]) ⊗ₜ[ℚ] (1 : F) :=
      (padicSemilocal_tmul p c (1 : 𝓞 F)).trans
        (congrArg (fun z : ℤ_[p.val] => (z : ℚ_[p.val]) ⊗ₜ[ℚ] (1 : F)) hxc)
    change semilocalEquiv F (basePlace p)
        ((padicSemilocal p).symm ((x : ℚ_[p.val]) ⊗ₜ[ℚ] (1 : F))) w = _
    rw [← hx, AlgEquiv.symm_apply_apply]
    change semilocalEquiv F (basePlace p)
        (algebraMap ((basePlace p).adicCompletion ℚ)
          ((basePlace p).adicCompletion ℚ ⊗[ℚ] F) (c : (basePlace p).adicCompletion ℚ)) w = _
    rw [AlgEquiv.commutes]
    rfl
  rw [hc] at h
  have hi : IsIntegral ((basePlace p).adicCompletionIntegers ℚ) (ρ u) :=
    RingHom.IsIntegralElem.of_comp h
  obtain ⟨z, hz⟩ := (IsIntegralClosure.isIntegral_iff (A := w.1.adicCompletionIntegers F)).mp hi
  change ρ u ∈ w.1.adicCompletionIntegers F
  exact hz ▸ z.property

variable {k : Type} [Field k] {A : PkgI3.AbVar k}

/-- The local CM factor belongs to the completed geometric order exactly
when its entries in all completions of the CM field above the prime are integral. -/
theorem reference_localCM_mem_iff (p : Prime) (S : Order a b) (j : A.End ≃+* S.ring)
    (action : 𝓞 F →+* A.End) (C : Subgroup (A.Pt k)) (N : ℕ) (hN : N ≠ 0)
    (hC : ∀ P ∈ C, P ^ N = 1) (hact : ∀ x : 𝓞 F, action x ∈ levelEnd A C)
    (s : 𝔸ᶠ[𝓞 F, F]ˣ) :
    localCMEmbedding p (referenceCMEmbedding S j action)
      (referenceCMComponents p s : ℚ_[p.val] ⊗[ℚ] F) ∈
        (levelOrderOfEndOrder S j C N hN hC).completion p.val ↔
      ∀ w : {w : HeightOneSpectrum (𝓞 F) // w.asIdeal.LiesOver (basePlace p).asIdeal},
        (s : 𝔸ᶠ[𝓞 F, F]) w.1 ∈ w.1.adicCompletionIntegers F := by
  let u : ℚ_[p.val] ⊗[ℚ] F := ↑(referenceCMComponents p s)
  have hu : (padicSemilocal p).symm u = (finiteIdeleSemilocalHom F (basePlace p) s : _) :=
    (padicSemilocal p).symm_apply_apply _
  have he (w : {w : HeightOneSpectrum (𝓞 F) // w.asIdeal.LiesOver (basePlace p).asIdeal}) :
      semilocalEquiv F (basePlace p) ((padicSemilocal p).symm u) w = (s : 𝔸ᶠ[𝓞 F, F]) w.1 :=
    (congrArg (fun v => semilocalEquiv F (basePlace p) v w) hu).trans
      (semilocalEquiv_finiteIdeleSemilocalHom s w)
  constructor
  · intro h w
    rw [← he w]
    exact adic_coordinates_of_localOrder p _ _ u h w
  · intro h
    obtain ⟨x, hx⟩ := integral_of_adic_coordinates p u (fun w => (he w).symm ▸ h w)
    change localCMEmbedding p (referenceCMEmbedding S j action) u ∈ _
    rw [← hx]
    exact localOrder_contains_CM_coordinates p S j action C N hN hC hact x

/-- The finite-idele map induced by the rational extension of the
specialized action. The restricted-product condition uses only the
finitely many nonintegral components of the idele and its inverse. -/
def referenceCMAdeles (R S : Order a b) (j : A.End ≃+* S.ring)
    (action : 𝓞 F →+* A.End) (C : Subgroup (A.Pt k)) (N : ℕ) (hN : N ≠ 0)
    (hC : ∀ P ∈ C, P ^ N = 1) (hact : ∀ x : 𝓞 F, action x ∈ levelEnd A C) :
    𝔸ᶠ[𝓞 F, F]ˣ →* Adelic.FiniteUnits R := by
  let E := levelOrderOfEndOrder S j C N hN hC
  let f (p : Prime) : 𝔸ᶠ[𝓞 F, F]ˣ →* (Bp p.val a b)ˣ :=
    (Units.map (localCMEmbedding p (referenceCMEmbedding S j action)).toMonoidHom).comp
      (referenceCMComponents p)
  let z (s : 𝔸ᶠ[𝓞 F, F]ˣ) : Adelic.FiniteUnits R := ⟨fun p => f p s, by
    have hbad (t : 𝔸ᶠ[𝓞 F, F]ˣ) :
        {w : HeightOneSpectrum (𝓞 F) | (t : 𝔸ᶠ[𝓞 F, F]) w ∉ w.adicCompletionIntegers F}.Finite :=
      Filter.eventually_cofinite.mp (t : 𝔸ᶠ[𝓞 F, F]).property
    let down (w : HeightOneSpectrum (𝓞 F)) : Prime := primesEquiv (w.under (𝓞 ℚ))
    apply (((hbad s).image down).union (((hbad s⁻¹).image down).union
      (finite_localLattice_ne E.full R.full))).subset
    intro p hp
    by_contra! h
    change ¬ (p ∈ _ ∨ p ∈ _ ∨ localLattice p.val E.lattice ≠ localLattice p.val R.lattice) at h
    push Not at h
    have hE : E.completion p.val = R.completion p.val := by
      apply Subalgebra.toSubmodule_injective
      rw [E.completion_toSubmodule, R.completion_toSubmodule]
      exact h.2.2
    have hw {t : 𝔸ᶠ[𝓞 F, F]ˣ} (ht : p ∉ down '' {w : HeightOneSpectrum (𝓞 F) |
        (t : 𝔸ᶠ[𝓞 F, F]) w ∉ w.adicCompletionIntegers F}) :
        (f p t : Bp p.val a b) ∈ E.completion p.val := by
      apply (reference_localCM_mem_iff p S j action C N hN hC hact t).mpr
      intro w
      by_contra hb
      apply ht
      exact ⟨w.1, hb, by
        dsimp [down]
        rw [under_eq_of_liesOver w.2]
        exact primesEquiv.apply_symm_apply p⟩
    apply hp
    change (f p s : Bp p.val a b) ∈ R.completion p.val ∧
      (↑(f p s)⁻¹ : Bp p.val a b) ∈ R.completion p.val
    rw [← hE, ← map_inv]
    exact ⟨hw h.1, hw h.2.1⟩⟩
  exact
    { toFun := z
      map_one' := Subtype.ext (funext fun p => map_one (f p))
      map_mul' s t := Subtype.ext (funext fun p => map_mul (f p) s t) }

/-- The stabilizer test of the original assembly, for the CM action of
a single framed geometric reference. -/
theorem reference_geometry_hunit {R S : Order a b} (j : A.End ≃+* S.ring)
    (action : 𝓞 F →+* A.End) (C : Subgroup (A.Pt k)) (N : ℕ) (hN : N ≠ 0)
    (hC : ∀ P ∈ C, P ^ N = 1) (hact : ∀ x : 𝓞 F, action x ∈ levelEnd A C)
    (z : Adelic.FiniteUnits R)
    (hz : ReferenceOrderCoordinates R (levelOrderOfEndOrder S j C N hN hC) z)
    (s : 𝔸ᶠ[𝓞 F, F]ˣ) :
    z⁻¹ * referenceCMAdeles R S j action C N hN hC hact s * z ∈ Adelic.integralUnits R ↔
      s ∈ FiniteAdeleRing.integralUnits (𝓞 F) F := by
  let J := referenceCMAdeles R S j action C N hN hC hact
  let E := levelOrderOfEndOrder S j C N hN hC
  rw [mem_integralUnits_iff_forall_mem_adicCompletionIntegers]
  have hlocal (p : Prime) (t : 𝔸ᶠ[𝓞 F, F]ˣ) :
      ((J t).val p : Bp p.val a b) ∈ E.completion p.val ↔
        ∀ w : {w : HeightOneSpectrum (𝓞 F) // w.asIdeal.LiesOver (basePlace p).asIdeal},
          (t : 𝔸ᶠ[𝓞 F, F]) w.1 ∈ w.1.adicCompletionIntegers F :=
    reference_localCM_mem_iff p S j action C N hN hC hact t
  have htest (p : Prime) :
      (z.val p)⁻¹ * (J s).val p * z.val p ∈ Adelic.localUnits R p ↔
        ((J s).val p : Bp p.val a b) ∈ E.completion p.val ∧
          ((J s⁻¹).val p : Bp p.val a b) ∈ E.completion p.val := by
    have he : (J s⁻¹).val p = ((J s).val p)⁻¹ := congrArg (fun t => t.val p) (map_inv J s)
    rw [he]
    change ((↑((z.val p)⁻¹ * (J s).val p * z.val p) : Bp p.val a b) ∈ R.completion p.val ∧
      (↑((z.val p)⁻¹ * (J s).val p * z.val p)⁻¹ : Bp p.val a b) ∈ R.completion p.val) ↔ _
    simpa only [mul_inv_rev, inv_inv, Units.val_mul, mul_assoc] using
      and_congr (hz p ((J s).val p : Bp p.val a b))
        (hz p (↑((J s).val p)⁻¹ : Bp p.val a b))
  change (∀ p : Prime, (z.val p)⁻¹ * (J s).val p * z.val p ∈ Adelic.localUnits R p) ↔ _
  simp only [htest, hlocal]
  constructor
  · intro h w
    let p : Prime := primesEquiv (w.under (𝓞 ℚ))
    have hw : w.asIdeal.LiesOver (basePlace p).asIdeal := by
      change w.asIdeal.LiesOver ((primesEquiv (R := 𝓞 ℚ)).symm p).asIdeal
      rw [show p = primesEquiv (w.under (𝓞 ℚ)) from rfl, primesEquiv.symm_apply_apply]
      infer_instance
    exact ⟨(h p).1 ⟨w, hw⟩, (h p).2 ⟨w, hw⟩⟩
  · intro h p
    exact ⟨fun w => (h w.1).1, fun w => (h w.1).2⟩

end

end ZInQ.Manuscript.RC.HCMV21
