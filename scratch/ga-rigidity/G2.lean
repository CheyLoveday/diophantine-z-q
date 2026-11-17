import ZInQKernel.OneProof.H.TailY

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.HeightSplit

namespace GaRigidity

variable {k : Type} [Field k]

/-! ## §3. The local ring of `ℙ¹` at `∞`: `R = k[s]_(s)` with `s = 1/x`, its translations and its residue map -/

/-- The prime `(s) ⊆ k[s]`. -/
abbrev P0 (k : Type) [Field k] : Ideal (Polynomial k) := Ideal.span {Polynomial.X}

instance P0.isPrime : (P0 k).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

/-- `K = k(s) = Frac k[s]`. -/
abbrev Kl (k : Type) [Field k] : Type := FractionRing (Polynomial k)

theorem P0_le : (P0 k).primeCompl ≤ nonZeroDivisors (Polynomial k) :=
  le_nonZeroDivisors_of_noZeroDivisors (fun h0 => h0 (Ideal.zero_mem _))

/-- `R = k[s]_(s) ⊆ K`, a discrete valuation ring (the local ring of `ℙ¹` at `∞`, with `s = 1/x`). -/
abbrev Rl (k : Type) [Field k] : Type :=
  ↥(Localization.subalgebra.ofField (Kl k) (P0 k).primeCompl P0_le)

instance : IsLocalization.AtPrime (Rl k) (P0 k) :=
  Localization.subalgebra.isLocalization_ofField (Kl k) (P0 k).primeCompl P0_le

instance : IsDiscreteValuationRing (Rl k) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Polynomial k)
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact Polynomial.X_ne_zero) (Rl k)

example : IsFractionRing (Rl k) (Kl k) := inferInstance
example : IsScalarTower k (Rl k) (Kl k) := inferInstance
example : IsScalarTower k (Polynomial k) (Rl k) := inferInstance

/-- The uniformizer `s ∈ R`. -/
abbrev sR (k : Type) [Field k] : Rl k := algebraMap (Polynomial k) (Rl k) Polynomial.X

theorem not_mem_P0 {y : Polynomial k} (hy : y ∈ (P0 k).primeCompl) : y.eval 0 ≠ 0 := by
  intro h
  apply hy
  show y ∈ P0 k
  rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero, h]

/-- The residue map `ρ : R → k`, `f ↦ f(0)` (value at `∞`). -/
def rho (k : Type) [Field k] : Rl k →ₐ[k] k :=
  IsLocalization.liftAlgHom (M := (P0 k).primeCompl) (f := Polynomial.aeval (0 : k)) (fun y => by
    rw [isUnit_iff_ne_zero, Polynomial.aeval_def, Polynomial.eval₂_at_zero]
    simpa [Polynomial.coeff_zero_eq_eval_zero] using not_mem_P0 y.2)

theorem rho_algebraMap (p : Polynomial k) : rho k (algebraMap (Polynomial k) (Rl k) p) = p.eval 0 := by
  rw [rho, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  simp [Polynomial.aeval_def, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero]

theorem rho_s : rho k (sR k) = 0 := by
  rw [rho_algebraMap]; simp

theorem rho_surjective : Function.Surjective (rho k) := fun c => ⟨algebraMap k _ c, by simp⟩

/-- An element of the local ring `R` with nonzero residue is a unit. -/
theorem isUnit_of_rho_ne_zero {x : Rl k} (hx : rho k x ≠ 0) : IsUnit x := by
  by_contra hu
  have hm : x ∈ IsLocalRing.maximalIdeal (Rl k) := (IsLocalRing.mem_maximalIdeal x).mpr hu
  rw [← IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective (rho k) rho_surjective)] at hm
  exact hx (RingHom.mem_ker.mp hm)

/-- `1 + c s` is a unit of `R`. -/
theorem isUnit_u (c : k) : IsUnit (1 + algebraMap k (Rl k) c * sR k) :=
  isUnit_of_rho_ne_zero (by simp [rho_s])

/-- `s/(1 + c s)`. -/
def sT (c : k) : Rl k := sR k * ↑(isUnit_u c).unit⁻¹

theorem rho_sT (c : k) : rho k (sT c) = 0 := by
  rw [sT, map_mul, rho_s, zero_mul]

/-- **The translation `x ↦ x + c` at `∞`**: `τ_c : R → R`, `s ↦ s/(1 + c s)`. -/
def tau (c : k) : Rl k →ₐ[k] Rl k :=
  IsLocalization.liftAlgHom (M := (P0 k).primeCompl) (f := Polynomial.aeval (sT c)) (fun y => by
    apply isUnit_of_rho_ne_zero
    rw [← Polynomial.aeval_algHom_apply, rho_sT, Polynomial.aeval_def, Polynomial.eval₂_at_zero]
    simpa [Polynomial.coeff_zero_eq_eval_zero] using not_mem_P0 y.2)

theorem tau_algebraMap (c : k) (p : Polynomial k) :
    tau c (algebraMap (Polynomial k) (Rl k) p) = Polynomial.aeval (sT c) p := by
  rw [tau, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

theorem tau_s (c : k) : tau c (sR k) = sT c := by
  rw [tau_algebraMap, Polynomial.aeval_X]

/-- `ρ ∘ τ_c = ρ`: the translation fixes the point at `∞`. -/
theorem rho_comp_tau (c : k) : (rho k).comp (tau c) = rho k := by
  apply IsLocalization.algHom_ext (P0 k).primeCompl
  apply Polynomial.algHom_ext
  change rho k (tau c (algebraMap _ _ Polynomial.X)) = rho k (algebraMap _ _ Polynomial.X)
  rw [tau_algebraMap, Polynomial.aeval_X, rho_sT, rho_algebraMap]
  simp

/-- `τ_{-c} ∘ τ_c = id`. -/
theorem tau_neg_comp_tau (c : k) : (tau (-c)).comp (tau c) = AlgHom.id k (Rl k) := by
  apply IsLocalization.algHom_ext (P0 k).primeCompl
  apply Polynomial.algHom_ext
  change tau (-c) (tau c (algebraMap _ _ Polynomial.X)) = algebraMap _ _ Polynomial.X
  rw [tau_algebraMap, Polynomial.aeval_X, sT, map_mul, tau_s]
  set a : Rl k := ↑(isUnit_u c).unit⁻¹
  set b : Rl k := ↑(isUnit_u (-c)).unit⁻¹
  have ha : a * (1 + algebraMap k (Rl k) c * sR k) = 1 := IsUnit.val_inv_mul (isUnit_u c)
  have hb : b * (1 + algebraMap k (Rl k) (-c) * sR k) = 1 := IsUnit.val_inv_mul (isUnit_u (-c))
  have h1 := congrArg (tau (-c)) ha
  rw [map_mul, map_one, map_add, map_one, map_mul, AlgHom.commutes, tau_s, sT] at h1
  change sR k * b * tau (-c) a = sR k
  rw [map_neg] at hb
  linear_combination (sR k * tau (-c) a) * hb + sR k * h1

theorem tau_injective (c : k) : Function.Injective (tau c) := by
  intro x y h
  have := congrArg (tau (-c)) h
  rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, tau_neg_comp_tau] at this

theorem sR_ne_zero : sR k ≠ 0 := by
  intro h
  have hinj : Function.Injective (algebraMap (Polynomial k) (Rl k)) :=
    IsLocalization.injective (Rl k) P0_le
  exact Polynomial.X_ne_zero (hinj (h.trans (map_zero _).symm))

/-- `j : R → K`. -/
abbrev jR (k : Type) [Field k] : Rl k →ₐ[k] Kl k := IsScalarTower.toAlgHom k (Rl k) (Kl k)

/-- `τ_c` on `K`. -/
theorem jtau_injective (c : k) : Function.Injective ((jR k).comp (tau c)) :=
  (IsFractionRing.injective (Rl k) (Kl k)).comp (tau_injective c)

def tauK (c : k) : Kl k →ₐ[k] Kl k :=
  IsFractionRing.liftAlgHom (g := (jR k).comp (tau c)) (jtau_injective c)

theorem tauK_comp_jR (c : k) : (tauK c).comp (jR k) = (jR k).comp (tau c) := by
  apply AlgHom.ext; intro x
  show tauK c (algebraMap (Rl k) (Kl k) x) = algebraMap (Rl k) (Kl k) (tau c x)
  rw [tauK, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]; rfl

/-- `x = 1/s ∈ K`. -/
abbrev xK (k : Type) [Field k] : Kl k := (algebraMap (Rl k) (Kl k) (sR k))⁻¹

/-- `τ_c(1/s) = 1/s + c`. -/
theorem tauK_xK (c : k) : tauK c (xK k) = xK k + algebraMap k (Kl k) c := by
  have h1 : tauK c (algebraMap (Rl k) (Kl k) (sR k)) = algebraMap (Rl k) (Kl k) (sT c) := by
    have := congrArg (fun f => f (sR k)) (tauK_comp_jR c)
    simpa [tau_s] using this
  rw [map_inv₀, h1, sT, RingHom.map_mul]
  have hs : algebraMap (Rl k) (Kl k) (sR k) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Rl k) (Kl k))).mpr sR_ne_zero
  have ha : (↑(isUnit_u c).unit⁻¹ : Rl k) * (1 + algebraMap k (Rl k) c * sR k) = 1 := IsUnit.val_inv_mul (isUnit_u c)
  have ha' := congrArg (algebraMap (Rl k) (Kl k)) ha
  rw [RingHom.map_mul, RingHom.map_one, RingHom.map_add, RingHom.map_one, RingHom.map_mul,
    ← IsScalarTower.algebraMap_apply] at ha'
  set A := algebraMap (Rl k) (Kl k) ↑(isUnit_u c).unit⁻¹
  set S := algebraMap (Rl k) (Kl k) (sR k)
  have hA : A = (1 + algebraMap k (Kl k) c * S)⁻¹ := eq_inv_of_mul_eq_one_left ha'
  have hu : 1 + algebraMap k (Kl k) c * S ≠ 0 := by
    intro h0; rw [h0, mul_zero] at ha'; exact zero_ne_one ha'
  rw [hA, xK]
  field_simp
  ring

end GaRigidity
