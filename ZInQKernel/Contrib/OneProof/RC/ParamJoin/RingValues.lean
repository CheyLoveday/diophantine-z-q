import ZInQKernel.Contrib.OneProof.RC.ParamJoin.AtScale
import Mathlib.LinearAlgebra.Unimodular

/-! The value for the existing rough companion form at its own conductor
(tex 2413–2416, 2428–2431, 2839–2844; provenance (c)). -/

noncomputable section

open Module NumberField ZInQ.Progressions TauCeti.GlobalNumberFields
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
  ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.PreparedParam

namespace ZInQ.Manuscript.RC.ParamJoin

/-- In a quadratic field, reducing the second coordinate of a basis `(1, ω)`
modulo the conductor has kernel `ℤ + c 𝓞 K`. -/
private theorem conductorOrder_discr {K : Type} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (c : ℕ) [NeZero c] :
    (conductorOrder K c).discr = NumberField.discr K * (c : ℤ) ^ 2 := by
  classical
  obtain ⟨b, hb⟩ := (Module.Free.isUnimodular_one (R := ℤ) (A := 𝓞 K)).exists_basis_zero_eq
    ((RingOfIntegers.rank K).trans hK)
  let m : 𝓞 K →ₗ[ℤ] ZMod c := (Algebra.linearMap ℤ (ZMod c)).comp (b.coord 1)
  have hm (x : 𝓞 K) : m x = ((b.repr x 1 : ℤ) : ZMod c) := rfl
  have hsurj : Function.Surjective m := by
    intro t
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective t
    refine ⟨z • b 1, ?_⟩
    rw [hm, map_smul, Finsupp.smul_apply, b.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  have hker : Subalgebra.toSubmodule (conductorOrder K c).toRingOfIntegers = LinearMap.ker m := by
    ext x
    change x ∈ (conductorOrder K c).toRingOfIntegers ↔ m x = 0
    rw [(conductorOrder K c).mem_toRingOfIntegers, hm, ZMod.intCast_zmod_eq_zero_iff_dvd]
    change (∃ a : ℤ, ∃ y : 𝓞 K, (x : K) = (a : K) + (c : K) * (y : K)) ↔
      (c : ℤ) ∣ b.repr x 1
    constructor
    · rintro ⟨a, y, he⟩
      have hx : x = a • b 0 + (c : ℤ) • y := by
        apply RingOfIntegers.coe_injective
        simpa [hb, zsmul_eq_mul] using he
      refine ⟨b.repr y 1, ?_⟩
      rw [hx, map_add, map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
        Finsupp.smul_apply, b.repr_self, Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      simp
    · rintro ⟨z, hz⟩
      refine ⟨b.repr x 0, z • b 1, ?_⟩
      have hx := b.sum_repr x
      rw [Fin.sum_univ_two, hz, mul_smul, hb] at hx
      simpa [zsmul_eq_mul, mul_assoc] using congrArg ((↑) : 𝓞 K → K) hx.symm
  have hi : (conductorOrder K c).index = c := by
    rw [NumberFieldOrder.index_def, hker,
      Nat.card_congr (m.quotKerEquivOfSurjective hsurj).toEquiv, Nat.card_zmod]
  rw [NumberFieldOrder.discr_eq_index_sq_mul, hi, mul_comm]

/-- The companion's selected point lies over the ring class field of the
order of conductor `|h|`, by the same fixed modular morphism. -/
theorem ring_values {ℓ : ℕ} (P : Prints) (hℓ : 0 < ℓ)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2} {Lat : PeriodPair} {κ : ℂ}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    (hLat : IsLatticeOf (Ecurve ℓ) Lat)
    (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ) (hr : ∃ c : ℚ, (c : ℂ) = κ)
    (hCM : letI : NeZero (newformLevel (Ecurve ℓ)) := ⟨(Gz34Instance.curve_form P hℓ).1.ne'⟩
           CMFieldOfDefinition (X0Branch.model (newformLevel (Ecurve ℓ)))) {s : ℤ} :
    ∀ h k (hp : Prepared (Ecurve ℓ) s h) (hk : Companion (Ecurve ℓ) Lat s h k),
      Gz34Instance.RingParamValue (Ecurve ℓ) f Lat κ (Gz34Instance.curve_form P hℓ).1 hp hk := by
  let _ := Gz34Instance.curve_elliptic hℓ
  have hN := (Gz34Instance.curve_form P hℓ).1
  let _ : NeZero (newformLevel (Ecurve ℓ)) := ⟨hN.ne'⟩
  intro h k hp hk
  let _ : Fact (¬ IsSquare (k : ℚ)) :=
    ⟨Qsqrt.not_isSquare_of_squarefree hk.2.2.1 (ne_of_lt (hk.1.trans zero_lt_one))⟩
  let _ : NeZero h.natAbs := ⟨Int.natAbs_ne_zero.mpr hp.1.ne'⟩
  let K := Qsqrt k
  have hdisc := StageSelector.qsqrt_discr hk.1 hk.2.2.1 hk.2.1
  have hO : (conductorOrder K h.natAbs).discr = k * (h.natAbs : ℤ) ^ 2 :=
    (conductorOrder_discr Qsqrt.finrank _).trans (congrArg (· * (h.natAbs : ℤ) ^ 2) hdisc)
  obtain ⟨hNc, hloc⟩ := Gz34Instance.companion_formConditions hp hk
  have hcop : IsCoprime (k * (h.natAbs : ℤ) ^ 2) (newformLevel (Ecurve ℓ) : ℤ) := by
    have hkN : IsCoprime k (newformLevel (Ecurve ℓ) : ℤ) := by
      apply Int.isCoprime_iff_gcd_eq_one.mpr
      change k.natAbs.Coprime (newformLevel (Ecurve ℓ))
      exact Nat.coprime_of_dvd fun p hp hpk hpN =>
        (hloc p hp (dvd_mul_of_dvd_right hpN 2)).1 (Int.natCast_dvd.mpr hpk)
    have hcN : IsCoprime (h.natAbs : ℤ) (newformLevel (Ecurve ℓ) : ℤ) := by
      apply Int.isCoprime_iff_gcd_eq_one.mpr
      change h.natAbs.Coprime (newformLevel (Ecurve ℓ))
      exact hNc.symm
    exact hkN.mul_left (hcN.pow_left)
  exact value_of_cmFieldOfDefinition hCM (algebraicParametrizationAtScale f hf hLat hκ hr)
    Qsqrt.finrank (Qsqrt.isTotallyComplex hk.1) (conductorOrder K h.natAbs)
    hO (mul_neg_of_neg_of_pos hk.1 (pow_pos (by exact_mod_cast NeZero.pos h.natAbs) 2)) hcop
    (Gz34Instance.companionForm hN hp hk).property

#print axioms conductorOrder_discr
#print axioms ring_values

end ZInQ.Manuscript.RC.ParamJoin
