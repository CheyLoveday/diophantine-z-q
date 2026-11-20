import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Decomp
import ZInQKernel.Contrib.OneProof.RC.Gz34Instance.Forms
import Mathlib.LinearAlgebra.Unimodular

/-! The discriminant and Heegner forms of the orders at tex 2839–2844
and 2915–2917. The explicit arithmetic is on-the-spot (c). -/

noncomputable section

open NumberField TauCeti.GlobalNumberFields ZInQ.Contrib.CloudB3RC53.CST
  ZInQ.Contrib.CloudB3RC53.GenusOdd ZInQ.Contrib.CloudB3RC53.GenusOdd.Decomp

namespace ZInQ.Manuscript.RC.HeegnerAnchor

/-- In a quadratic field, reducing the second coordinate of a basis `(1, ω)`
modulo the conductor has kernel `ℤ + c 𝓞 K`. -/
theorem conductorOrder_discr {K : Type} [Field K] [NumberField K]
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

/-- A split prime has a degree-one prime above it and is prime to the discriminant. -/
private theorem splitPrime {K : Type} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) (hs : SplitsIn K p) :
    (∃ P ∈ primesAbove K p, Ideal.absNorm P.asIdeal = p) ∧ ¬ (p : ℤ) ∣ discr K := by
  obtain ⟨a, b, ha, hb, hab, hprod⟩ := hs
  have hpab : ((p : ℤ) : 𝓞 K) ∈ a * b := by
    rw [← hprod, Int.cast_natCast]
    exact Ideal.mem_span_singleton_self _
  have hpa : ((p : ℤ) : 𝓞 K) ∈ a := Ideal.mul_le_left hpab
  have hpb : ((p : ℤ) : 𝓞 K) ∈ b := Ideal.mul_le_right hpab
  let A : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := ⟨a, ha.isPrime, ne_bot_of_mem hp hpa⟩
  let B : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := ⟨b, hb.isPrime, ne_bot_of_mem hp hpb⟩
  have hA : A ∈ primesAbove K p := hpa
  have hB : B ∈ primesAbove K p := hpb
  have hAB : A ≠ B := fun h => hab (congrArg (fun P => P.asIdeal) h)
  have not_singleton (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
      primesAbove K p ≠ {P} := by
    intro h
    rw [h, Set.mem_singleton_iff] at hA hB
    exact hAB (hA.trans hB.symm)
  rcases primesAbove_cases hK hp with
    ⟨P, Q, -, hset, heP, hfP, heQ, -⟩ | ⟨P, hset, -, -⟩ | ⟨P, hset, -, -⟩
  · have hP : P ∈ primesAbove K p := by rw [hset]; simp
    refine ⟨⟨P, hP, by rw [absNorm_eq_pow hp hP, hfP, pow_one]⟩, ?_⟩
    rw [dvd_discr_iff hp, hset]
    rintro ⟨R, hR, he⟩
    rcases hR with rfl | rfl
    · exact he heP
    · exact he heQ
  · exact (not_singleton P hset).elim
  · exact (not_singleton P hset).elim

/-- The split hypothesis at twice the level supplies both discriminant
coprimality and a primitive form with leading coefficient equal to the level. -/
theorem conductorForm {K : Type} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) {N d : ℕ} (hN : 0 < N)
    (hs : ∀ p : ℕ, p.Prime → p ∣ 2 * N → SplitsIn K p)
    (hcop : Nat.Coprime d (N * (discr K).natAbs)) :
    IsCoprime (discr K * (d : ℤ) ^ 2) (N : ℤ) ∧
      ∃ B C : ℤ, IsHeegnerForm N (discr K * (d : ℤ) ^ 2) N B C := by
  have hodd : Odd (discr K) := by
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    exact (splitPrime hK Nat.prime_two (hs 2 Nat.prime_two (dvd_mul_right 2 N))).2
  have hlocal (p : ℕ) (hp : p.Prime) (hpN : p ∣ 2 * N) : SquareAt p (discr K) := by
    obtain ⟨⟨P, hP, hn⟩, hnd⟩ := splitPrime hK hp (hs p hp hpN)
    have hk := kronecker_eq_one_of_absNorm hK hodd hp hP hn hnd
    rcases kronecker_cases_of_not_dvd (discr_mod_four_of_odd hK hodd) hp hnd with
      ⟨-, h⟩ | h
    · exact h
    · rw [hk] at h
      norm_num at h
  have hdN : d.Coprime N := hcop.coprime_dvd_right (dvd_mul_right N (discr K).natAbs)
  have hD : IsCoprime (discr K) (N : ℤ) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    change (discr K).natAbs.Coprime N
    exact Nat.coprime_of_dvd fun p hp hpD hpN =>
      (hlocal p hp (dvd_mul_of_dvd_right hpN 2)).1 (Int.natCast_dvd.mpr hpD)
  have hd : IsCoprime (d : ℤ) (N : ℤ) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    simpa using hdN
  exact ⟨hD.mul_left hd.pow_left,
    Gz34Instance.exists_ringHeegnerForm hN (squarefree_discr_of_odd hK hodd) hlocal hdN.symm⟩


end ZInQ.Manuscript.RC.HeegnerAnchor
