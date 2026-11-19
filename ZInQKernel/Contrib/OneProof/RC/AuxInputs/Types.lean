import ZInQKernel.Contrib.OneProof.RC.Wiring.AuxFactor3
import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Realize
import ZInQKernel.Contrib.OneProof.RC.AppE.Phase

/-! The fixed even alphabet (tex 2015–2044, 2162–2168), including the full unit
squareclass at two. The modulus uses each odd support prime once. -/

noncomputable section

namespace ZInQ.Manuscript.RC.AuxInputs

open AddressGenuine Symbols ZInQ.Manuscript.RC.Even
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

def conductor (S : Finset ℕ) : ℕ := 8 * ∏ p ∈ S.erase 2, p

theorem conductor_pos {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) : 0 < conductor S := by
  exact Nat.mul_pos (by decide) (Finset.prod_pos fun p hp => (hS p (Finset.mem_of_mem_erase hp)).pos)

theorem eight_dvd_conductor (S : Finset ℕ) : 8 ∣ conductor S := dvd_mul_right _ _

theorem conductor_support {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) (h2 : 2 ∈ S) {p : ℕ} (hp : p.Prime) :
    p ∣ conductor S ↔ p ∈ S := by
  classical
  constructor
  · intro h
    rcases (hp.dvd_mul.mp h) with h8 | hprod
    · have hd : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 from h8)
      rwa [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd]
    · obtain ⟨q, hq, hpd⟩ := (hp.prime.dvd_finsetProd_iff id).mp hprod
      have hqS := Finset.mem_of_mem_erase hq
      rwa [← (Nat.prime_dvd_prime_iff_eq hp (hS q hqS)).mp hpd] at hqS
  · intro hpS
    by_cases h : p = 2
    · subst p
      exact (show (2 : ℕ) ∣ 8 by decide).trans (eight_dvd_conductor S)
    · exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨h, hpS⟩)) _

def evenSign (S : Finset ℕ) : SqClass (conductor S) →+ ZMod 2 :=
  signChar _ ((show (4 : ℕ) ∣ 8 by decide).trans (eight_dvd_conductor S))

def evenTypes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    TypeData (SqClass (conductor S)) (evenSign S) :=
  typeData _ (conductor_pos hS) ((show (4 : ℕ) ∣ 8 by decide).trans (eight_dvd_conductor S))

theorem evenTypes_sign {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {p : ℕ}
    (hp : (evenTypes S hS).Good p) :
    evenSign S ((evenTypes S hS).typ p) = (((p - 1) / 2 : ℕ) : ZMod 2) := by
  rw [(evenTypes S hS).sign p hp.1 hp.2]
  have ho : Odd p := odd_of_coprime_of_two_dvd ((evenTypes S hS).two_dvd) hp.2
  apply congrArg (fun n : ℕ => (n : ZMod 2))
  obtain ⟨k, hk⟩ := ho
  omega

/-- Every quadratic residue character at a divisor of the fixed modulus
reads a coordinate of the same squareclass type. -/
theorem quadratic_character_factors {m n : ℕ} (hmn : n ∣ m)
    (χ : (ZMod n)ˣ →* Multiplicative (ZMod 2)) :
    ∃ c : SqClass m →+ ZMod 2, ∀ u : (ZMod m)ˣ,
      c (sqMk u) = Multiplicative.toAdd (χ (ZMod.unitsMap hmn u)) := by
  let f : (ZMod m)ˣ → ZMod 2 := fun u => Multiplicative.toAdd (χ (ZMod.unitsMap hmn u))
  have hf : ∀ u v, f (u * v) = f u + f v := by
    intro u v
    dsimp only [f]
    rw [map_mul, map_mul]
    rfl
  exact ⟨liftChar f hf, liftChar_sqMk f hf⟩

theorem coprime_conductor {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (h2 : 2 ∈ S) (D : ℕ) :
    D.Coprime (conductor S) ↔ ∀ p ∈ S, ¬ p ∣ D := by
  constructor
  · intro hc p hp hpd
    have hpg := Nat.dvd_gcd hpd ((conductor_support hS h2 (hS p hp)).2 hp)
    rw [hc.gcd_eq_one] at hpg
    exact (hS p hp).not_dvd_one hpg
  · exact coprime_of_support (fun _ hp => (conductor_support hS h2 hp).1)

theorem total_of_good_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (V : Finset ℕ)
    (hV : ∀ p ∈ V, (evenTypes S hS).Good p) :
    (primeConfig V (evenTypes S hS).typ).total =
      sqClassOf (conductor S) ((∏ p ∈ V, p : ℕ) : ℤ) := by
  change (∑ p ∈ V, sqClassOf (conductor S) (p : ℤ)) = _
  rw [Nat.cast_prod]
  exact (RealizeAux.sqClassOf_prod V id (fun p hp => (hV p hp).2)).1.symm

theorem good_primeFactors {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {D : ℕ}
    (hc : D.Coprime (conductor S)) :
    ∀ p ∈ D.primeFactors, (evenTypes S hS).Good p :=
  fun _ hp => ⟨Nat.prime_of_mem_primeFactors hp,
    Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp) hc⟩

/-- The signed source uses positive Fourier indices. Its squareclass filter is exactly
the fixed-support filter of Appendix E, with the sign chosen separately. -/
theorem s0Filter_iff_type {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (h2 : 2 ∈ S)
    {D₀ D : ℕ} (hD₀ : D₀.Coprime (conductor S)) :
    S0Filter S D₀ D ↔ 0 < D ∧ Squarefree D ∧ D.Coprime (conductor S) ∧
      sqClassOf (conductor S) (D : ℤ) = sqClassOf (conductor S) (D₀ : ℤ) := by
  have hsq (hc : D.Coprime (conductor S)) :
      sqClassOf (conductor S) (D : ℤ) = sqClassOf (conductor S) (D₀ : ℤ) ↔
        IsSquare ((D * D₀ : ℕ) : ZMod (conductor S)) := by
    have hu := AddressGenuine.isUnit_natCast_of_coprime hc
    have hu₀ := AddressGenuine.isUnit_natCast_of_coprime hD₀
    have hprod := AddressGenuine.isUnit_natCast_of_coprime (hc.mul_left hD₀)
    rw [show ((D * D₀ : ℕ) : ZMod (conductor S)) =
        (((D * D₀ : ℕ) : ℤ) : ZMod (conductor S)) by simp,
      ← sqClassOf_eq_zero_iff hprod, Nat.cast_mul, sqClassOf_mul hu hu₀]
    constructor
    · intro he
      rw [he, sqClass_add_self]
    · intro hz
      let a := sqClassOf (conductor S) (D : ℤ)
      let b := sqClassOf (conductor S) (D₀ : ℤ)
      change a + b = 0 at hz
      change a = b
      calc
        a = a + 0 := (add_zero a).symm
        _ = a + (b + b) := congrArg (fun x : SqClass (conductor S) => a + x)
          (sqClass_add_self b).symm
        _ = (a + b) + b := (add_assoc a b b).symm
        _ = 0 + b := congrArg (fun x : SqClass (conductor S) => x + b) hz
        _ = b := zero_add b
  constructor
  · rintro ⟨hpos, hsf, hcop, hloc⟩
    have hc := (coprime_conductor hS h2 D).2 hcop
    refine ⟨hpos, hsf, hc, (hsq hc).2 ?_⟩
    exact AppE.isSquare_zmod_of_local (D * D₀) _ (conductor_pos hS).ne' (hc.mul_left hD₀)
      (fun p hp hpd => hloc p ((conductor_support hS h2 hp).1 hpd))
  · rintro ⟨hpos, hsf, hc, ht⟩
    have h := (hsq hc).1 ht
    refine ⟨hpos, hsf, (coprime_conductor hS h2 D).1 hc, fun p hp => ⟨?_, ?_⟩⟩
    · rintro rfl
      let f : ZMod (conductor S) →+* ZMod 8 := ZMod.castHom (eight_dvd_conductor S) _
      have hu : IsUnit ((D * D₀ : ℕ) : ZMod 8) := by
        simpa only [map_natCast] using
          ((ZMod.isUnit_iff_coprime _ _).2 (hc.mul_left hD₀)).map f
      have hs : IsSquare ((D * D₀ : ℕ) : ZMod 8) := by
        simpa only [map_natCast] using h.map f
      obtain ⟨r, hr⟩ := hs
      have hur : IsUnit r := isUnit_of_mul_isUnit_left (hr ▸ hu)
      have key : ∀ x y : ZMod 8, x * y = 1 → x * x = 1 := by decide
      let u := hur.unit
      have hu' : r * (↑u⁻¹ : ZMod 8) = 1 :=
        (congrArg (fun a : ZMod 8 => a * (↑u⁻¹ : ZMod 8)) hur.unit_spec.symm).trans u.mul_inv
      have he := hr.trans (key r (↑u⁻¹) hu')
      have hh := (ZMod.natCast_eq_natCast_iff (D * D₀) 1 8).1
        (he.trans (Nat.cast_one : (1 : ZMod 8) = (1 : ℕ)).symm)
      exact hh
    · intro _
      let f : ZMod (conductor S) →+* ZMod p :=
        ZMod.castHom ((conductor_support hS h2 (hS p hp)).2 hp) _
      simpa only [map_natCast] using h.map f

#print axioms conductor_pos
#print axioms eight_dvd_conductor
#print axioms conductor_support
#print axioms evenTypes_sign
#print axioms quadratic_character_factors
#print axioms coprime_conductor
#print axioms total_of_good_primes
#print axioms good_primeFactors
#print axioms s0Filter_iff_type

end ZInQ.Manuscript.RC.AuxInputs
