import ZInQKernel.Contrib.RC53Assist.TateCurve.KummerUniformization

/-!
# The Galois columns in the Kummer basis

The second coordinate of a Tate-module point can be read by taking powers
of its multiplicative representatives. This proves the cyclotomic and Kummer
columns from pointwise equivariance of a uniformization, without assuming a
Tate-module representation formula.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, Appendix C, §14,
read with elementary Kummer theory. Pages have not been checked.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open TauCeti Module

section Coordinates

variable {F P : Type*} [Field F] [AddCommGroup P] {q : Fˣ}
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable (U : MultiplicativeUniformization (P := P) q) (S : KummerRoots q ℓ)
variable (hq : Function.Injective fun m : ℤ => q ^ m)
variable (hcard : ∀ n, Nat.card (TateModuleLevel ℓ P n) = (ℓ ^ n) ^ 2)

/-- **PROVED**: projection of a point expressed in the Kummer basis.
Locator: `TateModule.proj_smul` and the two constructed basis vectors. -/
theorem kummer_coordinate_projection (t : TateModule ℓ P) (n : ℕ) :
    (TateModule.proj n t : P) = U.map (Additive.ofMul
      (S.unity n ^ (PadicInt.toZModPow n ((kummerTateBasis U S hq hcard).repr t 0)).val *
        S.root n ^ (PadicInt.toZModPow n ((kummerTateBasis U S hq hcard).repr t 1)).val)) := by
  classical
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let b := kummerTateBasis U S hq hcard
  have hdec : t = b.repr t 0 • b 0 + b.repr t 1 • b 1 := by
    conv_lhs => rw [← b.sum_repr t]
    rw [Fin.sum_univ_two]
  have hproj := congrArg (fun x : TateModule ℓ P => (TateModule.proj n x : P)) hdec
  simpa only [map_add, TateModule.proj_smul, AddSubgroup.coe_add,
    TateModule.coe_zmod_smul, b, kummerTateBasis_zero, kummerTateBasis_one,
    unityTate, rootTate, TateModule.proj_mk, unityLevel, rootLevel,
    ofMul_mul, ofMul_pow, map_add, map_nsmul] using hproj

/-- **PROVED**: a multiplicative representative with `N`-th power `q^k`
has second Kummer coordinate congruent to `k` modulo `N`.
Locator: the exact uniformization kernel and the infinite order of `q`. -/
theorem kummer_second_coordinate_mod (t : TateModule ℓ P) (n : ℕ) (z : Fˣ) (k : ℤ)
    (hz : z ^ (ℓ ^ n) = q ^ k)
    (ht : (TateModule.proj n t : P) = U.map (Additive.ofMul z)) :
    PadicInt.toZModPow n ((kummerTateBasis U S hq hcard).repr t 1) =
      (k : ZMod (ℓ ^ n)) := by
  classical
  let a := (PadicInt.toZModPow n ((kummerTateBasis U S hq hcard).repr t 0)).val
  let d := (PadicInt.toZModPow n ((kummerTateBasis U S hq hcard).repr t 1)).val
  have hmap : U.map (Additive.ofMul (S.unity n ^ a * S.root n ^ d)) =
      U.map (Additive.ofMul z) := (kummer_coordinate_projection U S hq hcard t n).symm.trans ht
  have hker : U.map (Additive.ofMul ((S.unity n ^ a * S.root n ^ d) / z)) = 0 := by
    change U.map (Additive.ofMul (S.unity n ^ a * S.root n ^ d) - Additive.ofMul z) = 0
    rw [map_sub, hmap, sub_self]
  obtain ⟨m, hm⟩ := (U.kernel _).mp hker
  have hp := congrArg (fun x : Fˣ => x ^ (ℓ ^ n)) hm
  have hpowζ : (S.unity n ^ a) ^ (ℓ ^ n) = 1 := by
    rw [pow_right_comm, (S.primitive n).pow_eq_one, one_pow]
  have hpowr : (S.root n ^ d) ^ (ℓ ^ n) = q ^ (d : ℤ) := by
    rw [pow_right_comm, S.root_power, zpow_natCast]
  rw [div_pow, mul_pow, hpowζ, hpowr, one_mul, hz,
    power_zpower_commute, div_eq_mul_inv, ← zpow_sub] at hp
  have hd : (ℓ ^ n : ℤ) ∣ (d : ℤ) - k := by
    refine ⟨m, ?_⟩
    apply hq
    simpa only [← zpow_natCast, ← zpow_mul, Nat.cast_pow] using hp
  have hc : (d : ZMod (ℓ ^ n)) = (k : ZMod (ℓ ^ n)) := by
    apply sub_eq_zero.mp
    rw [← Int.cast_natCast d, ← Int.cast_sub]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
  rw [← ZMod.natCast_zmod_val
    (PadicInt.toZModPow n ((kummerTateBasis U S hq hcard).repr t 1))]
  exact hc

/-- **PROVED**: powers at every level determine the second `ℤ_ℓ`
coordinate. Locator: `PadicInt.ext_of_toZModPow`. -/
theorem kummer_second_coordinate (t : TateModule ℓ P) (z : ℕ → Fˣ) (k : ℤ)
    (hz : ∀ n, z n ^ (ℓ ^ n) = q ^ k)
    (ht : ∀ n, (TateModule.proj n t : P) = U.map (Additive.ofMul (z n))) :
    (kummerTateBasis U S hq hcard).repr t 1 = (k : ℤ_[ℓ]) := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  simpa only [map_intCast] using
    kummer_second_coordinate_mod U S hq hcard t n (z n) k (hz n) (ht n)

end Coordinates

section GaloisColumns

variable {F P G : Type*} [Field F] [AddCommGroup P] [Group G] {q : Fˣ}
variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **PROVED**: a pointwise signed Galois uniformization gives the two
Tate-module columns. The basis is constructed from roots; neither column is
an input. The sign is an integer with square one, as for a quadratic twist.
Locator: `kummer_second_coordinate` and the definition of the actual Tate
module by its projections. -/
theorem signed_kummer_columns
    (U : MultiplicativeUniformization (P := P) q) (S : KummerRoots q ℓ)
    (hq : Function.Injective fun m : ℤ => q ^ m)
    (hcard : ∀ n, Nat.card (TateModuleLevel ℓ P n) = (ℓ ^ n) ^ 2)
    (ρ : Representation ℤ_[ℓ] G (TateModule ℓ P))
    (pointAct : G → P →+ P) (unitAct : G → Fˣ →* Fˣ)
    (ε : G → ℤ) (hε : ∀ g, ε g * ε g = 1)
    (hqfix : ∀ g, unitAct g q = q)
    (hproj : ∀ g t n, (TateModule.proj n (ρ g t) : P) =
      pointAct g (TateModule.proj n t : P))
    (hU : ∀ g x, pointAct g (U.map (Additive.ofMul x)) =
      ε g • U.map (Additive.ofMul (unitAct g x))) :
    ∃ χ κ : G → ℤ_[ℓ],
      (∀ g, ρ g (kummerTateBasis U S hq hcard 0) =
        ((ε g : ℤ_[ℓ]) * χ g) • kummerTateBasis U S hq hcard 0) ∧
      (∀ g, ρ g (kummerTateBasis U S hq hcard 1) =
        (ε g : ℤ_[ℓ]) • (kummerTateBasis U S hq hcard 1 +
          κ g • kummerTateBasis U S hq hcard 0)) := by
  classical
  let b := kummerTateBasis U S hq hcard
  let χ := fun g => (ε g : ℤ_[ℓ]) * b.repr (ρ g (b 0)) 0
  let κ := fun g => (ε g : ℤ_[ℓ]) * b.repr (ρ g (b 1)) 0
  have hsign : ∀ g, (ε g : ℤ_[ℓ]) * (ε g : ℤ_[ℓ]) = 1 := by
    intro g
    exact_mod_cast hε g
  have hzero : ∀ g, b.repr (ρ g (b 0)) 1 = 0 := by
    intro g
    apply kummer_second_coordinate U S hq hcard _
      (fun n => unitAct g (S.unity n) ^ ε g) 0
    · intro n
      rw [power_zpower_commute, ← map_pow, (S.primitive n).pow_eq_one,
        map_one, one_zpow, zpow_zero]
    · intro n
      rw [hproj, kummerTateBasis_zero]
      change pointAct g (U.map (Additive.ofMul (S.unity n))) = _
      rw [hU, ofMul_zpow, map_zsmul]
  have hone : ∀ g, b.repr (ρ g (b 1)) 1 = (ε g : ℤ_[ℓ]) := by
    intro g
    apply kummer_second_coordinate U S hq hcard _
      (fun n => unitAct g (S.root n) ^ ε g) (ε g)
    · intro n
      rw [power_zpower_commute, ← map_pow, S.root_power, hqfix]
    · intro n
      rw [hproj, kummerTateBasis_one]
      change pointAct g (U.map (Additive.ofMul (S.root n))) = _
      rw [hU, ofMul_zpow, map_zsmul]
  refine ⟨χ, κ, ?_, ?_⟩
  · intro g
    have hdec := (b.sum_repr (ρ g (b 0))).symm
    rw [Fin.sum_univ_two, hzero, zero_smul, add_zero] at hdec
    change ρ g (b 0) = ((ε g : ℤ_[ℓ]) * χ g) • b 0
    rw [hdec]
    dsimp [χ]
    rw [← mul_assoc, hsign, one_mul]
  · intro g
    have hdec := (b.sum_repr (ρ g (b 1))).symm
    rw [Fin.sum_univ_two, hone] at hdec
    change ρ g (b 1) = (ε g : ℤ_[ℓ]) • (b 1 + κ g • b 0)
    rw [hdec]
    dsimp [κ]
    rw [smul_add, smul_smul, ← mul_assoc, hsign, one_mul, add_comm]

end GaloisColumns

end ZInQ.Contrib.RC53Assist.TateCurve
