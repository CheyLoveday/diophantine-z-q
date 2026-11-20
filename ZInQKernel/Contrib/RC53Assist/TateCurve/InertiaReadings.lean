import ZInQKernel.Contrib.RC53Assist.TateCurve.KummerAction

/-!
# The sign, cyclotomic character, and Kummer inertia readings

Unipotence forces the quotient character of a two-dimensional Tate-shaped
representation to be trivial. Fixing the compatible roots of unity forces
its cyclotomic character to be one. Moving one compatible root of the
parameter forces its Kummer coefficient to be nonzero.

The statements about roots are field-theoretic inputs to these elementary
proofs, not Tate-module or coinvariant assertions.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open Module TauCeti

section UnipotentSign

variable {R G V : Type*} [CommRing R] [IsDomain R] [Group G]
variable [AddCommGroup V] [Module R V]

/-- **PROVED**: a unipotent upper-triangular action has quotient character
one. Locator: the second coordinate functional in the displayed basis. -/
theorem tate_sign_eq_one_of_unipotent (ρ : Representation R G V)
    (b : Basis (Fin 2) R V) (ε χ κ : G → R) (g : G)
    (h0 : ρ g (b 0) = (ε g * χ g) • b 0)
    (h1 : ρ g (b 1) = ε g • (b 1 + κ g • b 0))
    (huni : IsNilpotent (ρ g - (1 : Module.End R V))) : ε g = 1 := by
  classical
  let φ : V →ₗ[R] R := b.coord 1
  have hφ : ∀ v, φ (ρ g v) = ε g * φ v := by
    intro v
    have hdec : v = b.repr v 0 • b 0 + b.repr v 1 • b 1 := by
      conv_lhs => rw [← b.sum_repr v]
      rw [Fin.sum_univ_two]
    rw [hdec, map_add, map_smul, map_smul, h0, h1]
    simp [φ, map_add, map_smul, Basis.coord_apply]
    ring
  have hδ : ∀ v, φ ((ρ g - 1) v) = (ε g - 1) * φ v := by
    intro v
    rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, hφ]
    ring
  have hp : ∀ n v, φ (((ρ g - 1) ^ n) v) = (ε g - 1) ^ n * φ v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, ih, hδ, pow_succ, mul_assoc]
  obtain ⟨n, hn⟩ := huni
  have hv := hp n (b 1)
  rw [hn, LinearMap.zero_apply, map_zero] at hv
  have hc : (ε g - 1) ^ n = 0 := by
    simpa [φ, Basis.coord_apply] using hv.symm
  have hnil : IsNilpotent (ε g - 1) := ⟨n, hc⟩
  exact sub_eq_zero.mp (isNilpotent_iff_eq_zero.mp hnil)

end UnipotentSign

section TorsionKernel

variable {F P : Type*} [Field F] [AddCommGroup P] {q : Fˣ}

/-- **PROVED**: the uniformization is injective on pairs whose quotient
is torsion. An infinite cyclic kernel has no nonidentity torsion element.
Locator: the exact uniformization kernel and injectivity of `m ↦ q^m`. -/
theorem uniformization_torsion_injective (U : MultiplicativeUniformization (P := P) q)
    (hq : Function.Injective fun m : ℤ => q ^ m) (N : ℕ) (hN : N ≠ 0)
    (x y : Fˣ) (hpow : x ^ N = y ^ N)
    (hmap : U.map (Additive.ofMul x) = U.map (Additive.ofMul y)) : x = y := by
  have hker : U.map (Additive.ofMul (x / y)) = 0 := by
    change U.map (Additive.ofMul x - Additive.ofMul y) = 0
    rw [map_sub, hmap, sub_self]
  obtain ⟨m, hm⟩ := (U.kernel _).mp hker
  have hp := congrArg (fun z : Fˣ => z ^ N) hm
  rw [div_pow, hpow, div_self', power_zpower_commute] at hp
  have hm0 : (N : ℤ) * m = 0 := by
    apply hq
    simpa only [← zpow_natCast, ← zpow_mul, zpow_zero] using hp.symm
  have hm' : m = 0 := (mul_eq_zero.mp hm0).resolve_left (Int.natCast_ne_zero.mpr hN)
  rw [hm', zpow_zero] at hm
  exact div_eq_one.mp hm

end TorsionKernel

section InertiaReadings

variable {F P G : Type*} [Field F] [AddCommGroup P] [Group G] {q : Fˣ}
variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **PROVED**: fixing the roots of unity makes the cyclotomic coefficient
one, provided the twist sign is one. Locator: projection of `unityTate`.
No cyclotomic-character inertia assertion is supplied as an input. -/
theorem kummer_chi_eq_one_of_unity_fixed
    (U : MultiplicativeUniformization (P := P) q) (S : KummerRoots q ℓ)
    (hq : Function.Injective fun m : ℤ => q ^ m)
    (hcard : ∀ n, Nat.card (TateModuleLevel ℓ P n) = (ℓ ^ n) ^ 2)
    (ρ : Representation ℤ_[ℓ] G (TateModule ℓ P))
    (pointAct : G → P →+ P) (unitAct : G → Fˣ →* Fˣ)
    (ε : G → ℤ) (χ : G → ℤ_[ℓ]) (i : G) (hε : ε i = 1)
    (h0 : ρ i (kummerTateBasis U S hq hcard 0) =
      ((ε i : ℤ_[ℓ]) * χ i) • kummerTateBasis U S hq hcard 0)
    (hproj : ∀ t n, (TateModule.proj n (ρ i t) : P) =
      pointAct i (TateModule.proj n t : P))
    (hU : ∀ x, pointAct i (U.map (Additive.ofMul x)) =
      ε i • U.map (Additive.ofMul (unitAct i x)))
    (hfix : ∀ n, unitAct i (S.unity n) = S.unity n) : χ i = 1 := by
  classical
  have ht : ρ i (unityTate U S) = unityTate U S := by
    apply TateModule.ext
    intro n
    apply Subtype.ext
    rw [hproj]
    change pointAct i (U.map (Additive.ofMul (S.unity n))) = _
    rw [hU, hε, one_zsmul, hfix]
    rfl
  rw [hε, Int.cast_one, one_mul, kummerTateBasis_zero] at h0
  have h := congrArg (fun v => (kummerTateBasis U S hq hcard).repr v 0)
    (h0.symm.trans ht)
  rw [← kummerTateBasis_zero U S hq hcard] at h
  simpa using h

/-- **PROVED**: if inertia moves a compatible root of `q`, then the
Kummer coefficient is nonzero on inertia. Locator: the projection of
`rootTate` and `uniformization_torsion_injective`. -/
theorem kummer_kappa_ne_zero_of_root_moved
    (U : MultiplicativeUniformization (P := P) q) (S : KummerRoots q ℓ)
    (hq : Function.Injective fun m : ℤ => q ^ m)
    (hcard : ∀ n, Nat.card (TateModuleLevel ℓ P n) = (ℓ ^ n) ^ 2)
    (ρ : Representation ℤ_[ℓ] G (TateModule ℓ P))
    (pointAct : G → P →+ P) (unitAct : G → Fˣ →* Fˣ)
    (ε : G → ℤ) (κ : G → ℤ_[ℓ]) (i : G) (hε : ε i = 1)
    (h1 : ρ i (kummerTateBasis U S hq hcard 1) =
      (ε i : ℤ_[ℓ]) • (kummerTateBasis U S hq hcard 1 +
        κ i • kummerTateBasis U S hq hcard 0))
    (hproj : ∀ t n, (TateModule.proj n (ρ i t) : P) =
      pointAct i (TateModule.proj n t : P))
    (hU : ∀ x, pointAct i (U.map (Additive.ofMul x)) =
      ε i • U.map (Additive.ofMul (unitAct i x)))
    (hqfix : unitAct i q = q) (n : ℕ)
    (hmove : unitAct i (S.root n) ≠ S.root n) : κ i ≠ 0 := by
  intro hk
  rw [hε, Int.cast_one, one_smul, hk, zero_smul, add_zero,
    kummerTateBasis_one] at h1
  have hp := congrArg (fun t : TateModule ℓ P => (TateModule.proj n t : P)) h1
  rw [hproj] at hp
  change pointAct i (U.map (Additive.ofMul (S.root n))) = _ at hp
  rw [hU, hε, one_zsmul] at hp
  apply hmove
  apply uniformization_torsion_injective U hq (ℓ ^ n)
    (pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero) _ _ _ hp
  rw [← map_pow, S.root_power, hqfix]

end InertiaReadings

end ZInQ.Contrib.RC53Assist.TateCurve
