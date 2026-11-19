import ZInQKernel.Contrib.RC53Assist.TateCurve.InertiaRoots

/-!
# The determinant on inertia from the printed Weil-pairing equivariance

The only printed input here is Galois equivariance of the Weil pairing,
Silverman, *The Arithmetic of Elliptic Curves*, second edition, III.8.1(d).
The manuscript bibitem is `silverman`. The page has not been checked.

Prime-to-`p` roots of unity are fixed by inertia by the proved reduction
argument. Alternating bilinearity and nondegeneracy of the pairing, already
proved for elliptic-curve torsion, then give determinant one on inertia.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open IsLocalRing TauCeti TauCeti.Isogeny
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion
open ZInQ.Contrib.RC53Assist.GlobalTrace
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
open scoped WithZero

/-- **PROVED**: a place above `p` has `p = 0` in its residue field.
Locator: `Arithmetic.LiesOver` and the residue-field kernel. -/
theorem residue_prime_eq_zero {p : ℕ} (D : LocalArithmeticFrobenius p) :
    (p : ResidueField D.place) = 0 := by
  rw [← map_natCast (residue D.place), residue_eq_zero_iff]
  exact (D.place.coe_mem_nonunits_iff).mp D.liesOver

/-- **PROVED**: `ℓ^n` is invertible in the residue field at `p ≠ ℓ`.
Locator: the integer Bezout identity for coprime primes. -/
theorem residue_other_prime_power_ne_zero {p : ℕ} (hp : p.Prime)
    (D : LocalArithmeticFrobenius p) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hpℓ : p ≠ ℓ) (n : ℕ) : ((ℓ ^ n : ℕ) : ResidueField D.place) ≠ 0 := by
  have hcop : p.Coprime (ℓ ^ n) := ((Nat.coprime_primes hp hℓ).mpr hpℓ).pow_right n
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have h : (a : ResidueField D.place) * (p : ResidueField D.place) +
      (b : ResidueField D.place) * ((ℓ ^ n : ℕ) : ResidueField D.place) = 1 := by
    have hc := congrArg (fun z : ℤ => (z : ResidueField D.place)) hab
    push_cast at hc
    simpa only [Nat.cast_pow] using hc
  rw [residue_prime_eq_zero D, mul_zero, zero_add] at h
  intro hz
  rw [hz, mul_zero] at h
  exact zero_ne_one h

/-- **PROVED**: the global inertia subgroup fixes every `ℓ^n`-th root of
unity for `p ≠ ℓ`. Locator: `inertia_fixes_torsion_unit`. -/
theorem global_inertia_fixes_unity {p : ℕ} (hp : p.Prime)
    (D : LocalArithmeticFrobenius p) (ℓ : ℕ) (hℓ : ℓ.Prime) (hpℓ : p ≠ ℓ)
    (n : ℕ) (x : GlueC10.Qbarˣ) (hx : x ^ (ℓ ^ n) = 1)
    (i : GlueC10.GQ) (hi : i ∈ inertiaAt D) :
    Units.map i.toAlgHom.toMonoidHom x = x := by
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hi
  apply Units.ext
  exact inertia_fixes_torsion_unit D.place (ℓ ^ n) (pow_ne_zero n hℓ.ne_zero)
    (by simpa only [Nat.cast_pow] using residue_other_prime_power_ne_zero hp D ℓ hℓ hpℓ n)
    x hx ⟨s, hs⟩

/-- **DEFINITION**: the value of the finite-level Weil pairing as a field
unit. Locator: the proved divisor construction of Silverman III.8.1(a)-(c). -/
def levelWeilUnit (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime]
    (n : ℕ) (P Q : TateModuleLevel ℓ (E.baseChange GlueC10.Qbar).toAffine.Point n) :
    GlueC10.Qbarˣ := by
  classical
  letI : NeZero (ℓ ^ n) := ⟨pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero⟩
  have hN : ((ℓ ^ n : ℕ) : GlueC10.Qbar) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero)
  exact (Additive.toMul (weilPairing (E.baseChange GlueC10.Qbar) (ℓ ^ n) hN P Q)).val

/-- **PROVED**: a Weil-pairing value is an `ℓ^n`-th root of unity.
Locator: the codomain of `weilPairing`. -/
theorem levelWeilUnit_pow (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    (P Q : TateModuleLevel ℓ (E.baseChange GlueC10.Qbar).toAffine.Point n) :
    levelWeilUnit E ℓ n P Q ^ (ℓ ^ n) = 1 := by
  classical
  letI : NeZero (ℓ ^ n) := ⟨pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero⟩
  exact (Additive.toMul (weilPairing (E.baseChange GlueC10.Qbar) (ℓ ^ n)
    (Nat.cast_ne_zero.mpr (pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero)) P Q)).property

/-- **DEFINITION (proved in `AdditiveOneInput.lean`)**: Galois equivariance of the Weil pairing:
`e_N(σP,σQ) = σ(e_N(P,Q))`; `silvermanIII81GaloisWeilPairingPrint_proved` derives it from the
vendored library. Locator: Silverman, *The Arithmetic of Elliptic
Curves*, second edition, III.8.1 (the property letter is not checked), manuscript bibitem
`silverman`.
Only `N = ℓ^n` and `E/ℚ` are used. Page not checked; this mathematical
transcription is not claimed to be a checked verbatim quotation.
This is a proposition, not an axiom. -/
def SilvermanIII81GaloisWeilPairingPrint : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime]
    (n : ℕ) (σ : GlueC10.GQ)
    (P Q : TateModuleLevel ℓ (E.baseChange GlueC10.Qbar).toAffine.Point n),
    levelWeilUnit E ℓ n
        (TateModule.levelMap (WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom) n P)
        (TateModule.levelMap (WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom) n Q) =
      Units.map σ.toAlgHom.toMonoidHom (levelWeilUnit E ℓ n P Q)

/-- **PROVED FROM THE PRINT**: the determinant of the actual integral Tate
representation is one on inertia away from `ℓ`. No determinant or
coinvariant conclusion is an input. Locator: the printed pairing
equivariance, `global_inertia_fixes_unity`, and the proved determinant
identity for an alternating nondegenerate pairing. -/
theorem integral_tate_det_inertia
    (hW : SilvermanIII81GaloisWeilPairingPrint)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime]
    (p : ℕ) (hp : p.Prime) (hpℓ : p ≠ ℓ) (D : LocalArithmeticFrobenius p)
    (i : GlueC10.GQ) (hi : i ∈ inertiaAt D) :
    LinearMap.det (integralTateRep E ℓ i) = 1 := by
  classical
  have hℓ : (ℓ : GlueC10.Qbar) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  change LinearMap.det (TateModule.mapLinearMap
    (WeierstrassCurve.Affine.Point.map (W' := E) i.toAlgHom)) = (1 : ℤ_[ℓ])
  apply ZInQ.Contrib.RC53Assist.DetDegree.det_tate_eq_of_weilPairing_compatibility
    (E.baseChange GlueC10.Qbar) ℓ hℓ _ 1
  intro n P Q
  rw [one_smul]
  have hu := (hW E ℓ n i P Q).trans
    (global_inertia_fixes_unity hp D ℓ (Fact.out : ℓ.Prime) hpℓ n
      (levelWeilUnit E ℓ n P Q) (levelWeilUnit_pow E ℓ n P Q) i hi)
  apply congrArg Additive.ofMul
  exact Subtype.ext hu

/-- **PROVED FROM THE PRINT**: rationalization preserves determinant one
on inertia. Locator: `LinearMap.det_baseChange`. -/
theorem rational_tate_det_inertia
    (hW : SilvermanIII81GaloisWeilPairingPrint)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime]
    (p : ℕ) (hp : p.Prime) (hpℓ : p ≠ ℓ) (D : LocalArithmeticFrobenius p)
    (i : GlueC10.GQ) (hi : i ∈ inertiaAt D) :
    LinearMap.det (rationalTateRep E ℓ i) = 1 := by
  have : Module.Free ℤ_[ℓ] (integralTate E ℓ) := Module.Free.of_basis (integralTateBasis E ℓ)
  have : Module.Finite ℤ_[ℓ] (integralTate E ℓ) := Module.Finite.of_basis (integralTateBasis E ℓ)
  rw [rationalTateRep, Representation.baseChange_apply, LinearMap.det_baseChange,
    integral_tate_det_inertia hW E ℓ p hp hpℓ D i hi, map_one]

/-- **PROVED**: local inertia fixes `ℓ^n`-th roots of unity away from
`p`. The prime-field map into the residue field is the proved map from the
local valuation extension. Locator: `inertia_fixes_torsion_unit`. -/
theorem local_inertia_fixes_unity (p : ℕ) (hp : p.Prime) (ℓ : ℕ) [Fact ℓ.Prime]
    (hpℓ : p ≠ ℓ) (Γ : Type) [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) Γ)
    (hw : (w.comap (algebraMap ((primeIdealQ p hp).adicCompletion ℚ)
      (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)))).IsEquiv
      (Valued.v : Valuation ((primeIdealQ p hp).adicCompletion ℚ) ℤᵐ⁰))
    (n : ℕ) (x : (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))ˣ)
    (hx : x ^ (ℓ ^ n) = 1) (σ : LocalGaloisQ p hp) (hσ : σ ∈ localInertia w) :
    Units.map σ.toAlgHom.toMonoidHom x = x := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hz : ((ℓ ^ n : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    have h : p ∣ ℓ ^ n := (CharP.cast_eq_zero_iff (ZMod p) p _).mp hzero
    have hdiv := hp.dvd_of_dvd_pow h
    rcases (Nat.dvd_prime (Fact.out : ℓ.Prime)).mp hdiv with h1 | hEq
    · exact hp.ne_one h1
    · exact hpℓ hEq
  let f := ZInQ.Contrib.RC53Assist.TateReduction.primeFieldHom p hp w hw
  have hk : ((ℓ ^ n : ℕ) : ResidueField w.valuationSubring) ≠ 0 := by
    simpa only [map_natCast] using (map_ne_zero_iff f f.injective).mpr hz
  obtain ⟨i, hi, rfl⟩ := Subgroup.mem_map.mp hσ
  apply Units.ext
  exact inertia_fixes_torsion_unit w.valuationSubring (ℓ ^ n)
    (pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero) hk x hx ⟨i, hi⟩

end ZInQ.Contrib.RC53Assist.TateCurve
