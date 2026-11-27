import ZInQKernel.Contrib.OneProof.RC.Rings.LambdaTwo
import ZInQKernel.Contrib.OneProof.RC.Determinant.OCoeff

/-!
# Lane RC20: `𝒪 = \widehat{Λ_{(2)}}` is a DVR with uniformizer `2`; its valuation on `Frac Λ`

Manuscript (`diophantine_zq.tex`, 11/5 version):
* tex 2747–2748, 3728: `𝒪 = \widehat{Λ_{(2)}} = \widehat{ℤ₂[[t]]_{(2)}}`;
* tex 4720–4730: `(5.3)` is formed from copies of `𝒪`, "a nonzero element ... is that power of two times a
  unit" — the property of `𝒪` itself that the outer DVR inherits;
* tex 4830: "the two-adic valuation of `𝒪`, where `t` is a unit";
* tex 4916–4918: "`v₂ u_prim ≥ −C(E,A)`, `u_prim ∈ Λ[1/2]`, where the first valuation is that of `𝒪`";
* tex 5694–5700: "its constant coefficient agrees with `f_0(0)` and has valuation `c` ... Nevertheless
  `v_𝒪(f_x) ≤ c`, so integrality of `d_x = f_x ũ_x` gives `v_𝒪(ũ_x) ≥ −c`".

The genuine `𝒪` is lane RC7's inverse-limit model `Determinant.OO = lim_n (ℤ/2ⁿ)((t))`
(`OModel.lean`: a domain, `2`-adically complete, every nonzero element `2^M` times a unit; `OCoeff.lean`:
Laurent coefficients `coeffZ`). This file proves:

* `irreducible_two_OO`, `instIsDiscreteValuationRingOO`, `maximalIdeal_OO`: `𝒪` is a DVR with uniformizer
  `2` and maximal ideal `(2)`; `instCharZeroOO`; `residueFieldOOEquiv : 𝒪/𝔪 ≃+* 𝔽₂((t))`;
* `vO : AddValuation (Frac 𝒪) (WithTop ℤ)`, the two-adic valuation of `𝒪` (`vO_two`, `vO_t`, `vO_nonneg_iff`);
* the Gauss form `two_pow_dvd_iff_forall_coeffZ`, `le_vO_iff_forall_coeffZ` (`v_𝒪(y) = min_i v₂([tⁱ]y)`),
  `vO_le_valuation_coeffZ` (`v_𝒪(y) ≤ v₂([tⁱ]y)`, tex 5697–5698) and `neg_le_vO_of_mul_mem` (tex 5698–5700);
* `lamTwoToO : Λ_{(2)} →+* 𝒪` (injective, `2 ↦ 2`, local), `iotaO : Frac Λ →+* Frac 𝒪`, and
  `vO_iotaO : v_𝒪 (ι x) = v_{(2)} x`: the valuation of `𝒪` restricted to `Frac Λ` is that of the DVR
  `Λ_{(2)}`;
* `valuationOfO_genuine : Uniform.ValuationOfO vO iotaO` — lane RC16's GLUE `ValuationOfO`, PROVED for the
  genuine `𝒪`; consequently `integral_form_of_valuation_bound_genuine` and
  `exLimitsUniformLowerBound_genuine` (RC16's Proposition `ex:limits-uniform-lower-bound` with no GLUE
  hypothesis left).

Everything here is `PROVED`.
-/

namespace ZInQ.Manuscript.RC.Rings

open ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Determinant

/-! ## `𝒪` is a DVR with uniformizer two -/

/-- **Tex 4726–4729 (PROVED).** `2` is not a unit of `𝒪`: its reduction in `𝒪/2 = 𝔽₂((t))` is `0`. -/
theorem not_isUnit_two_OO : ¬ IsUnit (2 : OO) := by
  intro h
  have h1 := h.map (proj 1)
  have h0 : proj 1 (2 : OO) = 0 :=
    (congrArg (proj 1) (by ring : (2 : OO) = 2 ^ 1 * 1)).trans (proj_two_pow_mul 1 1)
  rw [h0] at h1
  exact not_isUnit_zero h1

/-- **Tex 4726–4729 (PROVED).** `2 ≠ 0` in `𝒪`. -/
theorem two_ne_zero_OO : (2 : OO) ≠ 0 := by
  simpa using two_pow_ne_zero_OO 1

/-- **Tex 4726–4729 (PROVED).** Every nonzero element of `𝒪` is associated to a power of `2`
(RC7's `exists_eq_two_pow_mul_unit`). -/
theorem associated_two_pow_OO {y : OO} (hy : y ≠ 0) : ∃ n : ℕ, Associated ((2 : OO) ^ n) y := by
  obtain ⟨M, u, rfl⟩ := exists_eq_two_pow_mul_unit y hy
  exact ⟨M, associated_mul_unit_right _ _ u.isUnit⟩

/-- **Tex 4729 "uniformizer two" (PROVED).** `2` is irreducible in `𝒪`. -/
theorem irreducible_two_OO : Irreducible (2 : OO) :=
  irreducible_of_forall_associated_pow' two_ne_zero_OO not_isUnit_two_OO
    (fun _ hy => associated_two_pow_OO hy)

/-- **Tex 2747–2748, 4720–4730 (PROVED).** The genuine `𝒪 = \widehat{Λ_{(2)}}` is a discrete valuation
ring. -/
instance instIsDiscreteValuationRingOO : IsDiscreteValuationRing OO :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨2, irreducible_two_OO, fun hy => associated_two_pow_OO hy⟩

/-- **Tex 4729 (PROVED).** The maximal ideal of `𝒪` is `(2)`. -/
theorem maximalIdeal_OO : IsLocalRing.maximalIdeal OO = Ideal.span {2} :=
  irreducible_two_OO.maximalIdeal_eq

/-- **Tex 4729–4730 "characteristic-zero fraction field" (PROVED).** `𝒪` has characteristic zero
(`Λ → 𝒪` is injective and `Λ` has characteristic zero). -/
instance instCharZeroOO : CharZero OO := by
  have : CharZero Lambda := RingHom.charZero (PowerSeries.constantCoeff (R := ℤ_[2]))
  refine ⟨fun m n h => ?_⟩
  have h' : lamToO (m : Lambda) = lamToO (n : Lambda) := by rw [map_natCast, map_natCast]; exact h
  exact Nat.cast_injective (lamToO_injective h')

/-- **Tex 7501 (PROVED).** The residue field of `𝒪` is `𝔽₂((t))` (`𝒪/2 ≅ (ℤ/2)((t))`, RC7's
`quotTwoPowEquiv 1`). -/
noncomputable def residueFieldOOEquiv : IsLocalRing.ResidueField OO ≃+* LaurentSeries (ZMod 2) :=
  (Ideal.quotEquivOfEq (by rw [maximalIdeal_OO, pow_one])).trans (quotTwoPowEquiv 1)

/-! ## The two-adic valuation of `𝒪` -/

/-- **The two-adic valuation `v_𝒪` of `𝒪`** on its fraction field (tex 4830, 4916–4918, 5698–5700;
`PROVED` construction): the valuation of the DVR `𝒪` with uniformizer `2`. -/
noncomputable def vO : AddValuation (FractionRing OO) (WithTop ℤ) :=
  dvrAddVal (R := OO) irreducible_two_OO

/-- **Tex 4729 (PROVED).** `v_𝒪(2) = 1`. -/
theorem vO_two : vO (2 : FractionRing OO) = 1 := by
  have h := dvrAddVal_uniformizer (K := FractionRing OO) irreducible_two_OO
  rwa [map_ofNat] at h

/-- **Tex 4830 "where `t` is a unit" (PROVED).** `v_𝒪(t) = 0`. -/
theorem vO_t : vO (algebraMap OO (FractionRing OO) (lamToO PowerSeries.X)) = 0 := by
  have h := dvrAddVal_unit (K := FractionRing OO) irreducible_two_OO isUnit_t.unit
  rw [IsUnit.unit_spec] at h
  exact h

/-- **Tex 4916–4918, 5698–5700 (PROVED).** The ring of integers of `v_𝒪` is `𝒪`. -/
theorem vO_nonneg_iff (x : FractionRing OO) :
    0 ≤ vO x ↔ x ∈ (algebraMap OO (FractionRing OO)).range :=
  dvrAddVal_nonneg_iff irreducible_two_OO

/-- **Tex 5626–5638, 5694–5700 (PROVED).** `2ᵏ ∣ y` in `𝒪` iff `2ᵏ` divides every Laurent coefficient
`[tⁱ]y ∈ ℤ₂` (RC7's `coeffZ`). -/
theorem two_pow_dvd_iff_forall_coeffZ (k : ℕ) (y : OO) :
    (2 : OO) ^ k ∣ y ↔ ∀ i : ℤ, (2 : ℤ_[2]) ^ k ∣ coeffZ y i := by
  rw [← Ideal.mem_span_singleton, ← proj_eq_zero_iff_mem]
  constructor
  · intro h i
    rw [← coeff_proj_eq_zero_iff, h, HahnSeries.coeff_zero]
  · intro h
    ext i
    rw [HahnSeries.coeff_zero, coeff_proj_eq_zero_iff]
    exact h i

/-- **The Gauss form of `v_𝒪`** (tex 5694–5700; `PROVED`): `k ≤ v_𝒪(y)` iff `2ᵏ` divides every Laurent
coefficient of `y`; i.e. `v_𝒪(y) = min_i v₂([tⁱ]y)`. -/
theorem le_vO_iff_forall_coeffZ (k : ℕ) (y : OO) :
    ((k : ℤ) : WithTop ℤ) ≤ vO (algebraMap OO (FractionRing OO) y) ↔
      ∀ i : ℤ, (2 : ℤ_[2]) ^ k ∣ coeffZ y i := by
  rw [vO, ← pow_dvd_iff_le_dvrAddVal irreducible_two_OO k, two_pow_dvd_iff_forall_coeffZ]

/-- **Tex 5694–5698 (PROVED).** "its constant coefficient ... has valuation `c` ... Nevertheless
`v_𝒪(f_x) ≤ c`": the valuation of `y ∈ 𝒪` is at most the two-adic valuation of any nonzero Laurent
coefficient. -/
theorem vO_le_valuation_coeffZ (y : OO) (i : ℤ) (hi : coeffZ y i ≠ 0) :
    vO (algebraMap OO (FractionRing OO) y) ≤ (((coeffZ y i).valuation : ℕ) : ℤ) := by
  by_contra hlt
  push Not at hlt
  set c := (coeffZ y i).valuation with hc
  have h1 : (((c + 1 : ℕ) : ℤ) : WithTop ℤ) ≤ vO (algebraMap OO (FractionRing OO) y) := by
    induction hv : vO (algebraMap OO (FractionRing OO) y) using WithTop.recTopCoe with
    | top => exact le_top
    | coe m =>
      rw [hv] at hlt
      have : (c : ℤ) < m := by exact_mod_cast hlt
      exact_mod_cast (show ((c + 1 : ℕ) : ℤ) ≤ m by push_cast; omega)
  have h2 := (le_vO_iff_forall_coeffZ (c + 1) y).mp h1 i
  have h3 : coeffZ y i ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ (c + 1)} := by
    rw [Ideal.mem_span_singleton]
    exact_mod_cast h2
  rw [PadicInt.mem_span_pow_iff_le_valuation _ hi] at h3
  omega

/-- **Tex 5698–5700 (PROVED).** "`v_𝒪(f_x) ≤ c`, so integrality of `d_x = f_x ũ_x` gives
`v_𝒪(ũ_x) ≥ −c`": for `f ≠ 0` with `v_𝒪(f) ≤ c` and `f u ∈ 𝒪`, `v_𝒪(u) ≥ −c`. -/
theorem neg_le_vO_of_mul_mem {f u : FractionRing OO} (c : ℤ) (hf0 : f ≠ 0)
    (hfc : vO f ≤ (c : WithTop ℤ)) (hfu : f * u ∈ (algebraMap OO (FractionRing OO)).range) :
    ((-c : ℤ) : WithTop ℤ) ≤ vO u := by
  have h0 : 0 ≤ vO (f * u) := (vO_nonneg_iff _).mpr hfu
  rw [AddValuation.map_mul] at h0
  have hfne : vO f ≠ ⊤ := fun h => hf0 ((dvrAddVal_eq_top_iff irreducible_two_OO).mp h)
  induction hv : vO f using WithTop.recTopCoe with
  | top => exact absurd hv hfne
  | coe a =>
    rw [hv] at hfc h0
    have hac : a ≤ c := by exact_mod_cast hfc
    induction hw : vO u using WithTop.recTopCoe with
    | top => exact le_top
    | coe b =>
      rw [hw] at h0
      have : (0 : ℤ) ≤ a + b := by exact_mod_cast h0
      exact_mod_cast (show -c ≤ b by omega)

/-! ## `Λ_{(2)} → 𝒪` and the comparison of valuations -/

/-- **Tex 2747–2748, 3728 (PROVED construction).** The canonical map `Λ_{(2)} → 𝒪`: elements of `Λ`
outside `(2)` are units of `𝒪` (RC7's `isUnit_algebraMap_of_not_mem_span_two`). -/
noncomputable def lamTwoToO : LambdaTwo →+* OO :=
  IsLocalization.lift (M := (Ideal.span {(2 : Lambda)}).primeCompl) (S := LambdaTwo)
    (g := lamToO) (fun s => isUnit_algebraMap_of_not_mem_span_two (s : Lambda) s.2)

/-- **Tex 2747–2748 (PROVED).** `Λ_{(2)} → 𝒪` extends `Λ → 𝒪`. -/
theorem lamTwoToO_algebraMap (a : Lambda) : lamTwoToO (algebraMap Lambda LambdaTwo a) = lamToO a :=
  IsLocalization.lift_eq _ a

/-- **Tex 2747–2748 (PROVED).** `Λ_{(2)} → 𝒪` sends the uniformizer `2` to the uniformizer `2`. -/
theorem lamTwoToO_two : lamTwoToO 2 = 2 := map_ofNat _ 2

/-- **Tex 2747–2748 (PROVED).** `Λ_{(2)} → 𝒪` is injective. -/
theorem lamTwoToO_injective : Function.Injective lamTwoToO := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨a, s⟩, hxs⟩ := IsLocalization.surj (Ideal.span {(2 : Lambda)}).primeCompl x
  have h := congrArg lamTwoToO hxs
  rw [map_mul, hx, zero_mul, lamTwoToO_algebraMap] at h
  have ha : a = 0 := lamToO_injective (by rw [← h, map_zero])
  rw [ha, map_zero] at hxs
  exact (IsLocalization.map_units LambdaTwo s).mul_left_eq_zero.mp hxs

/-- **Tex 2747–2748 (PROVED).** `Λ_{(2)} → 𝒪` is a local homomorphism. -/
theorem isLocalHom_lamTwoToO : IsLocalHom lamTwoToO := by
  refine ⟨fun x hx => ?_⟩
  by_contra hnu
  have hm : x ∈ IsLocalRing.maximalIdeal LambdaTwo := hnu
  rw [maximalIdeal_lambdaTwo, Ideal.mem_span_singleton] at hm
  obtain ⟨y, rfl⟩ := hm
  rw [map_mul, lamTwoToO_two] at hx
  exact not_isUnit_two_OO (isUnit_of_mul_isUnit_left hx)

/-- The injective map `Λ_{(2)} → Frac 𝒪`. -/
theorem lamTwoToFracO_injective :
    Function.Injective ((algebraMap OO (FractionRing OO)).comp lamTwoToO) :=
  (IsFractionRing.injective OO (FractionRing OO)).comp lamTwoToO_injective

/-- **Tex 2747–2748, 4916–4918 (PROVED construction).** The embedding `ι : Frac Λ → Frac 𝒪` induced by
`Λ_{(2)} → 𝒪` (`Frac Λ` is the fraction field of `Λ_{(2)}`). -/
noncomputable def iotaO : FractionRing Lambda →+* FractionRing OO :=
  IsFractionRing.lift (A := LambdaTwo) lamTwoToFracO_injective

/-- **Tex 2747–2748 (PROVED).** `ι` extends `Λ_{(2)} → 𝒪`. -/
theorem iotaO_algebraMap_lambdaTwo (r : LambdaTwo) :
    iotaO (algebraMap LambdaTwo (FractionRing Lambda) r) = algebraMap OO (FractionRing OO) (lamTwoToO r) :=
  IsFractionRing.lift_algebraMap lamTwoToFracO_injective r

/-- **Tex 2747–2748 (PROVED).** `ι` extends `Λ → 𝒪`. -/
theorem iotaO_algebraMap (a : Lambda) :
    iotaO (algebraMap Lambda (FractionRing Lambda) a) = algebraMap OO (FractionRing OO) (lamToO a) := by
  rw [IsScalarTower.algebraMap_apply Lambda LambdaTwo (FractionRing Lambda),
    iotaO_algebraMap_lambdaTwo, lamTwoToO_algebraMap]

/-- **The valuation of `𝒪` restricted to `Frac Λ` is the valuation of `Λ_{(2)}`** (tex 2747–2748,
3728, 4916–4918; `PROVED`): `v_𝒪 (ι x) = v_{(2)} x`. -/
theorem vO_iotaO (x : FractionRing Lambda) : vO (iotaO x) = v2 x :=
  dvrAddVal_map irreducible_two_lambdaTwo irreducible_two_OO lamTwoToO lamTwoToO_two iotaO
    iotaO_algebraMap_lambdaTwo x

/-- **Lane RC16's `ValuationOfO`, PROVED for the genuine `𝒪`** (tex 3729–3730, 4916–4918). For the
two-adic valuation `v_𝒪` of `𝒪 = \widehat{Λ_{(2)}}` and the embedding `ι : Frac Λ → Frac 𝒪`: an element of
`Frac Λ` is `𝒪`-integral iff it lies in `Λ_{(2)}` (`RegularAt 2`), and `v_𝒪(2) = 1`. This removes the
`GLUE` hypothesis of RC16's `integral_form_of_valuation_bound` and `exLimitsUniformLowerBound`. -/
theorem valuationOfO_genuine : ValuationOfO vO iotaO where
  integral_iff x := by rw [vO_iotaO]; exact v2_nonneg_iff_regularAt x
  val_two := by rw [vO_iotaO]; exact v2_two

/-- **Tex 4914–4920 (PROVED).** RC16's `integral_form_of_valuation_bound` for the genuine `𝒪`: from
`v_𝒪(u) ≥ −C` and `u ∈ Λ[1/2]`, `2^C u ∈ Λ`. -/
theorem integral_form_of_valuation_bound_genuine (C : ℕ) (u : LambdaHalf)
    (hC : (((-C : ℤ)) : WithTop ℤ) ≤ vO (iotaO (lambdaHalfToFrac u))) :
    (2 : LambdaHalf) ^ C * u ∈ (algebraMap Lambda LambdaHalf).range :=
  integral_form_of_valuation_bound vO iotaO valuationOfO_genuine C u hC

/-- **Proposition `ex:limits-uniform-lower-bound` over the genuine `𝒪`** (tex 4909–5202): lane RC16's
`exLimitsUniformLowerBound` with `K = Frac 𝒪`, `v = v_𝒪`, `ι : Frac Λ → Frac 𝒪`, and the `GLUE`
hypothesis `ValuationOfO` discharged by `valuationOfO_genuine`. The remaining hypotheses `outer`,
`regular` are RC16's `ELLIOT` inputs, verbatim. Kind: PROVED from RC16's inputs. -/
theorem exLimitsUniformLowerBound_genuine (A : ℕ) {Inst : Type*} (uprim : Inst → FractionRing Lambda)
    (outer : ∀ inst : ℕ → Inst, ∃ (a : ℕ) (P : OuterSwitchProcess vO (Filter.hyperfilter ℕ) a)
      (S₀ : P.Stage), ∀ᶠ j in ((Filter.hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ),
        vO (P.coord S₀ j) = vO (iotaO (uprim (inst j))))
    (regular : ∀ i, uprim i = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 →
      P ≠ Ideal.span {2} →
      ∃ (Pr : RegularitySwitchProcess (RegularAtPrime P)) (S₀ : Pr.Stage), Pr.coord S₀ = uprim i) :
    ∃ C : ℕ,
      (∀ i, (((-C : ℤ)) : WithTop ℤ) ≤ vO (iotaO (uprim i))) ∧
      (∀ i, ∃ uh : LambdaHalf, lambdaHalfToFrac uh = uprim i ∧
        (2 : LambdaHalf) ^ C * uh ∈ (algebraMap Lambda LambdaHalf).range ∧
        ∀ (j_rc ω sh shk C₀ : ℤ) (P : Finset ℕ) (t : ℕ → ℤ),
          centralSpecialization uh ≠ 0 → (∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 2) → P.card ≤ A →
          |Padic.valuation (centralSpecialization uh) -
              (2 * j_rc - 4 * ω - sh - shk - ∑ p ∈ P, t p)| ≤ C₀ →
          2 * j_rc ≥ 4 * ω + sh + shk - ((C : ℤ) + (C₀ + 2 * A))) :=
  exLimitsUniformLowerBound vO iotaO valuationOfO_genuine A uprim outer regular

/-! ## Non-vacuity -/

/-- Non-vacuity: `ι (1/2)` is not `𝒪`-integral, `ι t` is a unit of valuation `0`, and `ι 2` has valuation
`1`. -/
example : ¬ (0 ≤ vO (iotaO (2 : FractionRing Lambda)⁻¹)) ∧
    vO (iotaO (algebraMap Lambda (FractionRing Lambda) PowerSeries.X)) = 0 ∧
    vO (iotaO 2) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [map_inv₀, AddValuation.map_inv, map_ofNat, vO_two]
    decide
  · rw [iotaO_algebraMap]
    exact vO_t
  · rw [map_ofNat]
    exact vO_two

end ZInQ.Manuscript.RC.Rings
