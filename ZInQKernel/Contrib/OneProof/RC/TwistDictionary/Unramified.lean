import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.TwistLocal
import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Invariance
import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.PointCount
import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.SplitField
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Basic

/-!
# Lane RC18-twist: the local polynomial of a twist at a prime not dividing `D`

At a place `v` of `ℚ` with `p = natGenerator v ∤ D` (and `D ≡ 1 (mod 4)` if `p = 2`), the local
polynomial of `E^{(D)}` is that of `E` with `T` replaced by `χ_D(p) T`
(`localPolynomial_qtwist_of_not_dvd`):

* good reduction: `a_p(E^{(D)}) = χ_D(p) a_p(E)` by counting points of the reduction
  (`natCard_point_twistInt_of_ringChar_ne_two` for odd `p`, `natCard_point_twistInt_zmod_two` for
  `p = 2`);
* multiplicative reduction: split and non-split are exchanged exactly when `χ_D(p) = −1`
  (`splits_splitPoly_twistInt_iff`, `splits_splitPoly_twistInt_zmod_two_iff`);
* additive reduction stays additive.

The model used is `twistInt` of Mathlib's chosen minimal model of `E` over `ℚ_v`, with
`D = 1 + 4c` in `ℤ_p`; it is minimal (`isMinimal_twistInt`), and `localPolynomial` may be computed
from it (`localPolynomial_smul`, `localPolynomial_of_isMinimal`).

All results here are `PROVED`.
-/

namespace ZInQ.Manuscript.RC.TwistDictionary

open WeierstrassCurve IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum
  ZInQ.Literature Polynomial ZInQ.Manuscript.RC.PrintsAnalytic

/-! ### The Kronecker symbol at a prime -/

/-- At an odd prime the Kronecker symbol is the Jacobi (= Legendre) symbol. -/
theorem kronecker_prime_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (D : ℤ) :
    kronecker D p = jacobiSym D p := by
  have hf : p.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd fun h2 =>
    hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  simp only [kronecker, hf, pow_zero, one_mul, Nat.div_one]

/-- At `2` the Kronecker symbol is `kroneckerTwo`. -/
theorem kronecker_two (D : ℤ) : kronecker D 2 = kroneckerTwo D := by
  simp only [kronecker, Nat.Prime.factorization_self Nat.prime_two, pow_one,
    Nat.div_self (show 0 < 2 by norm_num), jacobiSym.one_right, mul_one]

/-! ### Polynomial identities -/

/-- Substituting `χ T` (`χ² = 1`) in `1 − aT + qT²` (PROVED). -/
theorem comp_good (a q χ : ℤ) (hχ : χ ^ 2 = 1) :
    (1 - C a * X + C q * X ^ 2 : ℤ[X]).comp (C χ * X) = 1 - C (χ * a) * X + C q * X ^ 2 := by
  simp only [sub_comp, add_comp, one_comp, mul_comp, C_comp, X_comp, pow_comp]
  rw [mul_pow, ← C_pow, hχ, C_1, one_mul, C_mul]
  ring

/-- Substituting `χ T` in `1 − T` (PROVED). -/
theorem comp_one_sub_X (χ : ℤ) : (1 - X : ℤ[X]).comp (C χ * X) = 1 - C χ * X := by
  simp only [sub_comp, one_comp, X_comp]

/-- Substituting `χ T` in `1 + T` (PROVED). -/
theorem comp_one_add_X (χ : ℤ) : (1 + X : ℤ[X]).comp (C χ * X) = 1 + C χ * X := by
  simp only [add_comp, one_comp, X_comp]

section Place

variable (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

/-- `D = 1 + 4c` in `𝒪_v`, with `c = (D - 1)/4 ∈ ℤ` when `p = 2`. -/
theorem exists_eq_one_add_four_mul {D : ℤ} (h4 : natGenerator v = 2 → D % 4 = 1) :
    ∃ c : v.adicCompletionIntegers ℚ, (D : v.adicCompletionIntegers ℚ) = 1 + 4 * c ∧
      (natGenerator v = 2 → c = (((D - 1) / 4 : ℤ) : v.adicCompletionIntegers ℚ)) := by
  by_cases hp : natGenerator v = 2
  · refine ⟨(((D - 1) / 4 : ℤ) : v.adicCompletionIntegers ℚ), ?_, fun _ => rfl⟩
    have h := h4 hp
    have hD : D = 1 + 4 * ((D - 1) / 4) := by omega
    conv_lhs => rw [hD]
    push_cast; ring
  · have hu : IsUnit ((4 : ℤ) : v.adicCompletionIntegers ℚ) := by
      rw [isUnit_intCast_iff]
      intro h
      have h' : natGenerator v ∣ 4 := by exact_mod_cast h
      have h'' : natGenerator v ∣ 2 ^ 2 := by norm_num; exact h'
      exact hp ((Nat.prime_dvd_prime_iff_eq (prime_natGenerator v) Nat.prime_two).mp
        ((prime_natGenerator v).dvd_of_dvd_pow h''))
    refine ⟨(hu.unit⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) * ((D - 1 : ℤ) : v.adicCompletionIntegers ℚ),
      ?_, fun h => absurd h hp⟩
    have key : (4 : v.adicCompletionIntegers ℚ) * ↑(hu.unit⁻¹) = 1 := by
      have h4c : ((4 : ℤ) : v.adicCompletionIntegers ℚ) = 4 := by norm_num
      have := hu.unit.mul_inv
      rw [IsUnit.unit_spec] at this
      rw [← h4c]; exact this
    rw [← mul_assoc, key, one_mul]; push_cast; ring

/-- The residue of an integer, read in `ZMod p`. -/
theorem residueEquiv_residue_intCast (n : ℤ) :
    residueEquiv v (IsLocalRing.residue (v.adicCompletionIntegers ℚ) (n : v.adicCompletionIntegers ℚ)) =
      (n : ZMod (natGenerator v)) :=
  map_intCast ((residueEquiv v).toRingHom.comp (IsLocalRing.residue _)) n

/-! ### The residue computations, in `ZMod p` -/

/-- `kronecker D 2` through `c = (D - 1)/4 (mod 2)`, for `D ≡ 1 (mod 4)`. -/
theorem kronecker_two_eq_ite {D : ℤ} (h4 : D % 4 = 1) :
    kronecker D 2 = if (((D - 1) / 4 : ℤ) : ZMod 2) = 0 then 1 else -1 := by
  rw [kronecker_two]
  have h8 : D % 8 = 1 ∨ D % 8 = 5 := by omega
  have hD2 : ¬ D % 2 = 0 := by omega
  rcases h8 with h8 | h8
  · have hd : (((D - 1) / 4 : ℤ) : ZMod 2) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hd)]
    simp only [kroneckerTwo, hD2, ite_false, h8, true_or, ite_true]
  · have hd : ¬ (((D - 1) / 4 : ℤ) : ZMod 2) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
    simp only [kroneckerTwo, hD2, ite_false, h8]
    norm_num

/-- `kronecker D p = ±1` for `p ∤ D`. -/
theorem kronecker_prime_eq_one_or {p : ℕ} (hp : p.Prime) {D : ℤ} (hpD : ¬ (p : ℤ) ∣ D)
    (h4 : p = 2 → D % 4 = 1) : kronecker D p = 1 ∨ kronecker D p = -1 := by
  by_cases hp2 : p = 2
  · subst hp2
    rw [kronecker_two_eq_ite (h4 rfl)]
    split_ifs <;> simp
  · have : Fact p.Prime := ⟨hp⟩
    rw [kronecker_prime_of_ne_two hp hp2, ← jacobiSym.legendreSym.to_jacobiSym]
    exact legendreSym.eq_one_or_neg_one p (by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd])

/-- **Points of the twisted reduction** (PROVED): over `ZMod p`, `p ∤ D`,
`|(twistInt V D c')(𝔽_p)| = p + 1 − χ_D(p) (p + 1 − |V(𝔽_p)|)`. -/
theorem natCard_twist_residue (p : ℕ) [hp : Fact p.Prime] (V : WeierstrassCurve (ZMod p))
    [V.IsElliptic] {D : ℤ} (hpD : ¬ (p : ℤ) ∣ D) (c' : ZMod p)
    (hc' : (D : ZMod p) = 1 + 4 * c') (h2 : p = 2 → c' = (((D - 1) / 4 : ℤ) : ZMod p))
    (h4 : p = 2 → D % 4 = 1) :
    (Nat.card (twistInt V (D : ZMod p) c').toAffine.Point : ℤ) =
      p + 1 - kronecker D p * (p + 1 - Nat.card V.toAffine.Point) := by
  by_cases hp2 : p = 2
  · subst hp2
    have hD1 : (D : ZMod 2) = 1 := by
      have h := h4 rfl
      have : (D : ZMod 2) = ((1 : ℤ) : ZMod 2) := by
        rw [ZMod.intCast_eq_intCast_iff_dvd_sub]; omega
      simpa using this
    rw [hD1, natCard_point_twistInt_zmod_two V c', kronecker_two_eq_ite (h4 rfl), ← h2 rfl]
    push_cast; ring
  · have hk : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
    have hD0 : (D : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [natCard_point_twistInt_of_ringChar_ne_two hk V hc' hD0, ZMod.card,
      kronecker_prime_of_ne_two hp.out hp2, ← jacobiSym.legendreSym.to_jacobiSym]
    rfl

/-- **Split versus non-split for the twisted reduction** (PROVED): over `ZMod p`, `p ∤ D`, for a
nodal `V` (`c₄ ≠ 0`, `Δ = 0`), `splitPoly` of the twist splits iff (`splitPoly V` splits iff
`χ_D(p) = 1`). -/
theorem splits_twist_residue (p : ℕ) [hp : Fact p.Prime] (V : WeierstrassCurve (ZMod p))
    (hc₄ : V.c₄ ≠ 0) (hΔ : V.Δ = 0) {D : ℤ} (hpD : ¬ (p : ℤ) ∣ D) (c' : ZMod p)
    (hc' : (D : ZMod p) = 1 + 4 * c') (h2 : p = 2 → c' = (((D - 1) / 4 : ℤ) : ZMod p))
    (h4 : p = 2 → D % 4 = 1) :
    Splits (splitPoly (twistInt V (D : ZMod p) c')) ↔
      (Splits (splitPoly V) ↔ kronecker D p = 1) := by
  by_cases hp2 : p = 2
  · subst hp2
    have hD1 : (D : ZMod 2) = 1 := by
      have h := h4 rfl
      have : (D : ZMod 2) = ((1 : ℤ) : ZMod 2) := by
        rw [ZMod.intCast_eq_intCast_iff_dvd_sub]; omega
      simpa using this
    rw [hD1, splits_splitPoly_twistInt_zmod_two_iff V hc₄ c', kronecker_two_eq_ite (h4 rfl),
      ← h2 rfl]
    split_ifs with h <;> simp [h]
  · have hk : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
    have hD0 : (D : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hc₆ : V.c₆ ≠ 0 := by
      intro h6
      have hrel := V.c_relation
      rw [hΔ, h6, mul_zero] at hrel
      exact hc₄ (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp (by linear_combination -hrel))
    rw [splits_splitPoly_twistInt_iff hk V hc₄ hc₆ hc' hD0, kronecker_prime_of_ne_two hp.out hp2,
      ← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p hD0]

/-- `Splits ∘ splitPoly` is invariant under ring isomorphisms of fields. -/
theorem splits_splitPoly_map_ringEquiv {F F' : Type*} [Field F] [Field F']
    (V : WeierstrassCurve F) (e : F ≃+* F') :
    Splits (splitPoly (V.map (e : F →+* F'))) ↔ Splits (splitPoly V) := by
  constructor
  · intro h
    have := h.map (e.symm : F' →+* F)
    rwa [splitPoly_map, WeierstrassCurve.map_map, RingEquiv.symm_comp,
      WeierstrassCurve.map_id] at this
  · intro h
    have := h.map (e : F →+* F')
    rwa [splitPoly_map] at this

/-! ### The local polynomial of the twist -/

/-- **The local polynomial of `E^{(D)}` at a place `v ∤ D`** (PROVED): with `p = natGenerator v`,
`p ∤ D` and `D ≡ 1 (mod 4)` if `p = 2`, the local polynomial of `E^{(D)}` over `ℚ_v` is that of
`E` composed with `T ↦ χ_D(p) T`. -/
theorem localPolynomial_qtwist_of_not_dvd (E : WeierstrassCurve ℚ) [hE : E.IsElliptic] {D : ℤ}
    (hpD : ¬ (natGenerator v : ℤ) ∣ D) (h4 : natGenerator v = 2 → D % 4 = 1) :
    ((ZInQ.Contrib.CloudB3RC53.qtwist E D).baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) =
      ((E.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ)).comp
        (C (kronecker D (natGenerator v)) * X) := by
  classical
  have hp : (natGenerator v).Prime := prime_natGenerator v
  have : Fact (natGenerator v).Prime := ⟨hp⟩
  have h2K : (2 : v.adicCompletion ℚ) ≠ 0 := two_ne_zero
  have hWΔ : (E.baseChange (v.adicCompletion ℚ)).Δ ≠ 0 := by
    rw [baseChange, map_Δ]
    exact (_root_.map_ne_zero _).mpr E.isUnit_Δ.ne_zero
  obtain ⟨M, hM_def⟩ : ∃ M, M = (E.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ) := ⟨_, rfl⟩
  have hMmin : IsMinimal (v.adicCompletionIntegers ℚ) M := hM_def ▸ inferInstance
  have hMW : ((E.baseChange (v.adicCompletion ℚ)).exists_isMinimal
      (v.adicCompletionIntegers ℚ)).choose • E.baseChange (v.adicCompletion ℚ) = M := by
    rw [hM_def]; rfl
  have hMΔ : M.Δ ≠ 0 := by
    rw [← hMW, variableChange_Δ]
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hWΔ
  obtain ⟨c, hc, hc2⟩ := exists_eq_one_add_four_mul v h4
  have hDu : IsUnit (D : v.adicCompletionIntegers ℚ) := (isUnit_intCast_iff v D).mpr hpD
  obtain ⟨T, hT⟩ : ∃ T, T = (twistInt (integralModel (v.adicCompletionIntegers ℚ) M)
      (D : v.adicCompletionIntegers ℚ) c).baseChange (v.adicCompletion ℚ) := ⟨_, rfl⟩
  have hTmin : IsMinimal (v.adicCompletionIntegers ℚ) T := hT ▸ isMinimal_twistInt h2K M hc hDu
  -- the twist over `ℚ_v` and the model `T`
  have hDK : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
      (D : v.adicCompletionIntegers ℚ) = (D : v.adicCompletion ℚ) := map_intCast _ _
  have hq : (ZInQ.Contrib.CloudB3RC53.qtwist E D).baseChange (v.adicCompletion ℚ) =
      twistK (E.baseChange (v.adicCompletion ℚ))
        (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (D : _)) := by
    rw [hDK, qtwist_eq_twistK, baseChange, twistK_map, map_intCast]
    rfl
  obtain ⟨C₂, hC₂⟩ := exists_smul_twistK_eq_twistInt (c := c) h2K M hc
  obtain ⟨C₃, hC₃⟩ := exists_smul_twistK_of_smul h2K hMW
    (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (D : _))
  have hTq : (C₂ * C₃) • (ZInQ.Contrib.CloudB3RC53.qtwist E D).baseChange (v.adicCompletion ℚ) =
      T := by
    rw [hq, mul_smul, hC₃, hC₂, hT]
  have hD0K : (D : v.adicCompletion ℚ) ≠ 0 := by
    intro h0
    have h0' : (D : ℤ) = 0 := by exact_mod_cast h0
    exact hpD (h0' ▸ dvd_zero _)
  have hqΔ : ((ZInQ.Contrib.CloudB3RC53.qtwist E D).baseChange (v.adicCompletion ℚ)).Δ ≠ 0 := by
    rw [hq, twistK_Δ _ h2K, hDK]
    exact mul_ne_zero (pow_ne_zero _ hD0K) hWΔ
  have hTΔ : T.Δ ≠ 0 := by
    rw [← hTq, variableChange_Δ]
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hqΔ
  rw [← localPolynomial_smul (R := v.adicCompletionIntegers ℚ) _ hqΔ (C₂ * C₃), hTq,
    localPolynomial_of_isMinimal T hTΔ,
    ← localPolynomial_smul (R := v.adicCompletionIntegers ℚ) _ hWΔ
      ((E.baseChange (v.adicCompletion ℚ)).exists_isMinimal (v.adicCompletionIntegers ℚ)).choose,
    hMW, localPolynomial_of_isMinimal M hMΔ, natCard_residueField v]
  -- the reductions, read in `ZMod p`
  have hTb : T.reduction (v.adicCompletionIntegers ℚ) =
      twistInt (M.reduction (v.adicCompletionIntegers ℚ))
        (IsLocalRing.residue _ (D : v.adicCompletionIntegers ℚ)) (IsLocalRing.residue _ c) := by
    subst hT; exact reduction_twistInt M (D : v.adicCompletionIntegers ℚ) c
  obtain ⟨c', hc'_def⟩ : ∃ c', c' = residueEquiv v (IsLocalRing.residue _ c) := ⟨_, rfl⟩
  have hc' : (D : ZMod (natGenerator v)) = 1 + 4 * c' := by
    have := congrArg (fun x => residueEquiv v (IsLocalRing.residue _ x)) hc
    simp only [map_add, map_mul, map_one, map_ofNat] at this
    rw [← residueEquiv_residue_intCast v D, hc'_def]; exact this
  have hc2' : natGenerator v = 2 → c' = (((D - 1) / 4 : ℤ) : ZMod (natGenerator v)) := fun h => by
    rw [hc'_def, hc2 h, residueEquiv_residue_intCast]
  have hTbe : (T.reduction (v.adicCompletionIntegers ℚ)).map (residueEquiv v : IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ) →+* ZMod (natGenerator v)) =
      twistInt ((M.reduction (v.adicCompletionIntegers ℚ)).map (residueEquiv v : IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ) →+* ZMod (natGenerator v)))
        (D : ZMod (natGenerator v)) c' := by
    rw [hTb, twistInt_map]
    congr 1
    · exact residueEquiv_residue_intCast v D
    · exact hc'_def.symm
  have hχ := kronecker_prime_eq_one_or hp hpD h4
  by_cases hg : M.HasGoodReduction (v.adicCompletionIntegers ℚ)
  · -- good reduction: count points
    have hTg : T.HasGoodReduction (v.adicCompletionIntegers ℚ) := by
      subst hT; exact (hasGoodReduction_twistInt_iff M hc hDu).mpr hg
    simp only [hg, hTg, ite_true]
    have hMe : (M.reduction (v.adicCompletionIntegers ℚ)).IsElliptic :=
      (hasGoodReduction_iff_isElliptic_reduction _).mp hg
    have hTe : (T.reduction (v.adicCompletionIntegers ℚ)).IsElliptic :=
      (hasGoodReduction_iff_isElliptic_reduction _).mp hTg
    have hpts : (Nat.card (T.reduction (v.adicCompletionIntegers ℚ)).toAffine.Point : ℤ) =
        natGenerator v + 1 - kronecker D (natGenerator v) *
          (natGenerator v + 1 - Nat.card (M.reduction (v.adicCompletionIntegers ℚ)).toAffine.Point) := by
      rw [← natCard_point_map_ringEquiv (T.reduction _) (residueEquiv v), hTbe,
        natCard_twist_residue _ _ hpD c' hc' hc2' h4, natCard_point_map_ringEquiv]
    rw [comp_good _ _ _ (by rcases hχ with h | h <;> rw [h] <;> norm_num)]
    have hcoef : ((natGenerator v : ℤ) + 1 -
        Nat.card (T.reduction (v.adicCompletionIntegers ℚ)).toAffine.Point) =
        kronecker D (natGenerator v) * ((natGenerator v : ℤ) + 1 -
          Nat.card (M.reduction (v.adicCompletionIntegers ℚ)).toAffine.Point) := by
      rw [hpts]; ring
    rw [hcoef]
  · by_cases hm : M.HasMultiplicativeReduction (v.adicCompletionIntegers ℚ)
    · -- multiplicative reduction: split and non-split
      have hTg : ¬ T.HasGoodReduction (v.adicCompletionIntegers ℚ) := fun h => hg (by
        subst hT; exact (hasGoodReduction_twistInt_iff M hc hDu).mp h)
      have hTm : T.HasMultiplicativeReduction (v.adicCompletionIntegers ℚ) := by
        subst hT; exact (hasMultiplicativeReduction_twistInt_iff M hc hDu).mpr hm
      have hc4 : ((M.reduction (v.adicCompletionIntegers ℚ)).map
          (residueEquiv v : IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ) →+* ZMod (natGenerator v))).c₄ ≠ 0 := by
        have h1 := hm.multiplicativeReduction
        rw [← integralModel_c₄_eq (v.adicCompletionIntegers ℚ) M, valuation_of_algebraMap, intValuation_eq_one_iff] at h1
        rw [map_c₄, reduction, map_c₄]
        intro h0
        apply h1
        show _ ∈ IsLocalRing.maximalIdeal _
        rw [← IsLocalRing.residue_eq_zero_iff]
        exact (map_eq_zero_iff _ (residueEquiv v).injective).mp h0
      have hΔ0 : ((M.reduction (v.adicCompletionIntegers ℚ)).map
          (residueEquiv v : IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ) →+* ZMod (natGenerator v))).Δ = 0 := by
        have h1 : ¬ (M.reduction (v.adicCompletionIntegers ℚ)).IsElliptic := fun h =>
          hg ((hasGoodReduction_iff_isElliptic_reduction _).mpr h)
        rw [isElliptic_iff, isUnit_iff_ne_zero, not_not] at h1
        rw [map_Δ, h1, map_zero]
      have hsplit : T.HasSplitMultiplicativeReduction (v.adicCompletionIntegers ℚ) ↔
          (M.HasSplitMultiplicativeReduction (v.adicCompletionIntegers ℚ) ↔
            kronecker D (natGenerator v) = 1) := by
        rw [hasSplitMultiplicativeReduction_iff T, hasSplitMultiplicativeReduction_iff M]
        simp only [hTm, hm, true_and]
        rw [← splits_splitPoly_map_ringEquiv (T.reduction _) (residueEquiv v), hTbe,
          splits_twist_residue _ _ hc4 hΔ0 hpD c' hc' hc2' h4, splits_splitPoly_map_ringEquiv]
      simp only [hg, hTg, ite_false, hm, hTm, ite_true]
      rcases hχ with h1 | h1
      · rw [h1] at hsplit ⊢
        by_cases hs : M.HasSplitMultiplicativeReduction (v.adicCompletionIntegers ℚ)
        · have hts : T.HasSplitMultiplicativeReduction (v.adicCompletionIntegers ℚ) :=
            hsplit.mpr (iff_of_true hs rfl)
          simp only [hs, hts, ite_true]
          rw [comp_one_sub_X, C_1, one_mul]
        · have hts : ¬ T.HasSplitMultiplicativeReduction (v.adicCompletionIntegers ℚ) :=
            fun h => hs ((hsplit.mp h).mpr rfl)
          simp only [hs, hts, ite_false]
          rw [comp_one_add_X, C_1, one_mul]
      · rw [h1] at hsplit ⊢
        by_cases hs : M.HasSplitMultiplicativeReduction (v.adicCompletionIntegers ℚ)
        · have hts : ¬ T.HasSplitMultiplicativeReduction (v.adicCompletionIntegers ℚ) :=
            fun h => by have := (hsplit.mp h).mp hs; norm_num at this
          simp only [hs, hts, ite_true, ite_false]
          rw [comp_one_sub_X, C_neg, C_1]
          ring
        · have hts : T.HasSplitMultiplicativeReduction (v.adicCompletionIntegers ℚ) :=
            hsplit.mpr (iff_of_false hs (by norm_num))
          simp only [hs, hts, ite_true, ite_false]
          rw [comp_one_add_X, C_neg, C_1]
          ring
    · -- additive reduction
      have hTg : ¬ T.HasGoodReduction (v.adicCompletionIntegers ℚ) := fun h => hg (by
        subst hT; exact (hasGoodReduction_twistInt_iff M hc hDu).mp h)
      have hTm : ¬ T.HasMultiplicativeReduction (v.adicCompletionIntegers ℚ) := fun h => hm (by
        subst hT; exact (hasMultiplicativeReduction_twistInt_iff M hc hDu).mp h)
      have hTs : ¬ T.HasSplitMultiplicativeReduction (v.adicCompletionIntegers ℚ) := fun h =>
        hTm h.toHasMultiplicativeReduction
      have hMs : ¬ M.HasSplitMultiplicativeReduction (v.adicCompletionIntegers ℚ) := fun h =>
        hm h.toHasMultiplicativeReduction
      simp only [hg, hTg, hm, hTm, hTs, hMs, ite_false, one_comp]

end Place

end ZInQ.Manuscript.RC.TwistDictionary
