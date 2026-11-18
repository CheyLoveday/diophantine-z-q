import ZInQKernel.Contrib.OneProof.RC.Rings.OValuation

/-!
# Lane RC20: `𝒪` is the two-adic completion of `Λ_{(2)}`

Manuscript (`diophantine_zq.tex`, 11/5 version):
* tex 2747–2748, Definition `ex:arith-data`: "Put `Λ = ℤ₂[[t]]` and `𝒪 = \widehat{Λ_{(2)}}`";
* tex 3728: `𝒪 = \widehat{ℤ₂[[t]]_{(2)}}`.

Lane RC7 models `𝒪` as the inverse limit `OO = lim_n (ℤ/2ⁿ)((t))` and states in prose (docstring of its
model file) that "modulo `2ⁿ`, inverting the elements of `Λ` outside `(2)` inverts exactly `t` ... Hence
`Λ_{(2)}/2ⁿ = (ℤ/2ⁿ)[[t]][t⁻¹] = (ℤ/2ⁿ)((t))`", without a proof. This file proves that claim and deduces
that RC7's `OO` is the two-adic completion of `LambdaTwo = Λ_{(2)}` along `lamTwoToO : Λ_{(2)} → 𝒪`:

* `lamTwoToO_mem_span_two_pow_iff` : `lamTwoToO x ∈ (2ⁿ) ↔ x ∈ (2ⁿ)` (both rings are DVRs with uniformizer
  `2`, and `lamTwoToO` sends units to units);
* `surjective_proj_comp_lamTwoToO` : every Laurent series over `ℤ/2ⁿ` is the reduction of an element
  `t^{-L} a` of `Λ_{(2)}`; `exists_sub_mk'_pow_X_mem` : modulo `2ⁿ`, every element of `Λ_{(2)}` is
  `a / t^L` (RC7's "inverts exactly `t`");
* `quotTwoPowLambdaTwoEquiv n : Λ_{(2)}/2ⁿ ≃+* 𝒪/2ⁿ` and `lambdaTwoQuotLaurentEquiv n :
  Λ_{(2)}/2ⁿ ≃+* (ℤ/2ⁿ)((t))`, with their values on classes;
* `exists_sub_lamTwoToO_mem` : `Λ_{(2)}` is dense in `𝒪`;
* a general criterion (`IsAdicCompletionAlong`, `IsAdicCompletionAlong.adicCompletionEquiv`): a ring map
  `f : R → S` with `f⁻¹(Jⁿ) = Iⁿ`, `R → S/Jⁿ` onto, and `S` `J`-adically complete identifies `S` with
  Mathlib's `AdicCompletion I R`;
* `isAdicCompletionAlong_lamTwoToO`, `OO_isCompletion_lambdaTwo` (the bundled statement), and the explicit
  ring isomorphism `adicCompletionLambdaTwoEquiv : AdicCompletion (2) Λ_{(2)} ≃+* 𝒪`, `x ↦ lamTwoToO x`.

Everything here is `PROVED`.
-/

namespace ZInQ.Manuscript.RC.Rings

open ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Determinant ZInQ.Manuscript.RC.Determinant.OModel

/-! ## Divisibility by powers of two is preserved and reflected -/

/-- **Tex 2747–2748, 3728 (PROVED).** `Λ_{(2)} → 𝒪` preserves and reflects divisibility by `2ⁿ`: both
rings are DVRs with uniformizer `2`, `lamTwoToO 2 = 2`, and units go to units. -/
theorem lamTwoToO_mem_span_two_pow_iff (n : ℕ) (x : LambdaTwo) :
    lamTwoToO x ∈ Ideal.span {(2 : OO) ^ n} ↔ x ∈ Ideal.span {(2 : LambdaTwo) ^ n} := by
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨k, u, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx irreducible_two_lambdaTwo
  have hu : IsUnit (lamTwoToO (u : LambdaTwo)) := u.isUnit.map lamTwoToO
  rw [map_mul, map_pow, lamTwoToO_two, hu.dvd_mul_left, u.isUnit.dvd_mul_left,
    pow_dvd_pow_iff two_ne_zero_OO not_isUnit_two_OO,
    pow_dvd_pow_iff irreducible_two_lambdaTwo.ne_zero irreducible_two_lambdaTwo.not_isUnit]

/-- **Tex 2747–2748, 3728 (PROVED).** Ideal form: the preimage of `(2ⁿ) ⊂ 𝒪` in `Λ_{(2)}` is `(2ⁿ)`. -/
theorem comap_lamTwoToO_span_two_pow (n : ℕ) :
    (Ideal.span {(2 : OO) ^ n}).comap lamTwoToO = Ideal.span {(2 : LambdaTwo) ^ n} := by
  ext x
  exact lamTwoToO_mem_span_two_pow_iff n x

/-! ## Modulo `2ⁿ`, inverting `Λ ∖ (2)` inverts exactly `t` -/

/-- **Tex 2747–2748, 3728 (PROVED).** `tᴸ ∉ (2)` in `Λ = ℤ₂[[t]]`, so `tᴸ` is inverted in `Λ_{(2)}`. -/
theorem pow_X_mem_primeCompl (L : ℕ) :
    (PowerSeries.X : Lambda) ^ L ∈ (Ideal.span {(2 : Lambda)}).primeCompl := by
  refine pow_mem ?_ L
  rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton]
  intro h
  have h1 := (two_dvd_iff_forall_coeff PowerSeries.X).mp h 1
  simp only [PowerSeries.coeff_X, ↓reduceIte] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 := congrArg (PadicInt.toZMod (p := 2)) hc
  rw [map_one, map_mul, map_ofNat, show (2 : ZMod 2) = 0 from rfl, zero_mul] at h2
  exact one_ne_zero h2

/-- **Tex 2747–2748, 3728 (PROVED).** The element `a / tᴸ ∈ Λ_{(2)}` maps to `t^{-L} a ∈ 𝒪`. -/
theorem lamTwoToO_mk'_pow_X (a : Lambda) (L : ℕ) :
    lamTwoToO (IsLocalization.mk' LambdaTwo a (⟨PowerSeries.X ^ L, pow_X_mem_primeCompl L⟩ :
      (Ideal.span {(2 : Lambda)}).primeCompl)) = tInv ^ L * lamToO a := by
  have h := congrArg lamTwoToO (IsLocalization.mk'_spec LambdaTwo a
    (⟨PowerSeries.X ^ L, pow_X_mem_primeCompl L⟩ : (Ideal.span {(2 : Lambda)}).primeCompl))
  rw [map_mul, lamTwoToO_algebraMap, lamTwoToO_algebraMap] at h
  dsimp only at h
  have ht : lamToO (PowerSeries.X ^ L) * tInv ^ L = 1 := by
    rw [map_pow, ← mul_pow, ← algebraMap_eq_lamToO, algebraMap_X_mul_tInv, one_pow]
  calc _ = lamTwoToO (IsLocalization.mk' LambdaTwo a
        (⟨PowerSeries.X ^ L, pow_X_mem_primeCompl L⟩ : (Ideal.span {(2 : Lambda)}).primeCompl)) *
        (lamToO (PowerSeries.X ^ L) * tInv ^ L) := by rw [ht, mul_one]
    _ = tInv ^ L * lamToO a := by rw [← mul_assoc, h, mul_comm]

/-- **Tex 2747–2748, 3728 (PROVED).** Every Laurent series over `ℤ/2ⁿ` is the reduction of `t^{-L} a`
for some `a ∈ Λ = ℤ₂[[t]]` and `L ∈ ℕ`: write it as `t^{-L}` times a power series and lift the
coefficients to `ℤ₂`. -/
theorem exists_proj_tInv_pow_mul_eq (n : ℕ) (z : LaurentSeries (ZMod (2 ^ n))) :
    ∃ (a : Lambda) (L : ℕ), proj n (tInv ^ L * lamToO a) = z := by
  obtain ⟨L, hL⟩ := laurent_exists_coeff_eq_zero z
  set a : Lambda := PowerSeries.mk fun m => (((z.coeff ((m : ℤ) - L)).val : ℕ) : ℤ_[2]) with ha
  refine ⟨a, L, ?_⟩
  rw [map_mul, map_pow, proj_tInv, ← algebraMap_eq_lamToO, proj_algebraMap,
    laurent_eq_single_mul_ofPowerSeries z L hL, HahnSeries.single_pow, one_pow]
  congr 2
  · simp
  · ext m
    simp [ha, PowerSeries.coeff_map]

/-- **Tex 2747–2748, 3728 (PROVED).** The reduction `Λ_{(2)} → 𝒪 → 𝒪/2ⁿ = (ℤ/2ⁿ)((t))` is surjective. -/
theorem surjective_proj_comp_lamTwoToO (n : ℕ) : Function.Surjective ((proj n).comp lamTwoToO) := by
  intro z
  obtain ⟨a, L, h⟩ := exists_proj_tInv_pow_mul_eq n z
  exact ⟨IsLocalization.mk' LambdaTwo a (⟨PowerSeries.X ^ L, pow_X_mem_primeCompl L⟩ :
      (Ideal.span {(2 : Lambda)}).primeCompl), by rw [RingHom.comp_apply, lamTwoToO_mk'_pow_X, h]⟩

/-- **Density of `Λ_{(2)}` in `𝒪`** (tex 2747–2748, 3728; `PROVED`): every `y ∈ 𝒪` is congruent modulo
`2ⁿ` to the image of some `x ∈ Λ_{(2)}`. -/
theorem exists_sub_lamTwoToO_mem (n : ℕ) (y : OO) :
    ∃ x : LambdaTwo, y - lamTwoToO x ∈ Ideal.span {(2 : OO) ^ n} := by
  obtain ⟨x, hx⟩ := surjective_proj_comp_lamTwoToO n (proj n y)
  refine ⟨x, ?_⟩
  rw [← proj_eq_zero_iff_mem, map_sub, sub_eq_zero]
  exact hx.symm

/-- **RC7's prose claim "modulo `2ⁿ`, inverting the elements of `Λ` outside `(2)` inverts exactly `t`"**
(tex 2747–2748, 3728; `PROVED`): every `x ∈ Λ_{(2)}` is congruent modulo `2ⁿ` to `a / tᴸ` with `a ∈ Λ`. -/
theorem exists_sub_mk'_pow_X_mem (n : ℕ) (x : LambdaTwo) :
    ∃ (a : Lambda) (L : ℕ), x - IsLocalization.mk' LambdaTwo a
      (⟨PowerSeries.X ^ L, pow_X_mem_primeCompl L⟩ : (Ideal.span {(2 : Lambda)}).primeCompl) ∈
        Ideal.span {(2 : LambdaTwo) ^ n} := by
  obtain ⟨a, L, h⟩ := exists_proj_tInv_pow_mul_eq n (proj n (lamTwoToO x))
  refine ⟨a, L, ?_⟩
  rw [← lamTwoToO_mem_span_two_pow_iff, map_sub, lamTwoToO_mk'_pow_X, ← proj_eq_zero_iff_mem,
    map_sub, h, sub_self]

/-! ## `Λ_{(2)}/2ⁿ ≅ 𝒪/2ⁿ ≅ (ℤ/2ⁿ)((t))` -/

/-- **Tex 2747–2748, 3728 (PROVED construction).** `Λ_{(2)}/2ⁿ ≃+* 𝒪/2ⁿ`, induced by `lamTwoToO`
(injective by `lamTwoToO_mem_span_two_pow_iff`, surjective by `surjective_proj_comp_lamTwoToO`). -/
noncomputable def quotTwoPowLambdaTwoEquiv (n : ℕ) :
    LambdaTwo ⧸ Ideal.span {(2 : LambdaTwo) ^ n} ≃+* OO ⧸ Ideal.span {(2 : OO) ^ n} :=
  RingEquiv.ofBijective
    (Ideal.quotientMap (Ideal.span {(2 : OO) ^ n}) lamTwoToO (comap_lamTwoToO_span_two_pow n).ge)
    ⟨Ideal.quotientMap_injective' (comap_lamTwoToO_span_two_pow n).le, fun q => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
      obtain ⟨x, hx⟩ := exists_sub_lamTwoToO_mem n y
      exact ⟨Ideal.Quotient.mk _ x, by
        rw [Ideal.quotientMap_mk]; exact (Ideal.Quotient.eq.mpr hx).symm⟩⟩

/-- **Tex 2747–2748, 3728 (PROVED).** The defining equation: the class of `x` goes to the class of
`lamTwoToO x`. -/
theorem quotTwoPowLambdaTwoEquiv_mk (n : ℕ) (x : LambdaTwo) :
    quotTwoPowLambdaTwoEquiv n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (lamTwoToO x) := rfl

/-- **Tex 2747–2748, 3728 (PROVED).** RC7's `quotTwoPowEquiv` on classes is `proj`. -/
theorem quotTwoPowEquiv_mk (n : ℕ) (y : OO) :
    quotTwoPowEquiv n (Ideal.Quotient.mk _ y) = proj n y := rfl

/-- **`Λ_{(2)}/2ⁿ = (ℤ/2ⁿ)((t))`** (tex 2747–2748, 3728; RC7's prose claim; `PROVED` construction):
the composite of `quotTwoPowLambdaTwoEquiv` with RC7's `quotTwoPowEquiv`. -/
noncomputable def lambdaTwoQuotLaurentEquiv (n : ℕ) :
    LambdaTwo ⧸ Ideal.span {(2 : LambdaTwo) ^ n} ≃+* LaurentSeries (ZMod (2 ^ n)) :=
  (quotTwoPowLambdaTwoEquiv n).trans (quotTwoPowEquiv n)

/-- **Tex 2747–2748, 3728 (PROVED).** `Λ_{(2)}/2ⁿ ≅ (ℤ/2ⁿ)((t))` sends the class of `x` to the reduction
of `lamTwoToO x`. -/
theorem lambdaTwoQuotLaurentEquiv_mk (n : ℕ) (x : LambdaTwo) :
    lambdaTwoQuotLaurentEquiv n (Ideal.Quotient.mk _ x) = proj n (lamTwoToO x) := rfl

/-- **Tex 2747–2748, 3728 (PROVED).** On `a ∈ Λ`, `Λ_{(2)}/2ⁿ ≅ (ℤ/2ⁿ)((t))` is coefficientwise reduction
modulo `2ⁿ`. -/
theorem lambdaTwoQuotLaurentEquiv_algebraMap (n : ℕ) (a : Lambda) :
    lambdaTwoQuotLaurentEquiv n (Ideal.Quotient.mk _ (algebraMap Lambda LambdaTwo a)) =
      HahnSeries.ofPowerSeries ℤ _ (PowerSeries.map (PadicInt.toZModPow n) a) := by
  rw [lambdaTwoQuotLaurentEquiv_mk, lamTwoToO_algebraMap, ← algebraMap_eq_lamToO, proj_algebraMap]

/-- **Tex 2747–2748, 3728 (PROVED).** Coefficient form: for `a ∈ Λ` and `i ∈ ℕ`, the `tⁱ`-coefficient of
the image of `a` in `(ℤ/2ⁿ)((t))` is `[tⁱ]a mod 2ⁿ`. -/
theorem coeff_lambdaTwoQuotLaurentEquiv_algebraMap (n : ℕ) (a : Lambda) (i : ℕ) :
    (lambdaTwoQuotLaurentEquiv n (Ideal.Quotient.mk _ (algebraMap Lambda LambdaTwo a))).coeff (i : ℤ) =
      PadicInt.toZModPow n (PowerSeries.coeff i a) := by
  rw [lambdaTwoQuotLaurentEquiv_algebraMap, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_map]

/-! ## A general completion criterion -/

section Generic

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **Tex 2747–2748 (PROVED; general fact used for `𝒪 = \widehat{Λ_{(2)}}`).** The levels `evalₐ` of
Mathlib's `AdicCompletion I R` are compatible with the transition maps `R/Iⁿ → R/Iᵐ`. -/
theorem factorPow_evalₐ (I : Ideal R) {m n : ℕ} (hle : m ≤ n) (c : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n c) = AdicCompletion.evalₐ I m c := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I R c
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk,
    Ideal.Quotient.eq]
  have h := s.2 hle
  rw [SModEq.sub_mem] at h
  have h' : (s.val m - s.val n) ∈ I ^ m := by simpa [smul_eq_mul, Ideal.mul_top] using h
  rw [← neg_sub]
  exact neg_mem h'

/-- **`S` is the `I`-adic completion of `R` along `f`** (tex 2747–2748, 3728; definition): `f⁻¹(Jⁿ) = Iⁿ`
and `R → S/Jⁿ` is onto for every `n` (so `R/Iⁿ ≅ S/Jⁿ`), and `S` is `J`-adically complete. -/
structure IsAdicCompletionAlong (I : Ideal R) (J : Ideal S) (f : R →+* S) : Prop where
  comap_pow_eq : ∀ n : ℕ, (J ^ n).comap f = I ^ n
  surjective_mod : ∀ n : ℕ, Function.Surjective ((Ideal.Quotient.mk (J ^ n)).comp f)
  isAdicComplete : IsAdicComplete J S

namespace IsAdicCompletionAlong

variable {I : Ideal R} {J : Ideal S} {f : R →+* S} (h : IsAdicCompletionAlong I J f)
include h

/-- **Tex 2747–2748 (PROVED).** Density: every `y ∈ S` is `f x` modulo `Jⁿ`. -/
theorem exists_sub_mem (n : ℕ) (y : S) : ∃ x : R, y - f x ∈ J ^ n := by
  obtain ⟨x, hx⟩ := h.surjective_mod n (Ideal.Quotient.mk _ y)
  exact ⟨x, Ideal.Quotient.eq.mp hx.symm⟩

/-- **Tex 2747–2748 (PROVED construction).** The level isomorphisms `R/Iⁿ ≃+* S/Jⁿ` induced by `f`. -/
noncomputable def quotEquiv (n : ℕ) : R ⧸ I ^ n ≃+* S ⧸ J ^ n :=
  RingEquiv.ofBijective (Ideal.quotientMap (J ^ n) f (h.comap_pow_eq n).ge)
    ⟨Ideal.quotientMap_injective' (h.comap_pow_eq n).le, fun q => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
      obtain ⟨x, hx⟩ := h.exists_sub_mem n y
      exact ⟨Ideal.Quotient.mk _ x, by
        rw [Ideal.quotientMap_mk]; exact (Ideal.Quotient.eq.mpr hx).symm⟩⟩

/-- **Tex 2747–2748 (PROVED).** `quotEquiv n` sends the class of `x` to the class of `f x`. -/
theorem quotEquiv_mk (n : ℕ) (x : R) :
    h.quotEquiv n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (f x) := rfl

/-- **Tex 2747–2748 (PROVED).** The inverse of `quotEquiv n` on the class of `y ≡ f x (mod Jⁿ)`. -/
theorem quotEquiv_symm_mk_of_sub_mem {n : ℕ} {y : S} {x : R} (hx : y - f x ∈ J ^ n) :
    (h.quotEquiv n).symm (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ x := by
  rw [RingEquiv.symm_apply_eq, quotEquiv_mk]
  exact Ideal.Quotient.eq.mpr hx

/-- The compatible family `S → S/Jⁿ ≅ R/Iⁿ` (tex 2747–2748). -/
noncomputable def quotFamily (n : ℕ) : S →+* R ⧸ I ^ n :=
  ((h.quotEquiv n).symm : S ⧸ J ^ n →+* R ⧸ I ^ n).comp (Ideal.Quotient.mk (J ^ n))

/-- **Tex 2747–2748 (PROVED).** Value of `quotFamily`. -/
theorem quotFamily_apply (n : ℕ) (y : S) :
    h.quotFamily n y = (h.quotEquiv n).symm (Ideal.Quotient.mk _ y) := rfl

/-- **Tex 2747–2748 (PROVED).** The family `quotFamily` is compatible with the transition maps. -/
theorem quotFamily_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow I hle).comp (h.quotFamily n) = h.quotFamily m := by
  ext y
  obtain ⟨x, hx⟩ := h.exists_sub_mem n y
  have hxm : y - f x ∈ J ^ m := Ideal.pow_le_pow_right hle hx
  rw [RingHom.comp_apply, quotFamily_apply, quotFamily_apply, h.quotEquiv_symm_mk_of_sub_mem hx,
    h.quotEquiv_symm_mk_of_sub_mem hxm, Ideal.Quotient.factor_mk]

/-- The map `S → AdicCompletion I R` (universal property of the completion; tex 2747–2748). -/
noncomputable def toAdicCompletion : S →+* AdicCompletion I R :=
  AdicCompletion.liftRingHom I h.quotFamily h.quotFamily_compat

/-- **Tex 2747–2748 (PROVED).** Level `n` of `toAdicCompletion y` is the class of `y` in `S/Jⁿ ≅ R/Iⁿ`. -/
theorem evalₐ_toAdicCompletion (n : ℕ) (y : S) :
    AdicCompletion.evalₐ I n (h.toAdicCompletion y) =
      (h.quotEquiv n).symm (Ideal.Quotient.mk _ y) := by
  rw [toAdicCompletion, AdicCompletion.evalₐ_liftRingHom, quotFamily_apply]

/-- **Tex 2747–2748 (PROVED).** `toAdicCompletion (f x) = of x`. -/
theorem toAdicCompletion_apply (x : R) : h.toAdicCompletion (f x) = AdicCompletion.of I R x := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_toAdicCompletion, AdicCompletion.evalₐ_of]
  exact h.quotEquiv_symm_mk_of_sub_mem (by rw [sub_self]; exact zero_mem _)

/-- **Tex 2747–2748 (PROVED).** `toAdicCompletion` is injective (`S` is `J`-adically separated). -/
theorem toAdicCompletion_injective : Function.Injective h.toAdicCompletion := by
  have := h.isAdicComplete
  rw [injective_iff_map_eq_zero]
  intro y hy
  refine IsHausdorff.haus' (I := J) y fun n => ?_
  have h1 := congrArg (AdicCompletion.evalₐ I n) hy
  rw [evalₐ_toAdicCompletion, map_zero, RingEquiv.symm_apply_eq, map_zero,
    Ideal.Quotient.eq_zero_iff_mem] at h1
  rw [SModEq.zero]
  simpa [smul_eq_mul, Ideal.mul_top] using h1

/-- **Tex 2747–2748 (PROVED).** `toAdicCompletion` is surjective (`S` is `J`-adically precomplete). -/
theorem toAdicCompletion_surjective : Function.Surjective h.toAdicCompletion := by
  have := h.isAdicComplete
  intro c
  choose x hx using fun n => Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n c)
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      f (x m) ≡ f (x n) [SMOD (J ^ m • ⊤ : Submodule S S)] := by
    intro m n hle
    have h1 := factorPow_evalₐ I hle c
    rw [← hx n, ← hx m, Ideal.Quotient.factor_mk, Ideal.Quotient.eq] at h1
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    have h2 : f (x n - x m) ∈ J ^ m := by
      rw [← Ideal.mem_comap, h.comap_pow_eq]; exact h1
    rw [← neg_sub, ← map_sub]
    exact neg_mem h2
  obtain ⟨y, hy⟩ := IsPrecomplete.prec' _ hcauchy
  refine ⟨y, AdicCompletion.ext_evalₐ fun n => ?_⟩
  rw [evalₐ_toAdicCompletion, ← hx n]
  apply h.quotEquiv_symm_mk_of_sub_mem
  have h1 := hy n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  rw [← neg_sub]
  exact neg_mem h1

/-- **The completion isomorphism** (tex 2747–2748; `PROVED` construction):
`AdicCompletion I R ≃+* S`. -/
noncomputable def adicCompletionEquiv : AdicCompletion I R ≃+* S :=
  (RingEquiv.ofBijective h.toAdicCompletion
    ⟨h.toAdicCompletion_injective, h.toAdicCompletion_surjective⟩).symm

/-- **Tex 2747–2748 (PROVED).** The completion isomorphism sends the image of `x` to `f x`. -/
theorem adicCompletionEquiv_of (x : R) :
    h.adicCompletionEquiv (AdicCompletion.of I R x) = f x := by
  rw [adicCompletionEquiv, RingEquiv.symm_apply_eq]
  exact (h.toAdicCompletion_apply x).symm

/-- **Tex 2747–2748 (PROVED).** Modulo `Jⁿ`, the completion isomorphism is level `n` followed by
`R/Iⁿ ≅ S/Jⁿ`. -/
theorem mk_adicCompletionEquiv (n : ℕ) (c : AdicCompletion I R) :
    Ideal.Quotient.mk (J ^ n) (h.adicCompletionEquiv c) =
      h.quotEquiv n (AdicCompletion.evalₐ I n c) := by
  obtain ⟨y, rfl⟩ := h.toAdicCompletion_surjective c
  have hy : h.adicCompletionEquiv (h.toAdicCompletion y) = y := by
    rw [adicCompletionEquiv, RingEquiv.symm_apply_eq]; rfl
  rw [hy, evalₐ_toAdicCompletion, RingEquiv.apply_symm_apply]

end IsAdicCompletionAlong

end Generic

/-! ## `𝒪 = \widehat{Λ_{(2)}}` -/

/-- **`𝒪` is the two-adic completion of `Λ_{(2)}` along `lamTwoToO`** (tex 2747–2748, 3728; `PROVED`):
`lamTwoToO⁻¹((2)ⁿ) = (2)ⁿ`, `Λ_{(2)} → 𝒪/(2)ⁿ` is onto, and `𝒪` is `2`-adically complete (RC7). -/
theorem isAdicCompletionAlong_lamTwoToO :
    IsAdicCompletionAlong (Ideal.span {(2 : LambdaTwo)}) (Ideal.span {(2 : OO)}) lamTwoToO where
  comap_pow_eq n := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, comap_lamTwoToO_span_two_pow]
  surjective_mod n q := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ideal.span_singleton_pow]
    obtain ⟨x, hx⟩ := exists_sub_lamTwoToO_mem n y
    exact ⟨x, (Ideal.Quotient.eq.mpr hx).symm⟩
  isAdicComplete := inferInstance

/-- **`𝒪 = \widehat{Λ_{(2)}}`, bundled** (tex 2747–2748, 3728; `PROVED`): `lamTwoToO : Λ_{(2)} → 𝒪` is
injective; for every `n` it induces an isomorphism `Λ_{(2)}/2ⁿ ≃+* 𝒪/2ⁿ` (`x ↦ lamTwoToO x`); `𝒪` is
`2`-adically complete and separated; and `Λ_{(2)}` is dense in `𝒪`. This characterizes `𝒪` as the
two-adic completion of `Λ_{(2)}`. -/
theorem OO_isCompletion_lambdaTwo :
    Function.Injective lamTwoToO ∧
      (∀ n : ℕ, ∃ e : LambdaTwo ⧸ Ideal.span {(2 : LambdaTwo) ^ n} ≃+* OO ⧸ Ideal.span {(2 : OO) ^ n},
        ∀ x : LambdaTwo, e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (lamTwoToO x)) ∧
      IsAdicComplete (Ideal.span {(2 : OO)}) OO ∧
      (∀ (n : ℕ) (y : OO), ∃ x : LambdaTwo, y - lamTwoToO x ∈ Ideal.span {(2 : OO) ^ n}) :=
  ⟨lamTwoToO_injective, fun n => ⟨quotTwoPowLambdaTwoEquiv n, quotTwoPowLambdaTwoEquiv_mk n⟩,
    inferInstance, exists_sub_lamTwoToO_mem⟩

/-- **The explicit isomorphism `\widehat{Λ_{(2)}} ≅ 𝒪`** (tex 2747–2748, 3728; `PROVED` construction):
Mathlib's two-adic completion of `Λ_{(2)}` is isomorphic to RC7's `OO`. -/
noncomputable def adicCompletionLambdaTwoEquiv :
    AdicCompletion (Ideal.span {(2 : LambdaTwo)}) LambdaTwo ≃+* OO :=
  isAdicCompletionAlong_lamTwoToO.adicCompletionEquiv

/-- **Tex 2747–2748, 3728 (PROVED).** `\widehat{Λ_{(2)}} ≅ 𝒪` sends the image of `x ∈ Λ_{(2)}` to
`lamTwoToO x`. -/
theorem adicCompletionLambdaTwoEquiv_of (x : LambdaTwo) :
    adicCompletionLambdaTwoEquiv (AdicCompletion.of _ LambdaTwo x) = lamTwoToO x :=
  isAdicCompletionAlong_lamTwoToO.adicCompletionEquiv_of x

/-- **Tex 2747–2748, 3728 (PROVED).** Modulo `(2)ⁿ`, `\widehat{Λ_{(2)}} ≅ 𝒪` is level `n` of the
completion followed by `Λ_{(2)}/(2)ⁿ ≅ 𝒪/(2)ⁿ`. -/
theorem mk_adicCompletionLambdaTwoEquiv (n : ℕ)
    (c : AdicCompletion (Ideal.span {(2 : LambdaTwo)}) LambdaTwo) :
    Ideal.Quotient.mk (Ideal.span {(2 : OO)} ^ n) (adicCompletionLambdaTwoEquiv c) =
      Ideal.quotientMap _ lamTwoToO (isAdicCompletionAlong_lamTwoToO.comap_pow_eq n).ge
        (AdicCompletion.evalₐ _ n c) :=
  isAdicCompletionAlong_lamTwoToO.mk_adicCompletionEquiv n c

/-! ## Non-vacuity -/

/-- Non-vacuity: `1 ∈ Λ_{(2)}` is not divisible by `2` in `𝒪`, `2` is; `t⁻¹ ∈ 𝒪` is the image of
`1/t ∈ Λ_{(2)}`; and the completion isomorphism sends `2` to `2`. -/
example : lamTwoToO 1 ∉ Ideal.span {(2 : OO) ^ 1} ∧ lamTwoToO 2 ∈ Ideal.span {(2 : OO) ^ 1} ∧
    lamTwoToO (IsLocalization.mk' LambdaTwo (1 : Lambda)
      (⟨PowerSeries.X ^ 1, pow_X_mem_primeCompl 1⟩ : (Ideal.span {(2 : Lambda)}).primeCompl)) = tInv ∧
    adicCompletionLambdaTwoEquiv (AdicCompletion.of _ LambdaTwo 2) = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [map_one, pow_one, Ideal.mem_span_singleton]
    exact fun h => not_isUnit_two_OO (isUnit_of_dvd_one h)
  · rw [lamTwoToO_two, pow_one]
    exact Ideal.mem_span_singleton_self 2
  · rw [lamTwoToO_mk'_pow_X, map_one, mul_one, pow_one]
  · rw [adicCompletionLambdaTwoEquiv_of, lamTwoToO_two]

/-- Non-vacuity: the reduction of `t⁻¹ ∈ 𝒪` modulo `2ⁿ` is hit by `Λ_{(2)}` (a genuinely non-power-series
Laurent series). -/
example (n : ℕ) : ∃ x : LambdaTwo, proj n (lamTwoToO x) = HahnSeries.single (-1) 1 :=
  surjective_proj_comp_lamTwoToO n _

end ZInQ.Manuscript.RC.Rings
