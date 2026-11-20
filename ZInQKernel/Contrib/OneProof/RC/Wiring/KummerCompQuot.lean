import ZInQKernel.Contrib.RC53Assist.CentralUniversal.Arithmetic

/-!
# Theorem 5.3, Lane RC37: elements of the coefficient quotient `C ⊗ ℚ₂/ℤ₂`

For a cochain complex `C` of `ℤ₂`-modules with torsion-free terms, the RC53 group's coefficient
quotient `coefficientQuotientComplex C` is the cokernel (in complexes) of the canonical
coefficient map `C → C ⊗ ℚ₂`. This file gives its elements and maps out of it concretely, as
needed for the coefficient comparison of the compact Kummer complex (manuscript
`diophantine_zq.tex`, the universal-coefficient step `C_K ⊗ ℚ₂/ℤ₂`, tex 4005–4014):

* `kc_tensor_normal`: every element of `ℚ₂ ⊗_{ℤ₂} X` is `2^{-m} ⊗ x`;
* `kcFrac m x = [x / 2^m]`, the class of `2^{-m} ⊗ x` in degree `n` of the quotient:
  every element of the quotient is such a class (`kcFrac_surjective`), the class vanishes exactly
  when `x ∈ 2^m C` (`kcFrac_eq_zero_iff`), the differential is `d [x/2^m] = [dx/2^m]`
  (`kcFrac_d`), and `[2^j x / 2^{m+j}] = [x/2^m]` (`kcFrac_shift`);
* `kcDesc`: a morphism from the quotient, read as a complex of abelian groups
  (`integerCoefficientComplex`), to any complex of abelian groups, from additive maps on the
  rational terms that kill the integral image and commute with the differentials
  (`kcDesc_apply`: it is the given map on every class).

Kinds: definitions and PROVED.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Manuscript.RC

open CategoryTheory CategoryTheory.Limits
open ZInQ.Manuscript.RC53Assist.CentralUniversal
open scoped TensorProduct

/-! ### Two-adic denominators -/

/-- Every two-adic number has a two-power multiple in `ℤ₂`. Kind: PROVED. -/
theorem kc_exists_two_pow_mul_norm_le (q : ℚ_[2]) : ∃ m : ℕ, ‖(2 : ℚ_[2]) ^ m * q‖ ≤ 1 := by
  by_cases hq : q = 0
  · exact ⟨0, by simp [hq]⟩
  refine ⟨(-q.valuation).toNat, ?_⟩
  have hn : -q.valuation ≤ ((-q.valuation).toNat : ℤ) := Int.self_le_toNat _
  rw [norm_mul, show ((2 : ℚ_[2]) ^ (-q.valuation).toNat) =
      ((2 : ℕ) : ℚ_[2]) ^ (-q.valuation).toNat by norm_num, Padic.norm_p_pow,
    Padic.norm_eq_zpow_neg_valuation hq, ← zpow_add₀ (by norm_num)]
  exact zpow_le_one_of_nonpos₀ (by norm_num) (by omega)

/-- `2^m · 2^{-m} = 1` in `ℚ₂`. Kind: PROVED. -/
theorem kc_two_pow_mul_inv (m : ℕ) : (2 : ℚ_[2]) ^ m * ((2 : ℚ_[2]) ^ m)⁻¹ = 1 :=
  mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero)

/-- The tensor `q ⊗ x` equals `2^{-m} ⊗ a x` for `a = 2^m q ∈ ℤ₂`. Kind: PROVED. -/
theorem kc_tmul_eq_inv_two_pow {X : Type} [AddCommGroup X] [Module ℤ_[2] X] (q : ℚ_[2])
    (m : ℕ) (h : ‖(2 : ℚ_[2]) ^ m * q‖ ≤ 1) (x : X) :
    (q ⊗ₜ[ℤ_[2]] x : ℚ_[2] ⊗[ℤ_[2]] X) =
      ((2 : ℚ_[2]) ^ m)⁻¹ ⊗ₜ[ℤ_[2]] (Padic.lift ((2 : ℚ_[2]) ^ m * q) h • x) := by
  rw [← TensorProduct.smul_tmul]
  congr 1
  change q = ((Padic.lift ((2 : ℚ_[2]) ^ m * q) h : ℤ_[2]) : ℚ_[2]) * ((2 : ℚ_[2]) ^ m)⁻¹
  rw [PadicInt.coe_lift, mul_comm ((2 : ℚ_[2]) ^ m) q, mul_assoc, kc_two_pow_mul_inv, mul_one]

/-- `2^{-m} ⊗ x = 2^{-(m+j)} ⊗ 2^j x`. Kind: PROVED. -/
theorem kc_inv_two_pow_tmul_shift {X : Type} [AddCommGroup X] [Module ℤ_[2] X] (m j : ℕ)
    (x : X) :
    (((2 : ℚ_[2]) ^ m)⁻¹ ⊗ₜ[ℤ_[2]] x : ℚ_[2] ⊗[ℤ_[2]] X) =
      ((2 : ℚ_[2]) ^ (m + j))⁻¹ ⊗ₜ[ℤ_[2]] ((2 : ℤ_[2]) ^ j • x) := by
  rw [← TensorProduct.smul_tmul]
  congr 1
  change ((2 : ℚ_[2]) ^ m)⁻¹ = (((2 : ℤ_[2]) ^ j : ℤ_[2]) : ℚ_[2]) * ((2 : ℚ_[2]) ^ (m + j))⁻¹
  rw [PadicInt.coe_pow, show ((2 : ℤ_[2]) : ℚ_[2]) = 2 from rfl, pow_add, mul_inv,
    mul_comm (((2 : ℚ_[2]) ^ m)⁻¹), ← mul_assoc, kc_two_pow_mul_inv, one_mul]

/-- **Normal form**: every element of `ℚ₂ ⊗_{ℤ₂} X` is `2^{-m} ⊗ x`. Kind: PROVED. -/
theorem kc_tensor_normal {X : Type} [AddCommGroup X] [Module ℤ_[2] X]
    (z : ℚ_[2] ⊗[ℤ_[2]] X) :
    ∃ (m : ℕ) (x : X), z = ((2 : ℚ_[2]) ^ m)⁻¹ ⊗ₜ[ℤ_[2]] x := by
  induction z using TensorProduct.inductionOn with
  | tmul q x =>
    obtain ⟨m, hm⟩ := kc_exists_two_pow_mul_norm_le q
    exact ⟨m, _, kc_tmul_eq_inv_two_pow q m hm x⟩
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨m₁, x₁, rfl⟩ := h₁
    obtain ⟨m₂, x₂, rfl⟩ := h₂
    refine ⟨m₁ + m₂, (2 : ℤ_[2]) ^ m₂ • x₁ + (2 : ℤ_[2]) ^ m₁ • x₂, ?_⟩
    rw [TensorProduct.tmul_add, ← kc_inv_two_pow_tmul_shift, add_comm m₁ m₂,
      ← kc_inv_two_pow_tmul_shift]

/-! ### The coefficient quotient in each degree -/

section Quot

variable (C : CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ)

/-- The element `q ⊗ x` of `C ⊗ ℚ₂` in degree `n`. Kind: definition. -/
abbrev kcTmul {n : ℤ} (q : ℚ_[2]) (x : C.X n) : (rationalCoefficientComplex C).X n :=
  (q ⊗ₜ[ℤ_[2]] x : ℚ_[2] ⊗[ℤ_[2]] C.X n)

/-- The coefficient map is `x ↦ 1 ⊗ x`. Kind: PROVED. -/
theorem kc_coefficientMap_apply (n : ℤ) (x : C.X n) :
    ((coefficientMap C).f n).hom x = kcTmul C 1 x :=
  rfl

/-- The differential of `C ⊗ ℚ₂` on `q ⊗ x`. Kind: PROVED. -/
theorem kc_rat_d_tmul (n n' : ℤ) (q : ℚ_[2]) (x : C.X n) :
    ((rationalCoefficientComplex C).d n n').hom (kcTmul C q x) =
      kcTmul C q ((C.d n n').hom x) :=
  rfl

/-- Every element of `C ⊗ ℚ₂` in degree `n` is `2^{-m} ⊗ x`. Kind: PROVED. -/
theorem kc_rat_normal (n : ℤ) (z : (rationalCoefficientComplex C).X n) :
    ∃ (m : ℕ) (x : C.X n), z = kcTmul C ((2 : ℚ_[2]) ^ m)⁻¹ x :=
  kc_tensor_normal (X := C.X n) z

/-- The projection `C ⊗ ℚ₂ → C ⊗ ℚ₂/ℤ₂` in degree `n`. Kind: definition. -/
abbrev kcPi (n : ℤ) :
    (rationalCoefficientComplex C).X n →ₗ[ℤ_[2]] (coefficientQuotientComplex C).X n :=
  ((cokernel.π (coefficientMap C)).f n).hom

/-- The projection commutes with the differentials. Kind: PROVED. -/
theorem kcPi_d (n n' : ℤ) (z : (rationalCoefficientComplex C).X n) :
    ((coefficientQuotientComplex C).d n n').hom (kcPi C n z) =
      kcPi C n' (((rationalCoefficientComplex C).d n n').hom z) := by
  have h := congrArg (fun f => f.hom z) ((cokernel.π (coefficientMap C)).comm n n')
  exact h

variable [∀ n : ℤ, Module.IsTorsionFree ℤ_[2] (C.X n)]

/-- The coefficient sequence is short exact in every degree. Kind: PROVED. -/
theorem kc_degreewise_shortExact (n : ℤ) :
    ((coefficientSequence C).map (HomologicalComplex.eval _ _ n)).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (coefficientSequence_shortExact C) n

/-- The projection is surjective in every degree. Kind: PROVED. -/
theorem kcPi_surjective (n : ℤ) : Function.Surjective (kcPi C n) :=
  (kc_degreewise_shortExact C n).moduleCat_surjective_g

/-- The kernel of the projection is the integral image. Kind: PROVED. -/
theorem kcPi_eq_zero_iff (n : ℤ) (z : (rationalCoefficientComplex C).X n) :
    kcPi C n z = 0 ↔ ∃ x : C.X n, kcTmul C 1 x = z := by
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (kc_degreewise_shortExact C n).exact
  exact hex z

/-- The coefficient map is injective (torsion-free terms). Kind: PROVED. -/
theorem kc_coefficientMap_injective (n : ℤ) :
    Function.Injective (fun x : C.X n => kcTmul C 1 x) :=
  (kc_degreewise_shortExact C n).moduleCat_injective_f

/-- **The class `[x / 2^m]`** of `2^{-m} ⊗ x` in `C ⊗ ℚ₂/ℤ₂`, degree `n`. Kind: definition. -/
def kcFrac {n : ℤ} (m : ℕ) (x : C.X n) : (coefficientQuotientComplex C).X n :=
  kcPi C n (kcTmul C ((2 : ℚ_[2]) ^ m)⁻¹ x)

/-- Every element of `C ⊗ ℚ₂/ℤ₂` is a class `[x / 2^m]`. Kind: PROVED. -/
theorem kcFrac_surjective (n : ℤ) (y : (coefficientQuotientComplex C).X n) :
    ∃ (m : ℕ) (x : C.X n), kcFrac C m x = y := by
  obtain ⟨z, rfl⟩ := kcPi_surjective C n y
  obtain ⟨m, x, rfl⟩ := kc_rat_normal C n z
  exact ⟨m, x, rfl⟩

omit [∀ n : ℤ, Module.IsTorsionFree ℤ_[2] (C.X n)] in
/-- `[x/2^m] + [x'/2^m] = [(x + x')/2^m]`. Kind: PROVED. -/
theorem kcFrac_add {n : ℤ} (m : ℕ) (x x' : C.X n) :
    kcFrac C m x + kcFrac C m x' = kcFrac C m (x + x') := by
  unfold kcFrac
  rw [← map_add, kcTmul, kcTmul, kcTmul, TensorProduct.tmul_add]
  rfl

omit [∀ n : ℤ, Module.IsTorsionFree ℤ_[2] (C.X n)] in
/-- `[x/2^m] - [x'/2^m] = [(x - x')/2^m]`. Kind: PROVED. -/
theorem kcFrac_sub {n : ℤ} (m : ℕ) (x x' : C.X n) :
    kcFrac C m x - kcFrac C m x' = kcFrac C m (x - x') := by
  unfold kcFrac
  rw [← map_sub, kcTmul, kcTmul, kcTmul, TensorProduct.tmul_sub]
  rfl

omit [∀ n : ℤ, Module.IsTorsionFree ℤ_[2] (C.X n)] in
/-- `[0/2^m] = 0`. Kind: PROVED. -/
theorem kcFrac_zero {n : ℤ} (m : ℕ) : kcFrac C m (0 : C.X n) = 0 := by
  have h : kcTmul C ((2 : ℚ_[2]) ^ m)⁻¹ (0 : C.X n) = 0 := TensorProduct.tmul_zero _ _
  unfold kcFrac
  rw [h, map_zero]

omit [∀ n : ℤ, Module.IsTorsionFree ℤ_[2] (C.X n)] in
/-- `[2^j x / 2^{m+j}] = [x/2^m]`. Kind: PROVED. -/
theorem kcFrac_shift {n : ℤ} (m j : ℕ) (x : C.X n) :
    kcFrac C (m + j) ((2 : ℤ_[2]) ^ j • x) = kcFrac C m x := by
  unfold kcFrac
  rw [kcTmul, kcTmul, ← kc_inv_two_pow_tmul_shift]

/-- `[x / 1] = 0`. Kind: PROVED. -/
theorem kcFrac_zero_level {n : ℤ} (x : C.X n) : kcFrac C 0 x = 0 := by
  unfold kcFrac
  rw [(kcPi_eq_zero_iff C n _).2 ⟨x, by simp⟩]

/-- **`[x/2^m] = 0` exactly when `x ∈ 2^m C`.** Kind: PROVED. -/
theorem kcFrac_eq_zero_iff {n : ℤ} (m : ℕ) (x : C.X n) :
    kcFrac C m x = 0 ↔ ∃ w : C.X n, x = (2 : ℤ_[2]) ^ m • w := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := (kcPi_eq_zero_iff C n _).1 h
    refine ⟨w, kc_coefficientMap_injective C n ?_⟩
    have h2 : (2 : ℤ_[2]) ^ m • kcTmul C 1 w =
        (2 : ℤ_[2]) ^ m • kcTmul C ((2 : ℚ_[2]) ^ m)⁻¹ x := congrArg _ hw
    change (1 : ℚ_[2]) ⊗ₜ[ℤ_[2]] x = (1 : ℚ_[2]) ⊗ₜ[ℤ_[2]] ((2 : ℤ_[2]) ^ m • w)
    change (2 : ℤ_[2]) ^ m • ((1 : ℚ_[2]) ⊗ₜ[ℤ_[2]] w) =
        (2 : ℤ_[2]) ^ m • (((2 : ℚ_[2]) ^ m)⁻¹ ⊗ₜ[ℤ_[2]] x) at h2
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul'] at h2
    rw [← TensorProduct.smul_tmul, h2]
    congr 1
    change (1 : ℚ_[2]) = (((2 : ℤ_[2]) ^ m : ℤ_[2]) : ℚ_[2]) * ((2 : ℚ_[2]) ^ m)⁻¹
    rw [PadicInt.coe_pow, show ((2 : ℤ_[2]) : ℚ_[2]) = 2 from rfl, kc_two_pow_mul_inv]
  · rintro ⟨w, rfl⟩
    have h := kcFrac_shift C 0 m w
    rw [zero_add] at h
    rw [h, kcFrac_zero_level]

omit [∀ n : ℤ, Module.IsTorsionFree ℤ_[2] (C.X n)] in
/-- **`d [x/2^m] = [dx/2^m]`.** Kind: PROVED. -/
theorem kcFrac_d (n n' : ℤ) (m : ℕ) (x : C.X n) :
    ((coefficientQuotientComplex C).d n n').hom (kcFrac C m x) =
      kcFrac C m ((C.d n n').hom x) := by
  unfold kcFrac
  rw [kcPi_d, kc_rat_d_tmul]

/-- A class `[x/2^m]` is a cocycle exactly when `dx ∈ 2^m C`. Kind: PROVED. -/
theorem kcFrac_d_eq_zero_iff (n n' : ℤ) (m : ℕ) (x : C.X n) :
    ((coefficientQuotientComplex C).d n n').hom (kcFrac C m x) = 0 ↔
      ∃ w : C.X n', (C.d n n').hom x = (2 : ℤ_[2]) ^ m • w := by
  rw [kcFrac_d, kcFrac_eq_zero_iff]

end Quot

/-! ### Maps out of the quotient, as complexes of abelian groups -/

section Desc

/-- An additive map out of a `ℤ₂`-module, as a morphism of abelian groups out of its
restriction of scalars. Kind: definition. -/
def kcIntHom {A : ModuleCat.{0} ℤ_[2]} {B : ModuleCat.{0} ℤ} (g : A →+ B) :
    (ModuleCat.restrictScalars (Int.castRingHom ℤ_[2])).obj A ⟶ B :=
  letI : Module ℤ A := Module.compHom A (Int.castRingHom ℤ_[2])
  ModuleCat.ofHom (X := A) (Y := B)
    { toFun := fun a => g a
      map_add' := fun a b => g.map_add a b
      map_smul' := fun c a => by
        have h1 : g ((c : ℤ_[2]) • a) = c • g a := by
          rw [Int.cast_smul_eq_zsmul, map_zsmul]
        exact h1.trans (int_smul_eq_zsmul _ c (g a)).symm }

/-- `kcIntHom` on elements. Kind: PROVED. -/
theorem kcIntHom_apply {A : ModuleCat.{0} ℤ_[2]} {B : ModuleCat.{0} ℤ} (g : A →+ B) (a : A) :
    (kcIntHom g).hom a = g a :=
  rfl

variable (C : CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ) [∀ n : ℤ, Module.IsTorsionFree ℤ_[2] (C.X n)]
  (P : CochainComplex (ModuleCat.{0} ℤ) ℤ)
  (Γ : ∀ n : ℤ, (rationalCoefficientComplex C).X n →+ P.X n)
  (hΓ0 : ∀ (n : ℤ) (x : C.X n), Γ n (kcTmul C 1 x) = 0)

include hΓ0 in
/-- The map vanishes on the kernel of the projection. Kind: PROVED. -/
theorem kc_ker_le (n : ℤ) :
    ((kcPi C n).toAddMonoidHom).ker ≤ (Γ n).ker := by
  intro z hz
  obtain ⟨x, rfl⟩ := (kcPi_eq_zero_iff C n z).1 hz
  exact hΓ0 n x

/-- The degree-`n` component of the descended map, on the quotient. Kind: definition. -/
def kcDescFun (n : ℤ) : (coefficientQuotientComplex C).X n →+ P.X n :=
  (QuotientAddGroup.lift ((kcPi C n).toAddMonoidHom).ker (Γ n) (kc_ker_le C P Γ hΓ0 n)).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective (kcPi C n).toAddMonoidHom
      (kcPi_surjective C n)).symm.toAddMonoidHom

/-- The descended map on a class. Kind: PROVED. -/
theorem kcDescFun_apply (n : ℤ) (z : (rationalCoefficientComplex C).X n) :
    kcDescFun C P Γ hΓ0 n (kcPi C n z) = Γ n z := by
  dsimp only [kcDescFun, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  have he : (QuotientAddGroup.quotientKerEquivOfSurjective (kcPi C n).toAddMonoidHom
      (kcPi_surjective C n)).symm (kcPi C n z) = QuotientAddGroup.mk z := by
    apply (QuotientAddGroup.quotientKerEquivOfSurjective _ (kcPi_surjective C n)).injective
    rw [AddEquiv.apply_symm_apply]
    rfl
  rw [he]
  rfl

/-- The descended maps commute with the differentials. Kind: PROVED. -/
theorem kcDescFun_comm
    (hΓd : ∀ (n : ℤ) (z : (rationalCoefficientComplex C).X n),
      (P.d n (n + 1)).hom (Γ n z) = Γ (n + 1) (((rationalCoefficientComplex C).d n (n + 1)).hom z))
    (i j : ℤ) (y : (coefficientQuotientComplex C).X i) :
    (P.d i j).hom (kcDescFun C P Γ hΓ0 i y) =
      kcDescFun C P Γ hΓ0 j (((coefficientQuotientComplex C).d i j).hom y) := by
  obtain ⟨z, rfl⟩ := kcPi_surjective C i y
  by_cases hij : i + 1 = j
  · subst hij
    rw [kcDescFun_apply, kcPi_d, kcDescFun_apply, hΓd]
  · have h1 : P.d i j = 0 := P.shape i j hij
    have h2 : (rationalCoefficientComplex C).d i j = 0 :=
      (rationalCoefficientComplex C).shape i j hij
    rw [kcDescFun_apply, kcPi_d, h1, h2]
    simp

/-- **The descended morphism** `C ⊗ ℚ₂/ℤ₂ → P` of complexes of abelian groups.
Kind: definition. -/
def kcDesc
    (hΓd : ∀ (n : ℤ) (z : (rationalCoefficientComplex C).X n),
      (P.d n (n + 1)).hom (Γ n z) =
        Γ (n + 1) (((rationalCoefficientComplex C).d n (n + 1)).hom z)) :
    integerCoefficientComplex (coefficientQuotientComplex C) ⟶ P where
  f n := kcIntHom (kcDescFun C P Γ hΓ0 n)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    change (P.d i j).hom (kcDescFun C P Γ hΓ0 i y) =
      kcDescFun C P Γ hΓ0 j (((coefficientQuotientComplex C).d i j).hom y)
    exact kcDescFun_comm C P Γ hΓ0 hΓd i j y

/-- **The descended morphism on a class** `π(z)`. Kind: PROVED. -/
theorem kcDesc_apply
    (hΓd : ∀ (n : ℤ) (z : (rationalCoefficientComplex C).X n),
      (P.d n (n + 1)).hom (Γ n z) = Γ (n + 1) (((rationalCoefficientComplex C).d n (n + 1)).hom z))
    (n : ℤ) (z : (rationalCoefficientComplex C).X n) :
    ((kcDesc C P Γ hΓ0 hΓd).f n).hom (kcPi C n z) = Γ n z :=
  kcDescFun_apply C P Γ hΓ0 n z

/-- The descended morphism on `[x/2^m]`. Kind: PROVED. -/
theorem kcDesc_frac
    (hΓd : ∀ (n : ℤ) (z : (rationalCoefficientComplex C).X n),
      (P.d n (n + 1)).hom (Γ n z) = Γ (n + 1) (((rationalCoefficientComplex C).d n (n + 1)).hom z))
    (n : ℤ) (m : ℕ) (x : C.X n) :
    ((kcDesc C P Γ hΓ0 hΓd).f n).hom (kcFrac C m x) = Γ n (kcTmul C ((2 : ℚ_[2]) ^ m)⁻¹ x) :=
  kcDescFun_apply C P Γ hΓ0 n _

end Desc

end ZInQ.Manuscript.RC
