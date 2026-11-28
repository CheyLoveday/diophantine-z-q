import ZInQKernel.Contrib.OneProof.CMHeight62Full.LatticeBasis

/-!
# Finite generation of the pole lattices `M_n`

Let `R` be a discrete valuation ring with uniformizer `ϖ`, `F` a field over `R`, `A` an
`R`-algebra with fraction field `Ω`, and `ρ : A →ₐ[R] R` a section whose kernel is principal,
`ker ρ = (t)`. Let `w` be a valuation on `Ω` that is `≤ 1` on `A`, `V` an `F`-subspace of `Ω`
and `n : ℕ`. The lattice `M_n = V ∩ 𝒪_w` is the set of `x ∈ V` with `w x ≤ 1`.

`exists_finite_span_of_poleBound` shows that `M_n` lies in the span of finitely many elements of
`Ω` over the `w`-integral elements of `F` (in fact over the image of `R`). This is the finiteness
hypothesis `ht` of `exists_residuallyIndependent_basis` and `exists_lattice_basis`
(`LatticeBasis.lean`); `exists_lattice_basis_of_poleBound` combines the two.

The Hartogs property of `A` and the description of the height-one primes containing `ϖ` enter as
hypotheses (`hhart`, `hcases`), in the shape of the depth-two Hartogs lemma.

## Proof

* `A = R + tA`, since `a - ρ(a) ∈ ker ρ = (t)`; by induction `A = R + R t + ⋯ + R tᵐ⁻¹ + tᵐ A`,
  so `A ⧸ (tᵐ)` is a finite `R`-module (`finite_quotient_span_pow`). No freeness is needed.
* If `t ≠ 0`: for `x ∈ M_n`, `x tⁿ` lies in `A_𝔮` for every height-one prime `𝔮`. If `ϖ ∈ 𝔮` then
  `𝔮 = (ϖ)` and `w x ≤ 1` applies; if `t ∈ 𝔮` then `𝔮 = (t)` (a nonzero prime below a height-one
  prime) and the pole bound applies; otherwise `x` is regular at `𝔮`. Hence `x tⁿ ∈ A` by
  Hartogs. The `R`-module `N = {a ∈ A : a / tⁿ ∈ M_n}` embeds into `A ⧸ (tⁿ⁺¹)`: if
  `a = c tⁿ⁺¹` then `a / tⁿ = t c` vanishes by `hzero`. So `N` is finitely generated
  (`R` Noetherian), and the images of its generators span `M_n`.
* If `t = 0`: `ρ` is injective, so `A = R`; for `x ∈ M_n`, `s x = r` with `s ∉ (ϖ)`, and `ρ s` is a
  unit of `R`, so `x ∈ R`, and `M_n ⊆ R · 1`.

Only Mathlib and `LatticeBasis.lean` are used.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open IsLocalRing Module

section Quotient

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]

/-- `A = R + R t + ⋯ + R tᵐ⁻¹ + tᵐ A` when `ρ : A →ₐ[R] R` has kernel `(t)`. -/
theorem exists_mem_span_pow_add_mul (ρ : A →ₐ[R] R) {t : A}
    (hker : RingHom.ker ρ = Ideal.span {t}) (m : ℕ) (a : A) :
    ∃ s ∈ Submodule.span R (Set.range fun i : Fin m => t ^ (i : ℕ)), ∃ b : A,
      a = s + t ^ m * b := by
  induction m with
  | zero => exact ⟨0, Submodule.zero_mem _, a, by rw [pow_zero, one_mul, zero_add]⟩
  | succ m ih =>
    obtain ⟨s, hs, b, hb⟩ := ih
    have hk : b - algebraMap R A (ρ b) ∈ RingHom.ker ρ := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        sub_self]
    rw [hker, Ideal.mem_span_singleton'] at hk
    obtain ⟨c, hc⟩ := hk
    have hmono : Submodule.span R (Set.range fun i : Fin m => t ^ (i : ℕ)) ≤
        Submodule.span R (Set.range fun i : Fin (m + 1) => t ^ (i : ℕ)) :=
      Submodule.span_mono (by
        rintro _ ⟨i, rfl⟩
        exact ⟨i.castSucc, rfl⟩)
    refine ⟨s + ρ b • t ^ m, Submodule.add_mem _ (hmono hs)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.last m, rfl⟩)), c, ?_⟩
    rw [hb, Algebra.smul_def, pow_succ]
    linear_combination (-(t ^ m)) * hc

/-- `A ⧸ (tᵐ)` is a finite `R`-module when `ρ : A →ₐ[R] R` has kernel `(t)`. -/
theorem finite_quotient_span_pow (ρ : A →ₐ[R] R) {t : A}
    (hker : RingHom.ker ρ = Ideal.span {t}) (m : ℕ) :
    Module.Finite R (A ⧸ Ideal.span {t ^ m}) := by
  have : Module.Finite R (Submodule.span R (Set.range fun i : Fin m => t ^ (i : ℕ))) :=
    Module.Finite.span_of_finite R (Set.finite_range _)
  refine Module.Finite.of_surjective ((Ideal.Quotient.mkₐ R (Ideal.span {t ^ m})).toLinearMap.comp
    (Submodule.span R (Set.range fun i : Fin m => t ^ (i : ℕ))).subtype) fun q => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨s, hs, b, rfl⟩ := exists_mem_span_pow_add_mul ρ hker m a
  refine ⟨⟨s, hs⟩, ?_⟩
  change Ideal.Quotient.mk _ s = Ideal.Quotient.mk _ (s + t ^ m * b)
  rw [Ideal.Quotient.eq]
  have h : s - (s + t ^ m * b) = t ^ m * (-b) := by ring
  rw [h]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end Quotient

/-- A height-one prime containing a nonzero element `t` that generates a prime ideal is `(t)`. -/
theorem eq_span_singleton_of_height_eq_one {A : Type*} [CommRing A] [IsDomain A] {t : A}
    (ht0 : t ≠ 0) (htp : (Ideal.span {t}).IsPrime) (𝔮 : Ideal A) (hp : 𝔮.IsPrime)
    (h1 : 𝔮.height = 1) (ht : t ∈ 𝔮) : 𝔮 = Ideal.span {t} := by
  by_contra hne
  have hlt : Ideal.span {t} < 𝔮 :=
    lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem _).mpr ht) (Ne.symm hne)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [h1] at h2
  have h0 : (Ideal.span {t}).height = 0 := by
    by_contra hx
    have h3 : (1 : ℕ∞) + 1 ≤ 1 :=
      (add_le_add (Order.one_le_iff_ne_zero.mpr hx) le_rfl).trans h2
    norm_num at h3
  rw [Ideal.height_eq_zero_iff_eq_bot, Ideal.span_singleton_eq_bot] at h0
  exact ht0 h0

section Lattice

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
variable {F : Type*} [Field F] [Algebra R F]
variable {Ω : Type*} [Field Ω] [Algebra A Ω] [Algebra F Ω] [Algebra R Ω]
  [IsScalarTower R A Ω] [IsScalarTower R F Ω]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- The lattice `V ∩ 𝒪_w` as an `R`-submodule of `Ω`, when `w ≤ 1` on the image of `R`. -/
def poleLatticeSubmodule (w : Valuation Ω Γ₀) (hwR : ∀ r : R, w (algebraMap R Ω r) ≤ 1)
    (V : Submodule F Ω) : Submodule R Ω where
  carrier := {x | x ∈ V ∧ w x ≤ 1}
  add_mem' := fun ⟨hx, hwx⟩ ⟨hy, hwy⟩ => ⟨V.add_mem hx hy, w.map_add_le hwx hwy⟩
  zero_mem' := ⟨V.zero_mem, by rw [map_zero]; exact zero_le⟩
  smul_mem' := fun r x ⟨hx, hwx⟩ => by
    refine ⟨?_, ?_⟩
    · rw [← algebraMap_smul F r x]
      exact V.smul_mem _ hx
    · rw [Algebra.smul_def, map_mul]
      exact mul_le_one' (hwR r) hwx

omit [Algebra A Ω] [IsScalarTower R A Ω] in
theorem mem_poleLatticeSubmodule (w : Valuation Ω Γ₀) (hwR : ∀ r : R, w (algebraMap R Ω r) ≤ 1)
    (V : Submodule F Ω) (x : Ω) : x ∈ poleLatticeSubmodule w hwR V ↔ x ∈ V ∧ w x ≤ 1 :=
  Iff.rfl

/-- Coefficients in `R` give coefficients in `F` that are `w`-integral. -/
theorem exists_coeff_of_exists_coeff_algebraMap (w : Valuation Ω Γ₀)
    (hwA : ∀ a : A, w (algebraMap A Ω a) ≤ 1) (V : Submodule F Ω) {k : ℕ} (g : Fin k → Ω)
    (hg : ∀ x ∈ V, w x ≤ 1 → ∃ r : Fin k → R, x = ∑ j, algebraMap R Ω (r j) * g j) :
    ∀ x ∈ V, w x ≤ 1 → ∃ c : Fin k → F,
      (∀ j, w (algebraMap F Ω (c j)) ≤ 1) ∧ x = ∑ j, algebraMap F Ω (c j) * g j := by
  intro x hx hwx
  obtain ⟨r, rfl⟩ := hg x hx hwx
  refine ⟨fun j => algebraMap R F (r j), fun j => ?_, ?_⟩
  · rw [← IsScalarTower.algebraMap_apply R F Ω, IsScalarTower.algebraMap_apply R A Ω]
    exact hwA _
  · simp only [← IsScalarTower.algebraMap_apply R F Ω]

omit [Algebra F Ω] [IsScalarTower R F Ω] in
/-- The case `t = 0`: then `ρ` is injective, `A = R`, and `M_n ⊆ R · 1`. -/
theorem exists_family_of_ker_eq_bot [IsDomain R] [IsDiscreteValuationRing R]
    (w : Valuation Ω Γ₀) (ρ : A →ₐ[R] R) (hker : RingHom.ker ρ = ⊥) {ϖ : R}
    (hϖ : Irreducible ϖ)
    (hw : ∀ g : Ω, w g ≤ 1 → ∃ r s : A, s ∉ Ideal.span {algebraMap R A ϖ} ∧
      algebraMap A Ω s * g = algebraMap A Ω r) :
    ∃ (k : ℕ) (g : Fin k → Ω), ∀ x : Ω, w x ≤ 1 →
      ∃ r : Fin k → R, x = ∑ j, algebraMap R Ω (r j) * g j := by
  have hsec : ∀ a : A, a = algebraMap R A (ρ a) := by
    intro a
    have h : a - algebraMap R A (ρ a) ∈ RingHom.ker ρ := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        sub_self]
    rw [hker, Ideal.mem_bot, sub_eq_zero] at h
    exact h
  have hmax : maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  refine ⟨1, fun _ => 1, fun x hwx => ?_⟩
  obtain ⟨r, s, hs, hrs⟩ := hw x hwx
  have hunit : IsUnit (ρ s) := by
    by_contra hnu
    apply hs
    have hmem : ρ s ∈ maximalIdeal R := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    rw [hmax, Ideal.mem_span_singleton'] at hmem
    obtain ⟨c, hc⟩ := hmem
    rw [hsec s, ← hc, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have h1 : algebraMap R Ω (ρ s) * x = algebraMap R Ω (ρ r) := by
    rw [IsScalarTower.algebraMap_apply R A Ω, IsScalarTower.algebraMap_apply R A Ω, ← hsec,
      ← hsec]
    exact hrs
  refine ⟨fun _ => ↑hunit.unit⁻¹ * ρ r, ?_⟩
  rw [Fin.sum_univ_one, mul_one]
  calc x = algebraMap R Ω (↑hunit.unit⁻¹ * ↑hunit.unit) * x := by
        rw [Units.inv_mul, map_one, one_mul]
    _ = algebraMap R Ω (↑hunit.unit⁻¹ * ρ r) := by
        rw [map_mul, mul_assoc, IsUnit.unit_spec, h1, map_mul]

variable [IsFractionRing A Ω]

/-- The case `t ≠ 0`: `M_n` embeds `R`-linearly into the finite `R`-module `A ⧸ (tⁿ⁺¹)`. -/
theorem exists_family_of_ne_zero [IsDomain R] [IsNoetherianRing R] (w : Valuation Ω Γ₀)
    (ρ : A →ₐ[R] R) {t : A} (hker : RingHom.ker ρ = Ideal.span {t}) (ht0 : t ≠ 0) {ϖ : R}
    (hhart : ∀ g : Ω, (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 →
      ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * g = algebraMap A Ω r) → g ∈ (algebraMap A Ω).range)
    (hcases : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → algebraMap R A ϖ ∈ 𝔮 →
      𝔮 = Ideal.span {algebraMap R A ϖ})
    (hw : ∀ g : Ω, w g ≤ 1 → ∃ r s : A, s ∉ Ideal.span {algebraMap R A ϖ} ∧
      algebraMap A Ω s * g = algebraMap A Ω r)
    (hwA : ∀ a : A, w (algebraMap A Ω a) ≤ 1)
    (V : Submodule F Ω) (n : ℕ)
    (hpole : ∀ f ∈ V, ∃ r s : A, s ∉ Ideal.span {t} ∧
      algebraMap A Ω s * (f * algebraMap A Ω t ^ n) = algebraMap A Ω r)
    (hreg : ∀ f ∈ V, ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → algebraMap R A ϖ ∉ 𝔮 →
      t ∉ 𝔮 → ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * f = algebraMap A Ω r)
    (hzero : ∀ f ∈ V, ∀ a : A, f = algebraMap A Ω (t * a) → f = 0) :
    ∃ (k : ℕ) (g : Fin k → Ω), ∀ x ∈ V, w x ≤ 1 →
      ∃ r : Fin k → R, x = ∑ j, algebraMap R Ω (r j) * g j := by
  have hinj := IsFractionRing.injective A Ω
  have : IsDomain A := Function.Injective.isDomain (algebraMap A Ω) hinj
  have htΩ : algebraMap A Ω t ≠ 0 := (map_ne_zero_iff _ hinj).mpr ht0
  have hT0 : algebraMap A Ω t ^ n ≠ 0 := pow_ne_zero _ htΩ
  have htp : (Ideal.span {t}).IsPrime := hker ▸ RingHom.ker_isPrime ρ
  have hwR : ∀ r : R, w (algebraMap R Ω r) ≤ 1 := fun r => by
    rw [IsScalarTower.algebraMap_apply R A Ω]
    exact hwA _
  -- every `x ∈ M_n` has `x tⁿ ∈ A`
  have hint : ∀ x ∈ V, w x ≤ 1 → ∃ a : A, algebraMap A Ω a = x * algebraMap A Ω t ^ n := by
    intro x hxV hwx
    have key : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → ∃ r s : A, s ∉ 𝔮 ∧
        algebraMap A Ω s * (x * algebraMap A Ω t ^ n) = algebraMap A Ω r := by
      intro 𝔮 hp h1
      by_cases hϖ𝔮 : algebraMap R A ϖ ∈ 𝔮
      · obtain ⟨r, s, hs, hrs⟩ := hw x hwx
        refine ⟨r * t ^ n, s, by rwa [hcases 𝔮 hp h1 hϖ𝔮], ?_⟩
        rw [map_mul, map_pow, ← hrs]
        ring
      by_cases ht𝔮 : t ∈ 𝔮
      · obtain ⟨r, s, hs, hrs⟩ := hpole x hxV
        refine ⟨r, s, ?_, hrs⟩
        rwa [eq_span_singleton_of_height_eq_one ht0 htp 𝔮 hp h1 ht𝔮]
      · obtain ⟨r, s, hs, hrs⟩ := hreg x hxV 𝔮 hp h1 hϖ𝔮 ht𝔮
        refine ⟨r * t ^ n, s, hs, ?_⟩
        rw [map_mul, map_pow, ← hrs]
        ring
    obtain ⟨a, ha⟩ := hhart _ key
    exact ⟨a, ha⟩
  -- the `R`-linear map `a ↦ a / tⁿ` and the module `N`
  let ψ : A →ₗ[R] Ω := (LinearMap.mulRight R (algebraMap A Ω t ^ n)⁻¹).comp
    (IsScalarTower.toAlgHom R A Ω).toLinearMap
  have hψ : ∀ a, ψ a = algebraMap A Ω a * (algebraMap A Ω t ^ n)⁻¹ := fun a => rfl
  let N : Submodule R A := (poleLatticeSubmodule w hwR V).comap ψ
  have hmemN : ∀ a, a ∈ N ↔ ψ a ∈ V ∧ w (ψ a) ≤ 1 := fun a => Iff.rfl
  have : Module.Finite R (A ⧸ Ideal.span {t ^ (n + 1)}) := finite_quotient_span_pow ρ hker _
  let π : N →ₗ[R] A ⧸ Ideal.span {t ^ (n + 1)} :=
    (Ideal.Quotient.mkₐ R (Ideal.span {t ^ (n + 1)})).toLinearMap.comp N.subtype
  have hπ : Function.Injective π := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, haN⟩ ha
    have ha' : Ideal.Quotient.mk (Ideal.span {t ^ (n + 1)}) a = 0 := ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp ha')
    have heq : ψ (c * t ^ (n + 1)) = algebraMap A Ω (t * c) := by
      rw [hψ, map_mul, map_mul, map_pow, pow_succ]
      field_simp
    have h0 := hzero _ ((hmemN _).mp haN).1 c heq
    rw [hψ, mul_eq_zero, inv_eq_zero, or_iff_left hT0, map_eq_zero_iff _ hinj] at h0
    exact Subtype.ext h0
  have : Module.Finite R N := Module.Finite.of_injective π hπ
  obtain ⟨k, g, hg⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp (Module.Finite.iff_fg.mp ‹_›)
  refine ⟨k, fun j => ψ (g j), fun x hxV hwx => ?_⟩
  obtain ⟨a, ha⟩ := hint x hxV hwx
  have hψa : ψ a = x := by rw [hψ, ha, mul_inv_cancel_right₀ hT0]
  have haN : a ∈ N := (hmemN a).mpr ⟨hψa ▸ hxV, hψa ▸ hwx⟩
  rw [← hg, Submodule.mem_span_range_iff_exists_fun] at haN
  obtain ⟨r, hr⟩ := haN
  refine ⟨r, ?_⟩
  rw [← hψa, ← hr, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Algebra.smul_def]

/-- **Finite generation of `M_n`** (blueprint node N8b). Let `ρ : A →ₐ[R] R` have kernel `(t)`,
`ϖ` be a uniformizer of `R`, and `A` satisfy the Hartogs property `hhart` with `(ϖ)` the only
height-one prime containing `ϖ` (`hcases`). Let `w ≤ 1` on `A` with `𝒪_w ⊆ A_(ϖ)` (`hw`). If every
`f ∈ V` has a pole of order at most `n` along `(t)` (`hpole`), is regular at every other
height-one prime not containing `ϖ` (`hreg`), and vanishes if it lies in `tA` (`hzero`), then
`M_n = V ∩ 𝒪_w` lies in the span of finitely many elements over the `w`-integral elements of `F`.
The conclusion is the hypothesis `ht` of `exists_lattice_basis` with `κ = Fin k`. -/
theorem exists_finite_span_of_poleBound [IsDomain R] [IsDiscreteValuationRing R]
    (w : Valuation Ω Γ₀) (ρ : A →ₐ[R] R) {t : A}
    (hker : RingHom.ker ρ = Ideal.span {t}) {ϖ : R} (hϖ : Irreducible ϖ)
    (hhart : ∀ g : Ω, (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 →
      ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * g = algebraMap A Ω r) → g ∈ (algebraMap A Ω).range)
    (hcases : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → algebraMap R A ϖ ∈ 𝔮 →
      𝔮 = Ideal.span {algebraMap R A ϖ})
    (hw : ∀ g : Ω, w g ≤ 1 → ∃ r s : A, s ∉ Ideal.span {algebraMap R A ϖ} ∧
      algebraMap A Ω s * g = algebraMap A Ω r)
    (hwA : ∀ a : A, w (algebraMap A Ω a) ≤ 1)
    (V : Submodule F Ω) (n : ℕ)
    (hpole : ∀ f ∈ V, ∃ r s : A, s ∉ Ideal.span {t} ∧
      algebraMap A Ω s * (f * algebraMap A Ω t ^ n) = algebraMap A Ω r)
    (hreg : ∀ f ∈ V, ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → algebraMap R A ϖ ∉ 𝔮 →
      t ∉ 𝔮 → ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * f = algebraMap A Ω r)
    (hzero : ∀ f ∈ V, ∀ a : A, f = algebraMap A Ω (t * a) → f = 0) :
    ∃ (k : ℕ) (b : Fin k → Ω), ∀ x ∈ V, w x ≤ 1 → ∃ c : Fin k → F,
      (∀ j, w (algebraMap F Ω (c j)) ≤ 1) ∧ x = ∑ j, algebraMap F Ω (c j) * b j := by
  suffices h : ∃ (k : ℕ) (g : Fin k → Ω), ∀ x ∈ V, w x ≤ 1 →
      ∃ r : Fin k → R, x = ∑ j, algebraMap R Ω (r j) * g j by
    obtain ⟨k, g, hg⟩ := h
    exact ⟨k, g, exists_coeff_of_exists_coeff_algebraMap w hwA V g hg⟩
  by_cases ht0 : t = 0
  · rw [ht0, Ideal.span_singleton_eq_bot.mpr rfl] at hker
    obtain ⟨k, g, hg⟩ := exists_family_of_ker_eq_bot w ρ hker hϖ hw
    exact ⟨k, g, fun x _ hwx => hg x hwx⟩
  · exact exists_family_of_ne_zero w ρ hker ht0 hhart hcases hw hwA V n hpole hreg hzero

/-- **Lattice basis of `M_n`.** Under the hypotheses of `exists_finite_span_of_poleBound`, if the
image of `ϖ` in `F` is a uniformizer of `w` and `V` is finite-dimensional, then
`exists_lattice_basis` applies: `V` has a residually independent `F`-basis `b`, `M_n` is the free
module on `b` over the `w`-integral elements of `F`, and its reduction modulo `ϖ` is injective. -/
theorem exists_lattice_basis_of_poleBound [IsDomain R] [IsDiscreteValuationRing R]
    (w : Valuation Ω Γ₀) (ρ : A →ₐ[R] R) {t : A}
    (hker : RingHom.ker ρ = Ideal.span {t}) {ϖ : R} (hϖ : Irreducible ϖ)
    (hunif : IsUniformizer (F := F) w (algebraMap R F ϖ))
    (hhart : ∀ g : Ω, (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 →
      ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * g = algebraMap A Ω r) → g ∈ (algebraMap A Ω).range)
    (hcases : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → algebraMap R A ϖ ∈ 𝔮 →
      𝔮 = Ideal.span {algebraMap R A ϖ})
    (hw : ∀ g : Ω, w g ≤ 1 → ∃ r s : A, s ∉ Ideal.span {algebraMap R A ϖ} ∧
      algebraMap A Ω s * g = algebraMap A Ω r)
    (hwA : ∀ a : A, w (algebraMap A Ω a) ≤ 1)
    (V : Submodule F Ω) [FiniteDimensional F V] (n : ℕ)
    (hpole : ∀ f ∈ V, ∃ r s : A, s ∉ Ideal.span {t} ∧
      algebraMap A Ω s * (f * algebraMap A Ω t ^ n) = algebraMap A Ω r)
    (hreg : ∀ f ∈ V, ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → algebraMap R A ϖ ∉ 𝔮 →
      t ∉ 𝔮 → ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * f = algebraMap A Ω r)
    (hzero : ∀ f ∈ V, ∀ a : A, f = algebraMap A Ω (t * a) → f = 0) :
    ∃ b : Fin (finrank F V) → Ω, ResiduallyIndependent (F := F) w b ∧ (∀ i, b i ∈ V) ∧
      LinearIndependent F b ∧ Submodule.span F (Set.range b) = V ∧
      (∀ x : Ω, x ∈ V ∧ w x ≤ 1 ↔ ∃ c : Fin (finrank F V) → F,
        (∀ i, w (algebraMap F Ω (c i)) ≤ 1) ∧ x = ∑ i, algebraMap F Ω (c i) * b i) ∧
      ∀ c : Fin (finrank F V) → F, w (∑ i, algebraMap F Ω (c i) * b i) < 1 ↔
        ∀ i, w (algebraMap F Ω (c i / algebraMap R F ϖ)) ≤ 1 := by
  obtain ⟨k, b, hb⟩ := exists_finite_span_of_poleBound w ρ hker hϖ hhart hcases hw hwA V n
    hpole hreg hzero
  exact exists_lattice_basis hunif V b hb

end Lattice

end ZInQ.Contrib.CMHeight62Full
