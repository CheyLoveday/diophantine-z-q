import ZInQKernel.Contrib.OneProof.CMHeight62Full.LocalStructure
import ZInQKernel.Contrib.OneProof.CMHeight62Full.WeierstrassDVR
import ZInQKernel.Contrib.OneProof.CMHeight62Full.GroupCurveNotP1

/-!
# The local parameter at the identity point (node N12-alg)

Setting. `R` is a domain with an element `ϖ`, `A` is a local domain and an `R`-algebra, `Ω` is the
fraction field of `A`, `w` is a valuation on `Ω` which is `≤ 1` on `A`, and `ρ : A →+* R` has
kernel `(t)`. In the application `R` is a discrete valuation ring with uniformizer `ϖ`, `A` is
the local ring of the model at the identity point of the special fibre (node N5,
`LocalStructure.lean`), with maximal ideal `(ϖ, t)`, `ρ` is the localized section, `w` is the
special-fibre valuation (node N6c) and `P` is the place `ē` of the residue field `κ_w`.

Let `x₀, y₀ ∈ Ω` be the coordinates of an integral Weierstrass model (`x₀ = e·x`, `y₀ = e·y`).
We prove:

* `exists_mul_pow_eq`: if `w f ≤ 1`, `f` has a pole of order at most `n` along `(t)` and `f` is
  regular at every other height-one prime, then `f·tⁿ ∈ A`. The input is the depth-two Hartogs
  property of `A` (node N6a), taken as the hypothesis `hhart` in the shape of the blueprint;
* `isUnit_of_reduce_notMem_nonunits`: an element of `A` whose reduction is a unit of `P` (order
  `0` at `ē`) is a unit of `A`;
* `exists_unit_localParameter`: `x₀·t² = a` and `y₀·t³ = b` with `a, b ∈ Aˣ`, hence
  `-x₀/y₀ = u·t` with `u = -a·b⁻¹ ∈ Aˣ`;
* `exists_unit_localParameter_of_maximalIdeal`: the same with the hypotheses at `ē` stated as in
  the blueprint: `𝔪_A = (ϖ, t)`, `w ϖ < 1`, the reductions of `A` lie in `P`, `t̄` is a
  uniformizer of `P`, and the reductions `x̄₀, ȳ₀` have poles of order at least `2, 3` at `P`;
* `exists_unit_localParameter_of_units_smul`: the version for `x₀ = e·x`, `y₀ = e·y`, `e ∈ Rˣ`;
* `exists_localParameter_of_standardSmooth`: the instance `A = (A₀)_𝔭` of node N5, with the
  parameter `t` produced by `localStructure_of_standardSmooth`.

Only the lower bounds on the pole orders at `ē` are needed: the upper bounds follow from
`x₀t², y₀t³ ∈ A`.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

namespace LocalParameter

open IsLocalRing

section HeightOne

variable {A : Type*} [CommRing A] [IsDomain A]

/-- In a domain, a height-one prime containing a nonzero element `t` with `(t)` prime is `(t)`. -/
theorem eq_span_of_height_eq_one {t : A} (ht0 : t ≠ 0) (htp : (Ideal.span {t}).IsPrime)
    (𝔮 : Ideal A) [𝔮.IsPrime] (h1 : 𝔮.height = 1) (ht : t ∈ 𝔮) : 𝔮 = Ideal.span {t} := by
  by_contra hne
  have hle : Ideal.span {t} ≤ 𝔮 := (Ideal.span_singleton_le_iff_mem _).2 ht
  have hlt : Ideal.span {t} < 𝔮 := lt_of_le_of_ne hle (Ne.symm hne)
  have hbot : (⊥ : Ideal A) < Ideal.span {t} := by
    rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]
    exact ht0
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h3 := Ideal.height_add_one_le_of_lt_of_isPrime hbot
  rw [h1] at h2
  have h4 : (1 : ℕ∞) ≤ (Ideal.span {t}).height := le_trans le_add_self h3
  have h5 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h2
  exact absurd h5 (by norm_num)

end HeightOne

section Hartogs

variable {R : Type*} [CommRing R] [IsDomain R] {A : Type*} [CommRing A] [IsDomain A]
  [Algebra R A] {Ω : Type*} [Field Ω] [Algebra A Ω]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation Ω Γ₀)

/-- **Integrality of `f·tⁿ`.** Let `f ∈ Ω` with `w f ≤ 1`, with a pole of order at most `n`
along `(t) = ker ρ` and regular at every height-one prime containing neither `ϖ` nor `t`. If `A`
has the Hartogs property `hhart` (node N6a) and every height-one prime containing `ϖ` is `(ϖ)`,
then `f·tⁿ ∈ A`. -/
theorem exists_mul_pow_eq (ρ : A →+* R) {t : A} (hker : RingHom.ker ρ = Ideal.span {t})
    (ht0 : t ≠ 0) {ϖ : R}
    (hhart : ∀ g : Ω, (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 →
      ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * g = algebraMap A Ω r) →
        g ∈ (algebraMap A Ω).range)
    (hcases : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → algebraMap R A ϖ ∈ 𝔮 →
      𝔮 = Ideal.span {algebraMap R A ϖ})
    (hw : ∀ g : Ω, w g ≤ 1 → ∃ r s : A, s ∉ Ideal.span {algebraMap R A ϖ} ∧
      algebraMap A Ω s * g = algebraMap A Ω r)
    (hwA : ∀ a : A, w (algebraMap A Ω a) ≤ 1) {f : Ω} (n : ℕ) (hfw : w f ≤ 1)
    (hpole : ∃ r s : A, s ∉ Ideal.span {t} ∧
      algebraMap A Ω s * (f * algebraMap A Ω t ^ n) = algebraMap A Ω r)
    (hreg : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → algebraMap R A ϖ ∉ 𝔮 →
      t ∉ 𝔮 → ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * f = algebraMap A Ω r) :
    ∃ a : A, algebraMap A Ω a = f * algebraMap A Ω t ^ n := by
  refine hhart (f * algebraMap A Ω t ^ n) fun 𝔮 hq h1 => ?_
  by_cases hϖ : algebraMap R A ϖ ∈ 𝔮
  · rw [hcases 𝔮 hq h1 hϖ]
    apply hw
    rw [map_mul, map_pow]
    exact mul_le_one' hfw (pow_le_one' (hwA t) n)
  by_cases htq : t ∈ 𝔮
  · have htp : (Ideal.span {t}).IsPrime := hker ▸ RingHom.ker_isPrime ρ
    rw [eq_span_of_height_eq_one ht0 htp 𝔮 h1 htq]
    exact hpole
  · obtain ⟨r, s, hs, hrs⟩ := hreg 𝔮 hq h1 hϖ htq
    exact ⟨r * t ^ n, s, hs, by rw [← mul_assoc, hrs, map_mul, map_pow]⟩

end Hartogs

section Residue

variable {A : Type*} [CommRing A] {Ω : Type*} [Field Ω] [Algebra A Ω]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation Ω Γ₀)

/-- The reduction map `A → κ_w`, for `w ≤ 1` on `A`. -/
def reduceHom (hwA : ∀ a : A, w (algebraMap A Ω a) ≤ 1) :
    A →+* ResidueField w.valuationSubring :=
  (residue w.valuationSubring).comp
    ((algebraMap A Ω).codRestrict w.valuationSubring
      fun a => (w.mem_valuationSubring_iff _).2 (hwA a))

theorem reduceHom_apply (hwA : ∀ a : A, w (algebraMap A Ω a) ≤ 1) (a : A) :
    reduceHom w hwA a = reduce w (algebraMap A Ω a) (hwA a) := rfl

theorem reduce_congr {x y : Ω} (h : x = y) (hx : w x ≤ 1) (hy : w y ≤ 1) :
    reduce w x hx = reduce w y hy := by
  subst h
  rfl

theorem reduce_mul {x y : Ω} (hx : w x ≤ 1) (hy : w y ≤ 1) (hxy : w (x * y) ≤ 1) :
    reduce w (x * y) hxy = reduce w x hx * reduce w y hy := by
  rw [reduce, reduce, reduce, ← map_mul]
  rfl

theorem reduce_pow {x : Ω} (hx : w x ≤ 1) (n : ℕ) (hxn : w (x ^ n) ≤ 1) :
    reduce w (x ^ n) hxn = reduce w x hx ^ n := by
  rw [reduce, reduce, ← map_pow]
  rfl

/-- An element with `w x < 1` reduces to `0`. -/
theorem reduce_eq_zero {x : Ω} (hx : w x ≤ 1) (hlt : w x < 1) : reduce w x hx = 0 := by
  rw [reduce, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  have hux : (u : w.valuationSubring).val = x := congrArg Subtype.val hu
  have hinv : (u⁻¹ : (w.valuationSubring)ˣ).val.val * x = 1 := by
    rw [← hux]
    exact congrArg Subtype.val u.inv_mul
  have hb : w ((u⁻¹ : (w.valuationSubring)ˣ).val.val) ≤ 1 :=
    (w.mem_valuationSubring_iff _).1 (u⁻¹ : (w.valuationSubring)ˣ).val.2
  have h1 := congrArg w hinv
  rw [map_mul, map_one] at h1
  have h2 : w ((u⁻¹ : (w.valuationSubring)ˣ).val.val) * w x < 1 :=
    (mul_le_of_le_one_left' hb).trans_lt hlt
  rw [h1] at h2
  exact lt_irrefl _ h2

end Residue

section Unit

variable {A : Type*} [CommRing A] [IsLocalRing A] {Ω : Type*} [Field Ω] [Algebra A Ω]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation Ω Γ₀)

/-- **Order `0` at `ē` gives a unit.** If the maximal ideal of `A` reduces into the maximal ideal
of the place `P` of `κ_w`, an element of `A` whose reduction is not in `P.nonunits` is a unit. -/
theorem isUnit_of_reduce_notMem_nonunits (hwA : ∀ a : A, w (algebraMap A Ω a) ≤ 1)
    (P : ValuationSubring (ResidueField w.valuationSubring))
    (hcenter : ∀ a ∈ maximalIdeal A, reduce w (algebraMap A Ω a) (hwA a) ∈ P.nonunits)
    {a : A} (hu : reduce w (algebraMap A Ω a) (hwA a) ∉ P.nonunits) : IsUnit a :=
  notMem_maximalIdeal.1 fun h => hu (hcenter a h)

/-- The centre condition from the blueprint data: `𝔪_A = (ϖ, t)`, `w ϖ < 1`, the reductions of
`A` lie in `P` and `t̄ ∈ P.nonunits`. -/
theorem reduce_mem_nonunits_of_maximalIdeal {R : Type*} [CommRing R] [Algebra R A] {ϖ : R}
    {t : A} (hmax : maximalIdeal A = Ideal.span {algebraMap R A ϖ, t})
    (hwA : ∀ a : A, w (algebraMap A Ω a) ≤ 1) (hϖw : w (algebraMap A Ω (algebraMap R A ϖ)) < 1)
    (P : ValuationSubring (ResidueField w.valuationSubring))
    (hAP : ∀ a : A, reduce w (algebraMap A Ω a) (hwA a) ∈ P)
    (htP : reduce w (algebraMap A Ω t) (hwA t) ∈ P.nonunits) :
    ∀ a ∈ maximalIdeal A, reduce w (algebraMap A Ω a) (hwA a) ∈ P.nonunits := by
  intro a ha
  rw [hmax, Ideal.mem_span_pair] at ha
  obtain ⟨c, d, rfl⟩ := ha
  rw [← reduceHom_apply] at htP ⊢
  have hϖ0 : reduceHom w hwA (algebraMap R A ϖ) = 0 := by
    rw [reduceHom_apply]
    exact reduce_eq_zero w _ hϖw
  have hd : reduceHom w hwA d ∈ P := by
    rw [reduceHom_apply]
    exact hAP d
  rw [map_add, map_mul, map_mul, hϖ0, mul_zero, zero_add]
  rw [ValuationSubring.mem_nonunits_iff] at htP ⊢
  rw [map_mul]
  exact (mul_le_of_le_one_left' ((P.valuation_le_one_iff _).2 hd)).trans_lt htP

/-- A pole of order at least `n + 1` at a place with uniformizer `π`: if `h·πⁿ ∉ P`, then
`h·πⁿ⁺¹` is not in the maximal ideal of `P`. -/
theorem mul_pow_succ_notMem_nonunits {K : Type*} [Field K] {P : ValuationSubring K} {π h : K}
    (hπ : IsUniformizerAt P π) (n : ℕ) (hn : h * π ^ n ∉ P) : h * π ^ (n + 1) ∉ P.nonunits := by
  intro hmem
  apply hn
  have := hπ.2.2 _ hmem
  rwa [pow_succ, ← mul_assoc, mul_assoc, mul_inv_cancel₀ hπ.1, mul_one] at this

end Unit

section Main

variable {R : Type*} [CommRing R] [IsDomain R] {A : Type*} [CommRing A] [IsDomain A]
  [IsLocalRing A] [Algebra R A] {Ω : Type*} [Field Ω] [Algebra A Ω] [IsFractionRing A Ω]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation Ω Γ₀)

/-- **Node N12-alg.** Let `x₀, y₀ ∈ Ω` with `w ≤ 1`, with poles of order at most `2, 3` along
`(t) = ker ρ`, regular at the other height-one primes, and whose reductions times `t̄², t̄³` are
not in the maximal ideal of the place `P` (order `0` at `ē`). Then `x₀t²` and `y₀t³` are units
`a, b` of `A`, and `-x₀/y₀ = u·t` with `u = -a·b⁻¹ ∈ Aˣ`. -/
theorem exists_unit_localParameter (ρ : A →+* R) {t : A}
    (hker : RingHom.ker ρ = Ideal.span {t}) {ϖ : R}
    (hhart : ∀ g : Ω, (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 →
      ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * g = algebraMap A Ω r) →
        g ∈ (algebraMap A Ω).range)
    (hcases : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → algebraMap R A ϖ ∈ 𝔮 →
      𝔮 = Ideal.span {algebraMap R A ϖ})
    (hw : ∀ g : Ω, w g ≤ 1 → ∃ r s : A, s ∉ Ideal.span {algebraMap R A ϖ} ∧
      algebraMap A Ω s * g = algebraMap A Ω r)
    (hwA : ∀ a : A, w (algebraMap A Ω a) ≤ 1)
    (P : ValuationSubring (ResidueField w.valuationSubring))
    (hcenter : ∀ a ∈ maximalIdeal A, reduce w (algebraMap A Ω a) (hwA a) ∈ P.nonunits)
    {x₀ y₀ : Ω} (hx₀ : w x₀ ≤ 1) (hy₀ : w y₀ ≤ 1)
    (hpx : ∃ r s : A, s ∉ Ideal.span {t} ∧
      algebraMap A Ω s * (x₀ * algebraMap A Ω t ^ 2) = algebraMap A Ω r)
    (hpy : ∃ r s : A, s ∉ Ideal.span {t} ∧
      algebraMap A Ω s * (y₀ * algebraMap A Ω t ^ 3) = algebraMap A Ω r)
    (hrx : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → algebraMap R A ϖ ∉ 𝔮 →
      t ∉ 𝔮 → ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * x₀ = algebraMap A Ω r)
    (hry : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → algebraMap R A ϖ ∉ 𝔮 →
      t ∉ 𝔮 → ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * y₀ = algebraMap A Ω r)
    (hox : reduce w x₀ hx₀ * reduce w (algebraMap A Ω t) (hwA t) ^ 2 ∉ P.nonunits)
    (hoy : reduce w y₀ hy₀ * reduce w (algebraMap A Ω t) (hwA t) ^ 3 ∉ P.nonunits) :
    ∃ a b : Aˣ, algebraMap A Ω a = x₀ * algebraMap A Ω t ^ 2 ∧
      algebraMap A Ω b = y₀ * algebraMap A Ω t ^ 3 ∧
      -x₀ / y₀ = algebraMap A Ω ↑(-a * b⁻¹) * algebraMap A Ω t := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hox
    rw [← reduceHom_apply, map_zero, zero_pow two_ne_zero, mul_zero]
    rw [ValuationSubring.mem_nonunits_iff, map_zero]
    exact zero_lt_one
  obtain ⟨a, ha⟩ := exists_mul_pow_eq w ρ hker ht0 hhart hcases hw hwA 2 hx₀ hpx hrx
  obtain ⟨b, hb⟩ := exists_mul_pow_eq w ρ hker ht0 hhart hcases hw hwA 3 hy₀ hpy hry
  have hred : ∀ (f : Ω) (hf : w f ≤ 1) (n : ℕ) (c : A),
      algebraMap A Ω c = f * algebraMap A Ω t ^ n →
        reduce w (algebraMap A Ω c) (hwA c) =
          reduce w f hf * reduce w (algebraMap A Ω t) (hwA t) ^ n := by
    intro f hf n c hc
    have hle : w (algebraMap A Ω t ^ n) ≤ 1 := by
      rw [map_pow]
      exact pow_le_one' (hwA t) n
    rw [reduce_congr w hc (hwA c) (by rw [← hc]; exact hwA c), reduce_mul w hf hle,
      reduce_pow w (hwA t)]
  have hau : IsUnit a := isUnit_of_reduce_notMem_nonunits w hwA P hcenter
    (by rw [hred x₀ hx₀ 2 a ha]; exact hox)
  have hbu : IsUnit b := isUnit_of_reduce_notMem_nonunits w hwA P hcenter
    (by rw [hred y₀ hy₀ 3 b hb]; exact hoy)
  obtain ⟨a, rfl⟩ := hau
  obtain ⟨b, rfl⟩ := hbu
  refine ⟨a, b, ha, hb, ?_⟩
  have hinj := IsFractionRing.injective A Ω
  have hT : algebraMap A Ω t ≠ 0 := fun h => ht0 (hinj (h.trans (map_zero _).symm))
  have hb0 : algebraMap A Ω (b : A) ≠ 0 := fun h =>
    b.ne_zero (hinj (h.trans (map_zero _).symm))
  have hy0 : y₀ ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hb
    exact hb0 hb
  have hbinv : algebraMap A Ω ↑b⁻¹ = (algebraMap A Ω ↑b)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  rw [Units.val_mul, Units.val_neg, map_mul, map_neg, hbinv, ha, hb]
  field_simp

/-- **Node N12-alg, blueprint form.** The hypotheses at `ē` as the earlier nodes provide them:
`𝔪_A = (ϖ, t)` (N5), `w ϖ < 1`, the reductions of `A` lie in `P` and `t̄` is a uniformizer of `P`
(N6c), and `x̄₀·t̄ ∉ P`, `ȳ₀·t̄² ∉ P` (poles of order at least `2, 3` at `ē`). -/
theorem exists_unit_localParameter_of_maximalIdeal (ρ : A →+* R) {t : A}
    (hker : RingHom.ker ρ = Ideal.span {t}) {ϖ : R}
    (hmax : maximalIdeal A = Ideal.span {algebraMap R A ϖ, t})
    (hhart : ∀ g : Ω, (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 →
      ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * g = algebraMap A Ω r) →
        g ∈ (algebraMap A Ω).range)
    (hcases : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → algebraMap R A ϖ ∈ 𝔮 →
      𝔮 = Ideal.span {algebraMap R A ϖ})
    (hw : ∀ g : Ω, w g ≤ 1 → ∃ r s : A, s ∉ Ideal.span {algebraMap R A ϖ} ∧
      algebraMap A Ω s * g = algebraMap A Ω r)
    (hwA : ∀ a : A, w (algebraMap A Ω a) ≤ 1)
    (hϖw : w (algebraMap A Ω (algebraMap R A ϖ)) < 1)
    (P : ValuationSubring (ResidueField w.valuationSubring))
    (hAP : ∀ a : A, reduce w (algebraMap A Ω a) (hwA a) ∈ P)
    (hπ : IsUniformizerAt P (reduce w (algebraMap A Ω t) (hwA t)))
    {x₀ y₀ : Ω} (hx₀ : w x₀ ≤ 1) (hy₀ : w y₀ ≤ 1)
    (hpx : ∃ r s : A, s ∉ Ideal.span {t} ∧
      algebraMap A Ω s * (x₀ * algebraMap A Ω t ^ 2) = algebraMap A Ω r)
    (hpy : ∃ r s : A, s ∉ Ideal.span {t} ∧
      algebraMap A Ω s * (y₀ * algebraMap A Ω t ^ 3) = algebraMap A Ω r)
    (hrx : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → algebraMap R A ϖ ∉ 𝔮 →
      t ∉ 𝔮 → ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * x₀ = algebraMap A Ω r)
    (hry : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → algebraMap R A ϖ ∉ 𝔮 →
      t ∉ 𝔮 → ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * y₀ = algebraMap A Ω r)
    (hox : reduce w x₀ hx₀ * reduce w (algebraMap A Ω t) (hwA t) ∉ P)
    (hoy : reduce w y₀ hy₀ * reduce w (algebraMap A Ω t) (hwA t) ^ 2 ∉ P) :
    ∃ a b : Aˣ, algebraMap A Ω a = x₀ * algebraMap A Ω t ^ 2 ∧
      algebraMap A Ω b = y₀ * algebraMap A Ω t ^ 3 ∧
      -x₀ / y₀ = algebraMap A Ω ↑(-a * b⁻¹) * algebraMap A Ω t := by
  have hcenter := reduce_mem_nonunits_of_maximalIdeal w hmax hwA hϖw P hAP hπ.2.1
  refine exists_unit_localParameter w ρ hker hhart hcases hw hwA P hcenter hx₀ hy₀ hpx hpy hrx
    hry ?_ ?_
  · exact mul_pow_succ_notMem_nonunits hπ 1 (by rwa [pow_one])
  · exact mul_pow_succ_notMem_nonunits hπ 2 hoy

/-- **Node N12-alg for `x₀ = e·x`, `y₀ = e·y`** with `e ∈ Rˣ` (the normalization of node N10a):
the hypotheses are stated for `x, y`. -/
theorem exists_unit_localParameter_of_units_smul [Algebra R Ω] [IsScalarTower R A Ω]
    (ρ : A →+* R) {t : A} (hker : RingHom.ker ρ = Ideal.span {t}) {ϖ : R}
    (hmax : maximalIdeal A = Ideal.span {algebraMap R A ϖ, t})
    (hhart : ∀ g : Ω, (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 →
      ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * g = algebraMap A Ω r) →
        g ∈ (algebraMap A Ω).range)
    (hcases : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → algebraMap R A ϖ ∈ 𝔮 →
      𝔮 = Ideal.span {algebraMap R A ϖ})
    (hw : ∀ g : Ω, w g ≤ 1 → ∃ r s : A, s ∉ Ideal.span {algebraMap R A ϖ} ∧
      algebraMap A Ω s * g = algebraMap A Ω r)
    (hwA : ∀ a : A, w (algebraMap A Ω a) ≤ 1)
    (hϖw : w (algebraMap A Ω (algebraMap R A ϖ)) < 1)
    (P : ValuationSubring (ResidueField w.valuationSubring))
    (hAP : ∀ a : A, reduce w (algebraMap A Ω a) (hwA a) ∈ P)
    (hπ : IsUniformizerAt P (reduce w (algebraMap A Ω t) (hwA t)))
    (e : Rˣ) {x y : Ω} (hx : w x ≤ 1) (hy : w y ≤ 1)
    (hpx : ∃ r s : A, s ∉ Ideal.span {t} ∧
      algebraMap A Ω s * (x * algebraMap A Ω t ^ 2) = algebraMap A Ω r)
    (hpy : ∃ r s : A, s ∉ Ideal.span {t} ∧
      algebraMap A Ω s * (y * algebraMap A Ω t ^ 3) = algebraMap A Ω r)
    (hrx : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → algebraMap R A ϖ ∉ 𝔮 →
      t ∉ 𝔮 → ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * x = algebraMap A Ω r)
    (hry : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → algebraMap R A ϖ ∉ 𝔮 →
      t ∉ 𝔮 → ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * y = algebraMap A Ω r)
    (hox : reduce w x hx * reduce w (algebraMap A Ω t) (hwA t) ∉ P)
    (hoy : reduce w y hy * reduce w (algebraMap A Ω t) (hwA t) ^ 2 ∉ P) :
    ∃ a b : Aˣ, algebraMap A Ω a = algebraMap R Ω e * x * algebraMap A Ω t ^ 2 ∧
      algebraMap A Ω b = algebraMap R Ω e * y * algebraMap A Ω t ^ 3 ∧
      -(algebraMap R Ω e * x) / (algebraMap R Ω e * y) =
        algebraMap A Ω ↑(-a * b⁻¹) * algebraMap A Ω t := by
  set E : A := algebraMap R A e
  set E' : A := algebraMap R A ↑e⁻¹
  have hE : algebraMap R Ω e = algebraMap A Ω E := IsScalarTower.algebraMap_apply R A Ω e
  have hle : ∀ {f : Ω}, w f ≤ 1 → w (algebraMap R Ω e * f) ≤ 1 := fun {f} hf => by
    rw [hE, map_mul]
    exact mul_le_one' (hwA E) hf
  have hEE : reduceHom w hwA E' * reduceHom w hwA E = 1 := by
    rw [← map_mul, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, map_one]
  have hord : ∀ {f : Ω} (hf : w f ≤ 1) (n : ℕ),
      reduce w f hf * reduce w (algebraMap A Ω t) (hwA t) ^ n ∉ P →
        reduce w (algebraMap R Ω e * f) (hle hf) * reduce w (algebraMap A Ω t) (hwA t) ^ n ∉ P := by
    intro f hf n hn hmem
    apply hn
    have hred : reduce w (algebraMap R Ω e * f) (hle hf) = reduceHom w hwA E * reduce w f hf := by
      rw [reduceHom_apply, ← reduce_mul w (hwA E) hf (by rw [← hE]; exact hle hf)]
      exact reduce_congr w (by rw [hE]) _ _
    have hE'P : reduceHom w hwA E' ∈ P := by
      rw [reduceHom_apply]
      exact hAP E'
    have := mul_mem hE'P hmem
    rwa [hred, ← mul_assoc, ← mul_assoc, hEE, one_mul] at this
  have hpole : ∀ {f : Ω} (n : ℕ), (∃ r s : A, s ∉ Ideal.span {t} ∧
      algebraMap A Ω s * (f * algebraMap A Ω t ^ n) = algebraMap A Ω r) →
        ∃ r s : A, s ∉ Ideal.span {t} ∧
          algebraMap A Ω s * (algebraMap R Ω e * f * algebraMap A Ω t ^ n) = algebraMap A Ω r := by
    rintro f n ⟨r, s, hs, h⟩
    exact ⟨E * r, s, hs, by rw [hE, map_mul, ← h]; ring⟩
  have hreg : ∀ {f : Ω}, (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → algebraMap R A ϖ ∉ 𝔮 →
      t ∉ 𝔮 → ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * f = algebraMap A Ω r) →
        ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → algebraMap R A ϖ ∉ 𝔮 →
          t ∉ 𝔮 → ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * (algebraMap R Ω e * f) =
            algebraMap A Ω r := by
    intro f hf 𝔮 hq h1 hϖ ht
    obtain ⟨r, s, hs, h⟩ := hf 𝔮 hq h1 hϖ ht
    exact ⟨E * r, s, hs, by rw [hE, map_mul, ← h]; ring⟩
  exact exists_unit_localParameter_of_maximalIdeal w ρ hker hmax hhart hcases hw hwA hϖw P hAP
    hπ (hle hx) (hle hy) (hpole 2 hpx) (hpole 3 hpy) (hreg hrx) (hreg hry)
    (by simpa using hord hx 1 (by simpa using hox)) (hord hy 2 hoy)

end Main

section Identity

/-- **Node N12-alg at the identity point of a standard smooth model (node N5).** Let `A₀` be
standard smooth of relative dimension one over the discrete valuation ring `R`, `σ` a section and
`A = (A₀)_𝔭` the local ring at the closed point of the section, assumed a domain (node N6a). The
parameter `t` of node N5 has `𝔪_A = (ϖ, t)`, `ker (localSection σ) = (t)`, and, once `t̄` is a
uniformizer of `P`, every pair `x₀, y₀` as in `exists_unit_localParameter_of_maximalIdeal` has
`x₀t², y₀t³ ∈ Aˣ` and `-x₀/y₀ = u·t` with `u ∈ Aˣ`. -/
theorem exists_localParameter_of_standardSmooth {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {A₀ : Type*} [CommRing A₀] [Algebra R A₀]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R A₀] (σ : A₀ →ₐ[R] R) {ϖ : R}
    (hϖ : Irreducible ϖ) [IsDomain (Localization.AtPrime (sectionPrime σ))]
    {Ω : Type*} [Field Ω] [Algebra (Localization.AtPrime (sectionPrime σ)) Ω]
    [IsFractionRing (Localization.AtPrime (sectionPrime σ)) Ω]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation Ω Γ₀)
    (hhart : ∀ g : Ω, (∀ 𝔮 : Ideal (Localization.AtPrime (sectionPrime σ)), 𝔮.IsPrime →
      𝔮.height = 1 → ∃ r s : Localization.AtPrime (sectionPrime σ), s ∉ 𝔮 ∧
        algebraMap _ Ω s * g = algebraMap _ Ω r) →
          g ∈ (algebraMap (Localization.AtPrime (sectionPrime σ)) Ω).range)
    (hcases : ∀ 𝔮 : Ideal (Localization.AtPrime (sectionPrime σ)), 𝔮.IsPrime → 𝔮.height = 1 →
      algebraMap R (Localization.AtPrime (sectionPrime σ)) ϖ ∈ 𝔮 →
        𝔮 = Ideal.span {algebraMap R (Localization.AtPrime (sectionPrime σ)) ϖ})
    (hw : ∀ g : Ω, w g ≤ 1 → ∃ r s : Localization.AtPrime (sectionPrime σ),
      s ∉ Ideal.span {algebraMap R (Localization.AtPrime (sectionPrime σ)) ϖ} ∧
        algebraMap _ Ω s * g = algebraMap _ Ω r)
    (hwA : ∀ a : Localization.AtPrime (sectionPrime σ), w (algebraMap _ Ω a) ≤ 1)
    (hϖw : w (algebraMap _ Ω (algebraMap R (Localization.AtPrime (sectionPrime σ)) ϖ)) < 1)
    (P : ValuationSubring (ResidueField w.valuationSubring))
    (hAP : ∀ a : Localization.AtPrime (sectionPrime σ), reduce w (algebraMap _ Ω a) (hwA a) ∈ P) :
    ∃ t : A₀, t ∈ RingHom.ker σ ∧
      maximalIdeal (Localization.AtPrime (sectionPrime σ)) =
        Ideal.span {algebraMap R (Localization.AtPrime (sectionPrime σ)) ϖ,
          algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t} ∧
      RingHom.ker (localSection σ) =
        Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t} ∧
      (IsUniformizerAt P (reduce w (algebraMap _ Ω
          (algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t)) (hwA _)) →
        ∀ {x₀ y₀ : Ω} (hx₀ : w x₀ ≤ 1) (hy₀ : w y₀ ≤ 1),
        (∃ r s : Localization.AtPrime (sectionPrime σ),
          s ∉ Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t} ∧
          algebraMap _ Ω s * (x₀ * algebraMap _ Ω
            (algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t) ^ 2) =
            algebraMap _ Ω r) →
        (∃ r s : Localization.AtPrime (sectionPrime σ),
          s ∉ Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t} ∧
          algebraMap _ Ω s * (y₀ * algebraMap _ Ω
            (algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t) ^ 3) =
            algebraMap _ Ω r) →
        (∀ 𝔮 : Ideal (Localization.AtPrime (sectionPrime σ)), 𝔮.IsPrime → 𝔮.height = 1 →
          algebraMap R (Localization.AtPrime (sectionPrime σ)) ϖ ∉ 𝔮 →
          algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t ∉ 𝔮 →
          ∃ r s : Localization.AtPrime (sectionPrime σ), s ∉ 𝔮 ∧
            algebraMap _ Ω s * x₀ = algebraMap _ Ω r) →
        (∀ 𝔮 : Ideal (Localization.AtPrime (sectionPrime σ)), 𝔮.IsPrime → 𝔮.height = 1 →
          algebraMap R (Localization.AtPrime (sectionPrime σ)) ϖ ∉ 𝔮 →
          algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t ∉ 𝔮 →
          ∃ r s : Localization.AtPrime (sectionPrime σ), s ∉ 𝔮 ∧
            algebraMap _ Ω s * y₀ = algebraMap _ Ω r) →
        reduce w x₀ hx₀ * reduce w (algebraMap _ Ω
          (algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t)) (hwA _) ∉ P →
        reduce w y₀ hy₀ * reduce w (algebraMap _ Ω
          (algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t)) (hwA _) ^ 2 ∉ P →
        ∃ a b : (Localization.AtPrime (sectionPrime σ))ˣ,
          algebraMap (Localization.AtPrime (sectionPrime σ)) Ω ↑a = x₀ * algebraMap _ Ω
            (algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t) ^ 2 ∧
          algebraMap (Localization.AtPrime (sectionPrime σ)) Ω ↑b = y₀ * algebraMap _ Ω
            (algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t) ^ 3 ∧
          -x₀ / y₀ = algebraMap (Localization.AtPrime (sectionPrime σ)) Ω ↑(-a * b⁻¹) *
            algebraMap _ Ω
            (algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t)) := by
  obtain ⟨t, ht, -, -, hmax, hker, -⟩ := localStructure_of_standardSmooth σ hϖ
  refine ⟨t, ht, hmax, hker, fun hπ x₀ y₀ hx₀ hy₀ hpx hpy hrx hry hox hoy => ?_⟩
  exact exists_unit_localParameter_of_maximalIdeal w (localSection σ) hker hmax hhart hcases hw
    hwA hϖw P hAP hπ hx₀ hy₀ hpx hpy hrx hry hox hoy

end Identity

end LocalParameter

end ZInQ.Contrib.CMHeight62Full
