import ZInQKernel.Contrib.RC53Assist.NewformGlueG0.GaloisCompletion

/-!
# Conjugacy of the places of the algebraic numbers above a rational prime

For a rational prime `p`, the absolute Galois group `G_ℚ` acts transitively on the valuation
subrings of `\bar ℚ` lying over `p` (`exists_galois_conj`). Consequently, for every algebraically
closed field `Ω` of characteristic zero and every valuation subring `A₀` of `Ω` lying over `p`,
every valuation subring of `\bar ℚ` lying over `p` is the pull-back of `A₀` along some embedding
`\bar ℚ → Ω` (`exists_algHom_comap_eq`).

The proof passes through the centre of a valuation subring on the integral closure `\bar ℤ` of
`ℤ` in `\bar ℚ`: two valuation subrings lying over `p` with the same centre coincide
(`le_of_centre_eq`), and the centres are permuted transitively by `G_ℚ`, by Mathlib
`Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite` (profinite form of the transitivity of
the Galois group on the primes above `p`: Lang, *Algebraic Number Theory*, Ch. I, §5, and
Milne, *Algebraic Number Theory*, v3.08, proof of Prop. 8.10, p. 139, at finite level).

## Classification

Definitions and PROVED statements only; no hypotheses are assumed.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.DecompositionGlue

open NumberField
open scoped Pointwise
open GlueC10 (Qbar GQ Zbar)
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic (LocMem locMem_or_inv LiesOver)

/-- **PROVED**, membership in the non-units of a valuation subring, read through its valuation
in `ValuationSubring.mem_nonunits_iff_or`. Locator: Mathlib `ValuationSubring.nonunits`. -/
theorem mem_nonunits_comap {F E : Type*} [Field F] [Field E] (A : ValuationSubring E)
    (f : F →+* E) {x : F} : x ∈ (A.comap f).nonunits ↔ f x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap, map_inv₀, map_eq_zero_iff f f.injective]

/-- **PROVED**, every algebraic integer lies in every valuation subring of `\bar ℚ`.
Locator: Mathlib `IsIntegrallyClosed.isIntegral_iff`, valuation subrings being integrally
closed. -/
theorem zbar_mem (A : ValuationSubring Qbar) (z : Zbar) : (z : Qbar) ∈ A := by
  have hz : IsIntegral ℤ (z : Qbar) := z.2
  have hzA : IsIntegral A (z : Qbar) := hz.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hzA
  rw [← hy]
  exact y.2

/-- **DEFINITION**, the inclusion of `\bar ℤ` in a valuation subring of `\bar ℚ`.
Locator: `zbar_mem`. -/
def zbarToPlace (A : ValuationSubring Qbar) : Zbar →+* A :=
  (algebraMap Zbar Qbar).codRestrict A (zbar_mem A)

/-- **DEFINITION**, the centre on `\bar ℤ` of a valuation subring of `\bar ℚ`: the contraction of
its maximal ideal. Locator: Mathlib `Ideal.comap`. -/
def centre (A : ValuationSubring Qbar) : Ideal Zbar :=
  (IsLocalRing.maximalIdeal A).comap (zbarToPlace A)

/-- **PROVED**, the centre is a prime ideal. Locator: Mathlib `Ideal.comap_isPrime`. -/
instance centre_isPrime (A : ValuationSubring Qbar) : (centre A).IsPrime :=
  Ideal.comap_isPrime _ _

/-- **PROVED**, membership in the centre. Locator: Mathlib
`ValuationSubring.valuation_lt_one_iff`, `ValuationSubring.mem_nonunits_iff`. -/
theorem mem_centre {A : ValuationSubring Qbar} {z : Zbar} :
    z ∈ centre A ↔ (z : Qbar) ∈ A.nonunits := by
  rw [centre, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff,
    ValuationSubring.mem_nonunits_iff]
  rfl

/-- **PROVED**, the centre of a valuation subring lying over `p` contracts to `(p)` in `ℤ`.
Locator: Mathlib `Int.ideal_span_isMaximal_of_prime`. -/
theorem centre_under {A : ValuationSubring Qbar} {p : ℕ} (hp : p.Prime) (hA : LiesOver A p) :
    (centre A).under ℤ = Ideal.span {(p : ℤ)} := by
  have : Fact p.Prime := ⟨hp⟩
  symm
  apply (Int.ideal_span_isMaximal_of_prime p).eq_of_le
  · exact Ideal.IsPrime.ne_top inferInstance
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under, Ideal.mem_comap,
      mem_centre]
    have : ((algebraMap ℤ Zbar (p : ℤ) : Zbar) : Qbar) = (p : Qbar) := by simp
    rw [this]
    exact hA

/-- **PROVED**, the valuation of an algebraic integer is at most one. Locator: `zbar_mem`. -/
theorem valuation_zbar_le_one (A : ValuationSubring Qbar) (z : Zbar) :
    A.valuation (z : Qbar) ≤ 1 :=
  (A.valuation_le_one_iff _).2 (zbar_mem A z)

/-- **PROVED**, an algebraic integer outside the centre has valuation one. Locator:
`mem_centre`. -/
theorem valuation_zbar_eq_one {A : ValuationSubring Qbar} {z : Zbar} (hz : z ∉ centre A) :
    A.valuation (z : Qbar) = 1 := by
  rw [mem_centre, ValuationSubring.mem_nonunits_iff, not_lt] at hz
  exact le_antisymm (valuation_zbar_le_one A z) hz

/-- **PROVED**, two valuation subrings of `\bar ℚ` lying over `p` with the same centre on
`\bar ℤ` are comparable, hence (by symmetry) equal. The input is the localization statement
`locMem_or_inv`: every algebraic number or its inverse is a fraction `a / s` of algebraic
integers with `s` outside the centre. -/
theorem le_of_centre_eq {A B : ValuationSubring Qbar} {p : ℕ} (hp : p.Prime)
    (hA : (centre A).under ℤ = Ideal.span {(p : ℤ)}) (h : centre A = centre B) : A ≤ B := by
  intro x hx
  rw [← ValuationSubring.valuation_le_one_iff] at hx ⊢
  rcases locMem_or_inv (centre A) p hp hA x with ⟨a, s, hs, ha⟩ | ⟨a, s, hs, ha⟩
  · have hsB : B.valuation (s : Qbar) = 1 := valuation_zbar_eq_one (h ▸ hs)
    have e := congrArg B.valuation ha
    rw [map_mul, hsB, mul_one] at e
    rw [e]
    exact valuation_zbar_le_one B a
  · by_cases hx0 : x = 0
    · rw [hx0, map_zero]
      exact zero_le_one
    have hsA : A.valuation (s : Qbar) = 1 := valuation_zbar_eq_one hs
    by_cases haA : a ∈ centre A
    · exfalso
      have haA' : A.valuation (a : Qbar) < 1 := by
        rw [mem_centre, ValuationSubring.mem_nonunits_iff] at haA
        exact haA
      have e := congrArg A.valuation ha
      rw [map_mul, hsA, mul_one, map_inv₀] at e
      have hv0 : A.valuation x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
      have h1 : 1 ≤ (A.valuation x)⁻¹ := one_le_inv₀ (zero_lt_iff.2 hv0) |>.2 hx
      rw [e] at h1
      exact absurd haA' (not_lt.2 h1)
    · have haB : B.valuation (a : Qbar) = 1 := valuation_zbar_eq_one (h ▸ haA)
      have e := congrArg B.valuation ha
      rw [map_mul, haB, map_inv₀] at e
      have hv0 : B.valuation x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
      have hs1 := valuation_zbar_le_one B s
      have : (B.valuation x)⁻¹ * B.valuation (s : Qbar) ≤ (B.valuation x)⁻¹ :=
        mul_le_of_le_one_right' hs1
      rw [e] at this
      exact (one_le_inv₀ (zero_lt_iff.2 hv0)).1 this

/-- **DEFINITION**, the action of `G_ℚ` on `\bar ℤ` by restriction. Locator: Mathlib
`galRestrict`. -/
@[reducible]
def zbarAction : MulSemiringAction GQ Zbar :=
  MulSemiringAction.compHom Zbar (galRestrict ℤ ℚ Qbar Zbar).toMonoidHom

/-- **PROVED**, the restricted action is the action on `\bar ℚ`. Locator: Mathlib
`algebraMap_galRestrict_apply`. -/
theorem coe_zbarAction_smul (g : GQ) (z : Zbar) :
    ((@HSMul.hSMul GQ Zbar Zbar (@instHSMul GQ Zbar zbarAction.toSMul) g z : Zbar) : Qbar) =
      g (z : Qbar) :=
  algebraMap_galRestrict_apply ℤ g z

/-- **PROVED**, `G_ℚ` acts transitively on the valuation subrings of `\bar ℚ` lying over a
rational prime `p`: for two such `A` and `B` there is `g ∈ G_ℚ` with `B = g⁻¹(A)`. Locator:
Mathlib `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite` (compactness of `G_ℚ` and the
finite-level transitivity on primes, Lang, Ch. I, §5), with `le_of_centre_eq`. -/
theorem exists_galois_conj {A B : ValuationSubring Qbar} {p : ℕ} (hp : p.Prime)
    (hA : LiesOver A p) (hB : LiesOver B p) : ∃ g : GQ, ∀ x : Qbar, x ∈ B ↔ g x ∈ A := by
  let _ : MulSemiringAction GQ Zbar := zbarAction
  have hsmul : ∀ (g : GQ) (z : Zbar), ((g • z : Zbar) : Qbar) = g (z : Qbar) :=
    coe_zbarAction_smul
  let _ : TopologicalSpace Zbar := ⊥
  have : DiscreteTopology Zbar := ⟨rfl⟩
  have : ContinuousSMul GQ Zbar := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro z
    convert stabilizer_isOpen_of_isIntegral (K := ℚ) (z : Qbar) using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    rw [← Subtype.coe_inj, hsmul]
    rfl
  have : SMulCommClass GQ ℤ Zbar :=
    ⟨fun g n z => by
      apply Subtype.ext
      rw [hsmul, AddSubgroupClass.coe_zsmul, AddSubgroupClass.coe_zsmul, hsmul, map_zsmul]⟩
  have : Algebra.IsInvariant ℤ Zbar GQ := ⟨fun z hz => by
    have hfix : ∀ g : GQ, g (z : Qbar) = (z : Qbar) := fun g => by rw [← hsmul, hz g]
    obtain ⟨q, hq⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (z : Qbar)).mpr hfix
    have hqi : IsIntegral ℤ q := by
      have h1 : IsIntegral ℤ (algebraMap ℚ Qbar q) := hq ▸ z.2
      exact isIntegral_algebraMap_iff.mp h1
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hqi
    refine ⟨n, Subtype.ext ?_⟩
    rw [← hq, ← hn]
    simp⟩
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := ℤ) (G := GQ)
    (centre B) (centre A) ((centre_under hp hB).trans (centre_under hp hA).symm)
  have hc : centre B = centre (A.comap (g : Qbar →+* Qbar)) := by
    ext z
    rw [← Ideal.smul_mem_pointwise_smul_iff (a := g), ← hg, mem_centre, hsmul, mem_centre,
      mem_nonunits_comap]
    rfl
  have hBA : B = A.comap (g : Qbar →+* Qbar) :=
    le_antisymm (le_of_centre_eq hp (centre_under hp hB) hc)
      (le_of_centre_eq hp (hc ▸ centre_under hp hB) hc.symm)
  refine ⟨g, fun x => ?_⟩
  rw [hBA, ValuationSubring.mem_comap]
  rfl

/-- **PROVED**, realisation of a given place of `\bar ℚ` above `p` by an embedding: if `Ω` is an
algebraically closed field of characteristic zero and `A₀` a valuation subring of `Ω` in which `p`
is a non-unit, then every valuation subring `B` of `\bar ℚ` lying over `p` is `ι⁻¹(A₀)` for some
`ℚ`-embedding `ι : \bar ℚ → Ω`. Locator: `exists_galois_conj` applied to `B` and the pull-back of
`A₀` along an arbitrary embedding (Mathlib `IsAlgClosed.lift`). -/
theorem exists_algHom_comap_eq {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω]
    (A₀ : ValuationSubring Ω) {p : ℕ} (hp : p.Prime) (h₀ : (p : Ω) ∈ A₀.nonunits)
    (B : ValuationSubring Qbar) (hB : LiesOver B p) :
    ∃ ι : Qbar →ₐ[ℚ] Ω, ∀ x : Qbar, x ∈ B ↔ ι x ∈ A₀ := by
  let ι₀ : Qbar →ₐ[ℚ] Ω := IsAlgClosed.lift
  have hA : LiesOver (A₀.comap (ι₀ : Qbar →+* Ω)) p := by
    rw [LiesOver, mem_nonunits_comap]
    simpa using h₀
  obtain ⟨g, hg⟩ := exists_galois_conj hp hA hB
  refine ⟨ι₀.comp (g : Qbar →ₐ[ℚ] Qbar), fun x => ?_⟩
  rw [hg x, ValuationSubring.mem_comap]
  rfl

end ZInQ.Contrib.RC53Assist.DecompositionGlue
