import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Unramified.Kummer
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Unramified.Inertia.Cyclotomic
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.UnitsDecomposition

/-!
# The tame character of an inert local Galois group

Manuscript `diophantine_zq.tex`, tex L5027–5037 (the tame structure of an inert local Galois group,
used by the switching coordinates) and the tame half of the model (4.4).

Let `K` be a nonarchimedean local field with residue field of cardinality `q` and residue
characteristic `p`, `G_K = Gal(K^{alg}/K)` its absolute Galois group and `I_K` its inertia
subgroup (Tau Ceti). Fix `n` prime to `p`, an element `a ∈ K` and an `n`-th root `α ∈ K^{alg}` of
`a`. For `g ∈ G_K`, the **Kummer value** `κ(g) = g(α)/α` is an `n`-th root of unity.

* `kummerVal_pow`, `apply_eq_kummerVal_mul`: `κ(g)ⁿ = 1`, `g(α) = κ(g) α`;
* `kummerVal_mul_of_mem`: on inertia, which fixes the prime-to-`p` roots of unity, `κ` is
  multiplicative; `tameChar : I_K →* μₙ(K^{alg})` is the resulting **tame character**;
* `kummerVal_conj_frobenius`: **for every arithmetic Frobenius lift `φ` and `σ ∈ I_K`,
  `κ(φ σ φ⁻¹) = κ(σ)^q`** — the relation `φ σ φ⁻¹ = σ^q` of the tame quotient, read through the
  tame character (Frobenius acts on prime-to-`p` roots of unity by the `q`-th power, Tau Ceti);
* `tameChar_surjective`: for `a` a uniformizer (`v_K(a) = 1`), the tame character is
  **surjective onto `μₙ`**: if its image had order `d < n`, inertia would fix `α^d`, an
  `(n/d)`-th root of `a`, so `K(α^d)` would be unramified and `n/d ∣ v_K(a) = 1`;
* `exists_tame_generator`: there is `σ ∈ I_K` with `κ(σ)` a primitive `n`-th root of unity, and
  `exists_frobeniusLift_fix`: there is an arithmetic Frobenius lift fixing `α`.

All PROVED. (Informally, not formalized here: `I_K → μₙ` is the tame quotient at level `n`, its
kernel fixes `K^{ur}(α)`, and with a Frobenius lift `φ` fixing `α` the group `Gal(K^{ur}(α)/K)` is
`μₙ ⋊ ⟨φ⟩`, `φ` acting by `q`.)
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.TameQuotient

open TauCeti ValuativeRel IntermediateField

variable {K : Type*} [Field K] {n : ℕ} {a : K} {α : AlgebraicClosure K}

/-- The Kummer value `κ(g) = g(α)/α`. -/
def kummerVal (α : AlgebraicClosure K) (g : Gal(AlgebraicClosure K/K)) : AlgebraicClosure K :=
  g α / α

theorem apply_eq_kummerVal_mul (hα0 : α ≠ 0) (g : Gal(AlgebraicClosure K/K)) :
    g α = kummerVal α g * α := by
  rw [kummerVal, div_mul_cancel₀ _ hα0]

theorem kummerVal_pow (hα : α ^ n = algebraMap K (AlgebraicClosure K) a) (hα0 : α ≠ 0)
    (g : Gal(AlgebraicClosure K/K)) : kummerVal α g ^ n = 1 := by
  rw [kummerVal, div_pow, ← map_pow, hα, AlgEquiv.commutes, ← hα, div_self (pow_ne_zero _ hα0)]

theorem kummerVal_ne_zero (hα0 : α ≠ 0) (g : Gal(AlgebraicClosure K/K)) :
    kummerVal α g ≠ 0 :=
  div_ne_zero ((map_ne_zero _).2 hα0) hα0

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **On inertia the Kummer value is multiplicative**: `κ(σ τ) = κ(σ) κ(τ)` for `σ ∈ I_K`. -/
theorem kummerVal_mul_of_mem (hn : n.Coprime (ringChar 𝓀[K]))
    (hα : α ^ n = algebraMap K (AlgebraicClosure K) a) (hα0 : α ≠ 0)
    {σ : Gal(AlgebraicClosure K/K)} (hσ : σ ∈ inertiaSubgroup K)
    (τ : Gal(AlgebraicClosure K/K)) : kummerVal α (σ * τ) = kummerVal α σ * kummerVal α τ := by
  have hfix := apply_eq_self_of_mem_inertiaSubgroup_of_pow_eq_one hσ hn (kummerVal_pow hα hα0 τ)
  rw [kummerVal, AlgEquiv.mul_apply, apply_eq_kummerVal_mul hα0 τ, map_mul, hfix,
    apply_eq_kummerVal_mul hα0 σ, mul_div_assoc, mul_div_assoc, div_self hα0, mul_one,
    mul_comm]

/-- **The Frobenius relation of the tame quotient**: for an arithmetic Frobenius lift `φ` and
`σ ∈ I_K`, `κ(φ σ φ⁻¹) = κ(σ)^q`. -/
theorem kummerVal_conj_frobenius (hn : n.Coprime (ringChar 𝓀[K]))
    (hα : α ^ n = algebraMap K (AlgebraicClosure K) a) (hα0 : α ≠ 0)
    {φ : Gal(AlgebraicClosure K/K)} (hφ : IsArithFrobeniusLift K φ)
    {σ : Gal(AlgebraicClosure K/K)} (hσ : σ ∈ inertiaSubgroup K) :
    kummerVal α (φ * σ * φ⁻¹) = kummerVal α σ ^ Nat.card 𝓀[K] := by
  set η := kummerVal α φ⁻¹
  have hη : η ^ n = 1 := kummerVal_pow hα hα0 φ⁻¹
  have hη0 : η ≠ 0 := kummerVal_ne_zero hα0 φ⁻¹
  have hκ : kummerVal α σ ^ n = 1 := kummerVal_pow hα hα0 σ
  have hση := apply_eq_self_of_mem_inertiaSubgroup_of_pow_eq_one hσ hn hη
  -- `φ α = α / η^q`
  have hφα : φ α * η ^ Nat.card 𝓀[K] = α := by
    have h1 : φ (φ⁻¹ α) = α := by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    rw [apply_eq_kummerVal_mul hα0 φ⁻¹, map_mul, hφ.apply_of_pow_eq_one hn hη] at h1
    rw [mul_comm]
    exact h1
  have key : (φ * σ * φ⁻¹) α =
      kummerVal α σ ^ Nat.card 𝓀[K] * α := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, apply_eq_kummerVal_mul hα0 φ⁻¹, map_mul, hση,
      apply_eq_kummerVal_mul hα0 σ, map_mul, map_mul, hφ.apply_of_pow_eq_one hn hη,
      hφ.apply_of_pow_eq_one hn hκ]
    linear_combination (kummerVal α σ ^ Nat.card 𝓀[K]) * hφα
  rw [kummerVal, key, mul_div_assoc, div_self hα0, mul_one]

/-- On inertia, `κ(σ^k) = κ(σ)^k`. -/
theorem kummerVal_pow_of_mem (hn : n.Coprime (ringChar 𝓀[K]))
    (hα : α ^ n = algebraMap K (AlgebraicClosure K) a) (hα0 : α ≠ 0)
    {σ : Gal(AlgebraicClosure K/K)} (hσ : σ ∈ inertiaSubgroup K) (k : ℕ) :
    kummerVal α (σ ^ k) = kummerVal α σ ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, kummerVal, AlgEquiv.one_apply, div_self hα0]
  | succ k ih => rw [pow_succ', kummerVal_mul_of_mem hn hα hα0 hσ, ih, pow_succ']

/-- **The tame relation `φ σ φ⁻¹ = σ^q` on `α`**: `φ σ φ⁻¹` and `σ^q` move `α` the same way. -/
theorem conj_frobenius_apply_eq_pow_apply (hn : n.Coprime (ringChar 𝓀[K]))
    (hα : α ^ n = algebraMap K (AlgebraicClosure K) a) (hα0 : α ≠ 0)
    {φ : Gal(AlgebraicClosure K/K)} (hφ : IsArithFrobeniusLift K φ)
    {σ : Gal(AlgebraicClosure K/K)} (hσ : σ ∈ inertiaSubgroup K) :
    (φ * σ * φ⁻¹) α = (σ ^ Nat.card 𝓀[K]) α := by
  rw [apply_eq_kummerVal_mul hα0, apply_eq_kummerVal_mul hα0 (σ ^ _),
    kummerVal_conj_frobenius hn hα hα0 hφ hσ, kummerVal_pow_of_mem hn hα hα0 hσ]

/-- **The tame character** `I_K →* μₙ(K^{alg})`, `σ ↦ σ(α)/α`. -/
def tameChar (hn : n.Coprime (ringChar 𝓀[K]))
    (hα : α ^ n = algebraMap K (AlgebraicClosure K) a) (hα0 : α ≠ 0) :
    inertiaSubgroup K →* rootsOfUnity n (AlgebraicClosure K) where
  toFun σ := ⟨Units.mk0 (kummerVal α σ.1)
      (kummerVal_ne_zero hα0 _), by
    rw [mem_rootsOfUnity]
    ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    exact kummerVal_pow hα hα0 _⟩
  map_one' := by
    ext
    change kummerVal α (1 : Gal(AlgebraicClosure K/K)) = 1
    rw [kummerVal, AlgEquiv.one_apply, div_self hα0]
  map_mul' σ τ := by
    ext
    exact kummerVal_mul_of_mem hn hα hα0 σ.2 τ.1

theorem coe_tameChar (hn : n.Coprime (ringChar 𝓀[K]))
    (hα : α ^ n = algebraMap K (AlgebraicClosure K) a) (hα0 : α ≠ 0) (σ : inertiaSubgroup K) :
    ((tameChar hn hα hα0 σ : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) =
      kummerVal α σ.1 :=
  rfl

/-- **An element whose roots are fixed by inertia has valuation divisible by the degree**: if
`γ^m = a` with `m` prime to `p` and inertia fixes `γ`, then `m ∣ v_K(a)` (`K(γ)` is unramified,
so the normalized valuation of `K(γ)` restricts to that of `K`). -/
theorem dvd_valuation_of_inertia_fix {m : ℕ} (hm : m.Coprime (ringChar 𝓀[K])) (ha : a ≠ 0)
    {γ : AlgebraicClosure K} (hγ : γ ^ m = algebraMap K (AlgebraicClosure K) a)
    (hfix : ∀ σ : Gal(AlgebraicClosure K/K), σ ∈ inertiaSubgroup K → σ γ = γ) :
    (m : ℤ) ∣ (normalizedValuation K (Units.mk0 a ha)).toAdd := by
  have hsep : IsSeparable K γ := by
    refine (Polynomial.separable_X_pow_sub_C a (natCast_ne_zero_of_coprime_ringChar hm) ha).of_dvd
      (minpoly.dvd K γ ?_)
    simp [hγ]
  set E := IntermediateField.adjoin K {γ}
  have : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral γ)
  have : Algebra.IsSeparable K E :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K (AlgebraicClosure K)).2 hsep
  let := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) E
  let := finiteIntermediateFieldTopology K (AlgebraicClosure K) E
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) E
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) E
  have hur : IsUnramified K E := (inertiaSubgroup_le_fixingSubgroup_iff E).1 <|
    (IntermediateField.le_iff_le _ _).1 (IntermediateField.adjoin_simple_le_iff.2 fun σ ↦
      hfix σ σ.2)
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      exact natCast_ne_zero_of_coprime_ringChar hm (by simp)
    · rw [zero_pow h.ne'] at hγ
      exact ha ((map_eq_zero _).1 hγ.symm)
  set y : Eˣ := Units.mk0 ⟨γ, IntermediateField.mem_adjoin_simple_self K γ⟩
    fun h ↦ hγ0 (by simpa using congrArg ((↑) : E → AlgebraicClosure K) h)
  have hy : Units.map (algebraMap K E : K →* E) (Units.mk0 a ha) = y ^ m := by
    ext
    simp [y, hγ]
  refine ⟨(normalizedValuation E y).toAdd, ?_⟩
  rw [← hur.normalizedValuation_algebraMap (Units.mk0 a ha), hy, map_pow, toAdd_pow, nsmul_eq_mul]

/-- **The tame character is surjective** when `a` is a uniformizer (`v_K(a) = 1`). -/
theorem tameChar_surjective (hn : n.Coprime (ringChar 𝓀[K]))
    (hα : α ^ n = algebraMap K (AlgebraicClosure K) a) (hα0 : α ≠ 0) (ha : a ≠ 0)
    (hv : (normalizedValuation K (Units.mk0 a ha)).toAdd = 1) :
    Function.Surjective (tameChar hn hα hα0) := by
  have : NeZero (n : K) := ⟨natCast_ne_zero_of_coprime_ringChar hn⟩
  have : NeZero n := .of_neZero_natCast K
  set H := (tameChar hn hα hα0).range
  set d := Nat.card H
  have hcard : Nat.card (rootsOfUnity n (AlgebraicClosure K)) = n :=
    HasEnoughRootsOfUnity.natCard_rootsOfUnity _ n
  have hdn : d ∣ n := by
    have := Subgroup.card_subgroup_dvd_card H
    rwa [hcard] at this
  obtain ⟨m, hm⟩ := hdn
  have hd0 : 0 < d := Nat.card_pos
  -- inertia fixes `γ = α ^ d`, an `m`-th root of `a`
  have hfix : ∀ σ : Gal(AlgebraicClosure K/K), σ ∈ inertiaSubgroup K → σ (α ^ d) = α ^ d := by
    intro σ hσ
    have h1 : (⟨tameChar hn hα hα0 ⟨σ, hσ⟩, ⟨_, rfl⟩⟩ : H) ^ d = 1 :=
      pow_card_eq_one'
    have h2 : kummerVal α σ ^ d = 1 := by
      have := congrArg (fun x : H => (((x : rootsOfUnity n (AlgebraicClosure K)) :
        (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) h1
      exact (by simpa using this : ((tameChar hn hα hα0 ⟨σ, hσ⟩ : (AlgebraicClosure K)ˣ) :
        AlgebraicClosure K) ^ d = 1)
    rw [map_pow, apply_eq_kummerVal_mul hα0 σ, mul_pow, h2, one_mul]
  have hγ : (α ^ d) ^ m = algebraMap K (AlgebraicClosure K) a := by
    rw [← pow_mul, ← hm, hα]
  have hmc : m.Coprime (ringChar 𝓀[K]) := Nat.Coprime.coprime_dvd_left ⟨d, by rw [hm, mul_comm]⟩ hn
  have hdv := dvd_valuation_of_inertia_fix hmc ha hγ hfix
  rw [hv] at hdv
  have hm1 : m = 1 := by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hdv
  have htop : H = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hcard]
    rw [hm1, mul_one] at hm
    exact hm.symm
  intro ζ
  have : ζ ∈ H := htop ▸ Subgroup.mem_top ζ
  exact this

/-- **A tame inertia generator**: some `σ ∈ I_K` has `κ(σ)` a primitive `n`-th root of unity
(`a` a uniformizer). -/
theorem exists_tame_generator (hn : n.Coprime (ringChar 𝓀[K]))
    (hα : α ^ n = algebraMap K (AlgebraicClosure K) a) (hα0 : α ≠ 0) (ha : a ≠ 0)
    (hv : (normalizedValuation K (Units.mk0 a ha)).toAdd = 1) :
    ∃ σ : Gal(AlgebraicClosure K/K), σ ∈ inertiaSubgroup K ∧ IsPrimitiveRoot (kummerVal α σ) n := by
  have : NeZero (n : K) := ⟨natCast_ne_zero_of_coprime_ringChar hn⟩
  have : NeZero n := .of_neZero_natCast K
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure K) n
  obtain ⟨σ, hσ⟩ := tameChar_surjective hn hα hα0 ha hv
    ⟨hζ.isUnit (NeZero.ne n) |>.unit, by
      rw [mem_rootsOfUnity]; ext; simp [hζ.pow_eq_one]⟩
  refine ⟨σ.1, σ.2, ?_⟩
  have := congrArg (fun x : rootsOfUnity n (AlgebraicClosure K) =>
    ((x : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) hσ
  simp only [coe_tameChar, IsUnit.unit_spec] at this
  rw [this]
  exact hζ

/-- The residue cardinality `q` is prime to `n`. -/
theorem coprime_card_residueField (hn : n.Coprime (ringChar 𝓀[K])) :
    (Nat.card 𝓀[K]).Coprime n := by
  let _ := Fintype.ofFinite 𝓀[K]
  obtain ⟨d, -, hd⟩ := FiniteField.card 𝓀[K] (ringChar 𝓀[K])
  rw [Nat.card_eq_fintype_card, hd]
  exact hn.symm.pow_left _

/-- **A Frobenius lift fixing `α`** (`a` a uniformizer): adjust any lift `φ₀` by `τ ∈ I_K` with
`κ(τ)^q = κ(φ₀)⁻¹`. -/
theorem exists_frobeniusLift_fix (hn : n.Coprime (ringChar 𝓀[K]))
    (hα : α ^ n = algebraMap K (AlgebraicClosure K) a) (hα0 : α ≠ 0) (ha : a ≠ 0)
    (hv : (normalizedValuation K (Units.mk0 a ha)).toAdd = 1) :
    ∃ φ : Gal(AlgebraicClosure K/K), IsArithFrobeniusLift K φ ∧ φ α = α := by
  have : NeZero (n : K) := ⟨natCast_ne_zero_of_coprime_ringChar hn⟩
  have : NeZero n := .of_neZero_natCast K
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : Gal(AlgebraicClosure K/K), IsArithFrobeniusLift K φ₀ :=
    exists_isArithFrobeniusLift K
  set c : rootsOfUnity n (AlgebraicClosure K) :=
    ⟨Units.mk0 (kummerVal α φ₀) (kummerVal_ne_zero hα0 _), by
      rw [mem_rootsOfUnity]; ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      exact kummerVal_pow hα hα0 φ₀⟩ with hc
  have hcard : Nat.card (rootsOfUnity n (AlgebraicClosure K)) = n :=
    HasEnoughRootsOfUnity.natCard_rootsOfUnity _ n
  have hq : (Nat.card (rootsOfUnity n (AlgebraicClosure K))).Coprime (Nat.card 𝓀[K]) := by
    rw [hcard]; exact (coprime_card_residueField hn).symm
  set ζ := (powCoprime hq).symm c⁻¹
  have hζ : ζ ^ Nat.card 𝓀[K] = c⁻¹ := (powCoprime hq).apply_symm_apply c⁻¹
  obtain ⟨τ, hτ⟩ := tameChar_surjective hn hα hα0 ha hv ζ
  set τ' : Gal(AlgebraicClosure K/K) := τ.1
  refine ⟨φ₀ * τ', hφ₀.isArithFrobeniusLift_iff_inv_mul_mem.2
    (by convert τ.2 using 1; exact inv_mul_cancel_left φ₀ τ'), ?_⟩
  have hκτ : kummerVal α τ' = ((ζ : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) :=
    congrArg (fun x : rootsOfUnity n (AlgebraicClosure K) =>
      ((x : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) hτ
  have hζ' : ((ζ : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) ^ Nat.card 𝓀[K] *
      kummerVal α φ₀ = 1 := by
    have := congrArg (fun x : rootsOfUnity n (AlgebraicClosure K) =>
      ((x : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) hζ
    simp only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val] at this
    rw [this]
    change (((c⁻¹ : rootsOfUnity n (AlgebraicClosure K)) : (AlgebraicClosure K)ˣ) :
      AlgebraicClosure K) * ((c : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) = 1
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have hζn : ((ζ : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) ^ n = 1 := by
    have := ζ.2
    rw [mem_rootsOfUnity] at this
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  rw [AlgEquiv.mul_apply, apply_eq_kummerVal_mul hα0 τ', map_mul, hκτ,
    hφ₀.apply_of_pow_eq_one hn hζn, apply_eq_kummerVal_mul hα0 φ₀, ← mul_assoc, hζ', one_mul]

end ZInQ.Contrib.CloudB3RC53.TameQuotient
