import ZInQKernel.Contrib.OneProof.CMHeight62Full.IdentityPointDepth

/-!
# Local rings of the special fibre at closed points are discrete valuation rings

Let `R` be a discrete valuation ring with uniformizer `ϖ` and perfect residue field `k`, let `B`
be a standard smooth `R`-algebra of relative dimension one, and let `𝔭` be a maximal ideal of
`B` containing `ϖ` (a closed point of the special fibre, not necessarily `k`-rational). We prove
that `B_𝔭 ⧸ (ϖ)`, the local ring of the special fibre at `𝔭`, is a domain and a discrete
valuation ring (`isDiscreteValuationRing_quotient_of_standardSmooth`). The bundled form
`closedPoint_depthTwo` also records the parameter `t` with `𝔪_{B_𝔭} = (ϖ, t)`, that `ϖ` is a
nonzerodivisor, and that `B_𝔭 ⧸ (ϖ)` has dimension one; `closedPoint_of_depthTwo` is the form
consumed by the depth-two lemmas. The same argument over a perfect field `k` (with `J = 𝔭²`)
shows that `B_𝔭` is a discrete valuation ring for a standard smooth `k`-algebra `B` of relative
dimension one and any maximal ideal `𝔭` (`isDiscreteValuationRing_localization_of_standardSmooth`).

The method is that of `LocalStructure.lean`, with the section replaced by the residue map
`π : B → κ = B ⧸ 𝔭`. Fix a basis `ω` of `Ω[B⁄R]` and put `D a = π (coordinate of da)`.

* `κ` is finite over `k` (Nullstellensatz), hence separable, hence formally étale over `k` and
  formally unramified over `R`. The conormal sequence then gives `t ∈ 𝔭` with `D t = 1`
  (`exists_mem_fibreDer_eq_one`).
* With `J = 𝔭² + (ϖ)`, the ring `B ⧸ J` is a `k`-algebra, and formal smoothness of `κ` over `k`
  gives a `k`-section `s` of `B ⧸ J → κ`. Then `a ↦ [a] - s (π a)` is an `R`-derivation into
  `B ⧸ J`, which shows that `x ∈ 𝔭` and `D x = 0` imply `x ∈ J` (`mem_of_fibreDer_eq_zero`).
  Hence `𝔭 ≤ (t) + J` and, by Nakayama, `𝔪_{B_𝔭} = (ϖ, t)`.
* Formal smoothness of `B` over `R` lifts `a ↦ π a + D a · X` to `B → κ[X] ⧸ (X^(n+1))`; since
  `ϖ` maps to zero there, `s tⁿ ∉ (ϖ)` for every `s ∉ 𝔭` (`mul_pow_notMem_span`). So the class
  of `t` in `B_𝔭 ⧸ (ϖ)` generates the maximal ideal and is not nilpotent, and the generic cores
  `IdentityPointDepth.isDomain_of_maximalIdeal_eq_span` and
  `IdentityPointDepth.isDiscreteValuationRing_of_maximalIdeal_eq_span` apply.

This also shows `dim (B_𝔭 ⧸ (ϖ)) ≥ 1` without any dimension theory of smooth algebras: the
non-nilpotence of `t` comes from the infinitesimal lifting property alone.

The perfectness of `k` is used only to make `κ ⧸ k` separable. It holds in the application,
where `k` is the residue field of a prime of a number field, a finite field.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open IsLocalRing Polynomial

namespace SpecialFibreDVR

section Derivation

variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B]
variable (𝔭 : Ideal B) (b : Module.Basis (Fin 1) B Ω[B⁄R])

/-- The derivation `B → B ⧸ 𝔭` along the residue map: the class of the coordinate of `da`. -/
def fibreDer (a : B) : B ⧸ 𝔭 :=
  Ideal.Quotient.mk 𝔭 (b.repr (KaehlerDifferential.D R B a) 0)

theorem fibreDer_add (x y : B) :
    fibreDer 𝔭 b (x + y) = fibreDer 𝔭 b x + fibreDer 𝔭 b y := by
  simp [fibreDer]

theorem fibreDer_sub (x y : B) :
    fibreDer 𝔭 b (x - y) = fibreDer 𝔭 b x - fibreDer 𝔭 b y := by
  simp [fibreDer]

theorem fibreDer_mul (x y : B) :
    fibreDer 𝔭 b (x * y) =
      Ideal.Quotient.mk 𝔭 x * fibreDer 𝔭 b y + Ideal.Quotient.mk 𝔭 y * fibreDer 𝔭 b x := by
  simp [fibreDer, Derivation.leibniz]

theorem fibreDer_algebraMap (r : R) : fibreDer 𝔭 b (algebraMap R B r) = 0 := by
  simp [fibreDer]

theorem fibreDer_zero : fibreDer 𝔭 b 0 = 0 := by
  simp [fibreDer]

theorem fibreDer_one : fibreDer 𝔭 b 1 = 0 := by
  simp [fibreDer]

/-- If `κ = B ⧸ 𝔭` is formally unramified over `R`, there is `t ∈ 𝔭` with `D t = 1`. -/
theorem exists_mem_fibreDer_eq_one [Algebra.FormallyUnramified R (B ⧸ 𝔭)] :
    ∃ t ∈ 𝔭, fibreDer 𝔭 b t = 1 := by
  have hsurj : Function.Surjective (algebraMap B (B ⧸ 𝔭)) := Ideal.Quotient.mk_surjective
  have hex := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R B (B ⧸ 𝔭) hsurj
  obtain ⟨y, hy⟩ := (hex (1 ⊗ₜ b 0)).1 (Subsingleton.elim _ _)
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ y
  refine ⟨x, ?_, ?_⟩
  · rw [RingHom.mem_ker, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact hx
  · rw [KaehlerDifferential.kerCotangentToTensor_toCotangent] at hy
    have := congrArg (fun z => (Algebra.TensorProduct.basis (B ⧸ 𝔭) b).repr z 0) hy
    simp [Algebra.TensorProduct.basis_repr_tmul] at this
    exact this

end Derivation

section Section

variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B]
variable (𝔭 : Ideal B) (b : Module.Basis (Fin 1) B Ω[B⁄R])
variable {J : Ideal B} (hJ𝔭 : J ≤ 𝔭)
variable {k : Type*} [CommRing k] [Algebra R k] [Algebra k (B ⧸ 𝔭)] [Algebra k (B ⧸ J)]
  [IsScalarTower R k (B ⧸ 𝔭)] [IsScalarTower R k (B ⧸ J)]

/-- The projection `B ⧸ J → B ⧸ 𝔭` as a `k`-algebra map, when `R → k` is surjective. -/
def factorAlgHom (hk : Function.Surjective (algebraMap R k)) : (B ⧸ J) →ₐ[k] (B ⧸ 𝔭) :=
  { Ideal.Quotient.factor hJ𝔭 with
    commutes' := fun r => by
      obtain ⟨r, rfl⟩ := hk r
      change Ideal.Quotient.factor hJ𝔭 _ = _
      rw [← IsScalarTower.algebraMap_apply R k (B ⧸ J),
        ← IsScalarTower.algebraMap_apply R k (B ⧸ 𝔭)]
      exact Ideal.Quotient.factor_mk hJ𝔭 _ }

theorem factorAlgHom_apply (hk : Function.Surjective (algebraMap R k)) (y : B ⧸ J) :
    factorAlgHom 𝔭 hJ𝔭 hk y = Ideal.Quotient.factor hJ𝔭 y :=
  rfl

theorem ker_factor_le :
    RingHom.ker (Ideal.Quotient.factor hJ𝔭) ≤ 𝔭.map (Ideal.Quotient.mk J) := by
  intro y hy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hy
  exact Ideal.mem_map_of_mem _ hy

variable (hsqJ : 𝔭 ^ 2 ≤ J)
include hsqJ

theorem ker_factor_sq : RingHom.ker (Ideal.Quotient.factor hJ𝔭) ^ 2 = ⊥ := by
  refine le_bot_iff.1 ?_
  calc RingHom.ker (Ideal.Quotient.factor hJ𝔭) ^ 2 ≤ (𝔭.map (Ideal.Quotient.mk J)) ^ 2 :=
        Ideal.pow_right_mono (ker_factor_le 𝔭 hJ𝔭) 2
    _ = (𝔭 ^ 2).map (Ideal.Quotient.mk J) := (Ideal.map_pow _ _ _).symm
    _ ≤ J.map (Ideal.Quotient.mk J) := Ideal.map_mono hsqJ
    _ = ⊥ := Ideal.map_quotient_self J

theorem isNilpotent_ker_factorAlgHom (hk : Function.Surjective (algebraMap R k)) :
    IsNilpotent (RingHom.ker (factorAlgHom 𝔭 hJ𝔭 hk : (B ⧸ J) →+* (B ⧸ 𝔭))) :=
  ⟨2, ker_factor_sq 𝔭 hJ𝔭 hsqJ⟩

variable (s : (B ⧸ 𝔭) →ₐ[k] (B ⧸ J)) (hs : ∀ y, Ideal.Quotient.factor hJ𝔭 (s y) = y)
include hs

omit hsqJ in
theorem sub_mem_ker_factor (a : B) :
    Ideal.Quotient.mk J a - s (Ideal.Quotient.mk 𝔭 a) ∈
      RingHom.ker (Ideal.Quotient.factor hJ𝔭) := by
  rw [RingHom.mem_ker, map_sub, Ideal.Quotient.factor_mk, hs, sub_self]

theorem sub_mul_sub_eq_zero (a c : B) :
    (Ideal.Quotient.mk J a - s (Ideal.Quotient.mk 𝔭 a)) *
      (Ideal.Quotient.mk J c - s (Ideal.Quotient.mk 𝔭 c)) = 0 := by
  have h := Ideal.mul_mem_mul (sub_mem_ker_factor 𝔭 hJ𝔭 s hs a)
    (sub_mem_ker_factor 𝔭 hJ𝔭 s hs c)
  rw [← sq, ker_factor_sq 𝔭 hJ𝔭 hsqJ, Ideal.mem_bot] at h
  exact h

/-- The `R`-derivation `a ↦ [a] - s (π a)` of `B` into `B ⧸ J`. -/
def secDiff : Derivation R B (B ⧸ J) :=
  Derivation.mk' ((Ideal.Quotient.mkₐ R J).toLinearMap -
      ((s.restrictScalars R).toLinearMap ∘ₗ (Ideal.Quotient.mkₐ R 𝔭).toLinearMap))
    (fun a c => by
      have h := sub_mul_sub_eq_zero 𝔭 hJ𝔭 hsqJ s hs a c
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        Ideal.Quotient.mkₐ_eq_mk, AlgHom.coe_restrictScalars' R, map_mul, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq]
      linear_combination -h)

theorem secDiff_apply (a : B) :
    secDiff (R := R) 𝔭 hJ𝔭 hsqJ s hs a = Ideal.Quotient.mk J a - s (Ideal.Quotient.mk 𝔭 a) :=
  rfl

/-- **Second-order step.** If `x ∈ 𝔭` and `D x = 0`, then `x ∈ J`. -/
theorem mem_of_fibreDer_eq_zero {x : B} (hx : x ∈ 𝔭) (hD : fibreDer 𝔭 b x = 0) : x ∈ J := by
  set d := secDiff (R := R) 𝔭 hJ𝔭 hsqJ s hs
  have hL : ∀ ω, d.liftKaehlerDifferential ω ∈ RingHom.ker (Ideal.Quotient.factor hJ𝔭) := by
    intro ω
    have hω : ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D R B)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hω using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      rw [Derivation.liftKaehlerDifferential_comp_D, secDiff_apply]
      exact sub_mem_ker_factor 𝔭 hJ𝔭 s hs a
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add]
      exact add_mem hy hz
    | smul a y _ hy =>
      rw [map_smul, Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ hy
  set c := b.repr (KaehlerDifferential.D R B x) 0
  have hrepr : KaehlerDifferential.D R B x = c • b 0 := by
    conv_lhs => rw [← b.sum_repr (KaehlerDifferential.D R B x)]
    simp [c]
  have hc : Ideal.Quotient.mk J c ∈ RingHom.ker (Ideal.Quotient.factor hJ𝔭) := by
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk]
    exact hD
  have h0 : d x = 0 := by
    rw [← Derivation.liftKaehlerDifferential_comp_D, hrepr, map_smul, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq]
    have h := Ideal.mul_mem_mul hc (hL (b 0))
    rw [← sq, ker_factor_sq 𝔭 hJ𝔭 hsqJ, Ideal.mem_bot] at h
    exact h
  rw [secDiff_apply, (Ideal.Quotient.eq_zero_iff_mem).2 hx, map_zero, sub_zero,
    Ideal.Quotient.eq_zero_iff_mem] at h0
  exact h0

end Section

section Generator

variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B]
variable (𝔭 : Ideal B) (b : Module.Basis (Fin 1) B Ω[B⁄R])

/-- `𝔭 ≤ (t) + J` once `D t = 1` and `D x = 0` forces `x ∈ J` on `𝔭`. -/
theorem le_span_sup {J : Ideal B} (hpar : ∀ x ∈ 𝔭, fibreDer 𝔭 b x = 0 → x ∈ J) {t : B}
    (ht : t ∈ 𝔭) (hDt : fibreDer 𝔭 b t = 1) : 𝔭 ≤ Ideal.span {t} ⊔ J := by
  intro x hx
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (fibreDer 𝔭 b x)
  have hy : x - a * t ∈ J := by
    refine hpar _ (sub_mem hx (Ideal.mul_mem_left _ _ ht)) ?_
    rw [fibreDer_sub, fibreDer_mul, hDt, (Ideal.Quotient.eq_zero_iff_mem).2 ht, ha]
    ring
  have : x = a * t + (x - a * t) := by ring
  rw [this]
  exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self t)) hy

/-- Key estimate: if `t ∈ 𝔭`, `D t = 1` and `p ∈ R` maps into `𝔭`, then `s tⁿ ∉ (p)` for
every `s ∉ 𝔭`. -/
theorem mul_pow_notMem_span [Algebra.FormallySmooth R B] {t : B} (ht : t ∈ 𝔭)
    (hDt : fibreDer 𝔭 b t = 1) {p : R} (hp : algebraMap R B p ∈ 𝔭) {s : B} (hs : s ∉ 𝔭)
    (n : ℕ) : s * t ^ n ∉ Ideal.span {algebraMap R B p} := by
  intro h0
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h0
  let π := Ideal.Quotient.mk 𝔭
  let E := (B ⧸ 𝔭)[X] ⧸ Ideal.span {(X : (B ⧸ 𝔭)[X]) ^ (n + 1)}
  let : CommRing E := Ideal.Quotient.commRing _
  let x : E := Ideal.Quotient.mk _ X
  have hx : x ^ (n + 1) = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  let J : Ideal E := Ideal.span {x ^ 2}
  have hJ : IsNilpotent J := by
    refine ⟨n + 1, ?_⟩
    rw [Ideal.zero_eq_bot, Ideal.span_singleton_pow, ← pow_mul, mul_comm, pow_mul, hx,
      zero_pow two_ne_zero, Ideal.span_singleton_eq_bot]
  let δ : B → E := fun a => algebraMap (B ⧸ 𝔭) E (π a) +
    algebraMap (B ⧸ 𝔭) E (fibreDer 𝔭 b a) * x
  have hδmul : ∀ a c, δ (a * c) - δ a * δ c ∈ J := by
    intro a c
    refine Ideal.mem_span_singleton'.2
      ⟨-(algebraMap (B ⧸ 𝔭) E (fibreDer 𝔭 b a) * algebraMap (B ⧸ 𝔭) E (fibreDer 𝔭 b c)), ?_⟩
    simp only [δ, fibreDer_mul, map_mul, map_add]
    ring
  let g : B →ₐ[R] E ⧸ J :=
    { toFun := fun a => Ideal.Quotient.mk J (δ a)
      map_one' := by simp [δ, fibreDer_one]
      map_mul' := fun a c => by
        rw [← (Ideal.Quotient.mk J).map_mul]
        exact Ideal.Quotient.eq.2 (hδmul a c)
      map_zero' := by simp [δ, fibreDer_zero]
      map_add' := fun a c => by
        rw [← (Ideal.Quotient.mk J).map_add]
        congr 1
        simp only [δ, map_add, fibreDer_add]
        ring
      commutes' := fun r => by
        simp only [δ, fibreDer_algebraMap, map_zero, zero_mul, add_zero, π]
        exact (IsScalarTower.algebraMap_apply R (B ⧸ 𝔭) (E ⧸ J) r).symm }
  let ψ := Algebra.FormallySmooth.lift J hJ g
  have key : ∀ a, ψ a - δ a ∈ J := fun a =>
    Ideal.Quotient.eq.1 (Algebra.FormallySmooth.mk_lift J hJ g a)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (key t)
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.1 (key s)
  have hπt : π t = 0 := (Ideal.Quotient.eq_zero_iff_mem).2 ht
  simp only [δ, hπt, hDt, map_zero, map_one, zero_add, one_mul] at hc
  have htt : ψ t = x * (1 + c * x) := by linear_combination -hc
  have hss : ψ s = algebraMap (B ⧸ 𝔭) E (π s) +
      x * (algebraMap (B ⧸ 𝔭) E (fibreDer 𝔭 b s) + c' * x) := by
    linear_combination -hc'
  have hp0 : algebraMap R E p = 0 := by
    have h : algebraMap R (B ⧸ 𝔭) p = 0 := (Ideal.Quotient.eq_zero_iff_mem).2 hp
    rw [IsScalarTower.algebraMap_apply R (B ⧸ 𝔭) E, h, map_zero]
  have hψ : ψ (s * t ^ n) = 0 := by
    rw [← hy, map_mul, ψ.commutes, hp0, mul_zero]
  rw [map_mul, map_pow, htt, hss, mul_pow] at hψ
  obtain ⟨e, he⟩ := sub_dvd_pow_sub_pow (1 + c * x) 1 n
  set r := algebraMap (B ⧸ 𝔭) E (π s)
  set d := algebraMap (B ⧸ 𝔭) E (fibreDer 𝔭 b s) + c' * x
  have hrx : r * x ^ n = 0 := by
    linear_combination hψ - r * x ^ n * he - (r * c * e + d * (1 + c * x) ^ n) * hx
  have hmk : Ideal.Quotient.mk (Ideal.span {(X : (B ⧸ 𝔭)[X]) ^ (n + 1)})
      (C (π s) * X ^ n) = 0 := by
    rw [map_mul, map_pow]
    exact hrx
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hmk
  obtain ⟨q, hq⟩ := hmk
  have hcoeff := congrArg (fun f : (B ⧸ 𝔭)[X] => f.coeff n) hq
  simp [coeff_X_pow_mul'] at hcoeff
  exact hs ((Ideal.Quotient.eq_zero_iff_mem).1 hcoeff)

end Generator

end SpecialFibreDVR

open SpecialFibreDVR IdentityPointDepth

/-- **Node L1a, the parameter.** Let `R` be a discrete valuation ring with perfect residue
field and uniformizer `ϖ`, let `B` be a standard smooth `R`-algebra of relative dimension one,
and let `𝔭` be a maximal ideal of `B` containing `ϖ`. There is `t ∈ 𝔭` with
`𝔪_{B_𝔭} = (ϖ, t)` such that `s tⁿ ∉ (ϖ)` for every `s ∉ 𝔭` and every `n`. -/
theorem closedPoint_param {R : Type*} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] {ϖ : R}
    (hϖ : Irreducible ϖ) {B : Type*} [CommRing B] [Algebra R B]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R B]
    (𝔭 : Ideal B) [𝔭.IsMaximal] (h𝔭 : algebraMap R B ϖ ∈ 𝔭) :
    ∃ t ∈ 𝔭, maximalIdeal (Localization.AtPrime 𝔭) =
        Ideal.span {algebraMap R (Localization.AtPrime 𝔭) ϖ,
          algebraMap B (Localization.AtPrime 𝔭) t} ∧
      ∀ s ∉ 𝔭, ∀ n : ℕ, s * t ^ n ∉ Ideal.span {algebraMap R B ϖ} := by
  have : Algebra.IsStandardSmooth R B :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  let : Field (B ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  have : Nontrivial B := (Ideal.Quotient.mk 𝔭).domain_nontrivial
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  have hΩ := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R)
    (S := B) 1
  have : Module.Finite B Ω[B⁄R] := Module.rank_lt_aleph0_iff.1 (by
    rw [hΩ]
    exact Cardinal.one_lt_aleph0)
  let b : Module.Basis (Fin 1) B Ω[B⁄R] :=
    Module.finBasisOfFinrankEq B Ω[B⁄R] (Module.finrank_eq_of_rank_eq (by simpa using hΩ))
  -- the residue field `κ` of `𝔭` over `k`
  have hm : maximalIdeal R = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hm𝔭 : maximalIdeal R ≤ 𝔭.comap (algebraMap R B) := by
    rw [hm, Ideal.span_le, Set.singleton_subset_iff]
    exact h𝔭
  let : Algebra (ResidueField R) (B ⧸ 𝔭) := Ideal.Quotient.algebraQuotientOfLEComap hm𝔭
  have : IsScalarTower R (ResidueField R) (B ⧸ 𝔭) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType R (B ⧸ 𝔭) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R 𝔭) Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType (ResidueField R) (B ⧸ 𝔭) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (ResidueField R) (B ⧸ 𝔭)
  have : Module.Finite (ResidueField R) (B ⧸ 𝔭) :=
    finite_of_finite_type_of_isJacobsonRing (ResidueField R) (B ⧸ 𝔭)
  have : Algebra.IsSeparable (ResidueField R) (B ⧸ 𝔭) := inferInstance
  have : Algebra.FormallyEtale (ResidueField R) (B ⧸ 𝔭) :=
    Algebra.FormallyEtale.of_isSeparable _ _
  have : Algebra.FormallyUnramified R (B ⧸ 𝔭) :=
    Algebra.FormallyUnramified.comp R (ResidueField R) (B ⧸ 𝔭)
  -- the parameter `t`
  obtain ⟨t, ht, hDt⟩ := exists_mem_fibreDer_eq_one 𝔭 b
  -- the second-order step with `J = 𝔭² + (ϖ)`
  set J : Ideal B := 𝔭 ^ 2 ⊔ Ideal.span {algebraMap R B ϖ}
  have hJ𝔭 : J ≤ 𝔭 :=
    sup_le (Ideal.pow_le_self two_ne_zero) (Ideal.span_le.2 (Set.singleton_subset_iff.2 h𝔭))
  have hsqJ : 𝔭 ^ 2 ≤ J := le_sup_left
  have hmJ : maximalIdeal R ≤ J.comap (algebraMap R B) := by
    rw [hm, Ideal.span_le, Set.singleton_subset_iff]
    exact le_sup_right (a := 𝔭 ^ 2) (Ideal.mem_span_singleton_self _)
  let : Algebra (ResidueField R) (B ⧸ J) := Ideal.Quotient.algebraQuotientOfLEComap hmJ
  have : IsScalarTower R (ResidueField R) (B ⧸ J) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hk : Function.Surjective (algebraMap R (ResidueField R)) := Ideal.Quotient.mk_surjective
  let g := factorAlgHom (k := ResidueField R) 𝔭 hJ𝔭 hk
  have hg : Function.Surjective g := fun y => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk J a, Ideal.Quotient.factor_mk hJ𝔭 a⟩
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id (ResidueField R) (B ⧸ 𝔭)) g hg
    (isNilpotent_ker_factorAlgHom 𝔭 hJ𝔭 hsqJ hk)
  have hs : ∀ y, Ideal.Quotient.factor hJ𝔭 (s y) = y := fun y =>
    Algebra.FormallySmooth.liftOfSurjective_apply _ g hg _ y
  have hpar : ∀ x ∈ 𝔭, fibreDer 𝔭 b x = 0 → x ∈ J := fun x hx hD =>
    mem_of_fibreDer_eq_zero 𝔭 b hJ𝔭 hsqJ s hs hx hD
  have hle : 𝔭 ≤ Ideal.span {t} ⊔ (𝔭 ^ 2 ⊔ Ideal.span {algebraMap R B ϖ}) :=
    le_span_sup 𝔭 b hpar ht hDt
  -- the local ring `A = B_𝔭`
  set A := Localization.AtPrime 𝔭
  set ι := algebraMap B A
  have hmap : 𝔭.map ι = maximalIdeal A := Localization.AtPrime.map_eq_maximalIdeal
  have hιm : ∀ x ∈ 𝔭, ι x ∈ maximalIdeal A := fun x hx => by
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ hx
  have hϖA : algebraMap R A ϖ = ι (algebraMap R B ϖ) := IsScalarTower.algebraMap_apply R B A ϖ
  have hmax : maximalIdeal A = Ideal.span {algebraMap R A ϖ, ι t} := by
    apply le_antisymm
    · have h2 : (𝔭 ^ 2).map ι = maximalIdeal A ^ 2 := by rw [Ideal.map_pow, hmap]
      have h3 : (Ideal.span {algebraMap R B ϖ}).map ι = Ideal.span {algebraMap R A ϖ} := by
        rw [Ideal.map_span, Set.image_singleton, hϖA]
      have h4 : (Ideal.span {t}).map ι = Ideal.span {ι t} := by
        rw [Ideal.map_span, Set.image_singleton]
      have hle' : maximalIdeal A ≤
          Ideal.span {ι t} ⊔ (maximalIdeal A ^ 2 ⊔ Ideal.span {algebraMap R A ϖ}) :=
        calc maximalIdeal A = 𝔭.map ι := hmap.symm
          _ ≤ (Ideal.span {t} ⊔ (𝔭 ^ 2 ⊔ Ideal.span {algebraMap R B ϖ})).map ι :=
            Ideal.map_mono hle
          _ = _ := by rw [Ideal.map_sup, Ideal.map_sup, h2, h3, h4]
      have hsp : Ideal.span {algebraMap R A ϖ, ι t} =
          Ideal.span {algebraMap R A ϖ} ⊔ Ideal.span {ι t} := Ideal.span_insert _ _
      have hsm : maximalIdeal A • maximalIdeal A = maximalIdeal A ^ 2 := by
        rw [Ideal.smul_eq_mul, sq]
      refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
        (I := maximalIdeal A)
        (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm) ?_
      rw [hsp, hsm]
      refine hle'.trans (sup_le (le_sup_of_le_left le_sup_right) ?_)
      exact sup_le le_sup_right (le_sup_of_le_left le_sup_left)
    · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff, hϖA]
      exact ⟨hιm _ h𝔭, hιm _ ht⟩
  exact ⟨t, ht, hmax, fun s hs n => mul_pow_notMem_span 𝔭 b ht hDt h𝔭 hs n⟩

/-- `ϖ` is a nonzerodivisor in `B_𝔭` (smooth implies flat). -/
theorem closedPoint_mem_nonZeroDivisors {R : Type*} [CommRing R] {B : Type*} [CommRing B]
    [Algebra R B] [Algebra.IsStandardSmoothOfRelativeDimension 1 R B] (𝔭 : Ideal B)
    [𝔭.IsPrime] {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) :
    algebraMap R (Localization.AtPrime 𝔭) ϖ ∈ nonZeroDivisors (Localization.AtPrime 𝔭) := by
  have := flat_of_standardSmooth (R := R) (A₀ := B)
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors
    (M := Localization.AtPrime 𝔭) hϖ
  refine mem_nonZeroDivisors_iff_left.mpr fun x hx => hreg ?_
  change ϖ • x = ϖ • 0
  rw [smul_zero, Algebra.smul_def]
  exact hx

/-- In `B_𝔭 ⧸ (ϖ)` the class of the parameter of `closedPoint_param` is not nilpotent. -/
theorem closedPoint_not_isNilpotent {R : Type*} [CommRing R] {ϖ : R} {B : Type*} [CommRing B]
    [Algebra R B] (𝔭 : Ideal B) [𝔭.IsPrime] {t : B}
    (hst : ∀ s ∉ 𝔭, ∀ n : ℕ, s * t ^ n ∉ Ideal.span {algebraMap R B ϖ}) :
    ¬ IsNilpotent (Ideal.Quotient.mk (Ideal.span {algebraMap R (Localization.AtPrime 𝔭) ϖ})
      (algebraMap B (Localization.AtPrime 𝔭) t)) := by
  set A := Localization.AtPrime 𝔭
  set ι := algebraMap B A
  have hϖA : algebraMap R A ϖ = ι (algebraMap R B ϖ) := IsScalarTower.algebraMap_apply R B A ϖ
  set P := Ideal.span {algebraMap R A ϖ}
  have hPmap : P = (Ideal.span {algebraMap R B ϖ}).map ι := by
    rw [Ideal.map_span, Set.image_singleton, ← hϖA]
  rintro ⟨n, hn⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, hPmap, ← map_pow] at hn
  obtain ⟨⟨⟨a, ha⟩, ⟨m, hm'⟩⟩, h⟩ := (IsLocalization.mem_map_algebraMap_iff 𝔭.primeCompl A).1 hn
  rw [← map_mul, IsLocalization.eq_iff_exists 𝔭.primeCompl] at h
  obtain ⟨⟨c, hc⟩, hc'⟩ := h
  have hcm : c * m ∉ 𝔭 := fun h =>
    ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hc hm')
  apply hst _ hcm n
  have : c * m * t ^ n = c * a := by
    rw [← hc']
    ring
  rw [this]
  exact Ideal.mul_mem_left _ _ ha

/-- **Node L1a, bundled.** The local ring `A = B_𝔭` at a closed point `𝔭` of the special fibre
satisfies the depth-two hypotheses: it is Noetherian, `𝔪 = (ϖ, t)`, `ϖ` is a nonzerodivisor in
`𝔪`, and `A ⧸ (ϖ)` is a domain and a discrete valuation ring of dimension one whose maximal ideal
is generated by the class of `t`. -/
theorem closedPoint_depthTwo {R : Type*} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] {ϖ : R}
    (hϖ : Irreducible ϖ) {B : Type*} [CommRing B] [Algebra R B]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R B]
    (𝔭 : Ideal B) [𝔭.IsMaximal] (h𝔭 : algebraMap R B ϖ ∈ 𝔭) :
    ∃ t ∈ 𝔭, IsNoetherianRing (Localization.AtPrime 𝔭) ∧
      maximalIdeal (Localization.AtPrime 𝔭) =
        Ideal.span {algebraMap R (Localization.AtPrime 𝔭) ϖ,
          algebraMap B (Localization.AtPrime 𝔭) t} ∧
      algebraMap R (Localization.AtPrime 𝔭) ϖ ∈ nonZeroDivisors (Localization.AtPrime 𝔭) ∧
      algebraMap R (Localization.AtPrime 𝔭) ϖ ∈ maximalIdeal (Localization.AtPrime 𝔭) ∧
      ∃ (_ : IsDomain (Localization.AtPrime 𝔭 ⧸
          Ideal.span {algebraMap R (Localization.AtPrime 𝔭) ϖ}))
        (_ : IsDiscreteValuationRing (Localization.AtPrime 𝔭 ⧸
          Ideal.span {algebraMap R (Localization.AtPrime 𝔭) ϖ})),
        maximalIdeal (Localization.AtPrime 𝔭 ⧸
            Ideal.span {algebraMap R (Localization.AtPrime 𝔭) ϖ}) =
          Ideal.span {(Ideal.Quotient.mk
            (Ideal.span {algebraMap R (Localization.AtPrime 𝔭) ϖ})
            (algebraMap B (Localization.AtPrime 𝔭) t))} ∧
        ringKrullDim (Localization.AtPrime 𝔭 ⧸
          Ideal.span {algebraMap R (Localization.AtPrime 𝔭) ϖ}) = 1 := by
  have : Algebra.IsStandardSmooth R B :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  have hnoeth : IsNoetherianRing (Localization.AtPrime 𝔭) := inferInstance
  obtain ⟨t, ht, hmax, hst⟩ := closedPoint_param hϖ 𝔭 h𝔭
  set A := Localization.AtPrime 𝔭
  set P := Ideal.span {algebraMap R A ϖ}
  have hpm : algebraMap R A ϖ ∈ maximalIdeal A :=
    hmax ▸ Ideal.subset_span (Set.mem_insert _ _)
  have : Nontrivial (A ⧸ P) := Submodule.Quotient.nontrivial_iff.mpr
    (Ideal.span_singleton_ne_top ((IsLocalRing.mem_maximalIdeal _).1 hpm))
  have : IsLocalRing (A ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hτ : maximalIdeal (A ⧸ P) = Ideal.span {Ideal.Quotient.mk P (algebraMap B A t)} :=
    maximalIdeal_quotient_eq_span hmax
  have hnil := closedPoint_not_isNilpotent 𝔭 hst
  have hdom := isDomain_of_maximalIdeal_eq_span hτ hnil
  have hdvr := isDiscreteValuationRing_of_maximalIdeal_eq_span hτ fun h => hnil (by
    rw [h]
    exact IsNilpotent.zero)
  exact ⟨t, ht, hnoeth, hmax,
    closedPoint_mem_nonZeroDivisors 𝔭 (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero), hpm,
    hdom, hdvr, hτ, IsDiscreteValuationRing.ringKrullDim_eq_one _⟩

/-- **Node L1a.** Let `R` be a discrete valuation ring with perfect residue field and
uniformizer `ϖ`, and let `B` be a standard smooth `R`-algebra of relative dimension one. At a
maximal ideal `𝔭` of `B` containing `ϖ` (a closed point of the special fibre), the local ring
`B_𝔭 ⧸ (ϖ)` of the special fibre is a domain and a discrete valuation ring. -/
theorem isDiscreteValuationRing_quotient_of_standardSmooth {R : Type*} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] {ϖ : R}
    (hϖ : Irreducible ϖ) {B : Type*} [CommRing B] [Algebra R B]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R B]
    (𝔭 : Ideal B) [𝔭.IsMaximal] (h𝔭 : algebraMap R B ϖ ∈ 𝔭) :
    ∃ (_ : IsDomain (Localization.AtPrime 𝔭 ⧸
        Ideal.span {algebraMap R (Localization.AtPrime 𝔭) ϖ})),
      IsDiscreteValuationRing (Localization.AtPrime 𝔭 ⧸
        Ideal.span {algebraMap R (Localization.AtPrime 𝔭) ϖ}) := by
  obtain ⟨-, -, -, -, -, -, hdom, hdvr, -⟩ := closedPoint_depthTwo hϖ 𝔭 h𝔭
  exact ⟨hdom, hdvr⟩

/-- **Node L1a, in the form consumed by node N6a.** Every statement proved for a Noetherian
local ring `A` and an element `π` under the depth-two hypotheses holds for the local ring at a
closed point of the special fibre and the image of `ϖ`. -/
theorem closedPoint_of_depthTwo {R : Type*} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] {ϖ : R}
    (hϖ : Irreducible ϖ) {B : Type*} [CommRing B] [Algebra R B]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R B]
    (𝔭 : Ideal B) [𝔭.IsMaximal] (h𝔭 : algebraMap R B ϖ ∈ 𝔭)
    (P : ∀ (A : Type _), A → Prop)
    (hP : ∀ (A : Type _) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (π : A),
      π ∈ nonZeroDivisors A → π ∈ maximalIdeal A →
      ∀ [IsDomain (A ⧸ Ideal.span {π})] [IsDiscreteValuationRing (A ⧸ Ideal.span {π})],
        P A π) :
    P (Localization.AtPrime 𝔭) (algebraMap R (Localization.AtPrime 𝔭) ϖ) := by
  obtain ⟨-, -, hnoeth, -, hnzd, hm, hdom, hdvr, -⟩ := closedPoint_depthTwo hϖ 𝔭 h𝔭
  exact hP _ _ hnzd hm

/-- **The field case.** For a standard smooth algebra `B` of relative dimension one over a
perfect field `k` and a maximal ideal `𝔭` of `B` (a closed point, not necessarily rational), the
local ring `B_𝔭` is a domain and a discrete valuation ring. -/
theorem isDiscreteValuationRing_localization_of_standardSmooth {k : Type*} [Field k]
    [PerfectField k] {B : Type*} [CommRing B] [Algebra k B]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k B] (𝔭 : Ideal B) [𝔭.IsMaximal] :
    ∃ (_ : IsDomain (Localization.AtPrime 𝔭)),
      IsDiscreteValuationRing (Localization.AtPrime 𝔭) := by
  have : Algebra.IsStandardSmooth k B :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  let : Field (B ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  have : Nontrivial B := (Ideal.Quotient.mk 𝔭).domain_nontrivial
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hΩ := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k)
    (S := B) 1
  have : Module.Finite B Ω[B⁄k] := Module.rank_lt_aleph0_iff.1 (by
    rw [hΩ]
    exact Cardinal.one_lt_aleph0)
  let b : Module.Basis (Fin 1) B Ω[B⁄k] :=
    Module.finBasisOfFinrankEq B Ω[B⁄k] (Module.finrank_eq_of_rank_eq (by simpa using hΩ))
  have : Algebra.FiniteType k (B ⧸ 𝔭) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k 𝔭) Ideal.Quotient.mk_surjective
  have : Module.Finite k (B ⧸ 𝔭) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ 𝔭)
  have : Algebra.IsSeparable k (B ⧸ 𝔭) := inferInstance
  have : Algebra.FormallyEtale k (B ⧸ 𝔭) := Algebra.FormallyEtale.of_isSeparable _ _
  have : Algebra.FormallyUnramified k (B ⧸ 𝔭) := Algebra.FormallyUnramified.of_isSeparable _ _
  obtain ⟨t, ht, hDt⟩ := exists_mem_fibreDer_eq_one 𝔭 b
  have hJ𝔭 : 𝔭 ^ 2 ≤ 𝔭 := Ideal.pow_le_self two_ne_zero
  have hk : Function.Surjective (algebraMap k k) := fun r => ⟨r, rfl⟩
  let g := factorAlgHom (R := k) (k := k) 𝔭 hJ𝔭 hk
  have hg : Function.Surjective g := fun y => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.factor_mk hJ𝔭 a⟩
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k (B ⧸ 𝔭)) g hg
    (isNilpotent_ker_factorAlgHom 𝔭 hJ𝔭 le_rfl hk)
  have hs : ∀ y, Ideal.Quotient.factor hJ𝔭 (s y) = y := fun y =>
    Algebra.FormallySmooth.liftOfSurjective_apply _ g hg _ y
  have hpar : ∀ x ∈ 𝔭, fibreDer 𝔭 b x = 0 → x ∈ 𝔭 ^ 2 := fun x hx hD =>
    mem_of_fibreDer_eq_zero 𝔭 b hJ𝔭 le_rfl s hs hx hD
  have hle : 𝔭 ≤ Ideal.span {t} ⊔ 𝔭 ^ 2 := le_span_sup 𝔭 b hpar ht hDt
  set A := Localization.AtPrime 𝔭
  set ι := algebraMap B A
  have hmap : 𝔭.map ι = maximalIdeal A := Localization.AtPrime.map_eq_maximalIdeal
  have hmax : maximalIdeal A = Ideal.span {ι t} := by
    apply le_antisymm
    · have hle' : maximalIdeal A ≤ Ideal.span {ι t} ⊔ maximalIdeal A • maximalIdeal A :=
        calc maximalIdeal A = 𝔭.map ι := hmap.symm
          _ ≤ (Ideal.span {t} ⊔ 𝔭 ^ 2).map ι := Ideal.map_mono hle
          _ = _ := by
            rw [Ideal.map_sup, Ideal.map_pow, hmap, Ideal.map_span, Set.image_singleton,
              Ideal.smul_eq_mul, sq]
      exact Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
        (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm) hle'
    · rw [Ideal.span_le, Set.singleton_subset_iff, ← hmap]
      exact Ideal.mem_map_of_mem _ ht
  have hnil : ¬ IsNilpotent (ι t) := by
    rintro ⟨n, hn⟩
    rw [← map_pow, IsLocalization.map_eq_zero_iff 𝔭.primeCompl] at hn
    obtain ⟨⟨c, hc⟩, hc'⟩ := hn
    refine mul_pow_notMem_span 𝔭 b ht hDt (p := 0) (by simp) hc n ?_
    rw [hc']
    exact Ideal.zero_mem _
  have hdom := isDomain_of_maximalIdeal_eq_span hmax hnil
  refine ⟨hdom, isDiscreteValuationRing_of_maximalIdeal_eq_span hmax fun h => hnil ?_⟩
  rw [h]
  exact IsNilpotent.zero

end ZInQ.Contrib.CMHeight62Full
