import ZInQKernel.Contrib.OneProof.SGRDirectNV

open Polynomial CategoryTheory AlgebraicGeometry
open GlueDescent.B2Q NumberField
open HDec HDec.G0ModField HDec.PropTSRed HDec.PropTSGlue HDec.HeckeRestNV HDec.TSHecke LeafQM LeafQM.AV

set_option linter.style.haveILetI false

noncomputable section

namespace SGRDirect.NVLocal

/-- **An inertia automorphism at an unramified prime is trivial.** -/
theorem eq_one_of_inertia_of_unram {K : Type*} [Field K] [NumberField K] (P : Ideal (𝓞 K))
    [P.IsPrime] (hun : P.ramificationIdx ℤ = 1) (σ : K ≃ₐ[ℚ] K)
    (hσ : ∀ x : 𝓞 K, σ • x - x ∈ P) : σ = 1 := by
  set G := Subgroup.zpowers σ
  haveI : Finite G := inferInstance
  set K₀ := FixedPoints.subfield G K
  haveI : CharZero K₀ := inferInstance
  haveI : FiniteDimensional ℚ K₀ := by
    exact Module.Finite.of_injective ((algebraMap K₀ K).toRatAlgHom.toLinearMap)
      (algebraMap K₀ K).injective
  haveI : NumberField K₀ := ⟨⟩
  haveI : FaithfulSMul G K := ⟨fun {g₁ g₂} h => Subtype.ext (AlgEquiv.ext h)⟩
  haveI : IsGaloisGroup G K₀ K := IsGaloisGroup.fixedPoints G K
  haveI : IsGaloisGroup G (𝓞 K₀) (𝓞 K) := IsGaloisGroup.of_isFractionRing G (𝓞 K₀) (𝓞 K) K₀ K
  set P₀ := P.under (𝓞 K₀)
  haveI : P₀.IsPrime := Ideal.IsPrime.under _ P
  haveI : P.LiesOver P₀ := ⟨rfl⟩
  have hg : (⟨σ, Subgroup.mem_zpowers σ⟩ : G) ∈ P.inertia G := by
    intro x
    exact hσ x
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := G) P₀ P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx P₀ P G] at hcard
  have htow := Ideal.ramificationIdx_tower (R := ℤ) P₀ P
  rw [hun] at htow
  have h1 : P.ramificationIdx (𝓞 K₀) = 1 := (Nat.eq_one_of_mul_eq_one_left htow.symm)
  rw [h1] at hcard
  have : (⟨σ, Subgroup.mem_zpowers σ⟩ : G) = 1 := by
    have hb : P.inertia G = ⊥ := Subgroup.card_eq_one.mp hcard
    rw [hb] at hg
    exact hg
  exact congrArg Subtype.val this


/-- The prime of `𝓞 L` cut out by a prime `𝔓` of a ring `C` mapping to `L` whose localization contains `𝓞 L`. -/
def primeOf {L : Type*} [Field L] {Cr : Type*} [CommRing Cr] (𝔓 : Ideal Cr) [𝔓.IsPrime]
    (ψ : Cr →+* L) (hker : ∀ c, ψ c = 0 → c ∈ 𝔓)
    (hN : ∀ y : 𝓞 L, ∃ c₁ c₂ : Cr, c₂ ∉ 𝔓 ∧ (y : L) * ψ c₂ = ψ c₁) : Ideal (𝓞 L) where
  carrier := {y | ∃ d₁ d₂ : Cr, d₁ ∈ 𝔓 ∧ d₂ ∉ 𝔓 ∧ (y : L) * ψ d₂ = ψ d₁}
  zero_mem' := ⟨0, 1, 𝔓.zero_mem, fun h => (Ideal.IsPrime.ne_top inferInstance)
    ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  add_mem' := by
    rintro x y ⟨a₁, a₂, ha₁, ha₂, hx⟩ ⟨b₁, b₂, hb₁, hb₂, hy⟩
    refine ⟨a₁ * b₂ + b₁ * a₂, a₂ * b₂, 𝔓.add_mem (𝔓.mul_mem_right _ ha₁) (𝔓.mul_mem_right _ hb₁),
      fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ha₂ hb₂, ?_⟩
    simp only [show ((x + y : 𝓞 L) : L) = (x : L) + y from rfl, map_add, map_mul, ← hx, ← hy]
    ring
  smul_mem' := by
    rintro r x ⟨d₁, d₂, hd₁, hd₂, hx⟩
    obtain ⟨c₁, c₂, hc₂, hr⟩ := hN r
    refine ⟨c₁ * d₁, c₂ * d₂, 𝔓.mul_mem_left _ hd₁,
      fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim hc₂ hd₂, ?_⟩
    simp only [show ((r • x : 𝓞 L) : L) = (r : L) * x from rfl, map_mul, ← hx, ← hr]
    ring

theorem primeOf_isPrime {L : Type*} [Field L] {Cr : Type*} [CommRing Cr] (𝔓 : Ideal Cr)
    [𝔓.IsPrime] (ψ : Cr →+* L) (hker : ∀ c, ψ c = 0 → c ∈ 𝔓)
    (hN : ∀ y : 𝓞 L, ∃ c₁ c₂ : Cr, c₂ ∉ 𝔓 ∧ (y : L) * ψ c₂ = ψ c₁) :
    (primeOf 𝔓 ψ hker hN).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ne, Ideal.eq_top_iff_one]
    rintro ⟨d₁, d₂, hd₁, hd₂, h⟩
    apply hd₂
    have h' : ψ (d₂ - d₁) = 0 := by
      rw [map_sub, ← h]; simp
    have := 𝔓.add_mem (hker _ h') hd₁
    simpa using this
  · rintro x y ⟨d₁, d₂, hd₁, hd₂, hxy⟩
    obtain ⟨a₁, a₂, ha₂, hx⟩ := hN x
    obtain ⟨b₁, b₂, hb₂, hy⟩ := hN y
    have key : ψ (a₁ * b₁ * d₂ - d₁ * a₂ * b₂) = 0 := by
      simp only [map_sub, map_mul]
      rw [← hx, ← hy, ← hxy, show ((x * y : 𝓞 L) : L) = (x : L) * y from rfl]
      ring
    have h1 : a₁ * b₁ * d₂ ∈ 𝔓 := by
      have := 𝔓.add_mem (hker _ key) (𝔓.mul_mem_right b₂ (𝔓.mul_mem_right a₂ hd₁))
      simpa using this
    rcases (Ideal.IsPrime.mem_or_mem inferInstance h1) with h2 | h2
    · rcases (Ideal.IsPrime.mem_or_mem inferInstance h2) with h3 | h3
      · exact Or.inl ⟨a₁, a₂, h3, ha₂, hx⟩
      · exact Or.inr ⟨b₁, b₂, h3, hb₂, hy⟩
    · exact absurd h2 hd₂

theorem mem_primeOf_of_mem {L : Type*} [Field L] {Cr : Type*} [CommRing Cr] (𝔓 : Ideal Cr)
    [𝔓.IsPrime] (ψ : Cr →+* L) (hker : ∀ c, ψ c = 0 → c ∈ 𝔓)
    (hN : ∀ y : 𝓞 L, ∃ c₁ c₂ : Cr, c₂ ∉ 𝔓 ∧ (y : L) * ψ c₂ = ψ c₁) (p : ℕ)
    (hp : (p : Cr) ∈ 𝔓) : ((p : ℤ) : 𝓞 L) ∈ primeOf 𝔓 ψ hker hN := by
  refine ⟨p, 1, hp, fun h => (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h), ?_⟩
  simp

theorem inertia_primeOf {L : Type*} [Field L] [CharZero L] {Cr : Type*} [CommRing Cr]
    (𝔓 : Ideal Cr) [𝔓.IsPrime] (ψ : Cr →+* L) (hker : ∀ c, ψ c = 0 → c ∈ 𝔓)
    (hN : ∀ y : 𝓞 L, ∃ c₁ c₂ : Cr, c₂ ∉ 𝔓 ∧ (y : L) * ψ c₂ = ψ c₁) (σ : L ≃ₐ[ℚ] L)
    (hσ : ∀ c : Cr, ∃ c' : Cr, σ (ψ c) = ψ c' ∧ c' - c ∈ 𝔓) :
    ∀ y : 𝓞 L, σ • y - y ∈ primeOf 𝔓 ψ hker hN := by
  intro y
  obtain ⟨c₁, c₂, hc₂, hy⟩ := hN y
  obtain ⟨c₁', hσ₁, h₁⟩ := hσ c₁
  obtain ⟨c₂', hσ₂, h₂⟩ := hσ c₂
  have hc₂' : c₂' ∉ 𝔓 := by
    intro h
    apply hc₂
    have := 𝔓.sub_mem h h₂
    simpa using this
  refine ⟨c₁' * c₂ - c₁ * c₂', c₂ * c₂', ?_,
    fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim hc₂ hc₂', ?_⟩
  · have : c₁' * c₂ - c₁ * c₂' = (c₁' - c₁) * c₂ - c₁ * (c₂' - c₂) := by ring
    rw [this]
    exact 𝔓.sub_mem (𝔓.mul_mem_right _ h₁) (𝔓.mul_mem_left _ h₂)
  · have hσy : σ (y : L) * ψ c₂' = ψ c₁' := by
      rw [← hσ₂, ← hσ₁, ← map_mul, hy]
    have hcoe : ((σ • y : 𝓞 L) : L) = σ (y : L) := rfl
    simp only [show ((σ • y - y : 𝓞 L) : L) = ((σ • y : 𝓞 L) : L) - y from rfl, hcoe, map_sub,
      map_mul, ← hσy, ← hy]
    ring


/-- **An inertia automorphism is trivial** (assembled): the prime `primeOf` is unramified. -/
theorem eq_one_of_primeOf {L : Type*} [Field L] [NumberField L] {Cr : Type*} [CommRing Cr]
    (𝔓 : Ideal Cr) [𝔓.IsPrime] (ψ : Cr →+* L) (hker : ∀ c, ψ c = 0 → c ∈ 𝔓)
    (hN : ∀ y : 𝓞 L, ∃ c₁ c₂ : Cr, c₂ ∉ 𝔓 ∧ (y : L) * ψ c₂ = ψ c₁) (σ : L ≃ₐ[ℚ] L)
    (hσ : ∀ c : Cr, ∃ c' : Cr, σ (ψ c) = ψ c' ∧ c' - c ∈ 𝔓) (p : ℕ) (hp : (p : Cr) ∈ 𝔓)
    (hun : ∀ P : Ideal (𝓞 L), P.IsPrime → ((p : ℤ) : 𝓞 L) ∈ P → P.ramificationIdx ℤ = 1) :
    σ = 1 := by
  haveI := primeOf_isPrime 𝔓 ψ hker hN
  exact eq_one_of_inertia_of_unram (primeOf 𝔓 ψ hker hN)
    (hun _ inferInstance (mem_primeOf_of_mem 𝔓 ψ hker hN p hp)) σ (inertia_primeOf 𝔓 ψ hker hN σ hσ)

/-! ## The inclusion `ℤ[X]`-closure → `ℚ[X]`-closure and the Galois action -/

/-- The inclusion of the integral closure of `ℤ[X]` in `E` into that of `ℚ[X]`. -/
def zqIncl (E : Type) [Field E] [Algebra ℚ[X] E] :
    letI := intPolyAlg E
    integralClosure ℤ[X] E →+* integralClosure ℚ[X] E :=
  letI := intPolyAlg E
  { toFun := fun c => ⟨(c : E), by
      obtain ⟨f, hf, hf0⟩ := c.2
      refine ⟨f.map (Polynomial.mapRingHom (Int.castRingHom ℚ)), hf.map _, ?_⟩
      rw [eval₂_map]
      exact hf0⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl }

variable {E : Type} [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
  [IsScalarTower ℚ[X] (RatFunc ℚ) E]

/-- A `ℚ(X)`-automorphism of `E` acting on the integral closure of `ℚ[X]`. -/
def galB (g : Gal(E/RatFunc ℚ)) : integralClosure ℚ[X] E ≃+* integralClosure ℚ[X] E where
  toFun x := ⟨g x, x.2.map ((g : E →ₐ[RatFunc ℚ] E).restrictScalars ℚ[X])⟩
  invFun x := ⟨g⁻¹ x, x.2.map (((g⁻¹ : Gal(E/RatFunc ℚ)) : E →ₐ[RatFunc ℚ] E).restrictScalars ℚ[X])⟩
  left_inv x := Subtype.ext (by
    show g⁻¹ (g (x : E)) = x
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply])
  right_inv x := Subtype.ext (by
    show g (g⁻¹ (x : E)) = x
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply])
  map_mul' x y := Subtype.ext (map_mul g (x : E) y)
  map_add' x y := Subtype.ext (map_add g (x : E) y)

theorem galB_apply (g : Gal(E/RatFunc ℚ)) (x : integralClosure ℚ[X] E) :
    ((galB g x : integralClosure ℚ[X] E) : E) = g x := rfl

/-- A `ℚ(X)`-automorphism maps the integral closure of `ℤ[X]` to itself. -/
theorem galC_mem (g : Gal(E/RatFunc ℚ)) :
    letI := intPolyAlg E
    ∀ c : integralClosure ℤ[X] E, ∃ c' : integralClosure ℤ[X] E, (c' : E) = g c := by
  letI := intPolyAlg E
  letI := intRatAlg
  haveI : IsScalarTower ℤ[X] (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap ℚ[X] E (a.map (Int.castRingHom ℚ)) =
      algebraMap (RatFunc ℚ) E (algebraMap ℚ[X] (RatFunc ℚ) (a.map (Int.castRingHom ℚ)))
    rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E])
  intro c
  exact ⟨⟨g c, c.2.map ((g : E →ₐ[RatFunc ℚ] E).restrictScalars ℤ[X])⟩, rfl⟩

end SGRDirect.NVLocal
