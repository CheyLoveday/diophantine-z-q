import ZInQKernel.HDecomp.Faltings.Models
import ZInQKernel.Contrib.RC53Assist.HodgeLatticeIdeal.Coordinates
import ZInQKernel.Contrib.OneProof.CMHeight62Full.Reduction
import ZInQKernel.Contrib.OneProof.CMHeight62Full.GenericComparison
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.RiemannRoch.Basic

/-!
# cmHeight62 (finite place): the tree-facing nodes, with their tree inputs as hypotheses

Statements of the tree-facing nodes of the step-7 blueprint (edition 3), compiled against the
tree objects whose import closures are small: `GroupModel` with `omegaAt`, `detLattice` and
`wedge` (`HDecomp/Faltings/Models.lean`), `coefficientSubmodule`
(`RC53Assist/HodgeLatticeIdeal/Coordinates.lean`), and Tau Ceti's places and Riemann-Roch
spaces (`TauCeti/FieldTheory/FunctionField/RiemannRoch/Basic.lean`). The objects with large
closures (`Step7`, `ShortData`, `etaW`, `originStalkEquiv`, `coefficientFractionalIdeal`,
`AbVarFunctionField`, `abVar_identityPoleSpaces`) enter only through explicit hypotheses, in the
shapes in which the hosted check discharges them.

* **N4 core.** `abs_norm_le_of_localModels`: the finite-place inequality from one local model
  per finite place, for any fractional ideal `J` whose submodule is the coefficient submodule of
  `η` in the Hodge lattice (`coefficientFractionalIdeal_coe` gives this by `rfl`).
  `abs_norm_le_of_comparisons`: the same from the N13 data at every place.
* **N13 core.** `valuation_mul_le_of_mem_line`, `localModel_of_comparison`: the local bound at
  `v` from (i) the Hodge lattice lying on the line `𝒪_v · θ`, (ii) `η = b • θ` with
  `v(b) = v(u)`, (iii) `C⁻¹ • W = W₀` with `v(Δ_{W₀}) = 1`.
* **N11-inst core.** `poleSpace_two_eq_span`, `exists_variableChange_of_riemannRoch`: for a
  place `P` with `dim L(nP) = n` (`n ≥ 1`), `L(2P) = span {1, x}` and `L(3P) = span {1, x, y}`,
  and the generic comparison (N11) applies with `w = v_P`, `δ = exp 1`, `S = 𝒪` away from `P`.
* **N6-bridge (finite part).** `poleSpaceIn`, `finrank_poleSpaceIn`: the pole spaces moved into
  another field along a `k`-algebra isomorphism keep dimension `n`.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.DefFaltings
open ZInQ.Contrib.RC53Assist.HodgeLatticeIdeal (coefficientSubmodule)
open TauCeti.AlgebraicGeometry (WeilDivisor)

/-! ## N13 core: the local bound from the line of the section parameter -/

section N13

variable {L : Type} [Field L] [NumberField L]

/-- If every element of `M` is `r • θ` with `v(r) ≤ 1`, `η = b • θ` with `θ ≠ 0` and
`v(c) = v(b)`, then `a • η ∈ M` gives `v(a · c) ≤ 1`. -/
theorem valuation_mul_le_of_mem_line {V : Type*} [AddCommGroup V] [Module L V]
    [Module (𝓞 L) V] (v : HeightOneSpectrum (𝓞 L)) (M : Submodule (𝓞 L) V) {θ η : V}
    (hθ : θ ≠ 0) (hM : ∀ m ∈ M, ∃ r : L, v.valuation L r ≤ 1 ∧ m = r • θ) {b c : L}
    (hη : η = b • θ) (hbc : v.valuation L c = v.valuation L b) {a : L} (ha : a • η ∈ M) :
    v.valuation L (a * c) ≤ 1 := by
  obtain ⟨r, hr, hreq⟩ := hM _ ha
  rw [hη, smul_smul] at hreq
  have hab : a * b = r := smul_left_injective L hθ hreq
  rw [map_mul, hbc, ← map_mul, hab]
  exact hr

/-- **N13 at one place.** From a comparison `C⁻¹ • W_L = W₀` with `v(Δ_{W₀}) = 1` (N10, N11)
and `η = b • θ` with `v(b) = v(u_C)` on a line `θ` carrying the local lattice (N5-bridge, N12,
N2): a local model in the shape of `abs_norm_algebraMap_le_of_models`. -/
theorem localModel_of_comparison {K : Type} [Field K] [Algebra K L]
    {V : Type*} [AddCommGroup V] [Module L V] [Module (𝓞 L) V]
    (v : HeightOneSpectrum (𝓞 L)) (W : WeierstrassCurve K) (W₀ : WeierstrassCurve L)
    (hW₀ : v.valuation L W₀.Δ = 1) (C : VariableChange L)
    (hC : C⁻¹ • W.map (algebraMap K L) = W₀) (M : Submodule (𝓞 L) V) {θ η : V}
    (hθ : θ ≠ 0) (hM : ∀ m ∈ M, ∃ r : L, v.valuation L r ≤ 1 ∧ m = r • θ) {b : L}
    (hη : η = b • θ) (hb : v.valuation L (C.u : L) = v.valuation L b) :
    ∃ C' : VariableChange L, v.valuation L (C' • W.map (algebraMap K L)).Δ = 1 ∧
      ∀ a : L, a • η ∈ M → v.valuation L (a * ↑C'.u⁻¹) ≤ 1 := by
  refine ⟨C⁻¹, by rw [hC]; exact hW₀, fun a ha => ?_⟩
  have hu : ((C⁻¹).u⁻¹ : Lˣ) = C.u := inv_inv C.u
  rw [hu]
  exact valuation_mul_le_of_mem_line v M hθ hM hη hb ha

end N13

/-! ## N4 core: the finite-place inequality from the local data -/

section N4

variable {K : Type} [Field K] {L : Type} [Field L] [NumberField L] [Algebra K L]
  {E : PkgI3.AbVar K}

/-- **N4 from local models.** `J` is any fractional ideal whose submodule is
`{a : a • η ∈ ⋀¹ω_𝒢}`; in the hosted check `J = coefficientFractionalIdeal 𝒢 hdim η hη`,
`hJ = coefficientFractionalIdeal_coe 𝒢 hdim η hη`, `η = D.etaW 𝒢`, `W = D.W`. -/
theorem abs_norm_le_of_localModels (𝒢 : GroupModel E L) (W : WeierstrassCurve K)
    (hΔ : W.Δ ≠ 0) (η : 𝒢.hodgeSpace 1) {J : FractionalIdeal (nonZeroDivisors (𝓞 L)) L}
    (hJ0 : J ≠ 0) (hJ : (J : Submodule (𝓞 L) L) = coefficientSubmodule (𝒢.detLattice 1) η)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 L), ∃ C : VariableChange L,
      v.valuation L (C • W.map (algebraMap K L)).Δ = 1 ∧
        ∀ a : L, a • η ∈ 𝒢.detLattice 1 → v.valuation L (a * ↑C.u⁻¹) ≤ 1) :
    |Algebra.norm ℚ (algebraMap K L W.Δ)| ≤ FractionalIdeal.absNorm J ^ 12 := by
  refine abs_norm_algebraMap_le_of_models W hΔ hJ0 fun v => ?_
  obtain ⟨C, hC, hCJ⟩ := hloc v
  refine ⟨C, hC, fun a ha => hCJ a ?_⟩
  have h : a ∈ (J : Submodule (𝓞 L) L) := FractionalIdeal.mem_coe.mpr ha
  rw [hJ] at h
  exact h

/-- **N4 from the N13 data at every finite place.** At `v`: `W₀` over `L` with `v(Δ_{W₀}) = 1`
(N10), `C` with `C⁻¹ • W_L = W₀` (N11-inst), the line `θ = 𝒢.wedge ![t_v]` of the section
parameter carrying `⋀¹ω_𝒢` with coefficients in `𝒪_v` (N5-bridge, N13), and `η = b • θ`
with `v(b) = v(u_C)` (N12, N2). -/
theorem abs_norm_le_of_comparisons (𝒢 : GroupModel E L) (W : WeierstrassCurve K)
    (hΔ : W.Δ ≠ 0) (η : 𝒢.hodgeSpace 1) {J : FractionalIdeal (nonZeroDivisors (𝓞 L)) L}
    (hJ0 : J ≠ 0) (hJ : (J : Submodule (𝓞 L) L) = coefficientSubmodule (𝒢.detLattice 1) η)
    (hcmp : ∀ v : HeightOneSpectrum (𝓞 L), ∃ (W₀ : WeierstrassCurve L) (C : VariableChange L)
      (θ : 𝒢.hodgeSpace 1) (b : L), v.valuation L W₀.Δ = 1 ∧
        C⁻¹ • W.map (algebraMap K L) = W₀ ∧ θ ≠ 0 ∧
        (∀ m ∈ 𝒢.detLattice 1, ∃ r : L, v.valuation L r ≤ 1 ∧ m = r • θ) ∧
        η = b • θ ∧ v.valuation L (C.u : L) = v.valuation L b) :
    |Algebra.norm ℚ (algebraMap K L W.Δ)| ≤ FractionalIdeal.absNorm J ^ 12 := by
  refine abs_norm_le_of_localModels 𝒢 W hΔ η hJ0 hJ fun v => ?_
  obtain ⟨W₀, C, θ, b, hW₀, hC, hθ, hM, hη, hb⟩ := hcmp v
  exact localModel_of_comparison v W W₀ hW₀ C hC (𝒢.detLattice 1) hθ hM hη hb

end N4

/-! ## N11-inst core: pole spaces of a place and the generic comparison -/

section N11Inst

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- The functions regular at every place other than `P`. -/
def regularAway (P : TauCeti.Place k F) : Set F :=
  {f | ∀ Q : TauCeti.Place k F, Q ≠ P → Q.valuation f ≤ 1}

/-- `L(nP)`, the Riemann-Roch space of `n • P`. -/
abbrev poleSpace (P : TauCeti.Place k F) (n : ℕ) : Submodule k F :=
  TauCeti.riemannRochSpace (Finsupp.single P (n : ℤ) : TauCeti.Divisor k F)

theorem mem_poleSpace_iff (P : TauCeti.Place k F) (n : ℕ) (f : F) :
    f ∈ poleSpace P n ↔ f ∈ regularAway P ∧ P.valuation f ≤ WithZero.exp (1 : ℤ) ^ n := by
  rw [poleSpace, TauCeti.mem_riemannRochSpace_iff, ← WithZero.exp_nsmul]
  constructor
  · intro h
    refine ⟨fun Q hQ => ?_, ?_⟩
    · simpa [WeilDivisor.coeff, Finsupp.single_apply, Ne.symm hQ] using h Q
    · simpa [WeilDivisor.coeff] using h P
  · rintro ⟨hS, hP⟩ Q
    by_cases hQ : Q = P
    · subst hQ
      simpa [WeilDivisor.coeff] using hP
    · simpa [WeilDivisor.coeff, Finsupp.single_apply, Ne.symm hQ] using
        hS Q hQ

theorem one_lt_exp_one_int : (1 : WithZero (Multiplicative ℤ)) < WithZero.exp (1 : ℤ) :=
  WithZero.one_lt_exp_iff.mpr one_pos

theorem poleSpace_mono (P : TauCeti.Place k F) {m n : ℕ} (h : m ≤ n) :
    poleSpace P m ≤ poleSpace P n := by
  intro f hf
  rw [mem_poleSpace_iff] at hf ⊢
  exact ⟨hf.1, hf.2.trans (pow_le_pow_right₀ one_lt_exp_one_int.le h)⟩

theorem one_mem_poleSpace (P : TauCeti.Place k F) {n : ℕ} : (1 : F) ∈ poleSpace P n := by
  rw [mem_poleSpace_iff]
  refine ⟨fun Q _ => by rw [map_one], ?_⟩
  rw [map_one]
  exact one_le_pow₀ one_lt_exp_one_int.le

/-- A subspace one dimension up containing a new vector `z` is `U ⊔ k ∙ z`. -/
theorem sup_span_singleton_eq_of_finrank_le {V : Type*} [AddCommGroup V] [Module k V]
    {U U' : Submodule k V} [FiniteDimensional k U'] (hle : U ≤ U')
    (hd : Module.finrank k U' ≤ Module.finrank k U + 1) {z : V} (hz : z ∈ U')
    (hzU : z ∉ U) : U ⊔ k ∙ z = U' := by
  have hle' : U ⊔ k ∙ z ≤ U' := sup_le hle ((Submodule.span_singleton_le_iff_mem _ _).mpr hz)
  have hlt : U < U ⊔ k ∙ z := by
    refine lt_of_le_of_ne le_sup_left fun h => hzU ?_
    rw [h]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)
  have : FiniteDimensional k (U ⊔ k ∙ z : Submodule k V) :=
    Submodule.finiteDimensional_of_le hle'
  have := Submodule.finrank_lt_finrank_of_lt hlt
  exact Submodule.eq_of_le_of_finrank_le hle' (by omega)

theorem finrank_poleSpace_of_dim {P : TauCeti.Place k F}
    (hdim : ∀ n : ℕ, 1 ≤ n →
      TauCeti.Divisor.dim (Finsupp.single P (n : ℤ) : TauCeti.Divisor k F) = n)
    {n : ℕ} (hn : 1 ≤ n) : Module.finrank k (poleSpace P n) = n := by
  have h := hdim n hn
  rwa [TauCeti.Divisor.dim_def] at h

/-- **The pole spaces of `P` in degrees 1, 2, 3** (the ladder of `abVar_identityPoleSpaces`):
`L(P) = k`, `L(2P) = span {1, x}`, `L(3P) = span {1, x, y}`. -/
theorem poleSpace_two_eq_span (P : TauCeti.Place k F)
    (hfd : ∀ n : ℕ, FiniteDimensional k (poleSpace P n))
    (hdim : ∀ n : ℕ, 1 ≤ n →
      TauCeti.Divisor.dim (Finsupp.single P (n : ℤ) : TauCeti.Divisor k F) = n)
    {x y : F} (hx : x ∈ poleSpace P 2) (hx1 : x ∉ poleSpace P 1) (hy : y ∈ poleSpace P 3)
    (hy2 : y ∉ poleSpace P 2) :
    poleSpace P 2 = Submodule.span k {1, x} ∧ poleSpace P 3 = Submodule.span k {1, x, y} := by
  have f1 := finrank_poleSpace_of_dim hdim (n := 1) le_rfl
  have f2 := finrank_poleSpace_of_dim hdim (n := 2) (by norm_num)
  have f3 := finrank_poleSpace_of_dim hdim (n := 3) (by norm_num)
  have := hfd 1
  have := hfd 2
  have := hfd 3
  have e1 : ⊥ ⊔ k ∙ (1 : F) = poleSpace P 1 :=
    sup_span_singleton_eq_of_finrank_le bot_le (by rw [f1, finrank_bot]) (one_mem_poleSpace P)
      (by rw [Submodule.mem_bot]; exact one_ne_zero)
  have e2 : poleSpace P 1 ⊔ k ∙ x = poleSpace P 2 :=
    sup_span_singleton_eq_of_finrank_le (poleSpace_mono P (by norm_num)) (by omega) hx hx1
  have e3 : poleSpace P 2 ⊔ k ∙ y = poleSpace P 3 :=
    sup_span_singleton_eq_of_finrank_le (poleSpace_mono P (by norm_num)) (by omega) hy hy2
  have s2 : Submodule.span k {(1 : F), x} = k ∙ (1 : F) ⊔ k ∙ x := Submodule.span_insert _ _
  have s3 : Submodule.span k {(1 : F), x, y} = k ∙ (1 : F) ⊔ (k ∙ x ⊔ k ∙ y) := by
    rw [Submodule.span_insert, Submodule.span_insert]
  rw [bot_sup_eq] at e1
  refine ⟨?_, ?_⟩
  · rw [s2, ← e2, ← e1]
  · rw [s3, ← e3, ← e2, ← e1, sup_assoc]

theorem setOf_eq_poleSpace (P : TauCeti.Place k F) (n : ℕ) :
    {f | f ∈ regularAway P ∧ P.valuation f ≤ WithZero.exp (1 : ℤ) ^ n} =
      (poleSpace P n : Set F) := by
  ext f
  exact (mem_poleSpace_iff P n f).symm

/-- **N11-inst core.** The generic comparison (N11) for a place `P` with the pole-space ladder:
`w = v_P`, `δ = exp 1`, `S = regularAway P`. In the hosted check `k = L`,
`F = AbVarFunctionField (E.baseChange L)`, `P = P_L`, `W = D.W.baseChange L`, `(x, y)` the images
of `(D.X, D.Y)`, `W₀ = W0.map (algebraMap R L)` and `(x₀, y₀)` the images of `(e x, e y)`
(N10). -/
theorem exists_variableChange_of_riemannRoch (P : TauCeti.Place k F)
    (hfd : ∀ n : ℕ, FiniteDimensional k (poleSpace P n))
    (hdim : ∀ n : ℕ, 1 ≤ n →
      TauCeti.Divisor.dim (Finsupp.single P (n : ℤ) : TauCeti.Divisor k F) = n)
    (W W₀ : WeierstrassCurve k) {x y x₀ y₀ : F} (hW : (W.baseChange F).toAffine.Equation x y)
    (hW₀ : (W₀.baseChange F).toAffine.Equation x₀ y₀)
    (hx : P.valuation x = WithZero.exp (1 : ℤ) ^ 2)
    (hy : P.valuation y = WithZero.exp (1 : ℤ) ^ 3)
    (hx₀ : P.valuation x₀ = WithZero.exp (1 : ℤ) ^ 2)
    (hy₀ : P.valuation y₀ = WithZero.exp (1 : ℤ) ^ 3) (hxS : x ∈ regularAway P)
    (hyS : y ∈ regularAway P) (hx₀S : x₀ ∈ regularAway P) (hy₀S : y₀ ∈ regularAway P) :
    ∃ C : VariableChange k, C • W₀ = W ∧ C⁻¹ • W = W₀ ∧
      x₀ = algebraMap k F (↑C.u ^ 2) * x + algebraMap k F C.r ∧
      y₀ = algebraMap k F (↑C.u ^ 3) * y + algebraMap k F (C.s * ↑C.u ^ 2) * x +
        algebraMap k F C.t := by
  have hδ := one_lt_exp_one_int
  have h21 : WithZero.exp (1 : ℤ) ^ 1 < WithZero.exp (1 : ℤ) ^ 2 :=
    pow_lt_pow_right₀ hδ (by norm_num)
  have h32 : WithZero.exp (1 : ℤ) ^ 2 < WithZero.exp (1 : ℤ) ^ 3 :=
    pow_lt_pow_right₀ hδ (by norm_num)
  have mx : x ∈ poleSpace P 2 := (mem_poleSpace_iff P 2 x).mpr ⟨hxS, hx.le⟩
  have my : y ∈ poleSpace P 3 := (mem_poleSpace_iff P 3 y).mpr ⟨hyS, hy.le⟩
  have nx : x ∉ poleSpace P 1 := fun h =>
    absurd ((mem_poleSpace_iff P 1 x).mp h).2 (by rw [hx]; exact not_le.mpr h21)
  have ny : y ∉ poleSpace P 2 := fun h =>
    absurd ((mem_poleSpace_iff P 2 y).mp h).2 (by rw [hy]; exact not_le.mpr h32)
  obtain ⟨e2, e3⟩ := poleSpace_two_eq_span P hfd hdim mx nx my ny
  have hL : ∀ c : k, c ≠ 0 → P.valuation (algebraMap k F c) = 1 := fun c hc =>
    Valuation.IsTrivialOn.eq_one c hc
  refine exists_variableChange_of_poleSpaces P.valuation hL hδ W W₀ (regularAway P) hW hW₀ hx
    hy hx₀ hy₀ hx₀S hy₀S ?_ ?_
  · rw [setOf_eq_poleSpace, e2]
  · rw [setOf_eq_poleSpace, e3]

end N11Inst

/-! ## N6-bridge, finite part: pole spaces moved along an isomorphism of fields -/

section N6Bridge

variable {k F Ω : Type*} [Field k] [Field F] [Field Ω] [Algebra k F] [Algebra k Ω]

/-- `V_n = Ψ⁻¹ L(nP) ⊆ Ω` for a `k`-algebra isomorphism `Ψ : Ω ≃ₐ[k] F`. In the hosted check
`Ω = FractionRing A` (`A` the local ring of the model at `e(s)`), `k = L`, `F = K(E_L)`,
`P = P_L`, and `Ψ` comes from `A_(t) ≅ 𝒪_{𝒢,ξ} ≅ 𝒪_{E_L,0}` (N5-bridge, `originStalkEquiv`). -/
def poleSpaceIn (Ψ : Ω ≃ₐ[k] F) (P : TauCeti.Place k F) (n : ℕ) : Submodule k Ω :=
  (poleSpace P n).map (Ψ.symm.toLinearEquiv : F →ₗ[k] Ω)

theorem mem_poleSpaceIn_iff (Ψ : Ω ≃ₐ[k] F) (P : TauCeti.Place k F) (n : ℕ) (f : Ω) :
    f ∈ poleSpaceIn Ψ P n ↔
      Ψ f ∈ regularAway P ∧ P.valuation (Ψ f) ≤ WithZero.exp (1 : ℤ) ^ n := by
  rw [poleSpaceIn, Submodule.mem_map_equiv, ← mem_poleSpace_iff]
  rfl

/-- `FiniteDimensional k V_n` and `finrank k V_n = n` (N6-bridge's finiteness outputs). -/
theorem finrank_poleSpaceIn (Ψ : Ω ≃ₐ[k] F) (P : TauCeti.Place k F)
    (hfd : ∀ n : ℕ, FiniteDimensional k (poleSpace P n))
    (hdim : ∀ n : ℕ, 1 ≤ n →
      TauCeti.Divisor.dim (Finsupp.single P (n : ℤ) : TauCeti.Divisor k F) = n)
    {n : ℕ} (hn : 1 ≤ n) :
    FiniteDimensional k (poleSpaceIn Ψ P n) ∧ Module.finrank k (poleSpaceIn Ψ P n) = n := by
  have := hfd n
  refine ⟨?_, ?_⟩
  · unfold poleSpaceIn
    infer_instance
  · rw [poleSpaceIn, LinearEquiv.finrank_map_eq, finrank_poleSpace_of_dim hdim hn]

end N6Bridge

end ZInQ.Contrib.CMHeight62Full
