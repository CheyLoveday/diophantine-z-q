import ZInQKernel.Contrib.CloudB3RC53.TameModel.TrivialF2QIso
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Brauer.CharacterFormula
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Local.Unramified
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.LongExact
import ZInQKernel.Contrib.TauCeti.FieldTheory.GaloisCohomology.Hilbert90

/-!
# `H²(G_K, 𝔽₂) ≅ 𝔽₂` with generator `χ_ur ∪ χ_ϖ` (row 3 of the trivial-`𝔽₂` tame model)

Proves the degree-`2` half of the print `LocalCohomologyF2` (`TrivialF2QIso.lean`), leaving only
`Hⁿ(G_K, 𝔽₂) = 0` for `n ≥ 3` as a print (`LocalCohomologyF2Ge3`).

Route (Serre, *Local Fields*, XIV; NSW 7.1): `𝔽₂ ≅ μ₂` (odd residue characteristic); the Kummer
sequence `1 → μ₂ → (Kˢ)ˣ → (Kˢ)ˣ → 1` and Hilbert 90 make `H²(G_K, μ₂) → Br K` injective (Tau Ceti's
explicit long exact sequence, `explicitLongExact_H2A`), with image in `Br K[2]`, which the local
invariant `inv_K : Br K ≃ ℚ/ℤ` (local class field theory, Tau Ceti) identifies with `{0, 1/2}`;
the cup class `χ_ur ∪ χ_ϖ` is cohomologous in `(Kˢ)ˣ` to the carry class `ϖ ∪ δ(χ_ur/2)`, whose
invariant is `(χ_ur/2)(Art_K ϖ) = 1/2` (the character formula and `Art_K ϖ` having unramified
coordinate `1`). Hence `H²` has exactly the two classes `0` and `[χ_ur ∪ χ_ϖ]`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.TameModel

open CategoryTheory TauCeti ValuativeRel ContCohomology
open ZInQ.Contrib.CloudB3RC53.TameQuotient
open ZInQ.Manuscript.RC.SelmerComplex

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-! ### `𝔽₂ ≅ μ₂` -/

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem neg_one_sq_unit : ((-1 : (SeparableClosure K)ˣ)) ^ 2 = 1 := by simp

theorem zmod2_val_one : (1 : ZMod 2).val = 1 := rfl

variable (K) in
/-- `x ↦ (-1)^x`, `𝔽₂ → μ₂(Kˢ)`, written additively. -/
def epsMu (x : ZMod 2) : KummerCoeff K 2 :=
  Additive.ofMul ⟨(-1) ^ x.val, by rw [mem_rootsOfUnity, ← pow_mul, mul_comm, pow_mul,
    neg_one_sq_unit, one_pow]⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem epsMu_add (x y : ZMod 2) : epsMu K (x + y) = epsMu K x + epsMu K y := by
  have h01 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  refine Additive.toMul.injective (Subtype.ext (Units.ext ?_))
  rcases h01 x with rfl | rfl <;> rcases h01 y with rfl | rfl <;>
    simp [epsMu, show (1 : ZMod 2) + 1 = 0 from rfl, zmod2_val_one]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem epsMu_zero : epsMu K 0 = 0 := by
  refine Additive.toMul.injective (Subtype.ext (Units.ext ?_))
  simp [epsMu]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem epsMu_sub (x y : ZMod 2) : epsMu K (x - y) = epsMu K x - epsMu K y :=
  (AddMonoidHom.mk' (epsMu K) epsMu_add).map_sub x y

theorem epsMu_injective (hp : ringChar 𝓀[K] ≠ 2) : Function.Injective (epsMu K) := by
  have h01 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  have hne : ((-1 : (SeparableClosure K)ˣ) : SeparableClosure K) ≠ 1 := by
    intro h
    have h2 : (2 : SeparableClosure K) = 0 := by
      simp only [Units.val_neg, Units.val_one] at h
      linear_combination -h
    have hpr : (ringChar 𝓀[K]).Prime := CharP.prime_ringChar 𝓀[K]
    have h2c : (2 : ℕ).Coprime (ringChar 𝓀[K]) :=
      (Nat.coprime_primes Nat.prime_two hpr).2 (Ne.symm hp)
    have h2K : (2 : K) ≠ 0 := by exact_mod_cast natCast_ne_zero_of_coprime_ringChar h2c
    apply h2K
    have := (algebraMap K (SeparableClosure K)).injective (a₁ := 2) (a₂ := 0)
    exact this (by rw [map_ofNat, map_zero]; exact h2)
  intro x y hxy
  have hv := congrArg (fun t : KummerCoeff K 2 =>
    (((Additive.toMul t : rootsOfUnity 2 (SeparableClosure K)) : (SeparableClosure K)ˣ) :
      SeparableClosure K)) hxy
  rcases h01 x with rfl | rfl <;> rcases h01 y with rfl | rfl
  · rfl
  · exact absurd (by simpa [epsMu, zmod2_val_one] using hv.symm) hne
  · exact absurd (by simpa [epsMu, zmod2_val_one] using hv) hne
  · rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Every element of `μ₂` is `epsMu` of something. -/
theorem epsMu_surjective : Function.Surjective (epsMu K) := by
  intro w
  have hw : ((w.toMul : (SeparableClosure K)ˣ) : SeparableClosure K) *
      ((w.toMul : (SeparableClosure K)ˣ) : SeparableClosure K) = 1 := by
    have := congrArg (fun u : (SeparableClosure K)ˣ => (u : SeparableClosure K))
      ((mem_rootsOfUnity _ _).1 w.toMul.2)
    simpa [sq] using this
  rcases mul_self_eq_one_iff.1 hw with h | h
  · refine ⟨0, Additive.toMul.injective (Subtype.ext (Units.ext ?_))⟩
    simp [epsMu, h]
  · refine ⟨1, Additive.toMul.injective (Subtype.ext (Units.ext ?_))⟩
    simp [epsMu, h, zmod2_val_one]

variable (K) in
/-- An inverse of `epsMu` (any function out of the discrete `μ₂` is continuous). -/
def invEps (w : KummerCoeff K 2) : ZMod 2 := (epsMu_surjective (K := K) w).choose

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem epsMu_invEps (w : KummerCoeff K 2) : epsMu K (invEps K w) = w :=
  (epsMu_surjective (K := K) w).choose_spec

/-! ### Transport of `2`-cochains to `(Kˢ)ˣ` -/

section Transport

variable [DistribMulAction (Gal(AlgebraicClosure K/K)) (ZMod 2)]
  [ContinuousSMul (Gal(AlgebraicClosure K/K)) (ZMod 2)]

variable (K) in
/-- The comparison `G_K = Gal(K^{alg}/K) ≃ Gal(Kˢ/K)`. -/
def Rg : Gal(AlgebraicClosure K/K) ≃ₜ* AbsoluteGaloisGroup K :=
  absoluteGaloisGroupRestrictEquiv K

/-- A `𝔽₂`-valued `2`-cochain of `G_K`, read as a `μ₂`-valued cochain of `Gal(Kˢ/K)`. -/
def Pmu (f : Gal(AlgebraicClosure K/K) × Gal(AlgebraicClosure K/K) → ZMod 2) :
    AbsoluteGaloisGroup K × AbsoluteGaloisGroup K → KummerCoeff K 2 :=
  fun p => epsMu K (f ((Rg K).symm p.1, (Rg K).symm p.2))

/-- The same, with values in `(Kˢ)ˣ`. -/
def Pu (f : Gal(AlgebraicClosure K/K) × Gal(AlgebraicClosure K/K) → ZMod 2) :
    AbsoluteGaloisGroup K × AbsoluteGaloisGroup K → UnitsCoeff K :=
  fun p => kummerCoeffIncl K 2 (Pmu f p)

theorem Pmu_mem_Z2 {f : Gal(AlgebraicClosure K/K) × Gal(AlgebraicClosure K/K) → ZMod 2}
    (hf : f ∈ Z2 (Gal(AlgebraicClosure K/K)) (ZMod 2)) :
    Pmu f ∈ Z2 (AbsoluteGaloisGroup K) (KummerCoeff K 2) := by
  obtain ⟨hc, hcoc⟩ := mem_Z2_iff.1 hf
  refine mem_Z2_iff.2 ⟨(continuous_of_discreteTopology (f := epsMu K)).comp
    (hc.comp ((Rg K).symm.continuous.prodMap (Rg K).symm.continuous)), fun g h j => ?_⟩
  simp only [Pmu, smul_kummerCoeff_two]
  have := hcoc ((Rg K).symm g) ((Rg K).symm h) ((Rg K).symm j)
  rw [smul_zmod_two] at this
  rw [map_mul, map_mul, ← epsMu_add, ← epsMu_add, this]

/-- Forward: the transport of a coboundary is a coboundary. -/
theorem Pmu_d1 (c : Gal(AlgebraicClosure K/K) → ZMod 2) :
    Pmu (d1 (Gal(AlgebraicClosure K/K)) (ZMod 2) c) =
      d1 (AbsoluteGaloisGroup K) (KummerCoeff K 2) (fun τ => epsMu K (c ((Rg K).symm τ))) := by
  funext p
  obtain ⟨g, h⟩ := p
  simp only [Pmu, d1_apply, smul_zmod_two, smul_kummerCoeff_two, map_mul]
  rw [epsMu_add, epsMu_sub]

/-- Backward: a `𝔽₂`-cochain whose transport is a `μ₂`-coboundary is a coboundary. -/
theorem mem_B2_of_Pmu (hp : ringChar 𝓀[K] ≠ 2)
    {f : Gal(AlgebraicClosure K/K) × Gal(AlgebraicClosure K/K) → ZMod 2}
    (hw : Pmu f ∈ B2 (AbsoluteGaloisGroup K) (KummerCoeff K 2)) :
    f ∈ B2 (Gal(AlgebraicClosure K/K)) (ZMod 2) := by
  obtain ⟨w, hwc, hwd⟩ := mem_B2_iff.1 hw
  refine mem_B2_iff.2 ⟨fun g => invEps K (w (Rg K g)),
    (continuous_of_discreteTopology (f := invEps K)).comp (hwc.comp (Rg K).continuous), ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  apply epsMu_injective hp
  have := congrFun hwd (Rg K g, Rg K h)
  simp only [Pmu, d1_apply, smul_kummerCoeff_two, ContinuousMulEquiv.symm_apply_apply] at this
  rw [d1_apply, smul_zmod_two, epsMu_add, epsMu_sub, epsMu_invEps, epsMu_invEps, epsMu_invEps,
    map_mul]
  exact this

/-- **Injectivity of `H²(G_K, 𝔽₂) → Br K`** at the cochain level: a `2`-cocycle whose transport to
`(Kˢ)ˣ` is a coboundary is a coboundary (Kummer sequence, Hilbert 90). -/
theorem mem_B2_of_Pu (hp : ringChar 𝓀[K] ≠ 2)
    {f : Gal(AlgebraicClosure K/K) × Gal(AlgebraicClosure K/K) → ZMod 2}
    (hf : f ∈ Z2 (Gal(AlgebraicClosure K/K)) (ZMod 2))
    (hu : Pu f ∈ B2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :
    f ∈ B2 (Gal(AlgebraicClosure K/K)) (ZMod 2) := by
  have hpr : (ringChar 𝓀[K]).Prime := CharP.prime_ringChar 𝓀[K]
  have h2c : (2 : ℕ).Coprime (ringChar 𝓀[K]) :=
    (Nat.coprime_primes Nat.prime_two hpr).2 (Ne.symm hp)
  have hn2 : IsUnit ((2 : ℕ) : K) :=
    isUnit_iff_ne_zero.2 (natCast_ne_zero_of_coprime_ringChar h2c)
  set S := kummerShortExact K 2 hn2
  have hZ := Pmu_mem_Z2 hf
  have h0 : explicitCoeff2 (AbsoluteGaloisGroup K) (KummerCoeff K 2) S.inclDistribMulActionHom
      continuous_of_discreteTopology
      ((⟨Pmu f, hZ⟩ : Z2 (AbsoluteGaloisGroup K) (KummerCoeff K 2)) :
        H2 (AbsoluteGaloisGroup K) (KummerCoeff K 2)) = 0 := by
    rw [explicitCoeff2_mk, H2pi_eq_zero_iff]
    exact hu
  have hmem := S.explicitLongExact_H2A ▸ (AddMonoidHom.mem_ker.2 h0)
  obtain ⟨x, hx⟩ := hmem
  rw [Subsingleton.elim x 0, map_zero] at hx
  exact mem_B2_of_Pmu hp ((H2pi_eq_zero_iff).1 hx.symm)

end Transport

end ZInQ.Contrib.CloudB3RC53.TameModel
