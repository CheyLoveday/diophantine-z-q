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

open CategoryTheory TauCeti ValuativeRel ContCohomology TauCeti.ClassFieldTheory
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

/-! ### The unramified quadratic character as a `ℚ/ℤ`-valued character -/

/-- `1/2 ∈ ℚ/ℤ`. -/
def halfQZ : AddCircle (1 : ℚ) := ((1 / 2 : ℚ) : AddCircle (1 : ℚ))

theorem two_zsmul_halfQZ : (2 : ℤ) • halfQZ = 0 := by
  have h : ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) + ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) = 0 := by
    rw [← AddCircle.coe_add (p := (1 : ℚ)), show (1 / 2 : ℚ) + 1 / 2 = 1 by norm_num]
    exact AddCircle.coe_period (1 : ℚ)
  change (2 : ℤ) • ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) = 0
  rw [two_zsmul]
  exact h

theorem halfQZ_ne_zero : halfQZ ≠ 0 := by
  intro h
  rw [halfQZ, AddCircle.coe_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have : (n : ℚ) = 1 / 2 := by simpa using hn
  have h2 : (2 * n : ℚ) = 1 := by rw [this]; norm_num
  have : (2 * n : ℤ) = 1 := by exact_mod_cast h2
  omega

/-- `𝔽₂ → ℚ/ℤ`, `x ↦ x/2`. -/
def zmod2ToQZ : ZMod 2 →+ AddCircle (1 : ℚ) :=
  ZMod.lift 2 ⟨zmultiplesHom _ halfQZ, by simpa using two_zsmul_halfQZ⟩

theorem zmod2ToQZ_one : zmod2ToQZ 1 = halfQZ := by
  have : ((1 : ℤ) : ZMod 2) = 1 := by simp
  rw [← this, zmod2ToQZ, ZMod.lift_coe]
  simp

theorem zmod2ToQZ_eq_zero_iff (x : ZMod 2) : zmod2ToQZ x = 0 ↔ x = 0 := by
  have h01 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases h01 x with rfl | rfl
  · simp
  · rw [zmod2ToQZ_one]
    exact ⟨fun h => absurd h halfQZ_ne_zero, fun h => absurd h (by decide)⟩

variable (K) in
/-- The unramified quadratic character on `Gal(Kˢ/K)`, additively. -/
def urA : Additive (AbsoluteGaloisGroup K) →+ ZMod 2 where
  toFun x := urChar K ((Rg K).symm x.toMul)
  map_zero' := by
    have := urChar_mul (K := K) 1 1
    rw [mul_one] at this
    change urChar K ((Rg K).symm 1) = 0
    rw [map_one]
    simpa using this
  map_add' x y := by
    change urChar K ((Rg K).symm (x.toMul * y.toMul)) = _
    rw [map_mul, urChar_mul]

variable (K) in
/-- **The `ℚ/ℤ`-valued unramified character of order two** `χ = χ_ur / 2`. -/
def chiQZ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ) := zmod2ToQZ.comp (urA K)

theorem continuous_urA : Continuous (fun τ : AbsoluteGaloisGroup K => urA K (Additive.ofMul τ)) :=
  continuous_urChar.comp (Rg K).symm.continuous

theorem isOpen_ker_chiQZ : IsOpen ((chiQZ K).ker : Set (Additive (AbsoluteGaloisGroup K))) := by
  have : ((chiQZ K).ker : Set (Additive (AbsoluteGaloisGroup K))) =
      (fun τ : AbsoluteGaloisGroup K => urA K (Additive.ofMul τ)) ⁻¹' {0} := by
    ext x
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, chiQZ, AddMonoidHom.comp_apply,
      zmod2ToQZ_eq_zero_iff]
    rfl
  rw [this]
  exact (isOpen_discrete _).preimage continuous_urA

instance : Fact ((0 : ℚ) < 1) := ⟨one_pos⟩

theorem equivIco_halfQZ : (AddCircle.equivIco (1 : ℚ) 0 halfQZ : ℚ) = 1 / 2 := by
  rw [halfQZ, AddCircle.equivIco_coe_eq (by norm_num : (1 / 2 : ℚ) ∈ Set.Ico 0 (0 + 1))]

theorem equivIco_zeroQZ : (AddCircle.equivIco (1 : ℚ) 0 (0 : AddCircle (1 : ℚ)) : ℚ) = 0 := by
  rw [← AddCircle.coe_zero, AddCircle.equivIco_coe_eq (by norm_num : (0 : ℚ) ∈ Set.Ico 0 (0 + 1))]

/-- **The carry of `χ_ur/2`** is the product of the two parities. -/
theorem characterCarry_chiQZ (g h : AbsoluteGaloisGroup K) :
    characterCarry (chiQZ K) g h =
      ((urA K (Additive.ofMul g)).val * (urA K (Additive.ofMul h)).val : ℤ) := by
  have h01 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  have hv : ∀ τ : AbsoluteGaloisGroup K, (AddCircle.equivIco (1 : ℚ) 0 (chiQZ K (.ofMul τ)) : ℚ) =
      (urA K (Additive.ofMul τ)).val / 2 := by
    intro τ
    change (AddCircle.equivIco (1 : ℚ) 0 (zmod2ToQZ (urA K (.ofMul τ))) : ℚ) = _
    rcases h01 (urA K (.ofMul τ)) with h | h <;> rw [h]
    · rw [map_zero, equivIco_zeroQZ]; simp
    · rw [zmod2ToQZ_one, equivIco_halfQZ, zmod2_val_one]; norm_num
  rw [characterCarry, hv, hv]
  rcases h01 (urA K (.ofMul g)) with hg | hg <;> rcases h01 (urA K (.ofMul h)) with hh | hh <;>
    simp [hg, hh, zmod2_val_one] <;> norm_num

/-- **The arithmetic Frobenius has unramified parity one**: an element representing `Art_K ϖ` for a
uniformizer `ϖ`. -/
theorem urChar_of_artinMap {ϖ : Kˣ} (hϖ : normalizedValuation K ϖ = .ofAdd 1)
    {σ : Field.absoluteGaloisGroup K}
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = artinMap K ϖ) :
    urChar K σ = 1 := by
  have hE : maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)
      (restrictMaximalUnramifiedHom K σ) = zHat.gen := by
    rw [← unramifiedCoordinate_mk, hσ, unramifiedCoordinate_artinMap, hϖ, zHat.ofInt_ofAdd,
      zpow_one]
  change Multiplicative.toAdd ((zHat.lift (Multiplicative.ofAdd (1 : ZMod 2)) :
    zHat →ₜ* Multiplicative (ZMod 2)) (maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)
      (restrictMaximalUnramifiedHom K σ))) = 1
  rw [hE, zHat.lift_gen, toAdd_ofAdd]

/-- **The invariant of the carry class `ϖ ∪ δ(χ_ur/2)` is `1/2`.** -/
theorem invMap_carry_eq_half {ϖ : Kˣ} (hϖ : normalizedValuation K ϖ = .ofAdd 1) :
    invMap K (unitsRepH2Equiv K (characterCarryCocycle (chiQZ K) isOpen_ker_chiQZ
        (baseUnitsEquivInvariants K (.ofMul ϖ)) : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K))) =
      halfQZ := by
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (artinMap K ϖ)
  rw [ClassFieldTheory.invMap_characterCarryCocycle_of_mk_eq_artinMap (chiQZ K)
    isOpen_ker_chiQZ ϖ σ hσ]
  change zmod2ToQZ (urChar K ((Rg K).symm (absoluteGaloisGroupRestrictEquiv K σ))) = halfQZ
  rw [show (Rg K).symm (absoluteGaloisGroupRestrictEquiv K σ) = σ from
    (Rg K).symm_apply_apply σ, urChar_of_artinMap hϖ hσ, zmod2ToQZ_one]

end ZInQ.Contrib.CloudB3RC53.TameModel
