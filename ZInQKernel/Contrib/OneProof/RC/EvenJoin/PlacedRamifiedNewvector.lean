import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedWhittakerEvaluation

/-! Reduce the scalar comparison on an intrinsic ramified source to the
Whittaker functional on its classical newvector (tex 9855–9861). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs BlocksPerU EvenBudget EvenExpansion HeckeRing.GL2 Matrix
open IsDedekindDomain ModularForm NumberField O12 O12Local PrintsArith Symbols ThetaCoeff Wiring
open UpperHalfPlane ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

section CoefficientField

variable {B : Type} [Fintype B] {N : ℕ} {m : B → ℕ} {a : B → ℕ → ℂ}
variable {A : ∀ b, CuspBlockExpansion (m b) (a b)} {hm : ∀ b, m b ∣ N}
variable {F : IntermediateField ℚ ℂ} [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

/-- Choose a receiving field containing the unitary square roots at all
the primes of this row, with a new receiving place over the fixed place. -/
theorem PlacedCuspLists.exists_with_local_square_roots (D : PlacedCuspLists A hm v)
    (U : Finset ℕ) :
    ∃ D' : PlacedCuspLists A hm v, D.E ≤ D'.E ∧
      ∀ p ∈ U, ((Real.sqrt (p : ℝ) : ℝ) : ℂ) ∈ D'.E := by
  let s : ↥U → ℂ := fun p => (Real.sqrt (p.val : ℝ) : ℂ)
  let H := IntermediateField.adjoin ℚ (Set.range s)
  have hs (p : ↥U) : IsIntegral ℚ (s p) := by
    apply IsIntegral.of_pow (n := 2) (by decide)
    have he : s p ^ 2 = (p.val : ℂ) := by
      change ((Real.sqrt (p.val : ℝ) : ℂ) ^ 2) = (p.val : ℂ)
      exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p.val)
    rw [he]
    exact isIntegral_natCast _
  let : FiniteDimensional ℚ H :=
    IntermediateField.finiteDimensional_adjoin (fun _ ⟨p, h⟩ => h ▸ hs p)
  let E := D.E ⊔ H
  let : FiniteDimensional ℚ E := IntermediateField.finiteDimensional_sup D.E H
  let : NumberField E := {}
  let hFE : F ≤ E := D.includes.trans le_sup_left
  let : Algebra F E := (IntermediateField.inclusion hFE).toAlgebra
  obtain ⟨w, hw⟩ := exists_constituent_place (E := E) v
  refine ⟨{ E := E
            numberField := inferInstance
            includes := hFE
            w := w
            liesOver := hw
            source_mem := fun x => (D.source_mem x).trans le_sup_left
            block_char_mem := fun b u => (show D.E ≤ E from le_sup_left) (D.block_char_mem b u) },
    le_sup_left, ?_⟩
  intro p hp
  exact (show H ≤ E from le_sup_right) (IntermediateField.subset_adjoin ℚ _ ⟨⟨p, hp⟩, rfl⟩)

end CoefficientField

section UnitModulus

variable (p : ℕ) [Fact p.Prime] {K : Type*} [Field K]

/-- The unitary half-modulus from the inverse square root of the tested
prime, read with the additive p-adic valuation. -/
def halfModulusOfRoot (r : Kˣ) : LocalCharacter p K where
  toFun u := r ^ (-Padic.valuation (u : ℚ_[p]))
  map_one' := by simp [Padic.valuation_one]
  map_mul' u v := by
    rw [Units.val_mul, Padic.valuation_mul u.ne_zero v.ne_zero, neg_add, _root_.zpow_add]

theorem halfModulusOfRoot_units (r : Kˣ) : charTrivialAt p (halfModulusOfRoot p r) 0 := by
  intro u hu
  have hp : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  have h := (Padic.norm_eq_zpow_neg_valuation u.ne_zero : ‖(u : ℚ_[p])‖ =
    (p : ℝ) ^ (-Padic.valuation (u : ℚ_[p])))
  rw [hu.1, ← zpow_zero (p : ℝ), zpow_right_inj₀ (by positivity : (0 : ℝ) < p) hp.ne'] at h
  change r ^ (-Padic.valuation (u : ℚ_[p])) = 1
  rw [← h, zpow_zero]

theorem halfModulusOfRoot_uniformizer (r : Kˣ) (hr : (r : K) ^ 2 = (p : K)) :
    (p : K) * (halfModulusOfRoot p r (uniformizer p) : K) ^ 2 = 1 := by
  have he : halfModulusOfRoot p r (uniformizer p) = r⁻¹ := by
    simp [halfModulusOfRoot, uniformizer]
  rw [he, Units.val_inv_eq_inv_val, inv_pow, ← hr,
    mul_inv_cancel₀ (pow_ne_zero 2 r.ne_zero)]

end UnitModulus

set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 1500000

section Local

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
variable {Q : LocalPair p} {ρ : GalQ →* GL (Fin 2) K}
variable (R : RamifiedFactor K Q ρ)

/-- On any fixed vector with functional value one, the finite sum of
the translated functional values reads the computed line scalar. -/
theorem ramified_scalar_complex_eq_sum (κ : K →+* ℂ) (v : R.V) (hv : v ∈ levelSpace p R.π 1)
    (ev : R.V →ₛₗ[κ] ℂ) (hev : ev v = 1) :
    κ (Classical.choice R.line).eigenvalue = ∑ b : Fin p, ev (R.π (representative p b) v) := by
  let C := Classical.choice R.line
  have hc := conductor_one p R.π R.χ R.central R.char_one R.exact_conductor R.occurs R.level_le
  have hdim : Module.finrank K (levelSpace p R.π 1) = 1 :=
    ((hc ▸ R.oldspace : CasselmanOldspace p R.π 1) 1).2
  let w : levelSpace p R.π 1 := ⟨C.gen, C.in_line⟩
  have hwn : w ≠ 0 := fun h => C.nonzero (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' w hwn).mp hdim ⟨v, hv⟩
  have he : c • C.gen = v := congrArg Subtype.val hc
  have hHecke : localHecke R.π v = C.eigenvalue • v := by
    rw [← he, smul_smul]
    exact C.on_copy c
  have heval := (congrArg ev hHecke).symm
  simpa only [localHecke, LinearMap.sum_apply, map_sum, map_smulₛₗ, smul_eq_mul, hev,
    mul_one, C] using heval

/-- GLUE (tex 9841–9856). The fixed vector from the classical newform has
normalized Whittaker functional value one. At each displayed translate
the same functional reads the classical Fourier integral of that source.
This is an identification of individual translations of a vector in
the local action. -/
def NormalizedCuspSource.LocalWhittakerTest (s : NormalizedCuspSource) (κ : K →+* ℂ) : Prop :=
  letI : NeZero s.level := ⟨s.level_ne⟩
  ∃ (v : R.V) (ev : R.V →ₛₗ[κ] ℂ), v ∈ levelSpace p R.π 1 ∧ ev v = 1 ∧
    ∀ b : Fin p, ev (R.π (representative p b) v) =
      whittakerIntegral s.newform.toCuspForm ⟨p, (Fact.out : p.Prime).ne_zero⟩
        (whittakerOffset ⟨p, (Fact.out : p.Prime).ne_zero⟩ (b.val : ℤ))

/-- For an actual width-one form, the sum of the individual translated
integrals is the first coefficient of Tau Ceti's classical slash sum. -/
theorem whittaker_translate_sum_eq_classical {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} [ModularFormClass F Γ 2]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F) (n : PosIndex) :
    ∑ b : Fin n.val, whittakerIntegral f n (whittakerOffset n (b.val : ℤ)) =
      (qExpansion 1 (heckeSlashUpperTri 2 n.val f)).coeff 1 := by
  rw [qExpansion_coeff_heckeSlashUpperTri' 2 n.val hΓ (Nat.pos_of_ne_zero n.property) f 1, mul_one]
  simp_rw [whittakerIntegral_eq hΓ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [Nat.cast_ne_zero.mpr n.property]

/-- The normalized integral of each translated newvector reads
`a_p / p`. Summing the local translates gives the classical coefficient
on the computed ramified line. -/
theorem ramified_scalar_complex_eq (s : NormalizedCuspSource) (κ : K →+* ℂ)
    (h : s.LocalWhittakerTest R κ) :
    κ (Classical.choice R.line).eigenvalue = s.coeff p := by
  let : NeZero s.level := ⟨s.level_ne⟩
  obtain ⟨v, ev, hv, hev, hW⟩ := h
  rw [ramified_scalar_complex_eq_sum R κ v hv ev hev]
  simp_rw [hW]
  have hΓ := TauCeti.one_mem_strictPeriods_Gamma1_map s.level
  change _ = (qExpansion 1 s.newform.toCuspForm).coeff p
  rw [whittaker_translate_sum_eq_classical hΓ s.newform.toCuspForm
      ⟨p, (Fact.out : p.Prime).ne_zero⟩,
    qExpansion_coeff_heckeSlashUpperTri' 2 p hΓ (Fact.out : p.Prime).pos, mul_one]

end Local

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {hS : SupportSpec W} {i : Fin 2} {U : Finset ℕ}
variable {F : IntermediateField ℚ ℂ} [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
variable {A : ∀ b : EvenBlock U, CuspBlockExpansion (evenBlockLevel P b)
  (evenBlockSeries P hS i b)}
variable [NeZero (movingLevel P U)]
variable (D : PlacedCuspLists A (evenBlockLevel_dvd (P := P)) v)
variable (hIndependent : OldNewIndependenceWeightTwo)
variable (H : D.sourceAttachments (hS := hS) hIndependent)
variable {p : ℕ} [Fact p.Prime] (Q : LocalPair p)

local notation "Columns" => ↥(distinctCuspColumns A (evenBlockLevel_dvd (P := P)))
local notation "Sources" => ↥(cuspSources (distinctCuspColumns A (evenBlockLevel_dvd (P := P))))
local notation "Y" => D.inventory (evenTypes W.S hS.1) hIndependent

/-- GLUE (tex 9773–9840, 9855–9861). Realize each required local factor on
the place and representation already chosen for the source. Supply the
individual classical Whittaker tests when the undilated column occurs. -/
def PlacedCuspLists.RamifiedLocalModelAt : Prop :=
  ∀ s : Sources, p ∣ (Y).sourceLevel s →
    ∃ R : RamifiedFactor (FixedField D.w) Q (H s).ρ,
      (∃ x : Columns, (Y).origin x = s ∧ (Y).degree x = 1) →
        s.val.LocalWhittakerTest R D.κ

/-- Compute the source coefficient on the local line from the
individual classical Whittaker tests. -/
theorem PlacedCuspLists.ramifiedNewvectorAt_of_whittakerTests
    (h : D.RamifiedLocalModelAt hIndependent H Q) :
    D.RamifiedNewvectorAt hIndependent H Q := by
  intro s hs
  obtain ⟨R, hW⟩ := h s hs
  refine ⟨R, fun h1 => D.κ.injective ?_⟩
  rw [ramified_scalar_complex_eq R s.val D.κ (hW h1)]
  change _ = D.κ ((s.val.eigen (T := evenTypes W.S hS.1) D.κ _ _).a p)
  rw [NormalizedCuspSource.eigen_a]

variable (hU : ∀ q ∈ U, (evenTypes W.S hS.1).Good q)
variable (hB : IsMovingCharacter P U (A none).χ)
variable (hJ : ∀ j : ↥(subscripts U), IsUnaryCharacter P i j.val (A (some j)).χ)

include hU hB hJ in
omit [Fact p.Prime] in
/-- A retained old degree greater than one contributes at neither Fourier
endpoint, since the tested prime cannot divide that degree. -/
theorem PlacedCuspLists.old_degree_endpoint_coefficients (hpU : p ∈ U) (x : Columns)
    (hd : (Y).degree x ≠ 1) :
    (Y).expansion x 1 = 0 ∧ (Y).expansion x p = 0 := by
  have hp := (hU p hpU).1
  have hdp : ¬ (Y).degree x ∣ p := by
    intro h
    rcases (Nat.dvd_prime hp).mp h with h1 | h2
    · exact hd h1
    · exact tested_not_dvd_degree hU hpU hB hJ x
        (show p ∣ (Y).degree x by rw [h2])
  simp [Inventory.expansion, Odd.divCoeff, hd, hdp]

variable [NeZero (conductor W.S)]
variable (C₀ : SourceAtPlace P (FixedRing v) (FixedField v))
variable (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
variable (horder : ∃ e : ℕ, P.phaseData.η ^ (2 ^ e) = 1)
variable (htwo : (2 : 𝓞 F) ∈ v.asIdeal)

include hB hJ in
/-- Supply the existing per-set binder once the intrinsic local models
and their individual newvector tests have been realized. -/
theorem PlacedCuspLists.placedGaloisInput_of_carayol_of_localModels
    (j : C₀.K₀ →+* F) (hK : (FinitePlace.embedding v).comp j = C₀.eK)
    (hC : F.subtype.comp j = C₀.eC) (hCarayol : CarayolRefold.CarayolThmAFrob) (B : ℕ)
    (hR : ∀ q (hq : q ∈ U) (Q : LocalPair q),
      letI : Fact q.Prime := ⟨(hU q hq).1⟩
      D.RamifiedLocalModelAt hIndependent
        (D.attachmentsOfCarayol hIndependent htwo hCarayol) Q) :
    PlacedGaloisInput (hS := hS) C₀ j hK hC htwo hodd horder hIndependent B U hU :=
  D.placedGaloisInput_of_carayol_of_ramified hU hIndependent C₀ hB hJ hodd horder htwo
    j hK hC hCarayol B (fun q hq Q =>
      letI : Fact q.Prime := ⟨(hU q hq).1⟩
      D.ramifiedNewvectorAt_of_whittakerTests hIndependent
        (D.attachmentsOfCarayol hIndependent htwo hCarayol) Q (hR q hq Q))

end ZInQ.Manuscript.RC.EvenJoin
