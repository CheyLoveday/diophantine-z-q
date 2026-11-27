import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedLocal
import Mathlib.NumberTheory.Padics.RingHoms

/-! The intrinsic nebentypus at a tested prime (tex 9754–9756, 9799–9811). -/

noncomputable section
set_option quotPrecheck false

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs BlocksPerU EvenBudget EvenExpansion HeckeRing.GL2
open IsDedekindDomain ModularForm NumberField O12 O12Local PrintsArith Symbols ThetaCoeff Wiring
open UpperHalfPlane
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd

section Residue

variable {p : ℕ} [Fact p.Prime]

/-- Reduction of an element of `ℚ_pˣ` of norm one. -/
def localUnitResidue (u : ℚ_[p]ˣ) (hu : ‖(u : ℚ_[p])‖ = 1) : (ZMod p)ˣ :=
  Units.map PadicInt.toZMod.toMonoidHom (PadicInt.mkUnits hu)

theorem localUnitResidue_eq_one {u : ℚ_[p]ˣ} (hu : unitAtLevel p 1 u) :
    localUnitResidue u hu.1 = 1 := by
  apply Units.ext
  let z := (PadicInt.mkUnits hu.1 : ℤ_[p])
  change PadicInt.toZMod z = 1
  have hz : PadicInt.toZMod (z - 1) = 0 := by
    change z - 1 ∈ RingHom.ker PadicInt.toZMod
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
    have h := hu.2.resolve_left (by decide : (1 : ℕ) ≠ 0)
    have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hlt : ‖(u : ℚ_[p]) - 1‖ < 1 := by
      simpa only [pow_one] using h.trans_lt
        (show ((p : ℝ)⁻¹)^1 < 1 by simpa using inv_lt_one_of_one_lt₀ hp)
    exact hlt
  simpa only [map_sub, map_one, sub_eq_zero] using hz

private theorem localUnitResidue_natCast (a : (ZMod p)ˣ) :
    ∃ (u : ℚ_[p]ˣ) (hu : ‖(u : ℚ_[p])‖ = 1), localUnitResidue u hu = a := by
  let n := (a : ZMod p).val
  have hcop := ZMod.val_coe_unit_coprime a
  have hn : ‖(n : ℚ_[p])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr hcop.symm
  let u := Units.mk0 (n : ℚ_[p]) (norm_ne_zero_iff.mp (by simp [hn]))
  refine ⟨u, hn, Units.ext ?_⟩
  change PadicInt.toZMod (PadicInt.mkUnits hn : ℤ_[p]) = (a : ZMod p)
  have he : (PadicInt.mkUnits hn : ℤ_[p]) = (n : ℤ_[p]) := by
    apply Subtype.ext
    rfl
  rw [he, map_natCast, ZMod.natCast_zmod_val]

/-- The norm-one restriction of the unitary central character determines its
conductor when that restriction is the nontrivial residual quadratic character. -/
theorem charConductor_of_localUnitResidue {K : Type*} [Field K] [CharZero K]
    (hp₂ : p ≠ 2) (χ : LocalCharacter p K)
    (hχ : ∀ u hu, (χ u : K) = (quadraticChar (ZMod p) (localUnitResidue u hu) : K)) :
    charConductor p χ 1 := by
  refine ⟨fun u hu => Units.ext ?_, fun n hn h => ?_⟩
  · simp only [hχ u hu.1, localUnitResidue_eq_one hu, Units.val_one, map_one, Int.cast_one]
  · have hn₀ : n = 0 := by omega
    subst n
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one'
      (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
    obtain ⟨u, hu, hur⟩ := localUnitResidue_natCast a
    have e := congrArg Units.val (h u ⟨hu, Or.inl rfl⟩)
    rw [hχ u hu, hur, ha, Int.cast_neg, Int.cast_one, Units.val_one] at e
    norm_num at e

end Residue

section Inventory

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {hS : SupportSpec W} {i : Fin 2} {U : Finset ℕ}
variable (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
variable {p : ℕ} (hpU : p ∈ U)
variable {A : ∀ b : EvenBlock U, CuspBlockExpansion (evenBlockLevel P b)
  (evenBlockSeries P hS i b)}
variable [hLevel : NeZero (movingLevel P U)]
variable (hB : IsMovingCharacter P U (A none).χ)
variable (hJ : ∀ j : ↥(subscripts U), IsUnaryCharacter P i j.val (A (some j)).χ)

local notation "Sources" => ↥(cuspSources (distinctCuspColumns A (evenBlockLevel_dvd (P := P))))

include hLevel hU hpU in
/-- At an intrinsically ramified source the tested prime occurs exactly once. -/
theorem tested_sourceLevel_exponent_one (s : Sources) (hs : p ∣ s.val.level) :
    ∃ M : ℕ, s.val.level = p * M ∧ p.Coprime M := by
  obtain ⟨M, hM⟩ := hs
  refine ⟨M, hM, (Nat.Prime.coprime_iff_not_dvd (hU p hpU).1).mpr ?_⟩
  intro h
  exact tested_square_not_dvd_movingLevel (P := P) (hS := hS) hU hpU
    ((show p ^ 2 ∣ s.val.level by rw [hM, pow_two]; exact Nat.mul_dvd_mul_left _ h).trans
      (cuspSource_dvd _ s))

include hU hpU hB hJ in
/-- Read the intrinsic character on a unit with trivial complementary component.
The lift is chosen to be one modulo the complementary ambient level. -/
theorem tested_sourceChar_at_tested_unit (s : Sources) (hs : p ∣ s.val.level)
    {n : ℕ} (hn : n.Coprime (movingLevel P U))
    (hnM : n ≡ 1 [MOD movingLevel P (U.erase p)]) :
    (s.val.char (ZMod.unitOfCoprime n (hn.of_dvd_right (cuspSource_dvd _ s))) : ℂ) =
      (jacobiSym (p : ℤ) n : ℂ) := by
  obtain ⟨x, hx⟩ := cuspSource_exists _ s
  obtain ⟨b, c, hc⟩ := (mem_distinctCuspColumns A (evenBlockLevel_dvd (P := P)) _).mp x.property
  have hsrc := (congrArg CuspDilation.source hc).trans hx
  have hb := (tested_dvd_source_iff hU hpU hB hJ b c).mp (by rw [hsrc]; exact hs)
  let u := ZMod.unitOfCoprime n hn
  have e := congrArg (fun χ => (χ u : ℂ))
    ((A b).liftColumn_char (evenBlockLevel_dvd (P := P) b) c)
  have hleft : ((A b).liftColumn (evenBlockLevel_dvd (P := P) b) c).char u =
      s.val.char (ZMod.unitOfCoprime n (hn.of_dvd_right (cuspSource_dvd _ s))) := by
    rw [CuspDilation.char, MonoidHom.comp_apply, ZMod.unitsMap_unitOfCoprime]
    have hsame (s₁ s₂ : NormalizedCuspSource) (he : s₁ = s₂)
        (h₁ : s₁.level ∣ movingLevel P U) (h₂ : s₂.level ∣ movingLevel P U) :
        s₁.char (ZMod.unitOfCoprime n (hn.of_dvd_right h₁)) =
          s₂.char (ZMod.unitOfCoprime n (hn.of_dvd_right h₂)) := by
      subst s₂
      rfl
    exact hsame _ _ hsrc ((A b).liftColumn (evenBlockLevel_dvd (P := P) b) c).source_dvd
      (cuspSource_dvd _ s)
  rw [hleft] at e
  refine e.trans ?_
  simpa only [u, MonoidHom.comp_apply, ZMod.unitsMap_unitOfCoprime,
    MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime] using
    even_blockChar_at_tested_unit hU hB hJ b hn hnM hb

variable [Fact p.Prime]

/-- GLUE (tex 9754–9756, 9799–9801). On norm-one scalars of the actual
local action the central character reads the source nebentypus.
The global lift is one at the complementary ambient level. -/
def SourceCentralCharacterAt {K : Type*} [Field K] (κ : K →+* ℂ)
    (s : Sources) (χ : LocalCharacter p K) : Prop :=
  ∀ (u : ℚ_[p]ˣ) (hu : ‖(u : ℚ_[p])‖ = 1)
    (n : ℕ) (hn : n.Coprime (movingLevel P U)),
      n ≡ 1 [MOD movingLevel P (U.erase p)] →
      (n : ZMod p) = (localUnitResidue u hu : ZMod p) →
      κ (χ u : K) = (s.val.char (ZMod.unitOfCoprime n
        (hn.of_dvd_right (cuspSource_dvd _ s))) : ℂ)

include hU hpU hB hJ in
/-- The central character on norm-one scalars is the quadratic character
of the residue, using the actual ramified source's nebentypus. -/
theorem sourceCentralCharacter_of_tested {K : Type*} [Field K] (κ : K →+* ℂ)
    (s : Sources) (hs : p ∣ s.val.level) (χ : LocalCharacter p K)
    (hχ : SourceCentralCharacterAt κ s χ) :
    ∀ u hu, (χ u : K) = (quadraticChar (ZMod p) (localUnitResidue u hu) : K) := by
  intro u hu
  let M := movingLevel P (U.erase p)
  have hsplit : movingLevel P U = p * M := by
    unfold M movingLevel
    rw [← Finset.mul_prod_erase U (fun q : ℕ => q) hpU]
    ac_rfl
  have hp := (hU p hpU).1
  have hcop : p.Coprime M := (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h =>
    tested_square_not_dvd_movingLevel (P := P) (hS := hS) hU hpU
      (by rw [hsplit, pow_two]; exact Nat.mul_dvd_mul_left _ h)
  let a := localUnitResidue u hu
  obtain ⟨n, hnp, hnM⟩ := Nat.chineseRemainder hcop (a : ZMod p).val 1
  have hnZ : (n : ZMod p) = (a : ZMod p) := by
    rw [← ZMod.natCast_zmod_val (a : ZMod p), ZMod.natCast_eq_natCast_iff']
    exact hnp
  have hnp' : n.Coprime p := (ZMod.isUnit_iff_coprime _ _).mp (hnZ.symm ▸ a.isUnit)
  have hnM' : n.Coprime M := by rw [Nat.Coprime, hnM.gcd_eq, Nat.gcd_one_left]
  have hn : n.Coprime (movingLevel P U) := by rw [hsplit]; exact hnp'.mul_right hnM'
  have h4 : 4 ∣ M := (evenMasked P hS).1.trans (dvd_mul_right _ _)
  have hn4 : n % 4 = 1 := Nat.ModEq.of_dvd h4 hnM
  apply κ.injective
  rw [hχ u hu n hn hnM hnZ, tested_sourceChar_at_tested_unit hU hpU hB hJ s hs hn hnM,
    jacobiSym.quadratic_reciprocity_one_mod_four' (hp.odd_of_ne_two (hU p hpU).ne_two) hn4,
    ← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast, hnZ, map_intCast]

end Inventory

end ZInQ.Manuscript.RC.EvenJoin
