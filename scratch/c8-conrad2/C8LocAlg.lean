import ZInQKernel.Contrib.OneProof.C8Conrad
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.ArtinMap

/-! # c8-conrad2: `LocAlgExponentEqWeight` from Tate's theorem over `\hat{K^{ur}}` -/

set_option linter.style.longLine false

noncomputable section

namespace HDec.G0Galois.C8Conrad

open Module

section Units

variable (p : ℕ) [Fact p.Prime]

/-- A `p`-adic number of valuation one (Tau Ceti's `ValuativeRel` valuation) has norm one. -/
theorem norm_eq_one_of_valuation_eq_one (x : ℚ_[p]ˣ) (h : ValuativeRel.valuation ℚ_[p] (x : ℚ_[p]) = 1) :
    ‖(x : ℚ_[p])‖ = 1 := by
  have h1 : Padic.mulValuation (x : ℚ_[p]) = 1 := by
    have he : (ValuativeRel.valuation ℚ_[p]).IsEquiv (Padic.mulValuation (p := p)) :=
      ValuativeRel.isEquiv _ _
    exact (he.eq_one_iff_eq_one).1 h
  rw [Padic.norm_eq_zpow_log_mulValuation x.ne_zero, h1]
  simp

/-- Every lift of an element of the inertia group of `ℚ_p` represents the Artin symbol of a unit of `ℤ_p`. -/
theorem exists_unit_isArtinLift (σ : PkgI4.GQp p)
    (hσ : (show Field.absoluteGaloisGroup ℚ_[p] from σ) ∈ TauCeti.inertiaSubgroup ℚ_[p]) :
    ∃ u : ℤ_[p]ˣ, IsArtinLift p σ (unitsQp p u) := by
  have hmem : (QuotientGroup.mk' _ (show Field.absoluteGaloisGroup ℚ_[p] from σ) :
      Field.absoluteGaloisGroupAbelianization ℚ_[p]) ∈
      (TauCeti.inertiaSubgroup ℚ_[p]).map (QuotientGroup.mk' _) := ⟨_, hσ, rfl⟩
  rw [← TauCeti.ClassFieldTheory.map_artinMap_unitFiltration_zero] at hmem
  obtain ⟨y, hy, hyσ⟩ := hmem
  have hn : ‖(y : ℚ_[p])‖ = 1 :=
    norm_eq_one_of_valuation_eq_one p y ((TauCeti.mem_unitFiltration_zero y).1 hy)
  let u : ℤ_[p]ˣ := PadicInt.mkUnits hn
  refine ⟨u, ?_⟩
  have hyu : unitsQp p u = y := Units.ext rfl
  rw [IsArtinLift, hyu, hyσ]
  rfl

/-- The cyclotomic character of an Artin lift of a unit `u` is `u⁻¹` (Tau Ceti). -/
theorem cyc_of_isArtinLift (σ : PkgI4.GQp p) (u : ℤ_[p]ˣ) (h : IsArtinLift p σ (unitsQp p u)) :
    PkgI4.cyc p σ = u⁻¹ :=
  TauCeti.ClassFieldTheory.localCyclotomicCharacter_artinMap_padic p u σ h

/-- If `σ` fixes a primitive `p^k`-th root of unity, its cyclotomic character is `1` modulo `p^k`. -/
theorem toZModPow_cyc_eq_one (k : ℕ) (ζ : PadicAlgCl p) (hζ : IsPrimitiveRoot ζ (p ^ k)) (σ : PkgI4.GQp p)
    (hσ : σ ζ = ζ) : PadicInt.toZModPow k ((PkgI4.cyc p σ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
  have hs := cyclotomicCharacter.spec (L := PadicAlgCl p) p σ.toRingEquiv ζ hζ.pow_eq_one
  have hs' : ζ ^ (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).toZModPow k).val
      = ζ ^ 1 := by
    rw [pow_one, ← hs]; exact hσ
  change PadicInt.toZModPow k ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) = 1
  set c := PadicInt.toZModPow k ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p])
  rcases k with _ | k
  · have : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  · have hp1 : 1 < p ^ (k + 1) := Nat.one_lt_pow (Nat.succ_ne_zero k) (Fact.out : p.Prime).one_lt
    haveI : NeZero (p ^ (k + 1)) := ⟨by positivity⟩
    have hv : c.val = 1 := hζ.pow_inj (ZMod.val_lt c) hp1 hs'
    apply ZMod.val_injective
    rw [hv, ZMod.val_one'' (by omega)]

end Units

/-- **LEAF candidate (Tate 1967, §3.3, Theorem 2, for the complete discretely valued field `\hat{K^{ur}}`; locator
UNVERIFIED).** J. Tate, *p-divisible groups*, Proc. Conf. Local Fields (Driebergen 1966), Springer 1967, §3.3,
Theorem 2: for a complete discretely valued field `L` of characteristic `0` with perfect residue field of
characteristic `p` and `i ≠ 0`, `H⁰(G_L, ℂ(i)) = 0`. Specialization: `L` the completion of the maximal unramified
extension of a finite `K/ℚ_p` inside `ℚ̄_p`; then `G_L` is the inertia group `I_K = G_K ∩ I_{ℚ_p}` acting on
`ℂ = ℂ_p` (a dictionary step, STANDARD: Krasner's lemma and the continuity of the action identify `Gal(\bar L/L)`
with `I_K` and the completion of `\bar L` with `ℂ_p`). The same theorem, specialized to `L = K` finite, is the tree's
`ZInQ.Contrib.HodgeSplit.TateTwistInvariants` (proved, `CloudB3W11.tateTwistInvariants_proof`). Inertia is Tau Ceti's
`TauCeti.inertiaSubgroup ℚ_[p]` (the fixing group of the maximal unramified extension). -/
def TateTwistInvariantsInertia : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (i : ℤ), i ≠ 0 → ∀ x : ℂ_[p],
      (∀ σ ∈ K.fixingSubgroup, (show Field.absoluteGaloisGroup ℚ_[p] from σ) ∈ TauCeti.inertiaSubgroup ℚ_[p] →
        PkgI4.cycPow p σ i • PkgI4.cpAct p σ x = x) → x = 0

/-- **`LocAlgExponentEqWeight` proved** from Tate's theorem over `\hat{K^{ur}}` and Tau Ceti's local class field
theory (the manuscript's "removing its integral local Hodge–Tate weight", diophantine_zq.tex L763-764). -/
theorem locAlgExponentEqWeight_of_tateInertia (hT : TateTwistInvariantsInertia) : LocAlgExponentEqWeight := by
  intro p _ E _ ψ w n _hcont hHT hLA
  by_contra hne
  obtain ⟨k, hk⟩ := hLA
  have h1 : PkgI4.htMult p (charRep ψ) w = 1 := by rw [hHT w]; simp
  have hne_bot : PkgI4.htSpace p (charRep ψ) (-w) ≠ ⊥ := by
    intro h
    rw [PkgI4.htMult, h, finrank_bot, Nat.zero_div] at h1
    exact zero_ne_one h1
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ0 (LinearMap.ext h)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (PadicAlgCl p) (p ^ k)
  let K : IntermediateField ℚ_[p] (PadicAlgCl p) := IntermediateField.adjoin ℚ_[p] {ζ}
  haveI : FiniteDimensional ℚ_[p] K :=
    IntermediateField.adjoin.finiteDimensional (hζ.isIntegral (pow_pos (Fact.out : p.Prime).pos k)).tower_top
  refine hv (hT p K (n - w) (sub_ne_zero.2 hne) (φ v) fun σ hσK hσI => ?_)
  obtain ⟨u, hu⟩ := exists_unit_isArtinLift p σ hσI
  have hcyc : PkgI4.cyc p σ = u⁻¹ := cyc_of_isArtinLift p σ u hu
  have hfix : σ ζ = ζ :=
    (IntermediateField.mem_fixingSubgroup_iff K σ).1 hσK ζ (IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ)
  have hk1 : PadicInt.toZModPow k (u : ℤ_[p]) = 1 := by
    have h2 := toZModPow_cyc_eq_one p k ζ hζ σ hfix
    rw [hcyc] at h2
    have h3 : PadicInt.toZModPow k ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * PadicInt.toZModPow k (u : ℤ_[p]) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rwa [h2, one_mul] at h3
  have hψ := hk u hk1 σ hu
  have hφσ := hφ σ v
  set a : ℚ_[p] := ((u : ℤ_[p]) : ℚ_[p]) with ha_def
  have ha : a ≠ 0 := by
    intro h0
    have : ((u : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
      rw [Ne, PadicInt.coe_eq_zero]; exact u.ne_zero
    exact this h0
  have hcp : ∀ i : ℤ, PkgI4.cycPow p σ i = a ^ (-i) := by
    intro i
    rw [PkgI4.cycPow, hcyc]
    change ((Units.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).toMonoidHom (u⁻¹ ^ i) : ℚ_[p]ˣ) : ℚ_[p]) = _
    rw [map_zpow, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, inv_zpow']
    rfl
  have hmv : Matrix.mulVec ((charRep ψ σ : GL (Fin 1) E) : Matrix (Fin 1) (Fin 1) E) v = (a ^ n) • v := by
    ext j
    simp [charRep, hψ, Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal, Algebra.smul_def, ha_def]
  rw [hmv, map_smul, hcp] at hφσ
  rw [hcp]
  calc a ^ (-(n - w)) • PkgI4.cpAct p σ (φ v) = a ^ (-n) • (a ^ (- -w) • PkgI4.cpAct p σ (φ v)) := by
        rw [smul_smul, ← zpow_add₀ ha]; ring_nf
    _ = a ^ (-n) • (a ^ n • φ v) := by rw [← hφσ]
    _ = φ v := by rw [smul_smul, ← zpow_add₀ ha]; simp

end HDec.G0Galois.C8Conrad

#print axioms HDec.G0Galois.C8Conrad.locAlgExponentEqWeight_of_tateInertia
