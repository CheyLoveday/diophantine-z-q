import ZInQKernel.Contrib.CloudB3RC53.Mattuck.IndexLemma
import ZInQKernel.Contrib.CloudB3RC53.Mattuck.FiniteIndex
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.ResidualCountsKummer
import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.Derivative
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.LocalConditions
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Mattuck, odd residue characteristic, part 4: `dim E(K_w)/2 = dim E(K_w)[2] = 2`, and the old
Kummer row at odd places

Manuscript `diophantine_zq.tex`, tex 4551–4556 (the old Kummer condition has residual dimensions
`(2, 2 + d_w)`: "`E^{(h)}(K_w)^∧_2 ≅ ℤ₂^{d_w} ⊕` (finite `2`-primary torsion with two
generators)", `E^{(h)}[2]` rational), and the table of tex 4561–4573. At a place `w ∤ 2`, `d_w = 0`.

Let `C` be a Weierstrass curve over `𝒪_u`, elliptic over `K_u`, with `𝒪_u` compact and `2 ∉ u`
(odd residue characteristic). Then (any reduction type):

* `card_modN_two_eq_card_twoTorsion`: `|E(K_u)/2E(K_u)| = |E(K_u)[2]|` — the kernel of reduction
  `E₁` has finite index (`finiteIndex_kerReduction`) and is uniquely `2`-divisible (Tau Ceti's
  `nsmul_kerReduction_bijective`, `2` a unit of `𝒪_u`), so the index lemma applies;
* **`finrank_odd`** (node `MattuckOdd`): with full rational `2`-torsion (`|E(K_u)[2]| = 4`),
  `dim_{𝔽₂} E(K_u)[2] = 2` and `dim_{𝔽₂} E(K_u)/2 = 2`;
* `kummerResidualDim C = dim E[2] + dim E/2` (the residual dimensions `h⁰ + h¹` of the derived
  Kummer condition: `H⁰ = E(K_u)[2]`, `H¹ = E(K_u)/2`), and `kummerResidualDim_odd`: it is
  `LocalCondition.dim .oldKummer 0 = 4`, the table's value at odd places;
* the link to RC6's input `hkum` (`hkum_of_mattuck`, `hcond_of_mattuck`) and to the genuine table
  `genCondDim2` (`genCondDim2_oldKummer_odd`): for local integral models `E_w` of the old curve
  with full rational `2`-torsion at the odd old-Kummer places, the Kummer dimension
  `kummerDimOfCurves` (Mattuck at odd places, the `p = 2` value `kd2` an input) satisfies `hkum`.

The Kummer map `E(K_w)/2 → H¹(K_w, E[2])` itself (so the condition as a subcomplex of the genuine
local complex, via `localConditionsOfCC`) is not available: it needs the Galois module
`E(K̄_w)`. The dimension count above is what the table consumes.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Mattuck

open IsDedekindDomain WeierstrassCurve

/-! ### Finite `𝔽₂`-dimension from cardinality -/

theorem finrank_eq_two_of_card {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (h : Nat.card V = 4) : Module.finrank (ZMod 2) V = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  have hH := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
  rw [h, Nat.card_zmod] at hH
  exact Nat.pow_right_injective le_rfl (hH.symm.trans (by norm_num : (4 : ℕ) = 2 ^ 2))

/-- `G[2]` as an `𝔽₂`-vector space. -/
abbrev twoTorsionModule (G : Type*) [AddCommGroup G] :
    Module (ZMod 2) (Submodule.torsionBy ℤ G 2) :=
  AddCommGroup.zmodModule (n := 2) fun x => Subtype.ext (by
    have := (Submodule.mem_torsionBy_iff _ _).mp x.2
    rw [two_zsmul] at this
    simpa [two_nsmul] using this)

/-- `dim_{𝔽₂} G[2]`. -/
def finrankTwoTorsion (G : Type*) [AddCommGroup G] : ℕ :=
  @Module.finrank (ZMod 2) (Submodule.torsionBy ℤ G 2) _ _ (twoTorsionModule G)

theorem finrankTwoTorsion_eq_two {G : Type*} [AddCommGroup G]
    (h : Nat.card (Submodule.torsionBy ℤ G 2) = 4) : finrankTwoTorsion G = 2 :=
  @finrank_eq_two_of_card _ _ (twoTorsionModule G) h

/-! ### The local statement -/

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F] (u : HeightOneSpectrum A)
  (C : WeierstrassCurve (u.adicCompletionIntegers F))
  [(C.baseChange (u.adicCompletion F)).IsElliptic]

open scoped Classical in
/-- **`|E(K_u)/2| = |E(K_u)[2]|` in odd residue characteristic** (any reduction type). PROVED. -/
theorem card_modN_two_eq_card_twoTorsion [CompactSpace (u.adicCompletionIntegers F)]
    (h2 : (2 : A) ∉ u.asIdeal) :
    Nat.card (ModN (C.baseChange (u.adicCompletion F)).toAffine.Point 2) =
      Nat.card (Submodule.torsionBy ℤ (C.baseChange (u.adicCompletion F)).toAffine.Point 2) := by
  have := finiteIndex_kerReduction u C
  exact card_modN_two_eq_card_torsionBy (B := C.kerReduction u)
    (C.nsmul_kerReduction_bijective u (n := 2) (by exact_mod_cast h2))

open scoped Classical in
/-- **Mattuck at an odd place, with full rational `2`-torsion**: `dim E(K_u)[2] = 2` and
`dim E(K_u)/2 = 2`. PROVED. -/
theorem finrank_odd [CompactSpace (u.adicCompletionIntegers F)] (h2 : (2 : A) ∉ u.asIdeal)
    (h4 : Nat.card (Submodule.torsionBy ℤ (C.baseChange (u.adicCompletion F)).toAffine.Point 2) =
      4) :
    finrankTwoTorsion (C.baseChange (u.adicCompletion F)).toAffine.Point = 2 ∧
      Module.finrank (ZMod 2) (ModN (C.baseChange (u.adicCompletion F)).toAffine.Point 2) = 2 :=
  ⟨finrankTwoTorsion_eq_two h4,
    finrank_eq_two_of_card ((card_modN_two_eq_card_twoTorsion u C h2).trans h4)⟩

open scoped Classical in
/-- **The residual dimension of the derived Kummer condition** at `u` (tex 4551–4556):
`h⁰ + h¹ = dim E(K_u)[2] + dim E(K_u)/2`. -/
def kummerResidualDim : ℕ :=
  finrankTwoTorsion (C.baseChange (u.adicCompletion F)).toAffine.Point +
    Module.finrank (ZMod 2) (ModN (C.baseChange (u.adicCompletion F)).toAffine.Point 2)

open scoped Classical in
/-- **The old Kummer row of the table at an odd place** (tex 4551–4556, 4561–4573): with full
rational `2`-torsion, `kummerResidualDim = LocalCondition.dim .oldKummer 0 = 4`. PROVED. -/
theorem kummerResidualDim_odd [CompactSpace (u.adicCompletionIntegers F)]
    (h2 : (2 : A) ∉ u.asIdeal)
    (h4 : Nat.card (Submodule.torsionBy ℤ (C.baseChange (u.adicCompletion F)).toAffine.Point 2) =
      4) :
    kummerResidualDim u C =
      ZInQ.Manuscript.RC.Limits.LocalCondition.dim .oldKummer 0 := by
  obtain ⟨h1, h2'⟩ := finrank_odd u C h2 h4
  rw [kummerResidualDim, h1, h2']
  rfl

open scoped Classical in
/-- **Mattuck's theorem in odd residue characteristic, full rational `2`-torsion** (tex
4551–4556). For a Dedekind domain `A` with fraction field `F`, a height-one prime `u ∌ 2` with
compact completed integers `𝒪_u`, and a Weierstrass curve over `𝒪_u` elliptic over `K_u` (any
reduction type) with `|E(K_u)[2]| = 4`: `dim_{𝔽₂} E(K_u)[2] = 2 = dim_{𝔽₂} E(K_u)/2E(K_u)`.
Kind: PROVED. -/
def MattuckOdd : Prop :=
  ∀ (A : Type) [CommRing A] [IsDedekindDomain A] (F : Type) [Field F] [Algebra A F]
    [IsFractionRing A F] (u : HeightOneSpectrum A)
    (C : WeierstrassCurve (u.adicCompletionIntegers F))
    [(C.baseChange (u.adicCompletion F)).IsElliptic] [CompactSpace (u.adicCompletionIntegers F)],
    (2 : A) ∉ u.asIdeal →
    Nat.card (Submodule.torsionBy ℤ (C.baseChange (u.adicCompletion F)).toAffine.Point 2) = 4 →
      finrankTwoTorsion (C.baseChange (u.adicCompletion F)).toAffine.Point = 2 ∧
        Module.finrank (ZMod 2) (ModN (C.baseChange (u.adicCompletion F)).toAffine.Point 2) = 2

theorem mattuckOdd_proof : MattuckOdd := fun _ _ _ _ _ _ _ u C _ _ h2 h4 => finrank_odd u C h2 h4

/-! ### The link to the old Kummer row of RC6's table -/

section Link

open NumberField ZInQ.Contrib.CloudB3RC53.RankCounts ZInQ.Manuscript.RC.Limits

variable (K : Type) [Field K] [NumberField K]
  (Ew : ∀ w : HeightOneSpectrum (𝓞 K), WeierstrassCurve (w.adicCompletionIntegers K))
  [hEw : ∀ w, ((Ew w).baseChange (w.adicCompletion K)).IsElliptic]

/-- The completed integers at a finite place of a number field are compact. -/
theorem compactSpace_place (w : HeightOneSpectrum (𝓞 K)) :
    CompactSpace (w.adicCompletionIntegers K) :=
  inferInstance

open Classical in
/-- **The old Kummer dimension from local integral models `E_w`** of the old curve: Mattuck's
residual dimension `kummerResidualDim` at places `w ∤ 2`, the value `kd2` (input) at places above
`2` (junk `0` off primes). -/
def kummerDimOfCurves (kd2 : Ideal (𝓞 K) → ℕ) (P : Ideal (𝓞 K)) : ℕ :=
  if h : P.IsPrime ∧ P ≠ ⊥ then
    (if ((2 : ℤ) : 𝓞 K) ∈ P then kd2 P else kummerResidualDim ⟨P, h.1, h.2⟩ (Ew ⟨P, h.1, h.2⟩))
  else 0

omit [NumberField K] in
theorem two_mem_iff_of_mem_primesAbove {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)}
    (hP : P ∈ primesAbove K p) (hne : P ≠ ⊥) : ((2 : ℤ) : 𝓞 K) ∈ P ↔ p = 2 := by
  have hpP : ((p : ℤ) : 𝓞 K) ∈ P := (natCast_mem_asIdeal_iff K hp ⟨P, hP.1, hne⟩).mpr hP
  constructor
  · intro h2
    exact Genus.prime_eq_of_mem hP.1.ne_top hp Nat.prime_two hpP (by exact_mod_cast h2)
  · rintro rfl
    exact_mod_cast hpP

open scoped Classical in
/-- **RC6's `hkum` at every place, odd places by Mattuck** (tex 4551–4556): if the local models
`E_w` have full rational `2`-torsion at the odd old-Kummer places and `kd2` has the table value
`4 + d_w` at the old-Kummer places above `2` (the `p = 2` piece, an input), then
`kummerDimOfCurves` satisfies the hypothesis `hkum` of `hcond_genuine`. PROVED. -/
theorem hkum_of_mattuck (cond : Ideal (𝓞 K) → LocalCondition) (kd2 : Ideal (𝓞 K) → ℕ)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      ((2 : ℤ) : 𝓞 K) ∉ w.asIdeal →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (h2 : ∀ (P : Ideal (𝓞 K)) (hP : P ∈ primesAbove K 2), cond P = .oldKummer →
      kd2 P = 4 + (placeEntry K ⟨2, Nat.prime_two⟩ P hP (cond P) 0).deg) :
    ∀ (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 K)) (hP : P ∈ primesAbove K p),
      cond P = .oldKummer →
        kummerDimOfCurves K Ew kd2 P = 4 + (placeEntry K ⟨p, hp⟩ P hP (cond P) 0).deg := by
  classical
  intro p hp P hP hc
  have hne : P ≠ ⊥ := ne_bot_of_mem_primesAbove K hp.ne_zero hP
  have hPP : P.IsPrime ∧ P ≠ ⊥ := ⟨hP.1, hne⟩
  unfold kummerDimOfCurves
  rw [dite_eq_left hPP]
  by_cases h2P : ((2 : ℤ) : 𝓞 K) ∈ P
  · rw [ite_eq_left h2P]
    obtain rfl := (two_mem_iff_of_mem_primesAbove K hp hP hne).mp h2P
    exact h2 P hP hc
  · rw [ite_eq_right h2P]
    have hp2 : p ≠ 2 := fun h => h2P ((two_mem_iff_of_mem_primesAbove K hp hP hne).mpr h)
    have hdeg : (placeEntry K ⟨p, hp⟩ P hP (cond P) 0).deg = 0 := by
      simp [placeEntry, hp2]
    rw [hdeg, add_zero]
    have h2A : (2 : 𝓞 K) ∉ (⟨P, hPP.1, hPP.2⟩ : HeightOneSpectrum (𝓞 K)).asIdeal := by
      exact_mod_cast h2P
    have := compactSpace_place K ⟨P, hPP.1, hPP.2⟩
    exact kummerResidualDim_odd _ _ h2A (hfull ⟨P, hPP.1, hPP.2⟩ hc (by exact_mod_cast h2P))

open scoped Classical in
/-- **RC6's `hcond` with the old Kummer dimension from Mattuck** (tex 4551–4573): the genuine
condition dimensions `condDimFun cond (kummerDimOfCurves …)` satisfy Elliot's table at every place
of every rational prime, given the PRINT leaves of `hcond_genuine`, that relaxed derivative
conditions occur only at odd primes, full rational `2`-torsion of the local models at the odd
old-Kummer places, and the `p = 2` piece `kd2`. PROVED. -/
theorem hcond_of_mattuck (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (cond : Ideal (𝓞 K) → LocalCondition) (kd2 : Ideal (𝓞 K) → ℕ)
    (hrel : ∀ (p : ℕ), p.Prime → ∀ P ∈ primesAbove K p, cond P = .derivRelaxed → p ≠ 2)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      ((2 : ℤ) : 𝓞 K) ∉ w.asIdeal →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (h2 : ∀ (P : Ideal (𝓞 K)) (hP : P ∈ primesAbove K 2), cond P = .oldKummer →
      kd2 P = 4 + (placeEntry K ⟨2, Nat.prime_two⟩ P hP (cond P) 0).deg) :
    ∀ p : ℕ, ∀ w ∈ placesList K cond (condDimFun K cond (kummerDimOfCurves K Ew kd2)) p,
      w.condDim = w.cond.dim w.deg :=
  hcond_genuine K h28 h23 cond (kummerDimOfCurves K Ew kd2) hrel
    (hkum_of_mattuck K Ew cond kd2 hfull h2)

open scoped Classical in
/-- **The genuine table's old Kummer row at an odd place is Mattuck's**: with the old Kummer
dimension `kummerResidualDim` of a local model with full rational `2`-torsion, `genCondDim2` (all
rows from genuine objects) gives the table value `4`. PROVED. -/
theorem genCondDim2_oldKummer_odd (S : Set (HeightOneSpectrum (𝓞 K)))
    (w : HeightOneSpectrum (𝓞 K)) (h2 : (2 : 𝓞 K) ∉ w.asIdeal)
    (h4 : Nat.card
      (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) = 4) :
    GenuineInst.genCondDim2 K S w .oldKummer (kummerResidualDim w (Ew w)) =
      LocalCondition.dim .oldKummer 0 :=
  kummerResidualDim_odd w (Ew w) h2 h4

end Link

end ZInQ.Contrib.CloudB3RC53.Mattuck
