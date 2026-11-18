import ZInQKernel.Contrib.CloudB3RC53.Mattuck.Counting
import ZInQKernel.Contrib.CloudB3RC53.Mattuck.FiniteIndex
import ZInQKernel.Contrib.CloudB3RC53.Mattuck.Odd

/-!
# Mattuck at `p = 2`, part 5: `dim E(K_w)/2 = 2 + [K_w : ℚ₂]`, and the old Kummer row at every place

Manuscript `diophantine_zq.tex`, tex 4551–4556 (`E^{(h)}(K_w)^∧_2 ≅ ℤ₂^{d_w} ⊕` (finite `2`-primary
torsion with two generators); residual dimensions `(2, 2 + d_w)`), tex 4561–4573 (the table).

Let `w | 2` be a place of a number field `K`, `𝒪_w` the completed integers with maximal ideal `𝔪`,
`e = e(w|2)`, and `C` a Weierstrass curve over `𝒪_w`, elliptic over `K_w` (any reduction type).

* The lattice `latticeU C = Ê(𝔪^{e+1}) ⊆ E₁(K_w) ⊆ E(K_w)` (the image of the level `lev (e+1)`
  of the formal group under Tau Ceti's `formalPointAddEquivKerReduction`):
  - `finiteIndex_latticeU`: finite index in `E(K_w)` (`[E : E₁]` finite, `finiteIndex_kerReduction`;
    `[Ê(𝔪) : Ê(𝔪^{e+1})]` finite, `finiteIndex_lev`);
  - `latticeU_noTwoTorsion`: no `2`-torsion (`𝔪^{e+1} = 2𝔪`, `Doubling.lean`);
  - **`card_modN_latticeU`**: `|U/2U| = [𝔪^{e+1} : 𝔪^{2e+1}] = 2^{[K_w : ℚ₂]}`.
* **`finrank_two`** (node `MattuckTwo`): with full rational `2`-torsion,
  `dim_{𝔽₂} E(K_w)/2 = 2 + [K_w : ℚ₂]`, and `kummerResidualDim_two`: the residual dimension of the
  derived Kummer condition is `4 + [K_w : ℚ₂] = LocalCondition.dim .oldKummer d_w`.
* **`hkum_of_mattuck_all`**, **`hcond_of_mattuck_all`**: RC6's `hkum` / `hcond` with the old Kummer
  dimension `kummerDimOfCurves … (kd2 := Mattuck at 2)` proved at **every** place (odd places:
  `Odd.lean`; places above `2`: here), given full rational `2`-torsion of the local models at the
  old-Kummer places. No old-Kummer input remains.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Mattuck

open IsDedekindDomain WeierstrassCurve NumberField ZInQ.Contrib.CloudB3RC53.RankCounts

/-- `ModN` is invariant under additive isomorphisms. -/
theorem natCard_modN_two_congr {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (e : G ≃+ G') :
    Nat.card (ModN G 2) = Nat.card (ModN G' 2) := by
  refine Nat.card_congr (Submodule.Quotient.equiv _ _ e.toIntLinearEquiv ?_).toEquiv
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.lsmul_apply]
  constructor
  · rintro ⟨x, ⟨g, rfl⟩, rfl⟩
    exact ⟨e g, by simp⟩
  · rintro ⟨g', rfl⟩
    exact ⟨_, ⟨e.symm g', rfl⟩, by simp⟩

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  (C : WeierstrassCurve (w.adicCompletionIntegers K))
  [(C.baseChange (w.adicCompletion K)).IsElliptic]

theorem isLinearTopology_O :
    IsLinearTopology (w.adicCompletionIntegers K) (w.adicCompletionIntegers K) :=
  w.isAdic_maximalIdeal_adicCompletionIntegers (K := K) ▸
    Ideal.isLinearTopology (IsLocalRing.maximalIdeal (w.adicCompletionIntegers K))

theorem fact_isAdic_O : Fact (IsAdic (IsLocalRing.maximalIdeal (w.adicCompletionIntegers K))) :=
  ⟨w.isAdic_maximalIdeal_adicCompletionIntegers (K := K)⟩

attribute [local instance] isLinearTopology_O fact_isAdic_O

open scoped Classical in
/-- The formal group as a subgroup of `E(K_w)`: `Ê(𝔪) ≃ E₁ ⊆ E(K_w)`. -/
def formalToE : FormalGroupPoint C (IsLocalRing.maximalIdeal (w.adicCompletionIntegers K)) →+
    (C.baseChange (w.adicCompletion K)).toAffine.Point :=
  (C.kerReduction w).subtype.comp (C.formalPointAddEquivKerReduction w).toAddMonoidHom

open scoped Classical in
theorem formalToE_injective : Function.Injective (formalToE K w C) :=
  Subtype.val_injective.comp (C.formalPointAddEquivKerReduction w).injective

open scoped Classical in
theorem formalToE_range : (formalToE K w C).range = C.kerReduction w := by
  ext P
  constructor
  · rintro ⟨Q, rfl⟩
    exact ((C.formalPointAddEquivKerReduction w) Q).2
  · intro hP
    obtain ⟨Q, hQ⟩ := (C.formalPointAddEquivKerReduction w).surjective ⟨P, hP⟩
    exact ⟨Q, congrArg Subtype.val hQ⟩

open scoped Classical in
/-- **The lattice `U = Ê(𝔪^{e+1}) ⊆ E(K_w)`**, `e = e(w|2)`. -/
def latticeU [w.asIdeal.LiesOver (vP two).asIdeal] :
    AddSubgroup (C.baseChange (w.adicCompletion K)).toAffine.Point :=
  (lev C (IsLocalRing.maximalIdeal (w.adicCompletionIntegers K))
    (w.asIdeal.ramificationIdx ℤ + 1)).map (formalToE K w C)

variable [w.asIdeal.LiesOver (vP two).asIdeal]

theorem two_ne_zero_O : (2 : w.adicCompletionIntegers K) ≠ 0 := by
  intro h
  have := valued_two_eq K w
  rw [h, ZeroMemClass.coe_zero, map_zero] at this
  exact WithZero.exp_ne_zero this.symm

open scoped Classical in
/-- **`U` has finite index in `E(K_w)`.** PROVED. -/
theorem finiteIndex_latticeU : (latticeU K w C).FiniteIndex := by
  have := compactSpace_place K w
  have h1 := finiteIndex_kerReduction w C
  have h2 := finiteIndex_lev (W := C) (I := IsLocalRing.maximalIdeal (w.adicCompletionIntegers K))
    (fun k _ => by
      rw [relIndex_maximalIdeal_pow_succ, natCard_residue_eq]
      positivity) (w.asIdeal.ramificationIdx ℤ + 1)
  constructor
  rw [latticeU, AddSubgroup.index_map_of_injective _ (formalToE_injective K w C),
    formalToE_range]
  exact mul_ne_zero h2.index_ne_zero h1.index_ne_zero

open scoped Classical in
/-- **`U` has no `2`-torsion.** PROVED. -/
theorem latticeU_noTwoTorsion : ∀ P ∈ latticeU K w C, 2 • P = 0 → P = 0 := by
  rintro _ ⟨Q, hQ, rfl⟩ h
  have hQ0 : 2 • Q = 0 := formalToE_injective K w C (by rw [map_nsmul, h, map_zero])
  rw [lev_noTwoTorsion (two_ne_zero_O K w) (mem_pow_succ_iff (valued_two_eq K w)) Q hQ hQ0,
    map_zero]

open scoped Classical in
/-- **`|U/2U| = 2^{[K_w : ℚ₂]}`.** PROVED. -/
theorem card_modN_latticeU :
    letI := qpAlg K two w
    Nat.card (ModN (latticeU K w C) 2) = 2 ^ Module.finrank ℚ_[2] (w.adicCompletion K) := by
  rw [latticeU, ← natCard_modN_two_congr (AddSubgroup.equivMapOfInjective _ _
    (formalToE_injective K w C)), card_modN_lev (mem_pow_succ_iff (valued_two_eq K w))
    (mem_pow_two_mul_succ_iff (valued_two_eq K w)), relIndex_two_level]

open scoped Classical in
/-- **Mattuck at a place above `2`, full rational `2`-torsion**: `dim E(K_w)[2] = 2` and
`dim E(K_w)/2 = 2 + [K_w : ℚ₂]`. PROVED. -/
theorem finrank_two
    (h4 : Nat.card (Submodule.torsionBy ℤ (C.baseChange (w.adicCompletion K)).toAffine.Point 2) =
      4) :
    letI := qpAlg K two w
    finrankTwoTorsion (C.baseChange (w.adicCompletion K)).toAffine.Point = 2 ∧
      Module.finrank (ZMod 2) (ModN (C.baseChange (w.adicCompletion K)).toAffine.Point 2) =
        2 + Module.finrank ℚ_[2] (w.adicCompletion K) := by
  have := finiteIndex_latticeU K w C
  exact ⟨finrankTwoTorsion_eq_two h4, finrank_modN_two_of_lattice (latticeU K w C)
    (latticeU_noTwoTorsion K w C) (card_modN_latticeU K w C) h4⟩

open scoped Classical in
/-- **The old Kummer row of the table at a place above `2`**: with full rational `2`-torsion,
`kummerResidualDim = 4 + [K_w : ℚ₂] = LocalCondition.dim .oldKummer [K_w : ℚ₂]`. PROVED. -/
theorem kummerResidualDim_two
    (h4 : Nat.card (Submodule.torsionBy ℤ (C.baseChange (w.adicCompletion K)).toAffine.Point 2) =
      4) :
    letI := qpAlg K two w
    kummerResidualDim w C = ZInQ.Manuscript.RC.Limits.LocalCondition.dim .oldKummer
      (Module.finrank ℚ_[2] (w.adicCompletion K)) := by
  have := finiteIndex_latticeU K w C
  exact kummerResidualDim_of_lattice w C (latticeU K w C) (latticeU_noTwoTorsion K w C)
    (card_modN_latticeU K w C) h4

open scoped Classical in
/-- **Mattuck's theorem at places above `2`, full rational `2`-torsion** (tex 4551–4556): for a
number field `K`, a place `w | 2`, and a Weierstrass curve over `𝒪_w` elliptic over `K_w` (any
reduction type) with `|E(K_w)[2]| = 4`: `dim_{𝔽₂} E(K_w)[2] = 2` and
`dim_{𝔽₂} E(K_w)/2E(K_w) = 2 + [K_w : ℚ₂]`. Kind: PROVED. -/
def MattuckTwo : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver (vP two).asIdeal] (C : WeierstrassCurve (w.adicCompletionIntegers K))
    [(C.baseChange (w.adicCompletion K)).IsElliptic],
    Nat.card (Submodule.torsionBy ℤ (C.baseChange (w.adicCompletion K)).toAffine.Point 2) = 4 →
      letI := qpAlg K two w
      finrankTwoTorsion (C.baseChange (w.adicCompletion K)).toAffine.Point = 2 ∧
        Module.finrank (ZMod 2) (ModN (C.baseChange (w.adicCompletion K)).toAffine.Point 2) =
          2 + Module.finrank ℚ_[2] (w.adicCompletion K)

theorem mattuckTwo_proof : MattuckTwo := fun K _ _ w _ C _ h4 => finrank_two K w C h4

/-! ### The old Kummer row at every place -/

section Link

open ZInQ.Manuscript.RC.Limits

variable (Ew : ∀ w : HeightOneSpectrum (𝓞 K), WeierstrassCurve (w.adicCompletionIntegers K))
  [hEw : ∀ w, ((Ew w).baseChange (w.adicCompletion K)).IsElliptic]

open Classical in
/-- Mattuck's residual dimension of the derived Kummer condition at every place (used at the
places above `2`; junk `0` off primes). -/
def kd2OfCurves (P : Ideal (𝓞 K)) : ℕ :=
  if h : P.IsPrime ∧ P ≠ ⊥ then kummerResidualDim ⟨P, h.1, h.2⟩ (Ew ⟨P, h.1, h.2⟩) else 0

omit [(C.baseChange (w.adicCompletion K)).IsElliptic] in
open scoped Classical in
/-- **The `p = 2` piece of `hkum`, by Mattuck at `2`.** PROVED. -/
theorem h2_of_mattuck (cond : Ideal (𝓞 K) → LocalCondition)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4) :
    ∀ (P : Ideal (𝓞 K)) (hP : P ∈ primesAbove K 2), cond P = .oldKummer →
      kd2OfCurves K Ew P = 4 + (placeEntry K ⟨2, Nat.prime_two⟩ P hP (cond P) 0).deg := by
  intro P hP hc
  have hPP : P.IsPrime ∧ P ≠ ⊥ := ⟨hP.1, ne_bot_of_mem_primesAbove K two_ne_zero hP⟩
  have := placeOf_liesOver K two P hP
  have hk := kummerResidualDim_two K (placeOf K two_ne_zero P hP) (Ew _)
    (hfull (placeOf K two_ne_zero P hP) hc)
  unfold kd2OfCurves
  rw [dite_eq_left hPP]
  refine hk.trans ?_
  simp [placeEntry, LocalCondition.dim]

omit [(C.baseChange (w.adicCompletion K)).IsElliptic] in
open scoped Classical in
/-- **RC6's `hkum` at every place, by Mattuck** (tex 4551–4556): if the local models `E_w` have full
rational `2`-torsion at the old-Kummer places, then `kummerDimOfCurves K Ew (kd2OfCurves K Ew)`
satisfies the hypothesis `hkum` of `hcond_genuine` at every place of every rational prime. No
old-Kummer input remains. PROVED. -/
theorem hkum_of_mattuck_all (cond : Ideal (𝓞 K) → LocalCondition)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4) :
    ∀ (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 K)) (hP : P ∈ primesAbove K p),
      cond P = .oldKummer →
        kummerDimOfCurves K Ew (kd2OfCurves K Ew) P =
          4 + (placeEntry K ⟨p, hp⟩ P hP (cond P) 0).deg :=
  hkum_of_mattuck K Ew cond (kd2OfCurves K Ew) (fun w hc _ => hfull w hc)
    (h2_of_mattuck K Ew cond hfull)

omit [(C.baseChange (w.adicCompletion K)).IsElliptic] in
open scoped Classical in
/-- **RC6's `hcond` with the old Kummer dimension from Mattuck at every place** (tex 4551–4573):
given the PRINT leaves of `hcond_genuine`, relaxed derivative conditions only at odd primes, and
full rational `2`-torsion of the local models at the old-Kummer places. PROVED. -/
theorem hcond_of_mattuck_all (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hrel : ∀ (p : ℕ), p.Prime → ∀ P ∈ primesAbove K p, cond P = .derivRelaxed → p ≠ 2)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4) :
    ∀ p : ℕ, ∀ v ∈ placesList K cond
        (condDimFun K cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p,
      v.condDim = v.cond.dim v.deg :=
  hcond_genuine K h28 h23 cond _ hrel (hkum_of_mattuck_all K Ew cond hfull)

end Link

end ZInQ.Contrib.CloudB3RC53.Mattuck
