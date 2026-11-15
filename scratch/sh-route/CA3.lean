import ShRG
import Top
import CA1
import CA2

/-!
# sh-route, part E: strict henselizations nest along finite extensions (`SHPair0`)

For `K'/K` finite and one valuation ring `w` of `Ω = K̄'` over `O' ⊆ K'`: the inertia field of `w`
over `K` lies in the inertia field over `K'`, and the latter lies in `E(K')` for `E` the former, so
it is finite over it.
-/

open IsLocalRing Polynomial

set_option linter.style.haveILetI false

namespace ShRoute

open ReductSplit ReductGlue

section Pair

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)

/-- The elements of `Gal(M/K)` acting trivially modulo `𝔪_w` on `w ∩ M`, as a submonoid. -/
def inertSub (M : IntermediateField K Ω) : Submonoid (M ≃ₐ[K] M) where
  carrier := {σ | ∀ y : M, (y : Ω) ∈ w → ((σ y : M) : Ω) - y ∈ w.nonunits}
  one_mem' := by
    intro y _
    simp only [AlgEquiv.one_apply, sub_self]
    exact zero_mem _
  mul_mem' := by
    intro σ ρ hσ hρ y hy
    have h1 := hρ y hy
    have hρy : ((ρ y : M) : Ω) ∈ w := by
      have : ((ρ y : M) : Ω) = (y : Ω) + (((ρ y : M) : Ω) - y) := by ring
      rw [this]; exact add_mem hy (ValuationSubring.nonunits_le h1)
    have h2 := hσ (ρ y) hρy
    have : (((σ * ρ) y : M) : Ω) - y = (((σ (ρ y)) : M) : Ω) - (ρ y : M) +
        (((ρ y : M) : Ω) - y) := by
      rw [AlgEquiv.mul_apply]; ring
    rw [this]
    exact add_mem h2 h1

/-- The inertia subgroup of `Gal(M/K)` (a submonoid of a finite group is a subgroup). -/
def inertM (M : IntermediateField K Ω) [FiniteDimensional K M] : Subgroup (M ≃ₐ[K] M) :=
  { inertSub w M with
    inv_mem' := by
      intro σ hσ
      have hn := orderOf_pos σ
      have h : σ⁻¹ = σ ^ (orderOf σ - 1) := by
        symm
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ, Nat.sub_add_cancel hn, pow_orderOf_eq_one]
      change σ⁻¹ ∈ inertSub w M
      rw [h]
      exact (inertSub w M).pow_mem hσ _ }

theorem mem_inertM {M : IntermediateField K Ω} [FiniteDimensional K M] {σ : M ≃ₐ[K] M} :
    σ ∈ inertM w M ↔ ∀ y : M, (y : Ω) ∈ w → ((σ y : M) : Ω) - y ∈ w.nonunits := Iff.rfl

variable [CharZero K] [IsAlgClosure K Ω]
variable {K' : Type} [Field K'] [Algebra K K'] [FiniteDimensional K K'] [Algebra K' Ω]
  [IsScalarTower K K' Ω] [CharZero K'] [IsAlgClosure K' Ω]

/-- The inertia field over `K` lies in the inertia field over `K'`. -/
theorem inertiaField_le {x : Ω} (hx : x ∈ inertiaField (K := K) w) :
    x ∈ inertiaField (K := K') w := by
  obtain ⟨M, ⟨hfd, hgal⟩, hxM, hfix⟩ := hx
  haveI := hfd
  obtain ⟨t, ht⟩ : M.FG := IntermediateField.essFiniteType_iff.mp inferInstance
  haveI : FiniteDimensional K' (IntermediateField.adjoin K' (t : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun z _ => Algebra.IsIntegral.isIntegral z)
  obtain ⟨M', hM', hNM'⟩ := isFG_of (K := K') (IntermediateField.adjoin K' (t : Set Ω))
  have hMM' : ∀ y ∈ M, y ∈ M' := by
    intro y hy
    rw [← ht] at hy
    have hle : IntermediateField.adjoin K (t : Set Ω) ≤ M'.restrictScalars K :=
      IntermediateField.adjoin_le_iff.mpr
        (fun z hz => hNM' (IntermediateField.subset_adjoin K' _ hz))
    exact hle hy
  exact ⟨M', hM', hMM' x hxM, fun τ hτ =>
    hfix (τ.restrictScalars K) (fun y hy hyw => hτ y (hMM' y hy) hyw)⟩

/-- The inertia field over `K'` lies in `E(t')` for `E` the inertia field over `K` and `t'` a
finite set generating `K'` over `K`. -/
theorem inertiaField_le_adjoin (t' : Finset Ω)
    (ht' : IntermediateField.adjoin K (t' : Set Ω) = (IsScalarTower.toAlgHom K K' Ω).fieldRange)
    {x : Ω} (hx : x ∈ inertiaField (K := K') w) :
    x ∈ IntermediateField.adjoin (inertiaField (K := K) w) (t' : Set Ω) := by
  set E := inertiaField (K := K) w
  set L := IntermediateField.adjoin E (t' : Set Ω)
  obtain ⟨M', ⟨hfd', hgal'⟩, hxM', hfix'⟩ := hx
  haveI := hfd'
  haveI : FiniteDimensional K M' := FiniteDimensional.trans K K' M'
  haveI : FiniteDimensional K (M'.restrictScalars K) := inferInstanceAs (FiniteDimensional K M')
  obtain ⟨M, ⟨hfd, hgal⟩, hM'M⟩ := isFG_of (K := K) (M'.restrictScalars K)
  haveI := hfd
  haveI := hgal
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  have hK'M : ∀ c : K', algebraMap K' Ω c ∈ M := fun c => hM'M (M'.algebraMap_mem c)
  let K'Ω : IntermediateField K Ω := (IsScalarTower.toAlgHom K K' Ω).fieldRange
  let K'M : IntermediateField K M := K'Ω.comap M.val
  let I := inertM w M
  let F := IntermediateField.fixedField I
  let x' : M := ⟨x, hM'M hxM'⟩
  have hx' : x' ∈ IntermediateField.fixedField (IntermediateField.fixingSubgroup (F ⊔ K'M)) := by
    rw [IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_fixedField]
    rintro ⟨σ, hσI, hσK'⟩
    let τ : Ω ≃ₐ[K] Ω := σ.liftNormal Ω
    have hτ : ∀ m : M, τ (algebraMap M Ω m) = algebraMap M Ω (σ m) := fun m =>
      AlgEquiv.liftNormal_commutes σ Ω m
    have hτK' : ∀ c : K', τ (algebraMap K' Ω c) = algebraMap K' Ω c := by
      intro c
      have h1 := hτ ⟨_, hK'M c⟩
      have h2 : σ ⟨_, hK'M c⟩ = ⟨_, hK'M c⟩ :=
        (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσK' _ ⟨c, rfl⟩
      rw [h2] at h1
      exact h1
    let τ' : Ω ≃ₐ[K'] Ω := { τ.toRingEquiv with commutes' := hτK' }
    have hcond : CondM w M' τ' := by
      intro y hy hyw
      have h1 := hσI ⟨y, hM'M hy⟩ hyw
      have h2 := hτ ⟨y, hM'M hy⟩
      change τ y - y ∈ w.nonunits
      change τ (algebraMap M Ω ⟨y, hM'M hy⟩) - y ∈ w.nonunits
      rw [h2]
      exact h1
    have h3 : τ x = x := hfix' τ' hcond
    apply Subtype.ext
    change algebraMap M Ω (σ x') = algebraMap M Ω x'
    rw [← hτ]
    exact h3
  rw [IsGalois.fixedField_fixingSubgroup] at hx'
  have hle : F ⊔ K'M ≤ (L.restrictScalars K).comap M.val := by
    apply sup_le
    · intro f hf
      have hfE : (f : Ω) ∈ E := by
        refine ⟨M, ⟨hfd, hgal⟩, f.2, fun τ hτ => ?_⟩
        let σ : M ≃ₐ[K] M := τ.restrictNormal M
        have hσ : ∀ m : M, algebraMap M Ω (σ m) = τ (algebraMap M Ω m) := fun m =>
          AlgEquiv.restrictNormal_commutes τ M m
        have hσI : σ ∈ I := by
          intro y hyw
          change algebraMap M Ω (σ y) - y ∈ w.nonunits
          rw [hσ]
          exact hτ y y.2 hyw
        have := (IntermediateField.mem_fixedField_iff _ _).mp hf σ hσI
        change τ (algebraMap M Ω f) = algebraMap M Ω f
        rw [← hσ, this]
      exact L.algebraMap_mem ⟨_, hfE⟩
    · intro m hm
      have h1 : (m : Ω) ∈ IntermediateField.adjoin K (t' : Set Ω) := by rw [ht']; exact hm
      have h2 : IntermediateField.adjoin K (t' : Set Ω) ≤ L.restrictScalars K :=
        IntermediateField.adjoin_le_iff.mpr (fun z hz => IntermediateField.subset_adjoin E _ hz)
      exact h2 h1
  exact hle hx'

end Pair

end ShRoute
