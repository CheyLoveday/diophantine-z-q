import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.CommonSections

/-! The restricted products of the common local covers and the base
groups, tex 8884–8886 and 8996–9004. The assembly is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Metaplectic WeilIndex Filter
open scoped MatrixGroups Classical

variable (a b : Fin 3 → ℕ) [∀ i, NeZero (2 * a i)] [∀ i, NeZero (2 * b i)]

def sectionSubgroup (p : Place) : Subgroup (LocalCommon p a b) :=
  if h : Good a b p then (commonSection a b p h).range else ⊥

abbrev FiniteLocalCover :=
  RestrictedProduct (fun p => LocalCommon p a b) (fun p => (sectionSubgroup a b p : Set _)) cofinite

abbrev FiniteSL :=
  RestrictedProduct (fun p : Place => SL(2, ℚ_[p.val]))
    (fun p => ((includeIntegral p).range : Set _)) cofinite

theorem sectionSubgroup_projection (p : Place) (g : LocalCommon p a b)
    (hg : g ∈ sectionSubgroup a b p) :
    localProjection p a b g ∈ (includeIntegral p).range := by
  by_cases h : Good a b p
  · rw [sectionSubgroup, dite_eq_left h] at hg
    obtain ⟨k, rfl⟩ := hg
    exact ⟨k, rfl⟩
  · rw [sectionSubgroup, dite_eq_right h, Subgroup.mem_bot] at hg
    rw [hg, map_one]
    exact (includeIntegral p).range.one_mem

theorem sectionSubgroup_fixes (p : Place) (g : LocalCommon p a b)
    (hg : g ∈ sectionSubgroup a b p) :
    (localFirst p a b g : LocalEnd p) (spherical p) = spherical p ∧
    (localSecond p a b g : LocalEnd p) (spherical p) = spherical p := by
  by_cases h : Good a b p
  · rw [sectionSubgroup, dite_eq_left h] at hg
    obtain ⟨k, rfl⟩ := hg
    exact ⟨commonSection_first a b p h k, commonSection_second a b p h k⟩
  · rw [sectionSubgroup, dite_eq_right h, Subgroup.mem_bot] at hg
    rw [hg, map_one, map_one]
    exact ⟨rfl, rfl⟩

def finiteProjection : FiniteLocalCover a b →* FiniteSL where
  toFun g := ⟨fun p => localProjection p a b (g p),
    g.2.mono fun p => sectionSubgroup_projection a b p (g p)⟩
  map_one' := by apply RestrictedProduct.ext; intro p; exact map_one (localProjection p a b)
  map_mul' g h := by apply RestrictedProduct.ext; intro p; exact map_mul (localProjection p a b) (g p) (h p)

theorem finiteProjection_surjective : Function.Surjective (finiteProjection a b) := by
  intro k
  let g (p : Place) : LocalCommon p a b :=
    if h₁ : Good a b p then
      if h₂ : k p ∈ (includeIntegral p).range then commonSection a b p h₁ h₂.choose
      else (localProjection_surjective p a b (k p)).choose
    else (localProjection_surjective p a b (k p)).choose
  refine ⟨⟨g, ?_⟩, ?_⟩
  · filter_upwards [eventually_good a b, k.2] with p hp hk
    change g p ∈ sectionSubgroup a b p
    change k p ∈ (includeIntegral p).range at hk
    dsimp only [g]
    rw [dite_eq_left hp, dite_eq_left hk, sectionSubgroup, dite_eq_left hp]
    exact ⟨hk.choose, rfl⟩
  · apply RestrictedProduct.ext
    intro p
    change localProjection p a b (g p) = k p
    by_cases h₁ : Good a b p <;> by_cases h₂ : k p ∈ (includeIntegral p).range
    · dsimp only [g]
      rw [dite_eq_left h₁, dite_eq_left h₂]
      exact h₂.choose_spec
    · simpa only [g, dite_eq_left h₁, dite_eq_right h₂] using (localProjection_surjective p a b (k p)).choose_spec
    · simpa only [g, dite_eq_right h₁] using (localProjection_surjective p a b (k p)).choose_spec
    · simpa only [g, dite_eq_right h₁] using (localProjection_surjective p a b (k p)).choose_spec

def firstTuple : FiniteLocalCover a b →* RestrictedUnits where
  toFun g := ⟨fun p => localFirst p a b (g p),
    g.2.mono fun p hp => (sectionSubgroup_fixes a b p (g p) hp).1⟩
  map_one' := by apply RestrictedProduct.ext; intro p; exact map_one (localFirst p a b)
  map_mul' g h := by apply RestrictedProduct.ext; intro p; exact map_mul (localFirst p a b) (g p) (h p)

def secondTuple : FiniteLocalCover a b →* RestrictedUnits where
  toFun g := ⟨fun p => localSecond p a b (g p),
    g.2.mono fun p hp => (sectionSubgroup_fixes a b p (g p) hp).2⟩
  map_one' := by apply RestrictedProduct.ext; intro p; exact map_one (localSecond p a b)
  map_mul' g h := by apply RestrictedProduct.ext; intro p; exact map_mul (localSecond p a b) (g p) (h p)

def firstTensorAction : FiniteLocalCover a b →* Module.End ℂ RestrictedTensor :=
  restrictedAction.comp (forgetUnits.comp (firstTuple a b))

def secondTensorAction : FiniteLocalCover a b →* Module.End ℂ RestrictedTensor :=
  restrictedAction.comp (forgetUnits.comp (secondTuple a b))

#print axioms sectionSubgroup_projection
#print axioms sectionSubgroup_fixes
#print axioms finiteProjection_surjective

end ZInQ.Manuscript.RC.Metaplectic2
