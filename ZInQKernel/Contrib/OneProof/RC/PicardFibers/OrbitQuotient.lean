import ZInQKernel.Contrib.OneProof.RC.PicardFibers.IdeleClass
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Orbits

/-! Tex 9161–9169: a selected embedded torus orbit has the desired class
group quotient once the two subgroup comparisons are known.
The quotient bookkeeping is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.PicardFibers

open IsDedekindDomain

private theorem leftRel_sup_iff_doubleCoset {G : Type*} [CommGroup G]
    (L U : Subgroup G) (a b : G) :
    QuotientGroup.leftRel (L ⊔ U) a b ↔ DoubleCoset.setoid (L : Set G) (U : Set G) a b := by
  rw [QuotientGroup.leftRel_apply, Subgroup.mem_sup, DoubleCoset.rel_iff]
  constructor
  · rintro ⟨l, hl, u, hu, h⟩
    exact ⟨l, hl, u, hu, calc
      b = a * (a⁻¹ * b) := by group
      _ = l * a * u := by rw [← h]; ac_rfl⟩
  · rintro ⟨l, hl, u, hu, rfl⟩
    exact ⟨l, hl, u, hu, by rw [mul_comm l a]; group⟩

private theorem doubleCoset_mulEquiv_iff {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (L U : Subgroup G) (L' U' : Subgroup H)
    (hl : ∀ a, e a ∈ L' ↔ a ∈ L) (hu : ∀ a, e a ∈ U' ↔ a ∈ U) (a b : G) :
    DoubleCoset.setoid (L : Set G) (U : Set G) a b ↔
      DoubleCoset.setoid (L' : Set H) (U' : Set H) (e a) (e b) := by
  rw [DoubleCoset.rel_iff, DoubleCoset.rel_iff]
  constructor
  · rintro ⟨l, hL, u, hU, rfl⟩
    exact ⟨e l, (hl l).mpr hL, e u, (hu u).mpr hU, by rw [map_mul, map_mul]⟩
  · rintro ⟨l, hL, u, hU, he⟩
    refine ⟨e.symm l, (hl _).mp (by simpa using hL),
      e.symm u, (hu _).mp (by simpa using hU), e.injective ?_⟩
    simpa only [map_mul, e.apply_symm_apply] using he

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The set of double classes represented by an embedded centralizer orbit.
The conditions on the idele equivalence identify only the rational and
integral subgroups of the torus. -/
def ideleOrbitEquiv {G : Type*} [Group G] (L H U : Subgroup G)
    (hLH : L ≤ H) (z : G) (e : (FiniteAdeleRing R K)ˣ ≃* H)
    (rational : ∀ a, (e a : G) ∈ L ↔ a ∈ (FiniteAdeleRing.unitEmbedding R K).range)
    (integral : ∀ a, z⁻¹ * (e a : G) * z ∈ U ↔ a ∈ (ideleToIdeal (R := R) (K := K)).ker) :
    ClassGroup R ≃ Set.range (fun a : H => DoubleCoset.mk L U ((a : G) * z)) := by
  let L₀ := (FiniteAdeleRing.unitEmbedding R K).range
  let U₀ := (ideleToIdeal (R := R) (K := K)).ker
  let U' := U.comap ((MulAut.conj z⁻¹).toMonoidHom.comp H.subtype)
  have hr (a : (FiniteAdeleRing R K)ˣ) : e a ∈ L.subgroupOf H ↔ a ∈ L₀ := rational a
  have hi (a : (FiniteAdeleRing R K)ˣ) : e a ∈ U' ↔ a ∈ U₀ := by
    have h := integral a
    change (MulAut.conj z⁻¹) (e a : G) ∈ U ↔ a ∈ U₀
    simpa only [MulAut.conj_apply, inv_inv] using h
  exact (ideleClassEquiv (R := R) (K := K)).symm.toEquiv.trans
    ((Quotient.congrRight (leftRel_sup_iff_doubleCoset L₀ U₀)).trans
      ((Quotient.congr e.toEquiv (doubleCoset_mulEquiv_iff e L₀ U₀ _ _ hr hi)).trans
        (O7Actual.doubleCoset_orbitEquiv L H U hLH z)))

end ZInQ.Manuscript.RC.PicardFibers
