import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic.Group

/-! Gluing local representatives in the restricted product (tex 9156–9164). -/

namespace ZInQ.Manuscript.RC.HCMV21

open Filter

/-- Local factorizations at a fixed reference give an adelic
factorization. The torus factors are integral almost everywhere because
the two original representatives are, and the unit intersection detects
integrality in the torus. This is a restricted-product assertion; it
does not supply the geometric meaning of the local cosets. -/
theorem restricted_coset_factor {I : Type*} {T G : I → Type*}
    [∀ i, Group (T i)] [∀ i, Group (G i)]
    (j : ∀ i, T i →* G i) (V : ∀ i, Subgroup (T i)) (U : ∀ i, Subgroup (G i))
    (g z : ∀ i, G i)
    (hg : ∀ᶠ i in cofinite, g i ∈ U i) (hz : ∀ᶠ i in cofinite, z i ∈ U i)
    (hunit : ∀ᶠ i in cofinite, ∀ a : T i, j i a ∈ U i ↔ a ∈ V i)
    (h : ∀ i, ∃ (a : T i) (u : U i), g i = j i a * z i * u.val) :
    ∃ (a : ∀ i, T i) (u : ∀ i, U i), (∀ᶠ i in cofinite, a i ∈ V i) ∧
      ∀ i, g i = j i (a i) * z i * (u i).val := by
  classical
  choose a u h using h
  refine ⟨a, u, ?_, h⟩
  filter_upwards [hg, hz, hunit] with i hg hz hunit
  apply (hunit (a i)).1
  rw [show j i (a i) = g i * ((u i).val)⁻¹ * (z i)⁻¹ by rw [h i]; group]
  exact (U i).mul_mem ((U i).mul_mem hg ((U i).inv_mem (u i).property))
    ((U i).inv_mem hz)

end ZInQ.Manuscript.RC.HCMV21
