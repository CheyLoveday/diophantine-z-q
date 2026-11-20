import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Presentation
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! The common central extension from the Bruhat relations (tex 8788–8799).
The pullback along the scalar quotient is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open scoped MatrixGroups

variable {B G : Type*} [Group B] [Group G]

/-- Pairs whose projected operators agree in the quotient. For two forms
the operator group is a product and the kernel to use is the diagonal sign. -/
def Cover (N : Subgroup G) [N.Normal] (ρ : B →* G ⧸ N) : Subgroup (B × G) :=
  (ρ.comp (MonoidHom.fst B G)).eqLocus ((QuotientGroup.mk' N).comp (MonoidHom.snd B G))

variable (N : Subgroup G) [N.Normal] (ρ : B →* G ⧸ N)

def coverProjection : Cover N ρ →* B := (MonoidHom.fst B G).comp (Cover N ρ).subtype

def coverOperator : Cover N ρ →* G := (MonoidHom.snd B G).comp (Cover N ρ).subtype

/-- Make a lift from a representative in the operator group. -/
def coverLift (b : B) (g : G) (h : ρ b = QuotientGroup.mk' N g) : Cover N ρ :=
  ⟨(b, g), h⟩

theorem coverProjection_surjective : Function.Surjective (coverProjection N ρ) := by
  intro b
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N (ρ b)
  exact ⟨coverLift N ρ b g hg.symm, rfl⟩

/-- A kernel element is specified by an operator in the quotient subgroup. -/
def coverKernelElement (g : N) : Cover N ρ :=
  coverLift N ρ 1 g (by
    rw [map_one]
    exact ((QuotientGroup.eq_one_iff _).2 g.property).symm)

theorem cover_kernel (x : Cover N ρ) :
    coverProjection N ρ x = 1 ↔ ∃ g : N, x = coverKernelElement N ρ g := by
  constructor
  · intro h
    have hx : ρ (coverProjection N ρ x) = QuotientGroup.mk' N (coverOperator N ρ x) := x.property
    rw [h, map_one] at hx
    refine ⟨⟨coverOperator N ρ x, (QuotientGroup.eq_one_iff _).mp hx.symm⟩, ?_⟩
    apply Subtype.ext
    exact Prod.ext h rfl
  · rintro ⟨g, rfl⟩
    rfl

theorem cover_kernel_pair (e : N) (hne : (e : G) ≠ 1)
    (hN : ∀ g : N, (g : G) = 1 ∨ g = e) :
    coverKernelElement N ρ e ≠ 1 ∧
      ∀ x, coverProjection N ρ x = 1 ↔ x = 1 ∨ x = coverKernelElement N ρ e := by
  refine ⟨fun h => hne (congrArg (coverOperator N ρ) h), fun x => ?_⟩
  rw [cover_kernel]
  constructor
  · rintro ⟨g, rfl⟩
    rcases hN g with h | rfl
    · left
      apply Subtype.ext
      exact Prod.ext rfl h
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨1, rfl⟩
    · exact ⟨e, rfl⟩

theorem cover_kernel_central (g : N) (hc : ∀ h : G, Commute (g : G) h) (x : Cover N ρ) :
    Commute (coverKernelElement N ρ g) x := by
  show coverKernelElement N ρ g * x = x * coverKernelElement N ρ g
  apply Subtype.ext
  change (1 * x.val.1, (g : G) * x.val.2) = (x.val.1 * 1, x.val.2 * (g : G))
  rw [one_mul, mul_one, (hc x.val.2).eq]

/-- If the generator relations hold modulo a given normal subgroup,
the pullback carries lifts with exactly the prescribed operators.
Use the diagonal sign subgroup for a common two-element kernel. -/
theorem cover_of_relations {k : Type*} [Field k]
    (U : k → G) (M : kˣ → G) (W : G)
    (R : NormalForm.Relations (fun b => QuotientGroup.mk' N (U b))
      (fun t => QuotientGroup.mk' N (M t)) (QuotientGroup.mk' N W)) :
    ∃ ρ : SL(2, k) →* G ⧸ N, ∃ (u : k → Cover N ρ) (m : kˣ → Cover N ρ)
      (w : Cover N ρ),
      (∀ b, coverProjection N ρ (u b) = upperMatrix b ∧ coverOperator N ρ (u b) = U b) ∧
      (∀ t, coverProjection N ρ (m t) = diagonalMatrix t ∧ coverOperator N ρ (m t) = M t) ∧
      coverProjection N ρ w = weylMatrix ∧ coverOperator N ρ w = W := by
  obtain ⟨f, hu, hm, hw⟩ := NormalForm.representation_of_relations R
  exact ⟨f, fun b => coverLift N f _ _ (hu b), fun t => coverLift N f _ _ (hm t),
    coverLift N f _ _ hw, fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, rfl, rfl⟩

#print axioms coverProjection_surjective
#print axioms cover_kernel
#print axioms cover_kernel_pair
#print axioms cover_kernel_central
#print axioms cover_of_relations

end ZInQ.Manuscript.RC.Metaplectic2
