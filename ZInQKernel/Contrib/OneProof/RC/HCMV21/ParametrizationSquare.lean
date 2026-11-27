import ZInQKernel.Contrib.OneProof.RC.HCMV21.Consumer

/-! The two evaluations of a single integral parametrization on the CM
sections, at the generic and special points of the detector base.
Tex 8470–8479 and 9279–9295. -/

namespace ZInQ.Manuscript.RC.HCMV21

open AlgebraicGeometry CategoryTheory Eichler PMGeometry
open scoped WeierstrassCurve

variable {S : Scheme} {X E : Over S}

/-- Regard a section over the detector base as a point over a specified
base change, by precomposing the section with the map to the base. -/
def restrictSection {U : Scheme} (u : U ⟶ S) {M : Over S}
    (x : Over.mk (𝟙 S) ⟶ M) : Over.mk u ⟶ M :=
  Over.homMk (U := Over.mk u) (V := Over.mk (𝟙 S)) u (Category.comp_id u) ≫ x

/-- A missing integral-model input. The analytic conjugates and the
special Abel–Jacobi quotient must be the two evaluations of one
morphism on the same integral modular curve. The test on the special
fibre is on modular points and does not mention CM or adelic classes. -/
def ParametrizationFibresAt {Cl Point Y P : Type*}
    {U V : Scheme} (g : U ⟶ S) (s : V ⟶ S)
    (sections : Cl → (Over.mk (𝟙 S) ⟶ X))
    (specialX : (Over.mk s ⟶ X) → Point)
    (genericE : (Over.mk g ⟶ E) → Y)
    (specialE : (Over.mk s ⟶ E) → P)
    (piSpecial : Point → P) (y : Cl → Y) : Prop :=
  ∃ π : X ⟶ E,
    (∀ c, genericE (restrictSection g (sections c) ≫ π) = y c) ∧
    ∀ x : Over.mk s ⟶ X, specialE (x ≫ π) = piSpecial (specialX x)

/-- Restrict the composite of the integral CM section with the integral
parametrization. Both sides come from this same elliptic curve section. -/
theorem parametrization_commutes_of_fibres {Cl Point Y P : Type*}
    {U V : Scheme} (g : U ⟶ S) (s : V ⟶ S)
    (sections : Cl → (Over.mk (𝟙 S) ⟶ X))
    (specialX : (Over.mk s ⟶ X) → Point)
    (genericE : (Over.mk g ⟶ E) → Y)
    (specialE : (Over.mk s ⟶ E) → P)
    (piSpecial : Point → P) (y : Cl → Y) (red : Y → P)
    (hred : ∀ e : Over.mk (𝟙 S) ⟶ E,
      specialE (restrictSection s e) = red (genericE (restrictSection g e)))
    (hπ : ParametrizationFibresAt g s sections specialX genericE specialE piSpecial y)
    (c : Cl) :
    piSpecial (specialX (restrictSection s (sections c))) = red (y c) := by
  obtain ⟨π, hg, hs⟩ := hπ
  have h := hred (sections c ≫ π)
  rw [← hs (restrictSection s (sections c)), ← hg c]
  simpa only [restrictSection, Category.assoc] using h

/-- The consumer's square with its original class-attachment hypotheses.
The special point used by the integral section is supplied by the
same-place reduction of the labelled CM point. -/
theorem point_reduction_of_integral_parametrization
    {a b : ℚ} {R : Order a b} {ell N : ℕ} [Fact ell.Prime]
    {A : Adelic (ell := ell) (N := N) R}
    {K : Type*} [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
    {Ebar : WeierstrassCurve (ZMod ell)} {ap : ℕ → ℤ}
    {Cl C Y T : Type*} [Group Cl] [MulAction Cl C] [MulAction Cl T] [AddCommGroup Y]
    {red : Y →+ PM.ReducedPoints (K := K) Ebar}
    {y : Cl → Y} {z : Cl → ClassSet R}
    (model : GeometricInput A K Ebar ap)
    (reduceLabelled : C → T) (x₀ : C) (z₀ : T) (h₀ : reduceLabelled x₀ = z₀)
    (h : OrientedCorrespondence (C := Cl) reduceLabelled)
    (forgetLabels : T → model.Point)
    (hclass : ∀ c : Cl, forgetLabels (c • z₀) = (model.classes (z c)).val)
    {U V : Scheme} (g : U ⟶ S) (s : V ⟶ S)
    (sections : Cl → (Over.mk (𝟙 S) ⟶ X))
    (specialX : (Over.mk s ⟶ X) → model.Point)
    (genericE : (Over.mk g ⟶ E) → Y)
    (specialE : (Over.mk s ⟶ E) → PM.ReducedPoints (K := K) Ebar)
    (hsections : ∀ c, specialX (restrictSection s (sections c)) =
      forgetLabels (reduceLabelled (c • x₀)))
    (hred : ∀ e : Over.mk (𝟙 S) ⟶ E,
      specialE (restrictSection s e) = red (genericE (restrictSection g e)))
    (hfibres : ParametrizationFibresAt g s sections specialX genericE specialE model.specialize y)
    (c : Cl) : model.geometry.pi (z c) = red (y c) := by
  apply point_reduction_of_orientedCorrespondence model reduceLabelled x₀ z₀ h₀ h
    forgetLabels hclass _ c
  intro d
  rw [← hsections d]
  exact parametrization_commutes_of_fibres g s sections specialX genericE specialE
    model.specialize y red hred hfibres d

end ZInQ.Manuscript.RC.HCMV21
