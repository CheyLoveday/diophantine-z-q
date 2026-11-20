import ZInQKernel.Contrib.OneProof.RC.O7Actual.Orientation
import Mathlib.GroupTheory.DoubleCoset

/-! The finite orbit bookkeeping before any use of the detector. -/
noncomputable section

namespace ZInQ.Manuscript.RC.O7Actual

open Visibility Visibility.ThetaStage

/-- The orbit set that actually occurs in the coefficient. -/
abbrev OrbitSet {O : Type*} [CommRing O] {a b : ℚ}
    (S : ThetaStage O a b) (n : ℚ) :=
  Σ z : S.X, MulAction.orbitRel.Quotient (S.G z) (S.supp z n)

/-- Local classification and the separate class-group identifications of the
fibers (tex 9136–9170). These data never refer to a point value or a sum. -/
structure OrbitFibers {O : Type*} [CommRing O] {a b : ℚ}
    (S : ThetaStage O a b) (n : ℚ) (ω : ℕ) (Cl : Type) where
  orientation : OrbitSet S n → Orientations ω
  fiber : ∀ t, Cl ≃ {p : OrbitSet S n // orientation p = t}

/-- Tex 9149–9170: assemble the disjoint orientation fibers. -/
def OrbitFibers.param {O : Type*} [CommRing O] {a b : ℚ}
    {S : ThetaStage O a b} {n : ℚ} {ω : ℕ} {Cl : Type}
    (A : OrbitFibers S n ω Cl) : Orientations ω × Cl ≃ OrbitSet S n :=
  (Equiv.sigmaEquivProd (Orientations ω) Cl).symm.trans
    ((Equiv.sigmaCongrRight A.fiber).trans (Equiv.sigmaFiberEquiv A.orientation))

/-- On-the-spot (c), tex 9160–9166. Inside a selected adelic orbit the only
new ambiguity after dividing on the right is the intersection with the
conjugate order-unit group. Here `H` models the embedded finite ideles,
`L ≤ H` the rational centralizer, and `U` the right order-unit group. -/
theorem doubleCoset_restrict {G : Type*} [Group G] (L H U : Subgroup G)
    (hLH : L ≤ H) (z : G) (a b : H) :
    DoubleCoset.setoid (L : Set G) (U : Set G) ((a : G) * z) ((b : G) * z) ↔
      DoubleCoset.setoid (L.subgroupOf H : Set H)
        (U.comap ((MulAut.conj z⁻¹).toMonoidHom.comp H.subtype) : Set H) a b := by
  rw [DoubleCoset.rel_iff, DoubleCoset.rel_iff]
  constructor
  · rintro ⟨l, hl, u, hu, he⟩
    let l' : H := ⟨l, hLH hl⟩
    let j : H := a⁻¹ * l'⁻¹ * b
    have hj : z⁻¹ * (j : G) * z = u := by
      change z⁻¹ * ((↑a : G)⁻¹ * l⁻¹ * ↑b) * z = u
      calc
        _ = z⁻¹ * ((↑a : G)⁻¹ * l⁻¹) * ((↑b : G) * z) := by group
        _ = u := by rw [he]; group
    refine ⟨l', hl, j, ?_, ?_⟩
    · change (MulAut.conj z⁻¹) (j : G) ∈ U
      simpa [MulAut.conj_apply, hj] using hu
    · dsimp [j]
      group
  · rintro ⟨l, hl, j, hj, he⟩
    refine ⟨l, hl, z⁻¹ * (j : G) * z, ?_, ?_⟩
    · change (MulAut.conj z⁻¹) (j : G) ∈ U at hj
      simpa [MulAut.conj_apply] using hj
    · have he' := congrArg (fun x : H => (x : G)) he
      push_cast at he'
      rw [he']
      group

/-- Tex 9157–9166: the quotient of the selected torus orbit, as a
subset of the ambient double quotient, is the double quotient of the torus. -/
def doubleCoset_orbitEquiv {G : Type*} [Group G] (L H U : Subgroup G)
    (hLH : L ≤ H) (z : G) :
    DoubleCoset.Quotient (L.subgroupOf H : Set H)
        (U.comap ((MulAut.conj z⁻¹).toMonoidHom.comp H.subtype) : Set H) ≃
      Set.range (fun a : H =>
        (Quotient.mk _ ((a : G) * z) : DoubleCoset.Quotient (L : Set G) (U : Set G))) := by
  let f : DoubleCoset.Quotient (L.subgroupOf H : Set H)
      (U.comap ((MulAut.conj z⁻¹).toMonoidHom.comp H.subtype) : Set H) →
      Set.range (fun a : H =>
        (Quotient.mk _ ((a : G) * z) : DoubleCoset.Quotient (L : Set G) (U : Set G))) :=
    Quotient.lift (fun a : H => ⟨Quotient.mk _ ((a : G) * z), ⟨a, rfl⟩⟩)
      (fun a b h => Subtype.ext (Quotient.sound ((doubleCoset_restrict L H U hLH z a b).mpr h)))
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b
    induction a using Quotient.inductionOn with
    | _ a =>
      induction b using Quotient.inductionOn with
      | _ b =>
        intro h
        exact Quotient.sound ((doubleCoset_restrict L H U hLH z a b).mp
          (Quotient.exact (congrArg Subtype.val h)))
  · rintro ⟨_, a, rfl⟩
    exact ⟨Quotient.mk _ a, rfl⟩

/-- Tex 9171–9194, 9297–9305: the right order-unit factor occurs twice,
with inverse powers. The class idele contributes only its norm character. -/
theorem torsor_weight {O : Type*} [CommRing O] (χ f χ₀ f₀ χF : O) (r : Oˣ)
    (hχ : χ = χ₀ * χF * (r : O)) (hf : f = f₀ * (↑r⁻¹ : O)) :
    χ * f = (χ₀ * f₀) * χF := by
  calc
    χ * f = (χ₀ * f₀ * χF) * ((r : O) * (↑r⁻¹ : O)) := by rw [hχ, hf]; ring
    _ = _ := by simp

end ZInQ.Manuscript.RC.O7Actual
