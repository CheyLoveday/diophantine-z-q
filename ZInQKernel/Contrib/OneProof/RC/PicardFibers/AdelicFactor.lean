import ZInQKernel.Contrib.OneProof.RC.Adelic.FiniteUnits

/-! Tex 9155–9160: glue order-unit intertwiners along the restricted
product. The exceptional set argument is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.PicardFibers

open Eichler Adelic

variable {a b : ℚ} {R : Order a b}

/-- The local conjugate of a fixed unit, in coordinates at a finite place. -/
def transportedUnit (x : LocalFamily a b) (z : FiniteUnits R) (p : Prime) :
    (Bp p.val a b)ˣ :=
  (z.val p)⁻¹ * x p * z.val p

/-- The centralizer of the chosen element in the adelic unit group. -/
def adelicCentralizer (R : Order a b) (x : LocalFamily a b) : Subgroup (FiniteUnits R) where
  carrier := {g | ∀ p, Commute (g.val p) (x p)}
  one_mem' _p := Commute.one_left _
  mul_mem' hg hh p := (hg p).mul_left (hh p)
  inv_mem' hg p := (hg p).inv_left

private theorem commute_factor {G : Type*} [Group G] (x r z w : G)
    (h : (z⁻¹ * x * z) * r = r * (w⁻¹ * x * w)) :
    Commute (w * r⁻¹ * z⁻¹) x := by
  have he : x * (z * r * w⁻¹) = (z * r * w⁻¹) * x := calc
    _ = z * ((z⁻¹ * x * z) * r) * w⁻¹ := by group
    _ = z * (r * (w⁻¹ * x * w)) * w⁻¹ := by rw [h]
    _ = _ := by group
  have hi := (show Commute (z * r * w⁻¹) x from he.symm).inv_left
  have he' : (z * r * w⁻¹)⁻¹ = w * r⁻¹ * z⁻¹ := by group
  rwa [he'] at hi

private theorem intertwines_factor {G : Type*} [Group G] {g x : G}
    (hg : Commute g x) (z r : G) :
    (z⁻¹ * x * z) * r = r * ((g * z * r)⁻¹ * x * (g * z * r)) := by
  calc
    _ = z⁻¹ * (g⁻¹ * (g * x)) * z * r := by group
    _ = z⁻¹ * (g⁻¹ * (x * g)) * z * r := by rw [hg.eq]
    _ = _ := by group

set_option maxHeartbeats 800000 in
/-- Local integral conjugation at every rational prime is equivalent to
membership in the centralizer orbit with right order units. No
restrictedness condition on the initially chosen intertwiners is needed. -/
theorem adelic_factor_iff (x : LocalFamily a b) (z w : FiniteUnits R) :
    (∀ p : Prime, ∃ r : localUnits R p,
      transportedUnit x z p * r.val = r.val * transportedUnit x w p) ↔
    ∃ g : adelicCentralizer R x, ∃ r : integralUnits R, w = g.val * z * r.val := by
  classical
  constructor
  · intro h
    let S : Set Prime := {p | z.val p ∉ localUnits R p} ∪ {p | w.val p ∉ localUnits R p}
    have hS : S.Finite := z.prop.union w.prop
    have hout (p : Prime) (hp : p ∉ S) :
        z.val p ∈ localUnits R p ∧ w.val p ∈ localUnits R p := by
      simpa only [S, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] using hp
    let r (p : Prime) : localUnits R p :=
      if hp : p ∈ S then (h p).choose else
        ⟨(z.val p)⁻¹ * w.val p, (localUnits R p).mul_mem
          ((localUnits R p).inv_mem (hout p hp).1) (hout p hp).2⟩
    let r₀ : FiniteUnits R := ⟨fun p => (r p).val, by
      change {p | (r p).val ∉ localUnits R p}.Finite
      exact Set.finite_empty.subset fun p hp => False.elim (hp (r p).prop)⟩
    let r₁ : integralUnits R := ⟨r₀, fun p => (r p).prop⟩
    let g (p : Prime) := w.val p * (r p).val⁻¹ * (z.val p)⁻¹
    have hg (p : Prime) (hp : p ∉ S) : g p = 1 := by
      dsimp [g, r]
      rw [dite_eq_right hp]
      dsimp
      group
    let g₀ : FiniteUnits R := ⟨g, hS.subset fun p hp => by
      by_contra hn
      exact hp (hg p hn ▸ (localUnits R p).one_mem)⟩
    have hg₀ : g₀ ∈ adelicCentralizer R x := by
      intro p
      change Commute (g p) (x p)
      by_cases hp : p ∈ S
      · simpa only [g, r, dite_eq_left hp] using commute_factor (x p) _ _ _ (h p).choose_spec
      · rw [hg p hp]
        exact Commute.one_left _
    refine ⟨⟨g₀, hg₀⟩, r₁, Subtype.ext (funext fun p => ?_)⟩
    change w.val p = g p * z.val p * (r p).val
    dsimp [g]
    group
  · rintro ⟨g, r, rfl⟩ p
    refine ⟨⟨r.val.val p, r.prop p⟩, ?_⟩
    exact intertwines_factor (G := (Bp p.val a b)ˣ) (g.prop p) (z.val p) (r.val.val p)

end ZInQ.Manuscript.RC.PicardFibers
