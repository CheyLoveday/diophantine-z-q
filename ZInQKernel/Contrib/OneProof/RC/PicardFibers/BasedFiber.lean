import ZInQKernel.Contrib.OneProof.RC.PicardFibers.Representatives
import ZInQKernel.Contrib.OneProof.RC.PicardFibers.OrbitQuotient
import ZInQKernel.Contrib.OneProof.RC.PicardFibers.RationalCentralizer

/-! Tex 9155–9169: identify the actual fiber through a selected adelic
representative with the corresponding double classes of the centralizer. -/

noncomputable section

set_option maxHeartbeats 800000

open IsDedekindDomain
open scoped NumberField

namespace ZInQ.Manuscript.RC.PicardFibers

open Eichler O7Actual O7Orbits Visibility Adelic

section Action

variable {a b : ℚ} (R : Order a b) (x₀ : (B a b)ˣ)

/-- The left subgroup in the fiber quotient is the diagonal rational
centralizer. -/
def diagonalCentralizer : Subgroup (FiniteUnits R) :=
  (rationalCentralizer x₀).map (diagonal R)

theorem diagonalCentralizer_le :
    diagonalCentralizer R x₀ ≤ adelicCentralizer R (diagonal R x₀).val := by
  rintro _ ⟨k, hk, rfl⟩ p
  exact (show Commute k x₀ from Subgroup.mem_centralizer_singleton_iff.mp hk).map
    (Units.map (toLocal p.val).toMonoidHom)

theorem centralizer_mul_admissible {α : B a b} (hα : 2 * α - 1 = x₀.val)
    (g : adelicCentralizer R (diagonal R x₀).val)
    {z : FiniteUnits R} (hz : AdelicAdmissible α z) :
    AdelicAdmissible α (g.val * z) := by
  intro p
  let u := g.val.val p
  let q := Units.map (toLocal p.val).toMonoidHom x₀
  have hc : Commute u⁻¹ q := (g.prop p).inv_left
  have hq : unitConjRing u⁻¹ (q : Bp p.val a b) = (q : Bp p.val a b) := by
    rw [unitConjRing_apply]
    change ((u⁻¹ : (Bp p.val a b)ˣ) : Bp p.val a b) * (q : Bp p.val a b) *
      ((u : (Bp p.val a b)ˣ) : Bp p.val a b) = (q : Bp p.val a b)
    rw [show ((u⁻¹ : (Bp p.val a b)ˣ) : Bp p.val a b) * (q : Bp p.val a b) =
      (q : Bp p.val a b) * ((u⁻¹ : (Bp p.val a b)ˣ) : Bp p.val a b) from
        congrArg Units.val hc.eq, Units.inv_mul_cancel_right]
  have hq' : (q : Bp p.val a b) = 2 * toLocal p.val α - 1 := by
    change toLocal p.val x₀.val = _
    rw [← hα, map_sub, map_mul, map_ofNat, map_one]
  rw [hq', map_sub, map_mul, map_ofNat, map_one] at hq
  have htwo : IsUnit (2 : Bp p.val a b) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ_[p.val]) ≠ 0)).map
        (algebraMap ℚ_[p.val] (Bp p.val a b))
  have ha := htwo.mul_left_cancel (sub_left_inj.mp hq)
  change unitConjRing (u * z.val p)⁻¹ (toLocal p.val α) ∈ R.completion p.val
  rw [mul_inv_rev, ← unitConjRing_mul, ha]
  exact hz p

end Action

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m : ℤ}

/-- One based actual orientation fiber is the double quotient of its
centralizer orbit (tex 9157–9165). -/
def basedFiberEquiv (s : StageAt O N M hN m) {D : ℤ}
    (A : AdmissibleD s D) (H : SupportBridge s D)
    (hh : legendreSym s.ell (-(s.weights.m : ℤ)) = -1)
    (x₀ : (B (-1) (-(s.ell : ℚ)))ˣ) {α : B (-1) (-(s.ell : ℚ))}
    (hα : 2 * α - 1 = x₀.val) (hx : x₀.val.re = 0) (hn : nrd x₀.val = index s D)
    (z : {z : FiniteUnits (ActualOrder s) // AdelicAdmissible α z})
    (t : Orientations N.primeFactors.card)
    (ht : orientation s H (orbitFromRep s H hα hx hn z) = t) :
    Set.range (fun g : adelicCentralizer (ActualOrder s) (diagonal (ActualOrder s) x₀).val =>
      DoubleCoset.mk (diagonalCentralizer (ActualOrder s) x₀) (integralUnits (ActualOrder s))
        (g.val * z.val)) ≃
      {P : OrbitSet s.visibility (index s D) // orientation s H P = t} := by
  let R := ActualOrder s
  let C := adelicCentralizer R (diagonal R x₀).val
  let Z (g : C) : {z : FiniteUnits R // AdelicAdmissible α z} :=
    ⟨g.val * z.val, centralizer_mul_admissible R x₀ hα g z.prop⟩
  let q (g : C) := DoubleCoset.mk (diagonalCentralizer R x₀) (integralUnits R) (Z g).val
  let f (g : C) : {P : OrbitSet s.visibility (index s D) // orientation s H P = t} :=
    ⟨orbitFromRep s H hα hx hn (Z g), ((orbitFromRep_orientation_iff s A H hh x₀ hα hx hn z
      (Z g)).mpr ⟨g, 1, by simp [Z]⟩).symm.trans ht⟩
  have he (g h : C) : q g = q h ↔ f g = f h := by
    rw [Subtype.ext_iff]
    change DoubleCoset.mk _ _ (Z g).val = DoubleCoset.mk _ _ (Z h).val ↔
      orbitFromRep s H hα hx hn (Z g) = orbitFromRep s H hα hx hn (Z h)
    rw [DoubleCoset.eq, orbitFromRep_eq_iff s H x₀ hα hx hn (Z g) (Z h)]
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, r, hr, h⟩
      exact ⟨k, Subgroup.mem_centralizer_singleton_iff.mp hk, ⟨r, hr⟩, h⟩
    · rintro ⟨k, hk, r, h⟩
      exact ⟨diagonal R k, ⟨k, Subgroup.mem_centralizer_singleton_iff.mpr hk, rfl⟩, r.val, r.prop, h⟩
  let F (q' : Set.range q) := f q'.prop.choose
  refine Equiv.ofBijective F ⟨?_, ?_⟩
  · intro a b h
    apply Subtype.ext
    exact a.prop.choose_spec.symm.trans (((he _ _).mpr h).trans b.prop.choose_spec)
  · intro P
    obtain ⟨w, hw⟩ := orbitFromRep_surjective s H x₀ hα hx hn P.val
    obtain ⟨g, r, hr⟩ := (orbitFromRep_orientation_iff s A H hh x₀ hα hx hn z w).mp
      (ht.trans ((congrArg (orientation s H) hw).trans P.prop).symm)
    let y : Set.range q := ⟨q g, g, rfl⟩
    refine ⟨y, ((he _ _).mp y.prop.choose_spec).trans ?_⟩
    apply Subtype.ext
    apply Eq.trans _ hw
    exact (orbitFromRep_eq_iff s H x₀ hα hx hn (Z g) w).mpr
      ⟨1, Commute.one_left _, r, by simpa only [map_one, one_mul] using hr⟩

/-- Assemble the actual Picard fibers from representatives of the local
tuples and the comparison of the completed torus and its integral units.
The two comparisons are hypotheses here, upstream of the class quotient. -/
def picardFibers_of_comparison (s : StageAt O N M hN m) {D : ℤ}
    (A : AdmissibleD s D) (H : SupportBridge s D)
    (hh : legendreSym s.ell (-(s.weights.m : ℤ)) = -1)
    (x₀ : (B (-1) (-(s.ell : ℚ)))ˣ) {α : B (-1) (-(s.ell : ℚ))}
    (hα : 2 * α - 1 = x₀.val) (hx : x₀.val.re = 0) (hn : nrd x₀.val = index s D)
    (F : Type) [Field F] [NumberField F]
    (e : (FiniteAdeleRing (𝓞 F) F)ˣ ≃*
      adelicCentralizer (ActualOrder s) (diagonal (ActualOrder s) x₀).val)
    (hrat : ∀ a, (e a).val ∈ diagonalCentralizer (ActualOrder s) x₀ ↔
      a ∈ (FiniteAdeleRing.unitEmbedding (𝓞 F) F).range)
    (hint : ∀ z : {z : FiniteUnits (ActualOrder s) // AdelicAdmissible α z}, ∀ a,
      z.val⁻¹ * (e a).val * z.val ∈ integralUnits (ActualOrder s) ↔
        a ∈ (ideleToIdeal (R := 𝓞 F) (K := F)).ker)
    (hocc : ∀ t : Orientations N.primeFactors.card,
      ∃ z : {z : FiniteUnits (ActualOrder s) // AdelicAdmissible α z},
        orientation s H (orbitFromRep s H hα hx hn z) = t) :
    PicardFibers s H (ClassGroup (𝓞 F)) := fun t =>
  let z := (hocc t).choose
  (ideleOrbitEquiv (diagonalCentralizer (ActualOrder s) x₀) _ _
    (diagonalCentralizer_le _ _) z.val e hrat (hint z)).trans
      (basedFiberEquiv s A H hh x₀ hα hx hn z t (hocc t).choose_spec)

end ZInQ.Manuscript.RC.PicardFibers
