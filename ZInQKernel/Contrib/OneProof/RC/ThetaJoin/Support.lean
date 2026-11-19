import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Schwartz

/-! Rational intersection for the Appendix F weight support, separately from the
fields of `PMLocal`. This file does not use the (O.7) coefficient comparison. -/

noncomputable section

namespace ZInQ.Manuscript.RC.ThetaJoin

open Adelic Eichler
open scoped Quaternion

variable {a b : ℚ} {R : Order a b} {O : Type} [CommRing O]

/-- The integral affine generator of the quadratic order (tex 9123–9129). -/
def HalfIntegral (T : Order a b) (x : B a b) : Prop :=
  ∃ t : T.ring, 2 * (t : B a b) - 1 = x

/-- The affine generator as a rational quaternion. -/
def affineGenerator (x : B a b) : B a b := (2⁻¹ : ℚ) • (x + 1)

theorem halfIntegral_iff (T : Order a b) (x : B a b) :
    HalfIntegral T x ↔ affineGenerator x ∈ T.ring := by
  have hd (t : B a b) : (2 : B a b) * t = (2 : ℚ) • t := by
    rw [Algebra.smul_def, map_ofNat]
  have ht : (2 : ℚ) • affineGenerator x = x + 1 := by
    rw [affineGenerator, smul_smul]
    norm_num
  constructor
  · rintro ⟨t, ht'⟩
    have he : (t : B a b) = affineGenerator x := by
      apply smul_right_injective _ (by norm_num : (2 : ℚ) ≠ 0)
      have hz := congrArg (fun y : B a b => y + 1) ht'
      simpa only [sub_add_cancel, ht, hd] using hz
    rw [← he]
    exact t.prop
  · intro hx
    exact ⟨⟨affineGenerator x, hx⟩, by rw [hd, ht, add_sub_cancel_right]⟩

/-- Rational intersection at the chosen adelic representative (tex 9123–9129). -/
theorem halfIntegral_iff_local (ha : a < 0) (hb : b < 0)
    (z : ClassSet R) (x : B a b) :
    HalfIntegral ((representative z).val.leftOrder ha hb) x ↔
      ∀ q : Prime, atRep (classRepresentative z) q (affineGenerator x) ∈ R.completion q.val := by
  rw [halfIntegral_iff]
  change affineGenerator x ∈ (representative z).val.leftRing ↔ _
  rw [← fromAdelic_classRepresentative z]
  exact mem_leftRing_iff (classRepresentative z) (affineGenerator x)

/-- Put together the separate local support tests. The forward implication needs
the local affine membership tests at exceptional primes; the backward implication
additionally uses integrality of the vector itself at every prime. -/
theorem weightAt_support_iff_affine [IsDomain O]
    (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (z : FiniteUnits R) (x : B a b)
    (hBad : ∀ q ∈ A.places, w q (atRep z q x) ≠ 0 ↔
      atRep z q (affineGenerator x) ∈ R.completion q.val)
    (hGood : ∀ q ∉ A.places, atRep z q x ∈ R.completion q.val ↔
      atRep z q (affineGenerator x) ∈ R.completion q.val)
    (hInt : (∀ q : Prime, atRep z q (affineGenerator x) ∈ R.completion q.val) →
      x ∈ (fromAdelic z).val.leftRing) :
    weightAt A w z x ≠ 0 ↔
      ∀ q : Prime, atRep z q (affineGenerator x) ∈ R.completion q.val := by
  classical
  constructor
  · intro hw
    have hx : x ∈ (fromAdelic z).val.leftRing := by
      by_contra hh
      exact hw (ite_eq_right hh)
    have hp : ∏ q ∈ A.places, w q (atRep z q x) ≠ 0 := by
      simpa only [weightAt, ite_eq_left hx] using hw
    intro q
    by_cases hq : q ∈ A.places
    · exact (hBad q hq).mp ((Finset.prod_ne_zero_iff.mp hp) q hq)
    · exact (hGood q hq).mp ((mem_leftRing_iff z x).mp hx q)
  · intro hx
    simpa only [weightAt, ite_eq_left (hInt hx)] using
      Finset.prod_ne_zero_iff.mpr (fun q hq => (hBad q hq).mpr (hx q))

end ZInQ.Manuscript.RC.ThetaJoin
