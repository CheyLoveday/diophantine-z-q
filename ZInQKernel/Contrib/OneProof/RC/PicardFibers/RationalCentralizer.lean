import ZInQKernel.Contrib.OneProof.RC.O7Actual.Embeddings
import ZInQKernel.Contrib.OneProof.RC.Adelic.FiniteUnits

/-! Tex 9150–9164: the rational left ambiguity is the group of
units of the embedded quadratic field. On-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.PicardFibers

open Eichler O7Actual

/-- The rational centralizer of the chosen unit in the quaternion algebra. -/
abbrev rationalCentralizer {a b : ℚ} (x : (B a b)ˣ) :=
  Subgroup.centralizer ({x} : Set (B a b)ˣ)

/-- The units of the embedded quadratic field are exactly the rational
quaternion units commuting with the chosen root. -/
theorem rationalCentralizer_eq_range {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    {F : Type*} [Field F] [NumberField F] {d : ℤ} (Q : QuadraticBasis F d)
    (ι : F →ₐ[ℚ] B a b) (x : (B a b)ˣ) (hx : x.val.re = 0)
    (h : x.val = ι (Q.model QuadraticAlgebra.omega)) :
    rationalCentralizer x = (Units.map ι.toMonoidHom).range := by
  ext u
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hu
    have hc : Commute u.val x.val := congrArg (fun w : (B a b)ˣ => w.val) hu
    obtain ⟨t, ht⟩ := centralizer_span ha hb hx x.ne_zero hc
    let y := algebraMap ℚ F u.val.re + t • Q.model QuadraticAlgebra.omega
    have hy : ι y = u.val := by
      rw [show y = _ from rfl, map_add, AlgHom.commutes, map_smul, ← h]
      exact ht.symm
    have hy0 : y ≠ 0 := fun hz => u.ne_zero (hy.symm.trans (by rw [hz, map_zero]))
    exact ⟨Units.mk0 y hy0, Units.ext hy⟩
  · rintro ⟨v, rfl⟩
    apply Units.ext
    change ι v.val * x.val = x.val * ι v.val
    rw [h, ← map_mul, ← map_mul, mul_comm v.val]

end ZInQ.Manuscript.RC.PicardFibers
