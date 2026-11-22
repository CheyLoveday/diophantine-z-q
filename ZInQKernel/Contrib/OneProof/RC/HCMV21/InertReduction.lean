import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Separability
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.KernelCard
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace ZInQ.Manuscript.RC.HCMV21

open TauCeti.Isogeny WeierstrassCurve WeierstrassCurve.Affine

/-- Over the geometric residue field the group killed by multiplication by `q`
has at most `q` elements: the inseparable degree of `[q]` is at least `q`. -/
theorem card_geometric_q_torsion_le {k : Type*} [Field k] [DecidableEq k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (W : WeierstrassCurve.Affine k) [W.IsElliptic] :
    Nat.card (AddSubgroup.torsionBy W.Point (q : ℤ)) ≤ q := by
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hψ := psiFunctionField_ne_zero_of_Δ_ne_zero W W.isUnit_Δ.ne_zero hq0
  let f := mulByIntIsogeny W hψ
  have hd : f.degree = q * q := by
    simp [f, pow_two, degree_mulByIntIsogeny]
  have hdiv : q ∣ f.inseparableDegree :=
    dvd_inseparableDegree_mulByIntIsogeny W q hψ (by simp)
  have hle : f.separableDegree * q ≤ q * q := calc
    _ ≤ f.separableDegree * f.inseparableDegree :=
      Nat.mul_le_mul_left _ (Nat.le_of_dvd f.inseparableDegree_pos hdiv)
    _ = _ := f.separableDegree_mul_inseparableDegree.trans hd
  have h : Nat.card (AddSubgroup.torsionBy (W⁄k).toAffine.Point (q : ℤ)) ≤ q := by
    rw [← ker_mulByIntIsogeny_eq_torsionBy W hψ]
    exact f.card_ker_le_separableDegree.trans (Nat.le_of_mul_le_mul_right hle hq)
  rwa [Affine.baseChange_self] at h

/-- Forward inert criterion on the reduced curve. `R` acts through the specialized
endomorphisms on geometric points. Since the quotient `R/(q)` is a field of size
`q²`, a single nonzero point in the `q`-torsion would generate at least `q²` points. -/
theorem supersingular_of_inert_action {k R : Type*} [Field k] [DecidableEq k] [CommRing R]
    (q : ℕ) [Fact q.Prime] [CharP k q] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
    [Module R W.Point] [(Ideal.span {(q : R)}).IsMaximal]
    (hqcard : Nat.card (R ⧸ Ideal.span {(q : R)}) = q ^ 2) :
    ∀ x : W.Point, q • x = 0 → x = 0 := by
  classical
  let J : Ideal R := Ideal.span {(q : R)}
  let : Field (R ⧸ J) := Ideal.Quotient.field J
  let T := Submodule.torsionBy R W.Point (q : R)
  have hqpos : 0 < q := (Fact.out : q.Prime).pos
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hqpos.ne'
  let e : T ≃ AddSubgroup.torsionBy W.Point (q : ℤ) := Equiv.subtypeEquivRight fun x => by
    rw [AddSubgroup.torsionBy.nsmul_iff]
    exact (Submodule.mem_torsionBy_iff _ _).trans (by rw [Nat.cast_smul_eq_nsmul])
  let : Finite (AddSubgroup.torsionBy W.Point (q : ℤ)) :=
    (W : WeierstrassCurve k).finite_torsionBy hq0
  let : Finite T := Finite.of_equiv _ e.symm
  have hcard : Nat.card T ≤ q :=
    (Nat.card_congr e).le.trans (card_geometric_q_torsion_le q W)
  intro x hx
  by_contra hn
  let X : T := ⟨x, (Submodule.mem_torsionBy_iff _ _).mpr ((Nat.cast_smul_eq_nsmul R q x).trans hx)⟩
  have hX : X ≠ 0 := fun h => hn (congrArg Subtype.val h)
  let g : R ⧸ J → T := fun a => a • X
  have hg : Function.Injective g := fun _ _ h => (smul_left_injective _ hX) h
  have hbound : q ^ 2 ≤ q := hqcard ▸ (Nat.card_le_card_of_injective g hg).trans hcard
  have hp : 1 < q := (Fact.out : q.Prime).one_lt
  have hle : q * q ≤ 1 * q := by simpa [pow_two] using hbound
  exact (not_le_of_gt hp) (Nat.le_of_mul_le_mul_right hle hqpos)

end ZInQ.Manuscript.RC.HCMV21
