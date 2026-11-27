import ZInQKernel.Contrib.OneProof.RC.Stages.ReducedCurve

/-!
# Lane RC27 (round 2): the Frobenius sign of the finite-field Kummer map, row on finite torsion

Manuscript (11/5), Appendix F, tex 8378–8391 and 8439–8456: `κ_M(P) = F²R − R ∈ E[n] = T/nT`
(tex 8382; `n = 2^M`, `nR = P`), and `λ_M = b κ_M` with the fixed integral row `b : T → ℤ₂`
(tex 8346–8347) taken modulo `2^M` (tex 8452–8453),
a row on the **finite torsion** `E[n]`; `κ_M(Fr_{ℓ₀} P) = C κ_M(P)` and `bC = b` give the Frobenius
sign `+1`.

Lane RC12's `Odd.lambda_frobenius_sign` used to take its row on the whole group of geometric points.
Lane RC27 restated it with the row on `E[n]` (`RC/Odd/Detector.lean`). This file ties the restated
statement to the stage construction of `FiniteField.lean` and `ReducedCurve.lean`:

* `torsionFrob_eq_torsionRestrict`, `kappa_eq_kummerTorsion`: the stage Frobenius on finite
  torsion and the stage Kummer value are lane RC12's `Odd.torsionRestrict` and
  `Odd.kummerTorsion` (at `F²`);
* `lambda_frobenius_plus_of_odd`: the stage statement `lambda_frobenius_plus` is an instance of the
  restated `Odd.lambda_frobenius_sign` (`F²` the Frobenius of `k₀ = 𝔽_{ℓ₀²}`, `F` the arithmetic
  Frobenius over `𝔽_{ℓ₀}`);
* `geometric_row_eq_zero`: on the geometric points of a reduced elliptic curve at an odd prime,
  over a separably closed field, every additive map to `ℤ/2^M` is zero (multiplication by `2^M` is
  onto, Tau Ceti's `nsmul_surjective`). So the old form of `Odd.lambda_frobenius_sign`, whose row
  lived on all geometric points, applied only to the zero row.

Every theorem in this file is PROVED.
-/

noncomputable section

open scoped WeierstrassCurve
open WeierstrassCurve

namespace ZInQ.Manuscript.RC.Stages

section Abstract

variable {X : Type*} [AddCommGroup X] (F : X →+ X) (n : ℕ)
  (hdiv : Function.Surjective (fun R : X => n • R))
  (htriv : ∀ t : X, n • t = 0 → F (F t) = t)

/-- **PROVED.** The stage Frobenius on finite torsion is lane RC12's restriction
`Odd.torsionRestrict`. -/
theorem torsionFrob_eq_torsionRestrict : torsionFrob F n = Odd.torsionRestrict n F :=
  rfl

/-- **PROVED.** The stage Kummer value is lane RC12's `Odd.kummerTorsion` at `F²` (tex 8382). -/
theorem kappa_eq_kummerTorsion (P : FixedSq F) {R : X} (hR : n • R = P.val) :
    kappa F n hdiv htriv P =
      Odd.kummerTorsion (F.comp F) n ((mem_fixedSq F).mp P.property) hR :=
  Subtype.ext (kappa_apply F n hdiv htriv P hR)

/-- **PROVED (tex 8389–8390, 8452–8456).** The stage form of the Frobenius sign,
`lambda_frobenius_plus`, from the restated `Odd.lambda_frobenius_sign`: the row `b` lives on the
finite torsion `E[n]` and is fixed there by Frobenius (`bC = b`). -/
theorem lambda_frobenius_plus_of_odd {B : Type*} [AddCommGroup B]
    (b : AddSubgroup.torsionBy X (n : ℤ) →+ B) (hb : ∀ T, b (torsionFrob F n T) = b T)
    (P : FixedSq F) :
    (b.comp (kappa F n hdiv htriv)) (fixedFrob F P) = (b.comp (kappa F n hdiv htriv)) P := by
  obtain ⟨R, hR⟩ := hdiv P.val
  change n • R = P.val at hR
  have hFR : n • F R = (fixedFrob F P).val := by rw [← map_nsmul, hR]; rfl
  simp only [AddMonoidHom.comp_apply]
  rw [kappa_eq_kummerTorsion F n hdiv htriv _ hFR, kappa_eq_kummerTorsion F n hdiv htriv P hR]
  exact Odd.lambda_frobenius_sign (F.comp F) n F (fun _ => rfl) b hb _ hR

end Abstract

section Reduced

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Algebra (ZMod p) K]

/-- **PROVED.** `2^M ≠ 0` in a field of odd characteristic `p`. -/
theorem two_pow_ne_zero_of_odd (hp : p ≠ 2) (M : ℕ) : ((2 ^ M : ℕ) : K) ≠ 0 := by
  push_cast
  refine pow_ne_zero _ ?_
  have hz : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).not.mpr hp
  intro h
  apply hz
  apply (algebraMap (ZMod p) K).injective
  rw [map_ofNat, map_zero]
  exact h

variable [DecidableEq K] (E : WeierstrassCurve (ZMod p))

/-- **PROVED (why the row lives on the finite torsion).** On the geometric points of a reduced
elliptic curve at an odd prime `p`, over a separably closed field, every additive map to `ℤ/2^M`
is zero: multiplication by `2^M` is onto (Tau Ceti's `nsmul_surjective`) and `2^M` kills `ℤ/2^M`.
The old form of `Odd.lambda_frobenius_sign`, with its row on all geometric points, therefore applied
only to the zero row. -/
theorem geometric_row_eq_zero [IsSepClosed K] [E.IsElliptic] (hp : p ≠ 2) (M : ℕ)
    (b : (E⁄K).toAffine.Point →+ ZMod (2 ^ M)) : b = 0 := by
  refine Odd.addMonoidHom_eq_zero_of_divisible (2 ^ M) (fun x => ?_) (fun y => ?_) b
  · exact (E⁄K).toAffine.nsmul_surjective (two_pow_ne_zero_of_odd (K := K) hp M) x
  · rw [nsmul_eq_mul]
    simp

end Reduced

end ZInQ.Manuscript.RC.Stages
