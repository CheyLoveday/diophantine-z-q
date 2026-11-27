import ZInQKernel.Contrib.OneProof.BergerComparison.FrobeniusGenerator
import Mathlib.RingTheory.AdicCompletion.RingHom

/-! Evaluation of restricted Witt series in a p-adically complete target.
Modulo p^k a restricted series is an actual polynomial, so no topology
on the target beyond completeness for the principal ideal is used. -/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4 BergerBst PowerSeries Ideal
open PanBergerSplit (Ainf)

variable (p : ℕ) [Fact p.Prime]

private abbrev pIdeal (S : Type*) [CommRing S] : Ideal S := Ideal.span {(p : S)}

private theorem coeff_reduction_zero {S : Type*} [CommRing S] (g : Ainf p →+* S) (k : ℕ)
    {a : Ainf p} (ha : (p : Ainf p)^k ∣ a) :
    Ideal.Quotient.mk (pIdeal p S ^ k) (g a) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  simpa only [map_pow, map_natCast] using map_dvd g ha

private abbrev reduceCoeffs {S : Type*} [CommRing S] (g : Ainf p →+* S) (k : ℕ) :=
  (PowerSeries.map ((Ideal.Quotient.mk (pIdeal p S ^ k)).comp g)).comp (restricted p).subtype

private theorem reduceCoeffs_exists {S : Type*} [CommRing S] (g : Ainf p →+* S)
    (k : ℕ) (f : restricted p) : ∃ Q : Polynomial (S ⧸ pIdeal p S ^ k),
    (Q : (S ⧸ pIdeal p S ^ k)⟦X⟧) = reduceCoeffs p g k f := by
  obtain ⟨N, hN⟩ := f.property k
  refine ⟨Polynomial.map ((Ideal.Quotient.mk (pIdeal p S ^ k)).comp g) (trunc N f.val), ?_⟩
  ext n
  simp only [Polynomial.coeff_coe, Polynomial.coeff_map, coeff_trunc,
    RingHom.comp_apply, Subring.subtype_apply, PowerSeries.coeff_map]
  split_ifs with h
  · rfl
  · rw [map_zero, map_zero]
    exact (coeff_reduction_zero p g k (hN n (le_of_not_gt h))).symm

private def reducePolynomial {S : Type*} [CommRing S] (g : Ainf p →+* S)
    (k : ℕ) : restricted p →+* Polynomial (S ⧸ pIdeal p S ^ k) where
  toFun f := Classical.choose (reduceCoeffs_exists p g k f)
  map_one' := Polynomial.coe_injective _ (by
    rw [Classical.choose_spec (reduceCoeffs_exists p g k 1), map_one, Polynomial.coe_one])
  map_zero' := Polynomial.coe_injective _ (by
    rw [Classical.choose_spec (reduceCoeffs_exists p g k 0), map_zero, Polynomial.coe_zero])
  map_mul' a b := Polynomial.coe_injective _ (by
    rw [Classical.choose_spec (reduceCoeffs_exists p g k (a * b)), Polynomial.coe_mul,
      Classical.choose_spec (reduceCoeffs_exists p g k a),
      Classical.choose_spec (reduceCoeffs_exists p g k b), map_mul])
  map_add' a b := Polynomial.coe_injective _ (by
    rw [Classical.choose_spec (reduceCoeffs_exists p g k (a + b)), Polynomial.coe_add,
      Classical.choose_spec (reduceCoeffs_exists p g k a),
      Classical.choose_spec (reduceCoeffs_exists p g k b), map_add])

private theorem reducePolynomial_coeff {S : Type*} [CommRing S] (g : Ainf p →+* S)
    (k : ℕ) (f : restricted p) (n : ℕ) :
    (reducePolynomial p g k f).coeff n =
      Ideal.Quotient.mk (pIdeal p S ^ k) (g (coeff n f.val)) := by
  have h := congrArg (coeff n) (Classical.choose_spec (reduceCoeffs_exists p g k f))
  simpa only [Polynomial.coeff_coe, reducePolynomial, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, RingHom.comp_apply, Subring.subtype_apply, PowerSeries.coeff_map] using h

private def evalMod {S : Type*} [CommRing S] (g : Ainf p →+* S) (x : S) (k : ℕ) :
    restricted p →+* S ⧸ pIdeal p S ^ k :=
  (Polynomial.evalRingHom (Ideal.Quotient.mk _ x)).comp (reducePolynomial p g k)

private theorem evalMod_compat {S : Type*} [CommRing S] (g : Ainf p →+* S) (x : S)
    {k l : ℕ} (hkl : k ≤ l) :
    (Ideal.Quotient.factorPow (pIdeal p S) hkl).comp (evalMod p g x l) = evalMod p g x k := by
  ext f
  let q := Ideal.Quotient.factorPow (pIdeal p S) hkl
  have hq : Polynomial.map q (reducePolynomial p g l f) = reducePolynomial p g k f := by
    ext n
    simp only [Polynomial.coeff_map, reducePolynomial_coeff]
    rfl
  change q ((reducePolynomial p g l f).eval (Ideal.Quotient.mk _ x)) =
    (reducePolynomial p g k f).eval (Ideal.Quotient.mk _ x)
  rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, hq]
  rfl

/-- Evaluate a restricted power series at an arbitrary element of an integral
p-adically complete target, after applying a ring map to its coefficients. -/
def restrictedEval {S : Type*} [CommRing S] [IsAdicComplete (pIdeal p S) S]
    (g : Ainf p →+* S) (x : S) : restricted p →+* S :=
  IsAdicComplete.liftRingHom (pIdeal p S) (evalMod p g x) (evalMod_compat p g x)

theorem restrictedEval_polynomial {S : Type*} [CommRing S] [IsAdicComplete (pIdeal p S) S]
    (g : Ainf p →+* S) (x : S) (Q : Polynomial (Ainf p))
    (hQ : (Q : (Ainf p)⟦X⟧) ∈ restricted p) :
    restrictedEval p g x ⟨Q, hQ⟩ = Q.eval₂ g x := by
  apply (IsHausdorff.eq_iff_smodEq (I := pIdeal p S)).mpr
  intro k
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
  rw [restrictedEval, IsAdicComplete.mk_liftRingHom]
  let q := Ideal.Quotient.mk (pIdeal p S ^ k)
  have hq : reducePolynomial p g k ⟨Q, hQ⟩ = Polynomial.map (q.comp g) Q := by
    ext n
    rw [reducePolynomial_coeff, Polynomial.coeff_coe, Polynomial.coeff_map, RingHom.comp_apply]
  change (reducePolynomial p g k ⟨Q, hQ⟩).eval (q x) = q (Q.eval₂ g x)
  rw [hq, Polynomial.eval_map, Polynomial.hom_eval₂]

end ZInQ.Manuscript.BergerComparison
