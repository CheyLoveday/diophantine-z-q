import ZInQKernel.Contrib.CloudB3RC53.Frobenius.Differential
import ZInQKernel.Contrib.CloudB3RC53.Frobenius.FixedPoints
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Fiber
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Neg
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# `deg(1 − π) = #E(𝔽_q)`

For an elliptic curve `E = W` over a finite field `F` with `q` elements, and the base change `π` of
its `q`-power Frobenius to a separably closed field `K ⊇ F` (e.g. `\bar F`), the endomorphism
`1 − π` of `E_K` has degree `#E(F)` (`degree_id_sub_frobeniusMap`; Silverman V.1.1, first step of
the proof of Hasse's bound).

* `1 − π ≠ 0` and it is separable: `π^* ω = 0` (`hom_pullbackDifferential_frobeniusMap`), so Tau
  Ceti's differential criterion applies to `r π − s` with `r = s = 1`
  (`zsmul_sub_zsmul_id_ne_zero_of_pullbackDifferential_eq_zero`,
  `isSeparable_toIsogeny_zsmul_sub_zsmul_id_iff_of_pullbackDifferential_eq_zero`).
* A separable isogeny over a separably closed field has `#ker = deg` (Tau Ceti's
  `card_ker_toPointHom_eq_degree`).
* The kernel of `π − 1` is the set of Frobenius-fixed points (`pointMap` is additive in the morphism
  and agrees with the class-group point map for separable isogenies), which is `E(F)`
  (`natCard_fixedPoints`).

Classification: PROVED.
-/

noncomputable section

open WeierstrassCurve.Affine

namespace ZInQ.Contrib.CloudB3RC53.Frobenius

open TauCeti

variable {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]
  {K : Type*} [Field K] [IsSepClosed K] [DecidableEq K] (f : F →+* K)

/-- **`deg(π − 1) = #E(F)`** over a separably closed field. PROVED. -/
theorem degree_frobeniusMap_sub_id :
    (Isogeny.Hom.ofIsogeny (frobeniusMap W f) - Isogeny.Hom.id (W.map f)).degree =
      Nat.card W.Point := by
  have hπ := hom_pullbackDifferential_frobeniusMap W f
  have hs : ((1 : ℤ) : K) ≠ 0 := by simp
  have hne := Isogeny.Hom.zsmul_sub_zsmul_id_ne_zero_of_pullbackDifferential_eq_zero hπ 1 1 hs
  have hsep :=
    (Isogeny.Hom.isSeparable_toIsogeny_zsmul_sub_zsmul_id_iff_of_pullbackDifferential_eq_zero
      hπ 1 1 hne).mpr hs
  have h1 : (1 : ℤ) • Isogeny.Hom.ofIsogeny (frobeniusMap W f) - (1 : ℤ) • Isogeny.Hom.id (W.map f) =
      Isogeny.Hom.ofIsogeny (frobeniusMap W f) - Isogeny.Hom.id (W.map f) := by
    simp only [one_zsmul]
  have hdeg : ((1 : ℤ) • Isogeny.Hom.ofIsogeny (frobeniusMap W f) -
      (1 : ℤ) • Isogeny.Hom.id (W.map f)).degree = (Isogeny.Hom.toIsogeny hne).degree := by
    rw [← Isogeny.Hom.degree_ofIsogeny, Isogeny.Hom.ofIsogeny_toIsogeny]
  have := (W.map f).isIntegrallyClosed_coordinateRing
  have := (W.map f).isDedekindDomain_coordinateRing_of_isIntegrallyClosed
  rw [← h1, hdeg, ← Isogeny.card_ker_toPointHom_eq_degree, ← natCard_fixedPoints W f]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun P => ?_)
  rw [AddMonoidHom.mem_ker, ← Isogeny.Hom.pointMap_ofIsogeny_eq_toPointHom,
    Isogeny.Hom.ofIsogeny_toIsogeny, Isogeny.Hom.sub_pointMap, Isogeny.Hom.zsmul_pointMap,
    Isogeny.Hom.zsmul_pointMap, one_zsmul, one_zsmul, Isogeny.Hom.id_pointMap, sub_eq_zero]

/-- **`deg(1 − π) = #E(F)`** over a separably closed field (Silverman V.1.1). PROVED. -/
theorem degree_id_sub_frobeniusMap :
    (Isogeny.Hom.id (W.map f) - Isogeny.Hom.ofIsogeny (frobeniusMap W f)).degree =
      Nat.card W.Point := by
  rw [← neg_sub, Isogeny.Hom.degree_neg, degree_frobeniusMap_sub_id]

omit [IsSepClosed K] [DecidableEq K] in
/-- **`deg(1 − π) = #E(𝔽_q)` over `\bar{𝔽}_q`**, for the Frobenius of `E` base-changed to the
algebraic closure. PROVED. -/
theorem degree_id_sub_frobenius_algebraicClosure :
    letI := Classical.decEq (AlgebraicClosure F)
    (Isogeny.Hom.id (W.map (algebraMap F (AlgebraicClosure F))) -
        Isogeny.Hom.ofIsogeny (frobeniusMap W (algebraMap F (AlgebraicClosure F)))).degree =
      Nat.card W.Point :=
  letI := Classical.decEq (AlgebraicClosure F)
  degree_id_sub_frobeniusMap W _

/-- **Node `DegreeOneSubFrobenius`** (Silverman V.1.1, first step of the proof of Hasse's bound;
infrastructure towards `LocalFactorInert`, not a manuscript line): for every elliptic curve `E`
over a finite field `𝔽_q`, the endomorphism `1 − π` of `E` over `\bar{𝔽}_q` has degree `#E(𝔽_q)`.
PROVED (`degreeOneSubFrobenius_proof`). -/
def DegreeOneSubFrobenius : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (W : WeierstrassCurve.Affine F) [W.IsElliptic],
    letI := Classical.decEq (AlgebraicClosure F)
    (Isogeny.Hom.id (W.map (algebraMap F (AlgebraicClosure F))) -
        Isogeny.Hom.ofIsogeny (frobeniusMap W (algebraMap F (AlgebraicClosure F)))).degree =
      Nat.card W.Point

theorem degreeOneSubFrobenius_proof : DegreeOneSubFrobenius :=
  fun _ _ _ W _ => degree_id_sub_frobenius_algebraicClosure W

end ZInQ.Contrib.CloudB3RC53.Frobenius
