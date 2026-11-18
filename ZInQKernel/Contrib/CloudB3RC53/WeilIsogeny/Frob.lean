import ZInQKernel.Contrib.CloudB3RC53.WeilIsogeny.Pairing
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Galois
import ZInQKernel.Contrib.CloudB3RC53.Frobenius.Points

/-!
# The Frobenius and the Weil pairing: `e_N(π S, π T) = e_N(S, T)^q`

Let `W` be an elliptic curve over a finite field `F` with `q` elements and `K ⊇ F` a separably
closed algebraic extension. The base-changed Frobenius `π` acts on the points of `W_K` as the
arithmetic Frobenius `σ : x ↦ x^q` of `K/F` (`pointGaloisAction_frobenius`, from
`pointMap_frobeniusMap_some`). The Weil pairing is Galois-equivariant (Tau Ceti's
`weilPairing_torsionGaloisAction`) and `σ` raises roots of unity to the `q`-th power, so
`e_N(σ S, σ T) = e_N(S, T)^q` (`weilPairing_frobenius`).

Classification: PROVED.
-/

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine TauCeti TauCeti.Isogeny

namespace ZInQ.Contrib.CloudB3RC53.WeilIsogeny

variable {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F) [W.IsElliptic]
  {K : Type*} [Field K] [DecidableEq K] [Algebra F K] [IsSepClosed K] [Algebra.IsAlgebraic F K]

/-- **The base-changed Frobenius acts on points as the arithmetic Frobenius.** PROVED. -/
theorem pointGaloisAction_frobenius (P : (W⁄K).toAffine.Point) :
    Multiplicative.toAdd (W.pointGaloisAction (FiniteField.frobeniusAlgEquivOfAlgebraic F K)) P =
      (Hom.ofIsogeny (Frobenius.frobeniusMap W.toAffine (algebraMap F K))).pointMap P := by
  rw [pointGaloisAction_apply]
  rcases P with _ | ⟨a, b, h⟩
  · exact (Hom.pointMap_zero _).symm
  · rw [Point.map_some]
    exact (Frobenius.pointMap_frobeniusMap_some W.toAffine (algebraMap F K) (a := a) (b := b)
      h).symm

variable (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)

/-- **`e_N(σ S, σ T) = e_N(S, T)^q`** for the arithmetic Frobenius `σ`. PROVED. -/
theorem weilPairing_frobenius (S T : Submodule.torsionBy ℤ (W⁄K).toAffine.Point (N : ℤ)) :
    weilPairing (W⁄K) N hN
        (Multiplicative.toAdd (W.torsionGaloisAction N
          (FiniteField.frobeniusAlgEquivOfAlgebraic F K)) S)
        (Multiplicative.toAdd (W.torsionGaloisAction N
          (FiniteField.frobeniusAlgEquivOfAlgebraic F K)) T) =
      Fintype.card F • weilPairing (W⁄K) N hN S T := by
  rw [weilPairing_torsionGaloisAction]
  apply Additive.toMul.injective
  rw [toMul_nsmul, toMul_ofMul]
  ext
  simp [restrictRootsOfUnity_coe_apply]

end ZInQ.Contrib.CloudB3RC53.WeilIsogeny
