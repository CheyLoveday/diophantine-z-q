import ZInQKernel.Contrib.CloudB3RC53.WeilIsogeny.Frob
import ZInQKernel.Contrib.CloudB3RC53.Frobenius.DegreeOneSub

/-!
# `deg(n π − m) = m² − a m n + q n²`

Let `W` be an elliptic curve over a finite field `F` with `q` elements, `a = q + 1 − |W(F)|`, and
`π` the base change of its Frobenius to a separably closed algebraic extension `K`. For integers
`m, n` with `m ≠ 0` in `K`, the morphism `n π − m` is a separable isogeny `ψ_{m,n}` (Tau Ceti's
differential criterion; `π^* ω = 0`) and

    deg ψ_{m,n} = m² − a m n + q n²        (`degree_psi`).

Proof: for `S, T ∈ W[N]` (`N` invertible), the compatibility of the Weil pairing with separable
isogenies (`weilPairing_torsionMap`), bilinearity, `e_N(π S, π T) = e_N(S, T)^q`
(`weilPairing_frobenius`) and the case `m = n = 1` (`deg(π − 1) = |W(F)|`) give
`e_N(S, T)^{deg ψ} = e_N(S, T)^{m² − amn + qn²}` (`weilPairing_degree`). At a prime `N = ℓ ≠ p` some
`e_ℓ(S, T)` is a primitive `ℓ`-th root of unity (nondegeneracy), so `ℓ` divides the difference of
the exponents; as `ℓ` is arbitrary, the exponents agree.

Classification: PROVED.
-/

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine TauCeti TauCeti.Isogeny

namespace ZInQ.Contrib.CloudB3RC53.WeilIsogeny

variable {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F) [W.IsElliptic]
  {K : Type*} [Field K] [DecidableEq K] [Algebra F K] [IsSepClosed K] [Algebra.IsAlgebraic F K]

/-- The trace of Frobenius `a = q + 1 − |W(F)|`. -/
def traceFrob : ℤ := Fintype.card F + 1 - Nat.card W.toAffine.Point

/-- The Frobenius of `W` base-changed to `K`, as an endomorphism of `W_K`. -/
def piK : Hom (W⁄K).toAffine (W⁄K).toAffine :=
  Hom.ofIsogeny (Frobenius.frobeniusMap W.toAffine (algebraMap F K))

omit [W.IsElliptic] [DecidableEq K] [IsSepClosed K] [Algebra.IsAlgebraic F K] in
theorem piK_pullbackDifferential :
    (piK W (K := K)).pullbackDifferential (invariantDifferential (W⁄K).toAffine) = 0 :=
  Frobenius.hom_pullbackDifferential_frobeniusMap W.toAffine (algebraMap F K)

omit [DecidableEq K] [IsSepClosed K] [Algebra.IsAlgebraic F K] in
/-- `n π − m ≠ 0` when `m ≠ 0` in `K`. -/
theorem psi_ne_zero {m : ℤ} (n : ℤ) (hm : (m : K) ≠ 0) :
    n • piK W (K := K) - m • Hom.id (W⁄K).toAffine ≠ 0 :=
  Hom.zsmul_sub_zsmul_id_ne_zero_of_pullbackDifferential_eq_zero (piK_pullbackDifferential W) n m hm

/-- **The isogeny `ψ_{m,n} = n π − m`.** -/
def psi {m : ℤ} (n : ℤ) (hm : (m : K) ≠ 0) :
    Isogeny (W⁄K).toAffine (W⁄K).toAffine :=
  Hom.toIsogeny (psi_ne_zero W n hm)

instance psi_isSeparable {m : ℤ} (n : ℤ) (hm : (m : K) ≠ 0) :
    Algebra.IsSeparable (psi W n hm).fieldPullback.fieldRange (W⁄K).toAffine.FunctionField :=
  (Hom.isSeparable_toIsogeny_zsmul_sub_zsmul_id_iff_of_pullbackDifferential_eq_zero
    (piK_pullbackDifferential W) n m (psi_ne_zero W n hm)).mpr hm

omit [IsSepClosed K] in
theorem pointMap_psi {m : ℤ} (n : ℤ) (hm : (m : K) ≠ 0) (P : (W⁄K).toAffine.Point) :
    (Hom.ofIsogeny (psi W n hm)).pointMap P =
      n • Multiplicative.toAdd (W.pointGaloisAction
        (FiniteField.frobeniusAlgEquivOfAlgebraic F K)) P - m • P := by
  rw [psi, Hom.ofIsogeny_toIsogeny, Hom.sub_pointMap, Hom.zsmul_pointMap, Hom.zsmul_pointMap,
    Hom.id_pointMap, piK, pointGaloisAction_frobenius]
  rfl

omit [Algebra.IsAlgebraic F K] in
theorem degree_psi_one_one :
    (psi W (m := 1) 1 (by simp : ((1 : ℤ) : K) ≠ 0)).degree = Nat.card W.toAffine.Point := by
  rw [psi, ← Hom.degree_ofIsogeny, Hom.ofIsogeny_toIsogeny, one_zsmul, one_zsmul, piK]
  exact Frobenius.degree_frobeniusMap_sub_id W.toAffine (algebraMap F K)

variable (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)

include hN in
/-- **`e_N(S, T)^{deg ψ} = e_N(S, T)^{m² − amn + qn²}`.** PROVED. -/
theorem weilPairing_degree {m : ℤ} (n : ℤ) (hm : (m : K) ≠ 0)
    (S T : Submodule.torsionBy ℤ (W⁄K).toAffine.Point (N : ℤ)) :
    ((psi W n hm).degree : ℤ) • weilPairing (W⁄K) N hN S T =
      (m ^ 2 - traceFrob W * m * n + Fintype.card F * n ^ 2) • weilPairing (W⁄K) N hN S T := by
  set σ := FiniteField.frobeniusAlgEquivOfAlgebraic F K
  set e := weilPairing (W⁄K) N hN
  set A := Multiplicative.toAdd (W.torsionGaloisAction N σ) S
  set B := Multiplicative.toAdd (W.torsionGaloisAction N σ) T
  have hψ : ∀ {m' : ℤ} (n' : ℤ) (hm' : (m' : K) ≠ 0)
      (U : Submodule.torsionBy ℤ (W⁄K).toAffine.Point (N : ℤ)),
      torsionMap (psi W n' hm') N U =
        n' • (Multiplicative.toAdd (W.torsionGaloisAction N σ) U :
          Submodule.torsionBy ℤ (W⁄K).toAffine.Point (N : ℤ)) - m' • U := by
    intro m' n' hm' U
    apply Subtype.ext
    change (Hom.ofIsogeny (psi W n' hm')).pointMap U = _
    rw [pointMap_psi]
    simp [torsionGaloisAction_apply_coe]
    rfl
  have hAB : e A B = (Fintype.card F : ℤ) • e S T := by
    rw [natCast_zsmul]; exact weilPairing_frobenius W N hN S T
  have hexp : ∀ {m' : ℤ} (n' : ℤ) (hm' : (m' : K) ≠ 0),
      ((psi W n' hm').degree : ℤ) • e S T =
        (n' ^ 2 * Fintype.card F + m' ^ 2) • e S T - (n' * m') • (e A T + e S B) := by
    intro m' n' hm'
    have h := weilPairing_torsionMap (psi W n' hm') N hN S T
    rw [hψ, hψ] at h
    simp only [map_sub, map_zsmul, AddMonoidHom.sub_apply, AddMonoidHom.coe_smul,
      Pi.smul_apply] at h
    rw [natCast_zsmul, ← h, hAB]
    module
  have h11 := hexp (m' := 1) 1 (by simp)
  rw [degree_psi_one_one] at h11
  have htr : e A T + e S B = traceFrob W • e S T := by
    rw [traceFrob]
    linear_combination (norm := module) h11
  rw [hexp n hm, htr]
  module

end ZInQ.Contrib.CloudB3RC53.WeilIsogeny
