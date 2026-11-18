import ZInQKernel.Contrib.CloudB3RC53.CoordLink.CoreExample
import ZInQKernel.Contrib.CloudB3RC53.Torsion.ConeCoord

/-!
# E1a, part 7: `PreCoreLink` from a retained comparison map

`PreCoreLink` (`RelCore.lean`: the pre-cancellation complex `C_x` and the integral two-term core of
the relaxed complex at `x` have the same Knudsen–Mumford coordinate) is derived from ONE named
input,
`RetainedComparison`, with stateable properties:

* a chain map `f : C_x → core` of four-term complexes (`FourMap`) with the augmented compatibility
  `f¹ z_x = z_core`, `λ_core f² = λ_x` (so `f` extends to the augmented complexes, `augMap`);
* the augmented `C_x` is acyclic;
* **the retained bases are compatible along `f`**: the torsion of the cone of the augmented `f` is
  the canonical sign `(−1)^{|κ_odd(aug C_x)|}` (the sign is fixed by the retained bases, so it is
  absorbed into the orientation).

Both `C_x` and the core are models of the relaxed Selmer complex at `x` (lane RC26's genuine
`galoisSelData`); `f` is the comparison of the two models and the cone condition says that it
carries the retained determinant basis to the retained determinant basis. (The comparison cannot be
stated literally against `galoisSelData`: the sign-evaluated model `C_x` over `Frac 𝒪` and the core
over `Λ` are not coefficient changes of one `SelData` in the project.)

* `kmCoord_eq_of_comparison`-style core: **`preCoreLink_of_comparison` (PROVED)**, by the cone
  invariance `kmCoord_eq_of_fourMap` (lane Torsion).
* `coordLink_of_comparison` (PROVED): E1a from the (4.7) data, the integral core and the retained
  comparison.
* `retainedComparison_ex` (LESSON 2): the input holds in the non-degenerate example of
  `CoreExample.lean` (corrected coordinate `−t`), with an explicit chain map.

**Caveat (round 4).** The core route takes an integral core with exact augmentation at EVERY
address (`core : Addr → IntegralCore`, `hcore : ∀ x, …`). RC0's `integralCore_coord_ne_zero` /
`uTilde_ne_zero_of_core` (`RC/Wiring/ClearingComplex4Bridge.lean`) show that this forces `ũ_x ≠ 0`
everywhere, which fails at generically acyclic constituents (tex 3889–3890, 5612–5615): as stated,
this route applies only to families with no degenerate constituent. RC0's input is now ONE GLUE,
`OrigCoordLink` (`RC/Wiring/ClearingComplex4.lean`); `CoordLink/OrigCoord.lean`
(`origCoordLink_of_cases`) reduces it by cases, using the core only where `c^{orig}_x ≠ 0`.

**Classification.** PROVED (`RetainedComparison` is the named GLUE).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.CoordLink

open Matrix ZInQ.Contrib.CloudB3RC53.Torsion ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup evK uK sgnChar)

variable {b dK hK cE tK : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 512 in
/-- **GLUE: the retained comparison** of the sign-evaluated pre-cancellation complex `C_x` with the
two-term core `[K^n --D--> K^n]` (class `z_c`, functional `w_c`): a chain map with the augmented
compatibility, `aug C_x` acyclic, and the cone of the augmented map of torsion the canonical
sign. -/
def RetainedComparison (M : Identification2 b dK hK cE tK) (x : Addr b)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b))
    (hz : M.D.d1 *ᵥ z = 0) (hlam : lam ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0)
    {n : ℕ} (D : Matrix (Fin n) (Fin n) (FractionRing OO)) (zc wc : Fin n → FractionRing OO)
    (hzc : (twoTerm D).d1 *ᵥ zc = 0) (hwc : wc ᵥ* (twoTerm D).d1 = 0) : Prop :=
  ∃ (F : FourMap (PreComplex'.toFour (Cev (M.C.map (φO b)) x)) (twoTerm D))
    (hzF : F.f1 *ᵥ (evK (sgnChar x) ∘ z) = zc) (hlF : wc ᵥ* F.f2 = evK (sgnChar x) ∘ lam),
    Nonempty (Contraction ((PreComplex'.toFour (Cev (M.C.map (φO b)) x)).aug
      (evK (sgnChar x) ∘ z) (evK (sgnChar x) ∘ lam) (hzev (hzC M.isUnit_B hz) x)
      (hlamev hlam x)).toBased) ∧
    torsion (BasedCx.cone (F.augMap _ _ (hzev (hzC M.isUnit_B hz) x) (hlamev hlam x) zc wc hzc
        hwc hzF hlF)) ((σ₀ n).sumCongr (σPre M.C.m0 M.C.m1 M.C.m2 M.C.N).symm) =
      (-1) ^ Fintype.card ((Fin M.C.m0 ⊕ Unit ⊕ Fin M.C.m1) ⊕ ((Fin M.C.m2 ⊕ M.C.N) ⊕ Unit))

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 512 in
/-- **`PreCoreLink` from the retained comparison** (PROVED; cone invariance of the coordinate). -/
theorem preCoreLink_of_comparison (M : Identification2 b dK hK cE tK) (x : Addr b)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b))
    (hz : M.D.d1 *ᵥ z = 0) (hlam : lam ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0)
    {n : ℕ} (D : Matrix (Fin n) (Fin n) (FractionRing OO)) (zc wc : Fin n → FractionRing OO)
    (hzc : (twoTerm D).d1 *ᵥ zc = 0) (hwc : wc ᵥ* (twoTerm D).d1 = 0)
    (hDc : Nonempty (Contraction ((twoTerm D).aug zc wc hzc hwc).toBased))
    (h : RetainedComparison M x z lam hz hlam D zc wc hzc hwc) :
    PreCoreLink M x z lam hz hlam D zc wc hzc hwc := by
  obtain ⟨F, hzF, hlF, ⟨hC⟩, hcone⟩ := h
  obtain ⟨hD⟩ := hDc
  unfold PreCoreLink
  exact kmCoord_eq_of_fourMap_retained F _ _ _ _ zc wc hzc hwc hzF hlF hC hD
    (σPre M.C.m0 M.C.m1 M.C.m2 M.C.N) (σ₀ n) hcone

/-- **E1a from the (4.7) data, the integral core and the retained comparison** (PROVED). -/
theorem coordLink_of_comparison {ℓ : ℕ} (Dd : RCData ℓ) (F : Family)
    (M : Identification2 F.b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup F.b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO F.b)).X (M.C.map (φO F.b)).Y = 0)
    (ηΛ : MonoidAlgebra Lam (SignGroup F.b))
    (hunit : ∀ x : Addr F.b, IsUnit (Determinant.signEval (sgnChar x) ηΛ)) (e₀ : Addr F.b → ℕ)
    (g₀ : Addr F.b → Lam) (h₀ : UTildeRep Dd F e₀ g₀)
    (T : ∀ x, CommonCoordinateTrianglesN Dd F x)
    (hcompat : ∀ x, (T x).chi (Central.eta (T x).Q (T x).v (T x).g) =
      ιQ (Determinant.signEval (sgnChar x) ηΛ))
    (core : Addr F.b → IntegralCore)
    (hcore : ∀ x, Central.IsClassFunctionalCoord ((core x).D.map ιQ) (ιQ ∘ (core x).zc)
      (ιQ ∘ (core x).wc) (T x).urel)
    (hcomp : ∀ x, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 →
      RetainedComparison M x z lam hz hlam ((core x).D.map ψO) (ψO ∘ (core x).zc)
        (ψO ∘ (core x).wc) (core x).hz (core x).hw) :
    ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
      CoordLink M.toIdentification.B (kappaOf M) (φO F.b ηΛ) 0 e g
        (cOf M.D z (transportFun (M.C.map (φO F.b)) lam) hz
          (hμ_cancel (M.C.map (φO F.b)) M.isUnit_B hlam)) :=
  coordLink_of_triangles_core Dd F M z lam hz hlam ηΛ hunit e₀ g₀ h₀ T hcompat core hcore
    fun x hΔ => preCoreLink_of_comparison M x z lam hz hlam _ _ _ _ _
      (exists_contraction _ (FourCx.isExact_toBased _ (core x).exact)) (hcomp x hΔ)

end ZInQ.Contrib.CloudB3RC53.CoordLink
