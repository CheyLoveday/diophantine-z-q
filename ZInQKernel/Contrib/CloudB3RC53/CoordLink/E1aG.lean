import ZInQKernel.Contrib.CloudB3RC53.CoordLink.OrigCoord

/-!
# E1a over the genuine identification `Identification2G`

Manuscript `diophantine_zq.tex`, tex 4219–4222 (`ũ = η u_rel`), 3877–3892 and 5513–5516 (the
relaxed coordinate is the coordinate of the original complex), 5510–5512 (`κ = det B`).

`CoordLink/E1a.lean` reduces E1a (`CoordLink`) to `CorrectedIsEta` and `RelIsKM`, but only for the
strengthened identification `Identification2`, whose new places are term-level tame models that
genuine continuous cochains cannot instantiate. For the genuine identification `Identification2G`
(`ClearingComplex/GenuineIdentification.lean`), E1a was a bare hypothesis of
`clearingInputsCx_of_kmG`. This file supplies the same reduction for `Identification2G`:

* `kappaOfG`, `isUnit_kappaG`: `κ = det B ∈ 𝒪[G]`, an `S`-unit.
* `RelIsKMG` (GLUE): where `Δ_x ≠ 0`, `u_{rel,x}` is the Knudsen–Mumford coordinate `kmOrig` of
  the sign-evaluated pre-cancellation complex of `M` (`OrigCoord.lean`).
* **`coordLink_of_kmG` (PROVED)**: `CorrectedIsEta` and `RelIsKMG` give E1a,
  `ũ_x = η_x κ_x c_x` with `c = cOf M.D z μ`, `μ = λ ∘ incl` (the generic core
  `coordLink_core`).
* **`clearingInputsCx_of_kmG_of_km` (PROVED)**: the body of RC0's `ClearingInputsCx` from
  `Identification2G` data together with `CorrectedIsEta` and `RelIsKMG`, with no bare E1a
  hypothesis left. `CorrectedIsEta` follows from (4.7) by `correctedIsEta_of_47`.
* `relIsKMG_kmOrig`: `RelIsKMG` holds for `u_rel := kmOrig`, so its content is the identification
  of the relaxed coordinate with `kmOrig`, together with `CorrectedIsEta`.

(No witness of `Identification2G` with nonempty new places exists, see
`GenuineIdentification.lean`; the reduction is stated for every such `M`.)

**Classification.** PROVED (`RelIsKMG`, `CorrectedIsEta` are the named GLUE).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.CoordLink

open Matrix NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.Torsion ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup evK uK sgnChar ScalarData)
open ZInQ.Manuscript.RC.SelmerComplex (NewPlaces)

variable {K : Type} [Field K] [NumberField K] {S S' : Set (HeightOneSpectrum (𝓞 K))}
  {hS : S ⊆ S'} [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')]
  {b dK hK cE tK : ℕ}

/-- **The determinant comparison factor** `κ = det B ∈ 𝒪[G]` of the genuine identification. -/
def kappaOfG (M : Identification2G K S S' hS b dK hK cE tK) : MonoidAlgebra OO (SignGroup b) :=
  (M.C.map (φO b)).B.det

/-- `κ` is an `S`-unit (tex 5510–5512). -/
theorem isUnit_kappaG (M : Identification2G K S S' hS b dK hK cE tK) : IsUnit (kappaOfG M) :=
  M.isUnit_B

/-- **GLUE: the relaxed coordinate is the Knudsen–Mumford coordinate of the original complex**
of the genuine identification, where `Δ_x ≠ 0` (tex 3877–3892, 5513–5516). -/
def RelIsKMG (M : Identification2G K S S' hS b dK hK cE tK) (urel : Addr b → FractionRing OO)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b))
    (hz : M.D.d1 *ᵥ z = 0) (hlam : lam ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0) :
    Prop :=
  ∀ x : Addr b, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 →
    urel x = kmOrig M z lam hz hlam x

/-- `RelIsKMG` holds for `u_rel := kmOrig` (its content is the identification of the relaxed
coordinate). -/
theorem relIsKMG_kmOrig (M : Identification2G K S S' hS b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b))
    (hz : M.D.d1 *ᵥ z = 0) (hlam : lam ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0) :
    RelIsKMG M (kmOrig M z lam hz hlam) z lam hz hlam :=
  fun _ _ => rfl

/-- **E1a over the genuine identification** (PROVED from `CorrectedIsEta` and `RelIsKMG`). -/
theorem coordLink_of_kmG {ℓ : ℕ} (Dd : RCData ℓ) (F : Family)
    (M : Identification2G K S S' hS F.b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup F.b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO F.b)).X (M.C.map (φO F.b)).Y = 0)
    (η : MonoidAlgebra OO (SignGroup F.b)) (urel : Addr F.b → FractionRing OO)
    (hη : CorrectedIsEta Dd F η urel) (hrel : RelIsKMG M urel z lam hz hlam) :
    ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
      CoordLink M.toIdentification.B (kappaOfG M) η 0 e g
        (cOf M.D z (transportFun (M.C.map (φO F.b)) lam) hz
          (hμ_cancel (M.C.map (φO F.b)) M.isUnit_B hlam)) :=
  coordLink_core Dd F (M.C.map (φO F.b)) M.isUnit_B M.toIdentification.B z lam hz hlam η urel
    hη hrel

/-- **RC0's `ClearingInputsCx` body from the genuine identification with E1a reduced** (PROVED):
the bare E1a hypothesis of `clearingInputsCx_of_kmG` is replaced by `CorrectedIsEta` and
`RelIsKMG`. -/
theorem clearingInputsCx_of_kmG_of_km {ℓ : ℕ} (Dd : RCData ℓ) (K : Type) [Field K]
    [NumberField K]
    (h : ∃ dK hK cE tK : ℕ, ∀ Co Ce : ℤ, ∀ F : Family, Dd.FinalFamilyAt Co Ce F →
      ∃ (S S' : Set (HeightOneSpectrum (𝓞 K))) (hS : S ⊆ S') (_ : Fintype (NewPlaces K S S'))
        (_ : DecidableEq (NewPlaces K S S')) (M : Identification2G K S S' hS F.b dK hK cE tK)
        (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b))
        (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup F.b))
        (hz : M.D.d1 *ᵥ z = 0)
        (hlam : lam ᵥ* fromRows (M.C.map (φO F.b)).X (M.C.map (φO F.b)).Y = 0)
        (η : MonoidAlgebra OO (SignGroup F.b)) (urel : Addr F.b → FractionRing OO),
        CorrectedIsEta Dd F η urel ∧ RelIsKMG M urel z lam hz hlam) :
    ∃ dK hK cE tK : ℕ, ∀ Co Ce : ℤ, ∀ F : Family, Dd.FinalFamilyAt Co Ce F →
      ∃ (I : SelmerIdentification F.b dK hK cE tK) (sd : ScalarData I.B)
        (κ ε η : MonoidAlgebra OO (SignGroup F.b)) (c : Addr F.b → FractionRing OO),
        CoordComputation I.B sd ε c I.D.RankOnePattern I.D.AcyclicPattern ∧
        ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
          CoordLink I.B κ η 0 e g c := by
  obtain ⟨dK, hK, cE, tK, hF⟩ := h
  refine clearingInputsCx_of_kmG Dd K ⟨dK, hK, cE, tK, fun Co Ce F hFam => ?_⟩
  obtain ⟨S, S', hS, i1, i2, M, z, lam, hz, hlam, η, urel, hη, hrel⟩ := hF Co Ce F hFam
  exact ⟨S, S', hS, i1, i2, M, z, transportFun (M.C.map (φO F.b)) lam, hz,
    hμ_cancel (M.C.map (φO F.b)) M.isUnit_B hlam, kappaOfG M, η,
    coordLink_of_kmG Dd F M z lam hz hlam η urel hη hrel⟩

end ZInQ.Contrib.CloudB3RC53.CoordLink
