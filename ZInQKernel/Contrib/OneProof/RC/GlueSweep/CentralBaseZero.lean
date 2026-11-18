import ZInQKernel.Contrib.OneProof.RC.Height.Discharge
import ZInQKernel.Contrib.OneProof.RC.Height.ArtinG2
import ZInQKernel.Contrib.OneProof.RC.Rings.LambdaT
import ZInQKernel.Contrib.CloudB3RC53.MinimalComplexes.BaseZeroBridge
import ZInQKernel.Contrib.CloudB3RC53.BaseZeroEndToEnd.TwoTerm

/-!
# Lane RC22 (glue sweep, central share): the base-zero node with its discharged inputs removed

Lemma `ex:arith-base-zero` of the 11/5 manuscript (`diophantine_zq.tex`, lines 4330–4373). Lane
RC15 produces the shared top layer's node `BaseZero E k C` as
`ZInQ.Manuscript.RC.Central.baseZero_node`, from these inputs (kinds as recorded by lane RC15):

* `CSTThm11`, `hCST`, `hheight` (PRINT and its application, tex 4345–4346: "the conductor-one height
  formula makes the specified point torsion");
* `hρ` and `hcoef` (the residue map kills the maximal ideal; GLUE identification of the package's
  datum `C.u 0 0` with the central value of `ũ₀`);
* the two-term model `D` with `hcentral` (DEPARTURE of form plus the GLUE minimal-complex
  cancellation, tex 4353–4368; the ELLIOT input "full Selmer corank one gives central dimensions
  `(1,1)`", tex 4350–4352);
* `hu` (definition), `h45`, `h47` (ELLIOT).

Three of these have since been proved in the project:

* `hheight` by lane RC19, `ZInQ.Manuscript.RC.Height.hheight_of_CST` (from the project's statement
  of Cai–Shu–Tian, the conductor-one Heegner data, the trace identity `hP` and lane RC19's GLUE
  `LFactorizationConductorOne`); RC19 composed it into `baseZero_node_of_CST`, which still takes
  `hρ` and `hcoef` over an abstract DVR;
* `hρ` and `hcoef` by lane RC20 over the genuine `A = Λ_(t)` (`rhoT_maximalIdeal`,
  `hcoef_of_lambdaHalf`); RC20 composed them into `baseZero_node_genuine`, which still takes
  `hheight`;
* the minimal-complex cancellation by the shared top layer's `MinimalComplexes`
  (`centralTwoTermModelAt_proof`: an actual bounded finite free complex over a local ring with
  central dimensions `(1,1)` in degrees one and two and zero elsewhere is, after a degree-preserving
  change of bases, unit disks plus a two-term model `(δ)` with `hcentral`); it was composed only with
  `baseZero_core`, not with the node.

This file composes them, so that no discharged input remains.

* `baseZero_node_genuine_of_CST`: `hheight`, `hρ`, `hcoef` all removed (RC19 + RC20).
* `baseZero_node_of_complex`: the two-term model and `hcentral` replaced by the actual complex with
  its central dimensions (MinimalComplexes); other inputs as in RC15.
* `baseZero_node_genuine_of_complex_CST`: all three discharges together.
* `complex_hypotheses_nonvacuous`: the complex hypotheses that replace `D`, `hcentral` hold for the
  two-term complex of the zero `1 × 1` differential (over any local ring, any residue map), so the
  two complex forms are not vacuous on that account.
* Lane RC27 (item 7): `baseZero_node_of_CST_of_artin`, `baseZero_node_genuine_of_CST_of_artin`,
  `baseZero_node_genuine_of_complex_CST_of_artin`: the same nodes with RC19's GLUE
  `LFactorizationConductorOne E K k` replaced by the shared top layer's GLUE
  `GenusOdd.ArtinFactorization`, `K` split at `2` and `K = ℚ(√k)` (lane RC27's
  `lFactorizationConductorOne_of_artin`; non-vacuity of the conditions on `K`:
  `artinG2_field_hypotheses_nonvacuous`).

Every theorem in this file is PROVED (from the stated remaining inputs).
-/

noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory IsDedekindDomain Complex

namespace ZInQ.Manuscript.RC.GlueSweep.Central

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
  ZInQ.Contrib.CloudB3RC53.MinimalComplexes Matrix
open ZInQ.Manuscript.RC.Uniform (Lambda LambdaHalf lambdaHalfToFrac centralSpecialization)
open ZInQ.Manuscript.RC.Rings (LambdaT rhoT)
open ZInQ.Contrib.CloudB3RC53.BaseZeroEndToEnd (ttDeg ttDiff resDimAt_tt ttDiff_graded ttDiff_sq)

/-! ### `hheight`, `hρ` and `hcoef` removed -/

open Classical in
/-- **`BaseZero` from Lemma `ex:arith-base-zero` with `hheight`, `hρ` and `hcoef` discharged**
(tex 4330–4373; `A = Λ_(t)`, residue field `ℚ₂`, fraction field `F`: tex 4341–4342; height
formula: tex 4345–4346; `ũ₀ = ε₀ u_{prim,0}`: tex 4369–4373).

Consumer: lane RC15's `ZInQ.Manuscript.RC.Central.baseZero_node`. Dischargers: lane RC19's
`ZInQ.Manuscript.RC.Height.hheight_of_CST` (for `CSTThm11 := CSTThm11Split`, `hheight`) and lane
RC20's `ZInQ.Manuscript.RC.Rings.baseZero_node_genuine` (instantiating `A := Λ_(t)`,
`ρ := rhoT`, with `hρ := rhoT_maximalIdeal` and `hcoef := hcoef_of_lambdaHalf`).

PROVED, from the remaining inputs: ellipticity of `E`; the print `CSTThm11Split` (PRINT) with the
conductor-one Heegner data of its hypotheses (`f, Lat, scale, K, a₀ b₀ c₀, ι, y` and the side
conditions) and the trace identity `hP` ("the specified point", tex 4345); lane RC19's GLUE
`LFactorizationConductorOne E K k`; lane RC15's `hcentral` (ELLIOT), `hu` (definition), `h45`,
`h47` (ELLIOT); and lane RC20's replacement of `hcoef`: the corrected coordinate lies in `Λ[1/2]`
(`wHalf`, `hwHalf`) and the package's datum is its central value (`hC`). No hypothesis is new
relative to the two composed bridges. -/
theorem baseZero_node_genuine_of_CST {E : WeierstrassCurve ℚ} [E.IsElliptic] {k : ℚ} {b : ℕ}
    (C : CoordData b)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) (hnCM : IsNonCMLattice Lat)
    (scale : ℂ) (hscale : IsParamScale (newformLevel E) f Lat scale)
    (K : Type) [Field K] [NumberField K] [DecidableEq K] (hK2 : Module.finrank ℚ K = 2)
    (hKc : IsTotallyComplex K) (hD3 : discr K ≠ -3) (hD4 : discr K ≠ -4)
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p)
    (a₀ b₀ c₀ : ℤ) (hH : IsHeegnerForm (newformLevel E) (discr K * (1 : ℕ) ^ 2) a₀ b₀ c₀)
    (ι : ringClassField (conductorOrder K 1) →ₐ[ℚ] ℂ)
    (y : (E.baseChange (ringClassField (conductorOrder K 1))).toAffine.Point)
    (hy : Point.map (W' := E.toAffine) ι y =
      phiAn E f Lat scale (cmPoint a₀ b₀ (discr K * (1 : ℕ) ^ 2)))
    (P : (E.baseChange K).toAffine.Point)
    (hP : Point.baseChange K (ringClassField (conductorOrder K 1)) P =
      ∑ σ : ringClassField (conductorOrder K 1) ≃ₐ[K] ringClassField (conductorOrder K 1),
        Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) y)
    (hL : ZInQ.Manuscript.RC.Height.LFactorizationConductorOne E K k) (hCST : CSTThm11Split)
    {m : ℕ} (D : Matrix (Fin (m + 1)) (Fin (m + 1)) LambdaT) (hcentral : (D.map rhoT).rank = m)
    (z w : Fin (m + 1) → LambdaT) (hz : D *ᵥ z = 0) (uprim : FractionRing Lambda)
    (hu : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
      (D.map (algebraMap LambdaT (FractionRing Lambda)))
      (fun i => algebraMap LambdaT (FractionRing Lambda) (z i))
      (fun i => algebraMap LambdaT (FractionRing Lambda) (w i)) uprim)
    (kum : (E.baseChange K).toAffine.Point →+ (Fin (m + 1) → ℚ_[2])) (Lm : ℤ)
    (h45 : (fun i => rhoT (z i)) = (Lm : ℚ_[2]) • kum P)
    (ε₀ : LambdaT) (utilde0 : FractionRing Lambda)
    (h47 : utilde0 = algebraMap LambdaT (FractionRing Lambda) ε₀ * uprim)
    (wHalf : LambdaHalf) (hwHalf : lambdaHalfToFrac wHalf = utilde0)
    (hC : C.u 0 0 = centralSpecialization wHalf) :
    BaseZero E k C :=
  ZInQ.Manuscript.RC.Rings.baseZero_node_genuine C K P CSTThm11Split hCST
    (ZInQ.Manuscript.RC.Height.hheight_of_CST E k f hf Lat hLat hnCM scale hscale K hK2 hKc hD3
      hD4 hsplit a₀ b₀ c₀ hH ι y hy P hP hL)
    D hcentral z w hz uprim hu kum Lm h45 ε₀ utilde0 h47 wHalf hwHalf hC

open Classical in
/-- **RC15's `baseZero_node` with `hheight` discharged through `ArtinFactorization`** (tex
4319–4373; tex 5736 with tex 2599, 2720). PROVED: lane RC15's `Central.baseZero_node` with
`CSTThm11 := CSTThm11Split` and `hheight` from lane RC27's `hheight_of_CST_of_artin`. The inputs
are those of RC19's `baseZero_node_of_CST` with `hL` (RC19's GLUE) replaced by the shared top
layer's GLUE `GenusOdd.ArtinFactorization`, `K` split at `2` (`h2`) and `K = ℚ(√k)` (`t`, `ht`,
`htk`). -/
theorem baseZero_node_of_CST_of_artin {E : WeierstrassCurve ℚ} [E.IsElliptic] {k : ℚ} {b : ℕ}
    (C : CoordData b)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) (hnCM : IsNonCMLattice Lat)
    (scale : ℂ) (hscale : IsParamScale (newformLevel E) f Lat scale)
    (K : Type) [Field K] [NumberField K] [DecidableEq K] (hK2 : Module.finrank ℚ K = 2)
    (hKc : IsTotallyComplex K) (hD3 : discr K ≠ -3) (hD4 : discr K ≠ -4)
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p)
    (a₀ b₀ c₀ : ℤ) (hH : IsHeegnerForm (newformLevel E) (discr K * (1 : ℕ) ^ 2) a₀ b₀ c₀)
    (ι : ringClassField (conductorOrder K 1) →ₐ[ℚ] ℂ)
    (y : (E.baseChange (ringClassField (conductorOrder K 1))).toAffine.Point)
    (hy : Point.map (W' := E.toAffine) ι y =
      phiAn E f Lat scale (cmPoint a₀ b₀ (discr K * (1 : ℕ) ^ 2)))
    (P : (E.baseChange K).toAffine.Point)
    (hP : Point.baseChange K (ringClassField (conductorOrder K 1)) P =
      ∑ σ : ringClassField (conductorOrder K 1) ≃ₐ[K] ringClassField (conductorOrder K 1),
        Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) y)
    (hA : GenusOdd.ArtinFactorization) (h2 : SplitsIn K 2) (t : K)
    (ht : t ∉ (algebraMap ℚ K).range) (htk : t ^ 2 = algebraMap ℚ K k) (hCST : CSTThm11Split)
    {A F : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field F]
    [Algebra A F] [IsFractionRing A F] (ρ : A →+* ℚ_[2])
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) {m : ℕ}
    (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (hcentral : (Dm.map ρ).rank = m)
    (z w : Fin (m + 1) → A) (hz : Dm *ᵥ z = 0) (uprim : F)
    (hu : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord (Dm.map (algebraMap A F))
      (fun i => algebraMap A F (z i)) (fun i => algebraMap A F (w i)) uprim)
    (kum : (E.baseChange K).toAffine.Point →+ (Fin (m + 1) → ℚ_[2])) (Lm : ℤ)
    (h45 : (fun i => ρ (z i)) = (Lm : ℚ_[2]) • kum P)
    (ε₀ : A) (utilde0 : F) (h47 : utilde0 = algebraMap A F ε₀ * uprim)
    (hcoef : ∀ a : A, algebraMap A F a = utilde0 → ρ a = C.u 0 0) :
    BaseZero E k C :=
  ZInQ.Manuscript.RC.Central.baseZero_node C K P CSTThm11Split hCST
    (ZInQ.Manuscript.RC.Height.hheight_of_CST_of_artin E k f hf Lat hLat hnCM scale hscale K hK2
      hKc hD3 hD4 hsplit a₀ b₀ c₀ hH ι y hy P hP hA h2 t ht htk)
    ρ hρ Dm hcentral z w hz uprim hu kum Lm h45 ε₀ utilde0 h47 hcoef

open Classical in
/-- **`BaseZero` with `hheight`, `hρ`, `hcoef` discharged and RC19's G2 from `ArtinFactorization`**
(tex 4330–4373; tex 5736 with tex 2599, 2720). PROVED: `baseZero_node_genuine_of_CST` with
`hL := lFactorizationConductorOne_of_artin hA E K hK2 hKc h2 hsplit ht htk` (lane RC27). The input
`hL` (RC19's GLUE) is replaced by the shared top layer's GLUE `GenusOdd.ArtinFactorization`, `K`
split at `2` (`h2`) and `K = ℚ(√k)` (`t`, `ht`, `htk`); all other inputs are those of
`baseZero_node_genuine_of_CST`. -/
theorem baseZero_node_genuine_of_CST_of_artin {E : WeierstrassCurve ℚ} [E.IsElliptic] {k : ℚ}
    {b : ℕ} (C : CoordData b)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) (hnCM : IsNonCMLattice Lat)
    (scale : ℂ) (hscale : IsParamScale (newformLevel E) f Lat scale)
    (K : Type) [Field K] [NumberField K] [DecidableEq K] (hK2 : Module.finrank ℚ K = 2)
    (hKc : IsTotallyComplex K) (hD3 : discr K ≠ -3) (hD4 : discr K ≠ -4)
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p)
    (a₀ b₀ c₀ : ℤ) (hH : IsHeegnerForm (newformLevel E) (discr K * (1 : ℕ) ^ 2) a₀ b₀ c₀)
    (ι : ringClassField (conductorOrder K 1) →ₐ[ℚ] ℂ)
    (y : (E.baseChange (ringClassField (conductorOrder K 1))).toAffine.Point)
    (hy : Point.map (W' := E.toAffine) ι y =
      phiAn E f Lat scale (cmPoint a₀ b₀ (discr K * (1 : ℕ) ^ 2)))
    (P : (E.baseChange K).toAffine.Point)
    (hP : Point.baseChange K (ringClassField (conductorOrder K 1)) P =
      ∑ σ : ringClassField (conductorOrder K 1) ≃ₐ[K] ringClassField (conductorOrder K 1),
        Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) y)
    (hA : GenusOdd.ArtinFactorization) (h2 : SplitsIn K 2) (t : K)
    (ht : t ∉ (algebraMap ℚ K).range) (htk : t ^ 2 = algebraMap ℚ K k) (hCST : CSTThm11Split)
    {m : ℕ} (D : Matrix (Fin (m + 1)) (Fin (m + 1)) LambdaT) (hcentral : (D.map rhoT).rank = m)
    (z w : Fin (m + 1) → LambdaT) (hz : D *ᵥ z = 0) (uprim : FractionRing Lambda)
    (hu : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
      (D.map (algebraMap LambdaT (FractionRing Lambda)))
      (fun i => algebraMap LambdaT (FractionRing Lambda) (z i))
      (fun i => algebraMap LambdaT (FractionRing Lambda) (w i)) uprim)
    (kum : (E.baseChange K).toAffine.Point →+ (Fin (m + 1) → ℚ_[2])) (Lm : ℤ)
    (h45 : (fun i => rhoT (z i)) = (Lm : ℚ_[2]) • kum P)
    (ε₀ : LambdaT) (utilde0 : FractionRing Lambda)
    (h47 : utilde0 = algebraMap LambdaT (FractionRing Lambda) ε₀ * uprim)
    (wHalf : LambdaHalf) (hwHalf : lambdaHalfToFrac wHalf = utilde0)
    (hC : C.u 0 0 = centralSpecialization wHalf) :
    BaseZero E k C :=
  baseZero_node_genuine_of_CST C f hf Lat hLat hnCM scale hscale K hK2 hKc hD3 hD4 hsplit a₀ b₀ c₀
    hH ι y hy P hP
    (ZInQ.Manuscript.RC.Height.lFactorizationConductorOne_of_artin hA E K hK2 hKc h2 hsplit ht htk)
    hCST D hcentral z w hz uprim hu kum Lm h45 ε₀ utilde0 h47 wHalf hwHalf hC

/-! ### The two-term model replaced by the actual complex -/

/-- The `1 × 1` two-term model `(δ)` cut out of a split differential `M` by the two minimal
indices `s₂` (degree two, row) and `s₁` (degree one, column): `δ = M s₂ s₁` (the model of
`MinimalComplexes.CentralTwoTermModelAt`, in lane RC15's shape `Fin (m + 1)` with `m = 0`). -/
def entryModel {A : Type*} {I : Type*} (M : Matrix I I A) (s₂ s₁ : I) :
    Matrix (Fin (0 + 1)) (Fin (0 + 1)) A :=
  Matrix.of fun _ _ => M s₂ s₁

/-- **`BaseZero` from the actual bounded complex** (tex 4330–4373, with tex 4350–4368: "Full Selmer
corank one gives central dimensions `(1,1)` in degrees one and two and zero in every other degree
[...] Over the DVR `A`, a bounded finite free complex decomposes [...] All cancellable disks have
unit differential").

Consumer: lane RC15's `ZInQ.Manuscript.RC.Central.baseZero_node`, whose inputs `D`, `hcentral` are
a two-term model (lane RC15's DEPARTURE D1, resting on the GLUE minimal-complex cancellation).
Discharger: the shared top layer's `MinimalComplexes.centralTwoTermModelAt_proof`. Here the input is
the actual bounded finite free complex over the DVR `A`, a graded matrix `d` on the index type `I`
(`IsGradedDiff deg d`, `d * d = 0`), with `ρ`-central dimensions `(1,1)` in degrees one and two and
zero elsewhere (`h0`, `h1`, `h2`: lane RC15's ELLIOT input "full Selmer corank one gives central
dimensions `(1,1)`", now stated on the actual complex). Conclusion: a degree-preserving change of
bases `Pm, Qm` puts `d` in split form (unit disks plus the minimal part spanned by `s₁`, `s₂`), the
model `(δ) = entryModel (Pm * d * Qm) s₂ s₁` has `δ ∈ 𝔪`, and for every integral cycle `z`, integral
functional `w` and generic coordinate `uprim` of that model, and every Kummer comparison `κ`, `Lm`,
`ε₀`, `ũ₀` satisfying lane RC15's remaining inputs (`hu` definition; `h45`, `h47` ELLIOT; `hcoef`
GLUE), `BaseZero E k C` holds.

PROVED, from lane RC15's remaining inputs (`CSTThm11`, `hCST`, `hheight`, `hρ`, `hcoef`, `hu`,
`h45`, `h47`) and the central dimensions of the actual complex. -/
theorem baseZero_node_of_complex {E : WeierstrassCurve ℚ} {k : ℚ} {b : ℕ} (C : CoordData b)
    (K : Type*) [Field K] [DecidableEq K] [Algebra ℚ K] (P : (E.baseChange K).toAffine.Point)
    (CSTThm11 : Prop) (hCST : CSTThm11)
    (hheight : CSTThm11 → ProductOrderGeTwo E k → IsOfFinAddOrder P)
    {A F : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field F]
    [Algebra A F] [IsFractionRing A F] (ρ : A →+* ℚ_[2])
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0)
    (I : Type*) [Fintype I] [DecidableEq I] (deg : I → ℤ) (d : Matrix I I A)
    (hg : IsGradedDiff deg d) (hd : d * d = 0)
    (h0 : ∀ n, n ≠ 1 → n ≠ 2 → resDimAt ρ deg d n = 0) (h1 : resDimAt ρ deg d 1 = 1)
    (h2 : resDimAt ρ deg d 2 = 1) :
    ∃ (Pm Qm : Matrix I I A) (kind : I → Fin 3) (partner : I → I) (s₁ s₂ : I),
      Pm * Qm = 1 ∧ Qm * Pm = 1 ∧ IsDegPreserving deg Pm ∧ IsDegPreserving deg Qm ∧
      SplitForm (Pm * d * Qm) kind partner ∧
      kind s₁ = 0 ∧ kind s₂ = 0 ∧ deg s₁ = 1 ∧ deg s₂ = 2 ∧
      (∀ x, kind x = 0 → x = s₁ ∨ x = s₂) ∧
      (Pm * d * Qm) s₂ s₁ ∈ IsLocalRing.maximalIdeal A ∧
      ∀ (z w : Fin (0 + 1) → A) (uprim : F),
        entryModel (Pm * d * Qm) s₂ s₁ *ᵥ z = 0 →
        ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
          ((entryModel (Pm * d * Qm) s₂ s₁).map (algebraMap A F))
          (fun i => algebraMap A F (z i)) (fun i => algebraMap A F (w i)) uprim →
        ∀ (κ : (E.baseChange K).toAffine.Point →+ (Fin (0 + 1) → ℚ_[2])) (Lm : ℤ),
        (fun i => ρ (z i)) = (Lm : ℚ_[2]) • κ P →
        ∀ (ε₀ : A) (utilde0 : F), utilde0 = algebraMap A F ε₀ * uprim →
        (∀ a : A, algebraMap A F a = utilde0 → ρ a = C.u 0 0) →
        BaseZero E k C := by
  obtain ⟨Pm, Qm, kind, partner, s₁, s₂, hPQ, hQP, hP, hQ, hS, hk₁, hk₂, hs₁, hs₂, hmin, hδ,
    hc⟩ := centralTwoTermModelAt_proof A ℚ_[2] ρ hρ I deg d hg hd h0 h1 h2
  refine ⟨Pm, Qm, kind, partner, s₁, s₂, hPQ, hQP, hP, hQ, hS, hk₁, hk₂, hs₁, hs₂, hmin, hδ, ?_⟩
  intro z w uprim hz hu κ Lm h45 ε₀ utilde0 h47 hcoef
  exact ZInQ.Manuscript.RC.Central.baseZero_node (F := F) C K P CSTThm11 hCST hheight ρ hρ
    (entryModel (Pm * d * Qm) s₂ s₁) hc z w hz uprim hu κ Lm h45 ε₀ utilde0 h47 hcoef

/-- **Non-vacuity of the complex hypotheses of `baseZero_node_of_complex` and
`baseZero_node_genuine_of_complex_CST`** (tex 4350–4352). For every local ring `A` and every map
`ρ` to a field, the two-term complex `[A --0--> A]` in degrees one and two (the shared top layer's
`BaseZeroEndToEnd.ttDiff` of the zero `1 × 1` matrix) is a graded complex with `ρ`-central dimensions
`(1,1)` in degrees one and two and zero elsewhere. More generally the shared top layer's
`BaseZeroEndToEnd.resDimAt_tt` turns every two-term model of lane RC15 with `hcentral` into a
complex satisfying these hypotheses, so the complex form contains lane RC15's model form. PROVED. -/
theorem complex_hypotheses_nonvacuous {A k : Type*} [CommRing A] [IsLocalRing A] [Field k]
    (ρ : A →+* k) :
    IsGradedDiff (ttDeg 0) (ttDiff (0 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) A)) ∧
      ttDiff (0 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) A) *
        ttDiff (0 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) A) = 0 ∧
      (∀ n, n ≠ 1 → n ≠ 2 →
        resDimAt ρ (ttDeg 0) (ttDiff (0 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) A)) n = 0) ∧
      resDimAt ρ (ttDeg 0) (ttDiff (0 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) A)) 1 = 1 ∧
      resDimAt ρ (ttDeg 0) (ttDiff (0 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) A)) 2 = 1 := by
  obtain ⟨h0, h1, h2⟩ := resDimAt_tt ρ (0 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) A) (by simp)
  exact ⟨ttDiff_graded _, ttDiff_sq _, h0, h1, h2⟩

/-! ### All three discharges together -/

open Classical in
/-- **`BaseZero` with every discharged input removed** (tex 4330–4373: `A = Λ_(t)`, tex
4341–4342; height formula, tex 4345–4346; central dimensions and Smith reduction, tex 4350–4368;
`ũ₀ = ε₀ u_{prim,0}`, tex 4369–4373).

Consumer: lane RC15's `ZInQ.Manuscript.RC.Central.baseZero_node`. Dischargers: lane RC19's
`ZInQ.Manuscript.RC.Height.hheight_of_CST` (`hheight`); lane RC20's `rhoT_maximalIdeal` and
`hcoef_of_lambdaHalf` through `ZInQ.Manuscript.RC.Rings.baseZero_node_genuine` (`hρ`, `hcoef`, over
the genuine `A = Λ_(t)`); the shared top layer's `MinimalComplexes.centralTwoTermModelAt_proof`
(the two-term model and `hcentral`, from the actual complex). This is
`baseZero_node_genuine_of_CST` applied to the model produced as in `baseZero_node_of_complex`.

PROVED, from the remaining inputs: ellipticity of `E`; `CSTThm11Split` (PRINT) with its
conductor-one Heegner data and the trace identity `hP`; RC19's GLUE
`LFactorizationConductorOne E K k`; the actual bounded finite free complex over `Λ_(t)` with central
dimensions `(1,1)` in degrees one and two and zero elsewhere (ELLIOT, tex 4350–4352); and, on the
produced model, `hu` (definition), `h45`, `h47` (ELLIOT), `ũ₀ ∈ Λ[1/2]` (`wHalf`, `hwHalf`) and
`C.u 0 0 = ũ₀(0)` (`hC`). -/
theorem baseZero_node_genuine_of_complex_CST {E : WeierstrassCurve ℚ} [E.IsElliptic] {k : ℚ}
    {b : ℕ} (C : CoordData b)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) (hnCM : IsNonCMLattice Lat)
    (scale : ℂ) (hscale : IsParamScale (newformLevel E) f Lat scale)
    (K : Type) [Field K] [NumberField K] [DecidableEq K] (hK2 : Module.finrank ℚ K = 2)
    (hKc : IsTotallyComplex K) (hD3 : discr K ≠ -3) (hD4 : discr K ≠ -4)
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p)
    (a₀ b₀ c₀ : ℤ) (hH : IsHeegnerForm (newformLevel E) (discr K * (1 : ℕ) ^ 2) a₀ b₀ c₀)
    (ι : ringClassField (conductorOrder K 1) →ₐ[ℚ] ℂ)
    (y : (E.baseChange (ringClassField (conductorOrder K 1))).toAffine.Point)
    (hy : Point.map (W' := E.toAffine) ι y =
      phiAn E f Lat scale (cmPoint a₀ b₀ (discr K * (1 : ℕ) ^ 2)))
    (P : (E.baseChange K).toAffine.Point)
    (hP : Point.baseChange K (ringClassField (conductorOrder K 1)) P =
      ∑ σ : ringClassField (conductorOrder K 1) ≃ₐ[K] ringClassField (conductorOrder K 1),
        Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) y)
    (hL : ZInQ.Manuscript.RC.Height.LFactorizationConductorOne E K k) (hCST : CSTThm11Split)
    (I : Type*) [Fintype I] [DecidableEq I] (deg : I → ℤ) (d : Matrix I I LambdaT)
    (hg : IsGradedDiff deg d) (hd : d * d = 0)
    (h0 : ∀ n, n ≠ 1 → n ≠ 2 → resDimAt rhoT deg d n = 0) (h1 : resDimAt rhoT deg d 1 = 1)
    (h2 : resDimAt rhoT deg d 2 = 1) :
    ∃ (Pm Qm : Matrix I I LambdaT) (kind : I → Fin 3) (partner : I → I) (s₁ s₂ : I),
      Pm * Qm = 1 ∧ Qm * Pm = 1 ∧ IsDegPreserving deg Pm ∧ IsDegPreserving deg Qm ∧
      SplitForm (Pm * d * Qm) kind partner ∧
      kind s₁ = 0 ∧ kind s₂ = 0 ∧ deg s₁ = 1 ∧ deg s₂ = 2 ∧
      (∀ x, kind x = 0 → x = s₁ ∨ x = s₂) ∧
      (Pm * d * Qm) s₂ s₁ ∈ IsLocalRing.maximalIdeal LambdaT ∧
      ∀ (z w : Fin (0 + 1) → LambdaT) (uprim : FractionRing Lambda),
        entryModel (Pm * d * Qm) s₂ s₁ *ᵥ z = 0 →
        ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
          ((entryModel (Pm * d * Qm) s₂ s₁).map (algebraMap LambdaT (FractionRing Lambda)))
          (fun i => algebraMap LambdaT (FractionRing Lambda) (z i))
          (fun i => algebraMap LambdaT (FractionRing Lambda) (w i)) uprim →
        ∀ (kum : (E.baseChange K).toAffine.Point →+ (Fin (0 + 1) → ℚ_[2])) (Lm : ℤ),
        (fun i => rhoT (z i)) = (Lm : ℚ_[2]) • kum P →
        ∀ (ε₀ : LambdaT) (utilde0 : FractionRing Lambda),
        utilde0 = algebraMap LambdaT (FractionRing Lambda) ε₀ * uprim →
        ∀ wHalf : LambdaHalf, lambdaHalfToFrac wHalf = utilde0 →
        C.u 0 0 = centralSpecialization wHalf →
        BaseZero E k C := by
  obtain ⟨Pm, Qm, kind, partner, s₁, s₂, hPQ, hQP, hPm, hQm, hS, hk₁, hk₂, hs₁, hs₂, hmin, hδ,
    hc⟩ := centralTwoTermModelAt_proof LambdaT ℚ_[2] rhoT
      ZInQ.Manuscript.RC.Rings.rhoT_maximalIdeal I deg d hg hd h0 h1 h2
  refine ⟨Pm, Qm, kind, partner, s₁, s₂, hPQ, hQP, hPm, hQm, hS, hk₁, hk₂, hs₁, hs₂, hmin, hδ, ?_⟩
  intro z w uprim hz hu kum Lm h45 ε₀ utilde0 h47 wHalf hwHalf hC
  exact baseZero_node_genuine_of_CST C f hf Lat hLat hnCM scale hscale K hK2 hKc hD3 hD4 hsplit
    a₀ b₀ c₀ hH ι y hy P hP hL hCST (entryModel (Pm * d * Qm) s₂ s₁) hc z w hz uprim hu kum Lm h45
    ε₀ utilde0 h47 wHalf hwHalf hC

open Classical in
/-- **`BaseZero` with every discharged input removed and RC19's G2 from `ArtinFactorization`**
(tex 4330–4373; tex 5736 with tex 2599, 2720). PROVED: `baseZero_node_genuine_of_complex_CST`
with `hL := lFactorizationConductorOne_of_artin hA E K hK2 hKc h2 hsplit ht htk` (lane RC27); the
input `hL` (RC19's GLUE) is replaced by the shared top layer's GLUE `GenusOdd.ArtinFactorization`,
`K` split at `2` and `K = ℚ(√k)`; the conclusion is that of
`baseZero_node_genuine_of_complex_CST`. -/
theorem baseZero_node_genuine_of_complex_CST_of_artin {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {k : ℚ} {b : ℕ} (C : CoordData b)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) (hnCM : IsNonCMLattice Lat)
    (scale : ℂ) (hscale : IsParamScale (newformLevel E) f Lat scale)
    (K : Type) [Field K] [NumberField K] [DecidableEq K] (hK2 : Module.finrank ℚ K = 2)
    (hKc : IsTotallyComplex K) (hD3 : discr K ≠ -3) (hD4 : discr K ≠ -4)
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p)
    (a₀ b₀ c₀ : ℤ) (hH : IsHeegnerForm (newformLevel E) (discr K * (1 : ℕ) ^ 2) a₀ b₀ c₀)
    (ι : ringClassField (conductorOrder K 1) →ₐ[ℚ] ℂ)
    (y : (E.baseChange (ringClassField (conductorOrder K 1))).toAffine.Point)
    (hy : Point.map (W' := E.toAffine) ι y =
      phiAn E f Lat scale (cmPoint a₀ b₀ (discr K * (1 : ℕ) ^ 2)))
    (P : (E.baseChange K).toAffine.Point)
    (hP : Point.baseChange K (ringClassField (conductorOrder K 1)) P =
      ∑ σ : ringClassField (conductorOrder K 1) ≃ₐ[K] ringClassField (conductorOrder K 1),
        Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) y)
    (hA : GenusOdd.ArtinFactorization) (h2 : SplitsIn K 2) (t : K)
    (ht : t ∉ (algebraMap ℚ K).range) (htk : t ^ 2 = algebraMap ℚ K k) (hCST : CSTThm11Split)
    (I : Type*) [Fintype I] [DecidableEq I] (deg : I → ℤ) (d : Matrix I I LambdaT)
    (hg : IsGradedDiff deg d) (hd : d * d = 0)
    (h0 : ∀ n, n ≠ 1 → n ≠ 2 → resDimAt rhoT deg d n = 0) (h1 : resDimAt rhoT deg d 1 = 1)
    (h2' : resDimAt rhoT deg d 2 = 1) :
    ∃ (Pm Qm : Matrix I I LambdaT) (kind : I → Fin 3) (partner : I → I) (s₁ s₂ : I),
      Pm * Qm = 1 ∧ Qm * Pm = 1 ∧ IsDegPreserving deg Pm ∧ IsDegPreserving deg Qm ∧
      SplitForm (Pm * d * Qm) kind partner ∧
      kind s₁ = 0 ∧ kind s₂ = 0 ∧ deg s₁ = 1 ∧ deg s₂ = 2 ∧
      (∀ x, kind x = 0 → x = s₁ ∨ x = s₂) ∧
      (Pm * d * Qm) s₂ s₁ ∈ IsLocalRing.maximalIdeal LambdaT ∧
      ∀ (z w : Fin (0 + 1) → LambdaT) (uprim : FractionRing Lambda),
        entryModel (Pm * d * Qm) s₂ s₁ *ᵥ z = 0 →
        ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
          ((entryModel (Pm * d * Qm) s₂ s₁).map (algebraMap LambdaT (FractionRing Lambda)))
          (fun i => algebraMap LambdaT (FractionRing Lambda) (z i))
          (fun i => algebraMap LambdaT (FractionRing Lambda) (w i)) uprim →
        ∀ (kum : (E.baseChange K).toAffine.Point →+ (Fin (0 + 1) → ℚ_[2])) (Lm : ℤ),
        (fun i => rhoT (z i)) = (Lm : ℚ_[2]) • kum P →
        ∀ (ε₀ : LambdaT) (utilde0 : FractionRing Lambda),
        utilde0 = algebraMap LambdaT (FractionRing Lambda) ε₀ * uprim →
        ∀ wHalf : LambdaHalf, lambdaHalfToFrac wHalf = utilde0 →
        C.u 0 0 = centralSpecialization wHalf →
        BaseZero E k C :=
  baseZero_node_genuine_of_complex_CST C f hf Lat hLat hnCM scale hscale K hK2 hKc hD3 hD4 hsplit
    a₀ b₀ c₀ hH ι y hy P hP
    (ZInQ.Manuscript.RC.Height.lFactorizationConductorOne_of_artin hA E K hK2 hKc h2 hsplit ht htk)
    hCST I deg d hg hd h0 h1 h2'

end ZInQ.Manuscript.RC.GlueSweep.Central
