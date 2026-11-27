import ZInQKernel.Contrib.OneProof.RC.Wiring.Central
import ZInQKernel.Contrib.OneProof.RC.Height.BaseZeroCST
import ZInQKernel.Contrib.OneProof.RC.Height.ArtinG2

/-!
# Theorem 5.3, Lane RC0 round 2: the conductor-one height formula in the base-zero inputs (lane RC19)

Lane RC15's base-zero node takes the conductor-one height formula as the hypothesis
`hheight : CSTThm11Split → ProductOrderGeTwo E k → IsOfFinAddOrder P` (tex 4345–4346). Lane RC19's
`hheight_of_CST` proves it from the blueprint's statement of Cai–Shu–Tian Theorem 1.1 and the
conductor-one Heegner data. This file replaces the field `hheight` of `BaseZeroModel` by those data
(`HeegnerData`): `baseZeroInputs_of_CST : BaseZeroInputsCST D → BaseZeroInputs D` (PROVED).

Lane RC27 (item 7): the conjunct `LFactorizationConductorOne E K k` (RC19's GLUE G2) of
`HeegnerData` follows from the shared top layer's GLUE `GenusOdd.ArtinFactorization` when `K` is
split at `2` and `K = ℚ(√k)` (`ArtinG2.lean`). `HeegnerDataSqrt` is `HeegnerData` with that
conjunct replaced by these two conditions on `K`; `heegnerData_of_sqrt` (PROVED) turns it into
`HeegnerData` given `ArtinFactorization`, and `hheight_of_heegnerDataSqrt` (PROVED) is the height
formula from it.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
  ZInQ.Contrib.CloudB3RC53.CST ZInQ.Manuscript.RC.Height
open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory WeierstrassCurve WeierstrassCurve.Affine
open Matrix

open Classical in
/-- **The conductor-one Heegner data** (tex 4330–4346; the hypotheses of lane RC19's
`hheight_of_CST`): the newform `f` of `E` and its parametrization (a lattice of `E`, non-CM, the
scale of the modular parametrization), `K` imaginary quadratic with `disc K ∉ {−3, −4}` in which
every prime of the level splits, a Heegner form of discriminant `disc K`, a point `y ∈ E(H₁)` over
the Hilbert class field with `ι(y) = φ(τ)` (the CM point), "the specified point" `P ∈ E(K)` the
trace of `y` (tex 4345–4346; the CM points, tex 2915–2932), and the conductor-one factorization
`L(E/K,s) = L(E,s)L(E^{(k)},s)` (GLUE, tex 5736). Kinds: existence claims — `f` PRINT (BCDT;
`newformLevel` the conductor by Carayol), `Lat` GLUE (uniformization), non-CM GLUE
(`j = 35152/9`), `κ` GLUE (Eichler–Shimura, a ℚ-isogeny `E_f → E`), the split hypothesis and the
Heegner form PROVED-able from `UnitSquareAt` at `2N`, `y` GLUE/PRINT (CM theory: `φ(τ) ∈ E(H₁)`),
`P` GLUE (Galois descent), the factorization GLUE (Artin formalism; it follows from
`RCLeaves.artin` at `(1, 1, disc K)` when `k = disc K`); owner RC19 / batch 3 HeegnerCohomology. -/
def HeegnerData (E : WeierstrassCurve ℚ) (hE : E.IsElliptic) (k : ℚ) (K : Type) [Field K]
    [NumberField K] [DecidableEq K] (P : (E.baseChange K).toAffine.Point) : Prop :=
  haveI := hE
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (_ : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (Lat : PeriodPair) (_ : IsLatticeOf E Lat) (_ : IsNonCMLattice Lat)
    (κ : ℂ) (_ : IsParamScale (newformLevel E) f Lat κ)
    (_ : Module.finrank ℚ K = 2) (_ : IsTotallyComplex K) (_ : discr K ≠ -3) (_ : discr K ≠ -4)
    (_ : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p)
    (A B C' : ℤ) (_ : IsHeegnerForm (newformLevel E) (discr K * (1 : ℕ) ^ 2) A B C')
    (ι : ringClassField (conductorOrder K 1) →ₐ[ℚ] ℂ)
    (y : (E.baseChange (ringClassField (conductorOrder K 1))).toAffine.Point),
    Point.map (W' := E.toAffine) ι y = phiAn E f Lat κ (cmPoint A B (discr K * (1 : ℕ) ^ 2)) ∧
    Point.baseChange K (ringClassField (conductorOrder K 1)) P =
      ∑ σ : ringClassField (conductorOrder K 1) ≃ₐ[K] ringClassField (conductorOrder K 1),
        Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) y ∧
    LFactorizationConductorOne E K k

/-- **The conductor-one height formula** from the Heegner data (PROVED from lane RC19's
`hheight_of_CST`). -/
theorem hheight_of_heegnerData {E : WeierstrassCurve ℚ} {hE : E.IsElliptic} {k : ℚ} {K : Type}
    [Field K] [NumberField K] [DecidableEq K] {P : (E.baseChange K).toAffine.Point}
    (h : HeegnerData E hE k K P) : CSTThm11Split → ProductOrderGeTwo E k → IsOfFinAddOrder P := by
  have := hE
  obtain ⟨f, hf, Lat, hLat, hnCM, κ, hκ, hK2, hKc, hD3, hD4, hsplit, A, B, C', hH, ι, y, hy, hP,
    hL⟩ := h
  exact hheight_of_CST E k f hf Lat hLat hnCM κ hκ K hK2 hKc hD3 hD4 hsplit A B C' hH ι y hy P hP hL

open Classical in
/-- **The conductor-one Heegner data with the factorization replaced by conditions on `K`**
(tex 4330–4346; tex 2599 "Fix `k` and `K = ℚ(√k)`", tex 2720 "`K = ℚ(√k)` … imaginary, split at
`2N`"): the data of `HeegnerData` (verbatim) with its conjunct `LFactorizationConductorOne E K k`
(GLUE) replaced by `K` split at `2` and a square root `t ∈ K \ ℚ` of `k`. Kinds: definition (the
Heegner point), as for `HeegnerData`. Non-vacuity: the replaced conjuncts are jointly satisfiable
with every other condition on `K` here except the level splitting (`K = ℚ(√−7)`, `k = −7`:
`ZInQ.Manuscript.RC.Height.artinG2_field_hypotheses_nonvacuous`); the remaining conjuncts are those
of `HeegnerData`. -/
def HeegnerDataSqrt (E : WeierstrassCurve ℚ) (hE : E.IsElliptic) (k : ℚ) (K : Type) [Field K]
    [NumberField K] [DecidableEq K] (P : (E.baseChange K).toAffine.Point) : Prop :=
  haveI := hE
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (_ : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (Lat : PeriodPair) (_ : IsLatticeOf E Lat) (_ : IsNonCMLattice Lat)
    (κ : ℂ) (_ : IsParamScale (newformLevel E) f Lat κ)
    (_ : Module.finrank ℚ K = 2) (_ : IsTotallyComplex K) (_ : discr K ≠ -3) (_ : discr K ≠ -4)
    (_ : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p)
    (A B C' : ℤ) (_ : IsHeegnerForm (newformLevel E) (discr K * (1 : ℕ) ^ 2) A B C')
    (ι : ringClassField (conductorOrder K 1) →ₐ[ℚ] ℂ)
    (y : (E.baseChange (ringClassField (conductorOrder K 1))).toAffine.Point),
    Point.map (W' := E.toAffine) ι y = phiAn E f Lat κ (cmPoint A B (discr K * (1 : ℕ) ^ 2)) ∧
    Point.baseChange K (ringClassField (conductorOrder K 1)) P =
      ∑ σ : ringClassField (conductorOrder K 1) ≃ₐ[K] ringClassField (conductorOrder K 1),
        Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) y ∧
    SplitsIn K 2 ∧ ∃ t : K, t ∉ (algebraMap ℚ K).range ∧ t ^ 2 = algebraMap ℚ K k

/-- **`HeegnerData` from `HeegnerDataSqrt` and `ArtinFactorization`** (tex 5736; PROVED from the
shared top layer's GLUE `GenusOdd.ArtinFactorization` by lane RC27's
`lFactorizationConductorOne_of_artin`). -/
theorem heegnerData_of_sqrt (hA : GenusOdd.ArtinFactorization) {E : WeierstrassCurve ℚ}
    {hE : E.IsElliptic} {k : ℚ} {K : Type} [Field K] [NumberField K] [DecidableEq K]
    {P : (E.baseChange K).toAffine.Point} (h : HeegnerDataSqrt E hE k K P) :
    HeegnerData E hE k K P := by
  have := hE
  obtain ⟨f, hf, Lat, hLat, hnCM, κ, hκ, hK2, hKc, hD3, hD4, hsplit, A, B, C', hH, ι, y, hy, hP,
    h2, t, ht, htk⟩ := h
  exact ⟨f, hf, Lat, hLat, hnCM, κ, hκ, hK2, hKc, hD3, hD4, hsplit, A, B, C', hH, ι, y, hy, hP,
    lFactorizationConductorOne_of_artin hA E K hK2 hKc h2 hsplit ht htk⟩

/-- **The conductor-one height formula from `HeegnerDataSqrt` and `ArtinFactorization`** (PROVED:
`hheight_of_heegnerData` after `heegnerData_of_sqrt`). -/
theorem hheight_of_heegnerDataSqrt (hA : GenusOdd.ArtinFactorization) {E : WeierstrassCurve ℚ}
    {hE : E.IsElliptic} {k : ℚ} {K : Type} [Field K] [NumberField K] [DecidableEq K]
    {P : (E.baseChange K).toAffine.Point} (h : HeegnerDataSqrt E hE k K P) :
    CSTThm11Split → ProductOrderGeTwo E k → IsOfFinAddOrder P :=
  hheight_of_heegnerData (heegnerData_of_sqrt hA h)

/-- **The base-zero model with the conductor-one Heegner data in place of the height formula**:
the fields of `BaseZeroModel` (tex 4330–4376; see there), with `K` a number field, `P` the
conductor-one Heegner point and `heegner` its data (`HeegnerData`), and no field `hheight`. -/
structure BaseZeroModelCST {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) : Type 1 where
  /-- `E_ℓ` is elliptic (`ℓ ≠ 0`) -/
  hE : (Ecurve ℓ).IsElliptic
  /-- the field `K = ℚ(√k)` -/
  K : Type
  [fieldK : Field K]
  [nfK : NumberField K]
  [decK : DecidableEq K]
  /-- the conductor-one Heegner point -/
  P : ((Ecurve ℓ).baseChange K).toAffine.Point
  /-- its Heegner data -/
  heegner : HeegnerData (Ecurve ℓ) hE (D.kfin : ℚ) K P
  m : ℕ
  Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT
  hcentral : (Dm.map Rings.rhoT).rank = m
  z : Fin (m + 1) → Rings.LambdaT
  hz : Dm *ᵥ z = 0
  CU : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ
  e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT)
  e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT)
  hd : ∀ y, e2 ((CU.d 1 2).hom y) = Dm *ᵥ e1 y
  lam : CU.X 2 →ₗ[Rings.LambdaT] Rings.LambdaT
  hlam : ∀ y : CU.X 1, lam ((CU.d 1 2).hom y) = 0
  uprim : FractionRing Uniform.Lambda
  hu : ∀ w : Fin (m + 1) → Rings.LambdaT, w ᵥ* Dm = 0 →
    (∀ y, lam (e2.symm y) = w ⬝ᵥ y) →
    Central.IsClassFunctionalCoord
      (Dm.map (algebraMap Rings.LambdaT (FractionRing Uniform.Lambda)))
      (fun i => algebraMap Rings.LambdaT (FractionRing Uniform.Lambda) (z i))
      (fun i => algebraMap Rings.LambdaT (FractionRing Uniform.Lambda) (w i)) uprim
  kappa : ((Ecurve ℓ).baseChange K).toAffine.Point →+ (Fin (m + 1) → ℚ_[2])
  Lm : ℤ
  h45 : (fun i => Rings.rhoT (z i)) = (Lm : ℚ_[2]) • kappa P
  eps0 : Rings.LambdaT
  utilde0 : FractionRing Uniform.Lambda
  h47 : utilde0 = algebraMap Rings.LambdaT (FractionRing Uniform.Lambda) eps0 * uprim
  wHalf : Uniform.LambdaHalf
  hwHalf : Uniform.lambdaHalfToFrac wHalf = utilde0
  hC : central (D.uTilde Fam 0) = Uniform.centralSpecialization wHalf

attribute [instance] BaseZeroModelCST.fieldK BaseZeroModelCST.nfK BaseZeroModelCST.decK

/-- The base-zero model from the Heegner-data model (PROVED: `hheight` by lane RC19). -/
def BaseZeroModelCST.toModel {ℓ : ℕ} {D : RCData ℓ} {Fam : Family} (M : BaseZeroModelCST D Fam) :
    BaseZeroModel D Fam where
  K := M.K
  P := M.P
  hheight := hheight_of_heegnerData M.heegner
  m := M.m
  Dm := M.Dm
  hcentral := M.hcentral
  z := M.z
  hz := M.hz
  CU := M.CU
  e1 := M.e1
  e2 := M.e2
  hd := M.hd
  lam := M.lam
  hlam := M.hlam
  uprim := M.uprim
  hu := M.hu
  kappa := M.kappa
  Lm := M.Lm
  h45 := M.h45
  eps0 := M.eps0
  utilde0 := M.utilde0
  h47 := M.h47
  wHalf := M.wHalf
  hwHalf := M.hwHalf
  hC := M.hC

/-- **The base-zero inputs with the height formula discharged** (tex 4330–4376): under the
lemma's hypotheses on the companion, every final family has a `BaseZeroModelCST`. -/
def BaseZeroInputsCST {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  SelmerCorankOneOverK ℓ D.kfin → AnalyticRank (Etw ℓ D.kfin) 0 →
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → Nonempty (BaseZeroModelCST D F)

/-- `BaseZeroInputs` from `BaseZeroInputsCST` (PROVED). -/
theorem baseZeroInputs_of_CST {ℓ : ℕ} {D : RCData ℓ} (h : BaseZeroInputsCST D) :
    BaseZeroInputs D := fun hSel hk Co Ce F hF => by
  obtain ⟨M⟩ := h hSel hk Co Ce F hF
  exact ⟨M.toModel⟩

end ZInQ.Manuscript.RC.Wiring
