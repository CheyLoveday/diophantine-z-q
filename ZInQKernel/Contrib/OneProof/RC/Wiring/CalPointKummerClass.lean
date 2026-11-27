import ZInQKernel.Contrib.RC53Assist.CentralKummer.RationalKummer
import ZInQKernel.Contrib.RC53Assist.DivisionPoints.Support

/-!
# Theorem 5.3, Lane RC34: the genuine global `2`-adic Kummer class of a rational point

Lemma `ex:arith-central-specialization` (`diophantine_zq.tex`, tex 3895–3986) identifies the
central class with the Kummer image of a point, `z₀ = i(LmP)`, and the proof of Proposition
`ex:arith-central-calibration` (tex 4005–4009) computes `H¹(C_K)_tors = E^{(h)}(K)[2^∞]` and the
Kummer sequence for the ordinary compact Kummer complex `C_K`. This file constructs the class of a
rational point in `H¹(C_K)` itself, for the genuine complex

`C_K = compactKummerComplex S W hFull = (selCx (tateKummerSelData S W hFull)).toCC`,

whose global part is the continuous cochains of `G_{K,S}` with values in `T₂E = TateS K S W` and
whose local conditions are the `2`-adic Kummer conditions `tateKummerCondition` (tex 3413–3438),
`U¹ = (ℤ₂-span of the local Kummer cocycles) ⊔ B¹`.

## Construction

* `IsGlobalDivTower W P R`: `R : ℕ → E(K_S)` is a compatible tower of `2`-power division points
  of `P ∈ E(K)` (`R 0` is the image of `P`, `2 R (n + 1) = R n`).
* `globalKummerCochain hR`: the cochain `g ↦ (g R n − R n)_n ∈ T₂E` of `G_{K,S}`, continuous
  (stabilizers of points of `E(K_S)` are open, `continuous_globalKummerFun`) and a cocycle
  (`globalKummerCochain_isCocycle`).
* `IsGlobalDivTower.isDivTower_compPt`: at `v`, the tower `compPt W v ∘ R` is a compatible tower
  of the image of `P` in `E(K_v)`, and `resDegOne_globalKummerCochain`: the restriction of the
  global cochain to `G_{K_v}` **is** the local `2`-adic Kummer cocycle `tateKummerCocycleOf` of
  that tower.
* `kummerSelmerCochain hR = (a_R, u_R, 0)`, with `u_R` at `v` the local Kummer cocycle in the
  condition (`tateKummerCocycleOf_mem_sup`), is a degree-one cocycle of the Selmer complex
  (`kummerSelmerCochain_d`); `kummerClassOf S W hFull P R hR ∈ H¹(C_K)` is its class.
* `kummerClassOf_eq`: two towers of `P` give the same class (the difference of the Selmer cochains
  is the coboundary of the constant `0`-cochain of the tower differences); `kummerClassOf_add`:
  the class of a sum of towers is the sum of the classes.
* `GlobalDivisionTowers S W` (every `P ∈ E(K)` has a tower in `E(K_S)`) and
  `kummerClass hdiv : E(K) →+ H¹(C_K)`, with `kummerClass_apply`: it is `kummerClassOf` for every
  tower.
* `rationalKummerClass hdiv : E(K) →+ H¹(K₀)`: the class `1 ⊗ kummerClass P` in the ordinary
  rational Kummer complex `K₀ = C_K ⊗ ℚ₂` (tex 3952–3962), the class `P` of `z₀ = i(LmP)`.
* `homologyMap_projG_kummerClassOf`: the projection `C_K → C^•_cont(G_{K,S}, T₂E)` sends the class
  to the global Kummer class `[a_R] ∈ H¹_cont(G_{K,S}, T₂E)` (`globalKummerClass`).
* `globalDivisionTowers_of_goodReduction`: the hypothesis holds when `S` contains the places above
  `2` and `E` has good reduction outside `S` (Silverman, AEC, VIII.1.5(b); from the division-point
  support theorem `DivisionPoints.exists_supportPoint_map_eq`); `globalDivisionTowers_curveEll`
  for `E_ℓ : y² = x(x − ℓ)(x + 3ℓ)`.

Kinds: definitions and PROVED. The only new hypothesis is `GlobalDivisionTowers` (GLUE, Silverman
AEC VIII.1.5(b)), which is PROVED here from good reduction outside `S`; non-vacuity:
`globalDivisionTowers_univ`, `kummerClassOf_zero`, `kummerClassOf_add`, and the class maps of
`y² = x³ − x` over `ℚ` with `S` all finite places (`kummerClassY2X3mX`) and of
`E_1 : y² = x(x − 1)(x + 3)` over `ℚ` with `S` the finite set of places above `2` and `3`
(`kummerClassE1`, `isGaloisSelData_curveEll_one`). No printed statement is assumed.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CalPoint

open CategoryTheory NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
  ZInQ.Manuscript.RC.KummerMaps ZInQ.Manuscript.RC.LambdaCoef
  ZInQ.Manuscript.RC53Assist.CentralKummer
open ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage (SupportPoints)
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside)

attribute [local instance] levTop

/-! ### Global towers and the global `2`-adic Kummer cochain -/

section Tower

variable {K : Type} [Field K] [NumberField K] [DecidableEq K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K)

variable (S) in
/-- **The image `E(K) → E(K_S)` of rational points** (tex 3895–3986: the point `P` of
`z₀ = i(LmP)` read in `E(K_S)`), the point map along `K → K_S`. Kind: definition. -/
def pointToKS : W.toAffine.Point →+ (W.baseChange (KS K S)).toAffine.Point :=
  (Affine.Point.map (W' := W) (Algebra.ofId K (KS K S))).comp
    (Affine.Point.equivBaseChangeSelf W.toAffine).toAddMonoidHom

omit [NumberField K] in
/-- The image of rational points is the support-field base point of the finite-level packet
(`supportBasePoint`, the same point map along `K → K_S`; tex 3895–3986). PROVED. -/
theorem pointToKS_eq_supportBasePoint (P : W.toAffine.Point) :
    pointToKS S W P = ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportBasePoint
      (S0 := S) W P :=
  rfl

omit [NumberField K] in
/-- Rational points are fixed by `G_{K,S}` (tex 3895–3986). PROVED. -/
theorem map_pointToKS (g : GKS K S) (P : W.toAffine.Point) :
    Affine.Point.map (W' := W) (galS K S g).toAlgHom (pointToKS S W P) =
      pointToKS S W P := by
  change Affine.Point.map (W' := W) (galS K S g).toAlgHom
      (Affine.Point.map (W' := W) (Algebra.ofId K (KS K S))
        (Affine.Point.equivBaseChangeSelf W.toAffine P)) =
    Affine.Point.map (W' := W) (Algebra.ofId K (KS K S))
      (Affine.Point.equivBaseChangeSelf W.toAffine P)
  rw [Affine.Point.map_map]
  rw [Subsingleton.elim ((galS K S g).toAlgHom.comp (Algebra.ofId K (KS K S)))
    (Algebra.ofId K (KS K S))]

/-- **A global tower of `2`-power division points** of `P ∈ E(K)` in `E(K_S)` (tex 3895–3986,
4005–4009: the division points defining the Kummer image of `P` over `G_{K,S}`): `R 0` is the
image of `P` and `2 R (n + 1) = R n`. Kind: definition. -/
def IsGlobalDivTower (P : W.toAffine.Point) (R : ℕ → (W.baseChange (KS K S)).toAffine.Point) :
    Prop :=
  R 0 = pointToKS S W P ∧ ∀ n, 2 • R (n + 1) = R n

variable {W}

omit [NumberField K] in
/-- `2^n R n = P` for a global tower (tex 3895–3986). PROVED. -/
theorem IsGlobalDivTower.two_pow_smul {P : W.toAffine.Point}
    {R : ℕ → (W.baseChange (KS K S)).toAffine.Point} (hR : IsGlobalDivTower W P R) (n : ℕ) :
    (2 ^ n : ℕ) • R n = pointToKS S W P := by
  induction n with
  | zero => simpa using hR.1
  | succ n ih => rw [pow_succ, mul_comm, mul_nsmul, hR.2 n, ih]

omit [NumberField K] in
/-- **Towers add**: the sum of towers of `P` and `P'` is a tower of `P + P'` (tex 4005–4009).
PROVED. -/
theorem IsGlobalDivTower.add {P P' : W.toAffine.Point}
    {R R' : ℕ → (W.baseChange (KS K S)).toAffine.Point} (hR : IsGlobalDivTower W P R)
    (hR' : IsGlobalDivTower W P' R') : IsGlobalDivTower W (P + P') (R + R') :=
  ⟨by rw [Pi.add_apply, hR.1, hR'.1, map_add], fun n => by
    rw [Pi.add_apply, Pi.add_apply, nsmul_add, hR.2 n, hR'.2 n]⟩

variable (W) in
omit [NumberField K] in
/-- Non-vacuity of `IsGlobalDivTower`: the zero tower is a tower of the zero point. PROVED. -/
theorem isGlobalDivTower_zero :
    IsGlobalDivTower W 0 (0 : ℕ → (W.baseChange (KS K S)).toAffine.Point) :=
  ⟨by rw [map_zero]; rfl, fun n => by simp⟩

/-- The level-`n` Kummer value `g ↦ g R n − R n ∈ E(K_S)[2^n]` of a global tower (tex 4005–4009).
Kind: definition. -/
def globalKummerLev {P : W.toAffine.Point} {R : ℕ → (W.baseChange (KS K S)).toAffine.Point}
    (hR : IsGlobalDivTower W P R) (n : ℕ) (g : GKS K S) : Lev K S W n :=
  ⟨Affine.Point.map (W' := W) (galS K S g).toAlgHom (R n) - R n, (mem_lev_iff _).2 (by
    rw [nsmul_sub, ← map_nsmul, hR.two_pow_smul n, map_pointToKS, sub_self])⟩

/-- The level-`n` Kummer value on points. PROVED. -/
theorem coe_globalKummerLev {P : W.toAffine.Point} {R : ℕ → (W.baseChange (KS K S)).toAffine.Point}
    (hR : IsGlobalDivTower W P R) (n : ℕ) (g : GKS K S) :
    (globalKummerLev hR n g : Pt K S W) =
      Affine.Point.map (W' := W) (galS K S g).toAlgHom (R n) - R n :=
  rfl

/-- **The `2`-adic Kummer function of a global tower**, `g ↦ (g R n − R n)_n ∈ T₂E`
(tex 3895–3986, 4005–4009). Kind: definition. -/
def globalKummerFun {P : W.toAffine.Point} {R : ℕ → (W.baseChange (KS K S)).toAffine.Point}
    (hR : IsGlobalDivTower W P R) (g : GKS K S) : TateS K S W :=
  ⟨fun n => globalKummerLev hR n g, fun n => Subtype.ext (by
    rw [coe_transLev, coe_globalKummerLev, coe_globalKummerLev, nsmul_sub, ← map_nsmul, hR.2 n])⟩

/-- The coordinates of the `2`-adic Kummer function. PROVED. -/
theorem globalKummerFun_pt {P : W.toAffine.Point} {R : ℕ → (W.baseChange (KS K S)).toAffine.Point}
    (hR : IsGlobalDivTower W P R) (g : GKS K S) (n : ℕ) :
    (globalKummerFun hR g).pt n = Affine.Point.map (W' := W) (galS K S g).toAlgHom (R n) - R n :=
  rfl

/-- The cocycle identity `κ(gh) = g κ(h) + κ(g)` (tex 4005–4009). PROVED. -/
theorem globalKummerFun_mul {P : W.toAffine.Point} {R : ℕ → (W.baseChange (KS K S)).toAffine.Point}
    (hR : IsGlobalDivTower W P R) (g h : GKS K S) :
    globalKummerFun hR (g * h) = g • globalKummerFun hR h + globalKummerFun hR g := by
  apply TateS.ext'
  intro n
  rw [TateS.pt_add, TateS.pt_smul, globalKummerFun_pt, globalKummerFun_pt, globalKummerFun_pt,
    map_sub, Affine.Point.map_map]
  have e : (galS K S g).toAlgHom.comp (galS K S h).toAlgHom = (galS K S (g * h)).toAlgHom := rfl
  rw [e]
  abel

/-- **The level-`n` Kummer value is continuous**: the stabilizer of the point `R n` of `E(K_S)`
in `G_{K,S}` is open (the action of `G_{K,S}` on the discrete points `E(K_S)` is continuous,
`supportPoints_continuousSMul`). PROVED. -/
theorem continuous_globalKummerLev {P : W.toAffine.Point}
    {R : ℕ → (W.baseChange (KS K S)).toAffine.Point} (hR : IsGlobalDivTower W P R) (n : ℕ) :
    Continuous (globalKummerLev hR n) := by
  let Q : SupportPoints (S0 := S) W := R n
  have hc : Continuous (fun g : GKS K S =>
      (⟨g • Q - Q, (globalKummerLev hR n g).2⟩ :
        AddSubgroup.torsionBy (SupportPoints (S0 := S) W) ((2 ^ n : ℕ) : ℤ))) :=
    Continuous.subtype_mk ((continuous_id.smul continuous_const).sub continuous_const) _
  exact (continuous_of_discreteTopology (f := fun x : AddSubgroup.torsionBy
    (SupportPoints (S0 := S) W) ((2 ^ n : ℕ) : ℤ) => (⟨x.1, x.2⟩ : Lev K S W n))).comp hc

/-- **The `2`-adic Kummer function is continuous** for the inverse-limit topology of `T₂E`.
PROVED. -/
theorem continuous_globalKummerFun {P : W.toAffine.Point}
    {R : ℕ → (W.baseChange (KS K S)).toAffine.Point} (hR : IsGlobalDivTower W P R) :
    Continuous (globalKummerFun hR) :=
  continuous_induced_rng.mpr (continuous_pi fun n => continuous_globalKummerLev hR n)

/-- **The global `2`-adic Kummer cochain** `a_R ∈ C¹_cont(G_{K,S}, T₂E)`, `g ↦ (g R n − R n)_n`
(tex 3895–3986: the Kummer image of the point; tex 4005–4009). Kind: definition. -/
def globalKummerCochain {P : W.toAffine.Point}
    {R : ℕ → (W.baseChange (KS K S)).toAffine.Point} (hR : IsGlobalDivTower W P R) :
    contCochain ℤ_[2] (GKS K S) (TateS K S W) 1 :=
  ⟨(fun g => globalKummerFun hR (g 0) : (Fin 1 → GKS K S) → TateS K S W),
    (continuous_globalKummerFun hR).comp (continuous_apply 0)⟩

/-- **The global `2`-adic Kummer cochain is a cocycle** (tex 4005–4009). PROVED. -/
theorem globalKummerCochain_isCocycle {P : W.toAffine.Point}
    {R : ℕ → (W.baseChange (KS K S)).toAffine.Point} (hR : IsGlobalDivTower W P R) :
    contD ℤ_[2] (GKS K S) (TateS K S W) 1 (globalKummerCochain hR) = 0 := by
  apply Subtype.ext
  funext g
  have h1 := contCochains_d_apply (k := ℤ_[2]) (G := GKS K S) (M := TateS K S W) 1
    (globalKummerCochain hR) g
  refine h1.trans ?_
  rw [Fin.sum_univ_two]
  change g 0 • globalKummerFun hR (g 1) +
    ((-1 : ℤ_[2]) ^ ((0 : ℕ) + 1) • globalKummerFun hR (g 0 * g 1) +
    (-1 : ℤ_[2]) ^ ((1 : ℕ) + 1) • globalKummerFun hR (g 0)) = 0
  rw [globalKummerFun_mul]
  simp only [zero_add, pow_one, neg_one_smul, Nat.reduceAdd, even_two, Even.neg_pow, one_pow,
    one_smul]
  abel

/-- **The global cochain of a sum of towers is the sum of the cochains** (tex 4005–4009).
PROVED. -/
theorem globalKummerCochain_add {P P' : W.toAffine.Point}
    {R R' : ℕ → (W.baseChange (KS K S)).toAffine.Point}
    (hR : IsGlobalDivTower W P R) (hR' : IsGlobalDivTower W P' R') :
    globalKummerCochain (hR.add hR') = globalKummerCochain hR + globalKummerCochain hR' := by
  apply Subtype.ext
  funext g
  change globalKummerFun (hR.add hR') (g 0) = globalKummerFun hR (g 0) + globalKummerFun hR' (g 0)
  apply TateS.ext'
  intro n
  rw [TateS.pt_add, globalKummerFun_pt, globalKummerFun_pt, globalKummerFun_pt, Pi.add_apply,
    map_add]
  abel

variable (W) in
/-- The global cochain of the zero tower is zero. PROVED. -/
theorem globalKummerCochain_zero :
    globalKummerCochain (isGlobalDivTower_zero (S := S) W) = 0 := by
  apply Subtype.ext
  funext g
  change globalKummerFun (isGlobalDivTower_zero (S := S) W) (g 0) = 0
  apply TateS.ext'
  intro n
  rw [globalKummerFun_pt, TateS.pt_zero, Pi.zero_apply, map_zero, sub_zero]

/-- **The element of `T₂E` given by the difference of two towers of the same point**,
`(R n − R' n)_n` (tex 4005–4009). Kind: definition. -/
def towerDiffTate {P : W.toAffine.Point} {R R' : ℕ → (W.baseChange (KS K S)).toAffine.Point}
    (hR : IsGlobalDivTower W P R) (hR' : IsGlobalDivTower W P R') : TateS K S W :=
  ⟨fun n => ⟨R n - R' n, (mem_lev_iff _).2 (by
      rw [nsmul_sub, hR.two_pow_smul n, hR'.two_pow_smul n, sub_self])⟩,
    fun n => Subtype.ext (by
      rw [coe_transLev]
      change 2 • (R (n + 1) - R' (n + 1)) = R n - R' n
      rw [nsmul_sub, hR.2 n, hR'.2 n])⟩

omit [DecidableEq K] in
/-- The coordinates of a difference in `T₂E`. PROVED. -/
theorem tateS_pt_sub_apply (x y : TateS K S W) (n : ℕ) : (x - y).pt n = x.pt n - y.pt n :=
  rfl

/-- **Two towers of the same point give Kummer functions differing by the coboundary of the
difference of the towers** (tex 4005–4009). PROVED. -/
theorem globalKummerFun_sub {P : W.toAffine.Point}
    {R R' : ℕ → (W.baseChange (KS K S)).toAffine.Point}
    (hR : IsGlobalDivTower W P R) (hR' : IsGlobalDivTower W P R') (g : GKS K S) :
    globalKummerFun hR g - globalKummerFun hR' g =
      g • towerDiffTate hR hR' - towerDiffTate hR hR' := by
  apply TateS.ext'
  intro n
  rw [tateS_pt_sub_apply, tateS_pt_sub_apply, TateS.pt_smul, globalKummerFun_pt, globalKummerFun_pt]
  change _ = Affine.Point.map (W' := W) (galS K S g).toAlgHom (R n - R' n) - (R n - R' n)
  rw [map_sub]
  abel

end Tower

/-! ### The local towers and the restriction of the global cochain -/

section Local

variable {K : Type} [Field K] [NumberField K] [DecidableEq K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) (v : HeightOneSpectrum (𝓞 K)) [DecidableEq (v.adicCompletion K)]

/-- **The image `E(K) → E(K_v)` of rational points** (tex 3413–3438: the local points carried by
the Kummer conditions), the point map along `K → K_v`. Kind: definition. -/
def pointToKv : W.toAffine.Point →+ (W.baseChange (v.adicCompletion K)).toAffine.Point :=
  (Affine.Point.map (W' := W) (Algebra.ofId K (v.adicCompletion K))).comp
    (Affine.Point.equivBaseChangeSelf W.toAffine).toAddMonoidHom

variable {W}

/-- The two images of a rational point in `E(K̄_v)`, through `K_S` and through `K_v`, agree
(tex 3413–3438, 3455–3463). PROVED. -/
theorem compPt_pointToKS (P : W.toAffine.Point) :
    compPt W v (pointToKS S W P) =
      basePt (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (pointToKv W v P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Affine.Point.zero_def, map_zero, map_zero, map_zero, map_zero]
  · change compPt W v (Affine.Point.map (W' := W) (Algebra.ofId K (KS K S))
        (Affine.Point.equivBaseChangeSelf W.toAffine (.some x y h))) =
      basePt (v.adicCompletion K) (W.baseChange (v.adicCompletion K))
        (Affine.Point.map (W' := W) (Algebra.ofId K (v.adicCompletion K))
          (Affine.Point.equivBaseChangeSelf W.toAffine (.some x y h)))
    rw [Affine.Point.equivBaseChangeSelf_some, Affine.Point.map_some, Affine.Point.map_some,
      compPt_some, basePt_some]
    congr 1
    refine some_eq_some ?_ ?_ _ _
    · change embS K S v (algebraMap K (KS K S) x) = algebraMap (v.adicCompletion K)
        (AlgebraicClosure (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) x)
      rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
    · change embS K S v (algebraMap K (KS K S) y) = algebraMap (v.adicCompletion K)
        (AlgebraicClosure (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) y)
      rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

/-- **The local tower of a global tower**: `compPt W v ∘ R` is a compatible tower of the image of
`P` in `E(K_v)` (tex 3413–3438). PROVED. -/
theorem IsGlobalDivTower.isDivTower_compPt {P : W.toAffine.Point}
    {R : ℕ → (W.baseChange (KS K S)).toAffine.Point} (hR : IsGlobalDivTower W P R) :
    IsDivTower (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (pointToKv W v P)
      (fun n => compPt W v (R n)) :=
  ⟨by show compPt W v (R 0) = _; rw [hR.1, compPt_pointToKS], fun n => by
    show 2 • compPt W v (R (n + 1)) = compPt W v (R n)
    rw [← map_nsmul, hR.2 n]⟩

/-- Restriction `C¹_cont(G_{K,S}, T₂E) → C¹_cont(G_{K_v}, T₂E)` along the localization
(tex 3455–3463). Kind: definition. -/
abbrev resDegOne : contCochain ℤ_[2] (GKS K S) (TateS K S W) 1 →ₗ[ℤ_[2]]
    contCochain ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W)) 1 :=
  ((resCochains (k := ℤ_[2]) (M := TateS K S W) (locMap K S v)).f 1).hom

variable (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n)) [W.IsElliptic]

/-- **The restriction of the global Kummer cochain is the local `2`-adic Kummer cocycle of the
local tower, exactly** (tex 3413–3438: the global class lies in the local Kummer conditions).
PROVED. -/
theorem resDegOne_globalKummerCochain {P : W.toAffine.Point}
    {R : ℕ → (W.baseChange (KS K S)).toAffine.Point} (hR : IsGlobalDivTower W P R) :
    resDegOne v (globalKummerCochain hR) =
      tateKummerCocycleOf W hFull v (hR.isDivTower_compPt v) := by
  apply Subtype.ext
  funext x
  change globalKummerFun hR (locMap K S v (x 0)) =
    tateKummerFunOf W hFull v (hR.isDivTower_compPt v) (x 0)
  apply Subtype.ext
  funext n
  change globalKummerLev hR n (locMap K S v (x 0)) =
    (compTorsEquiv W (2 ^ n) (hFull n) v).symm (towerKummerOf (hR.isDivTower_compPt v) n (x 0))
  rw [AddEquiv.eq_symm_apply]
  apply Subtype.ext
  rw [compTorsEquiv_apply, coe_compTors, coe_towerKummerOf, coe_globalKummerLev, map_sub,
    compPt_smul]

end Local

/-! ### Degree-one classes of a cochain complex of modules -/

section Cycles

variable {A : Type} [CommRing A] (C : CochainComplex (ModuleCat.{0} A) ℤ)

/-- A degree-one cocycle of a cochain complex of modules, as an element of its cycles (the
degree-one classes of `C_K`, tex 4005–4009). Kind: definition. -/
def degOneCycle (c : C.X 1) (hc : (C.d 1 2).hom c = 0) : C.cycles 1 :=
  (C.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton A (C.X 1) c)) 2 (by simp)
    (by ext; simp [hc])).hom 1

/-- The cycle `degOneCycle C c hc` has underlying cochain `c` (tex 4005–4009). PROVED. -/
theorem iCycles_degOneCycle (c : C.X 1) (hc : (C.d 1 2).hom c = 0) :
    (C.iCycles 1).hom (degOneCycle C c hc) = c := by
  have h := congrArg (fun f => f.hom (1 : A))
    (C.liftCycles_i (ModuleCat.ofHom (LinearMap.toSpanSingleton A (C.X 1) c)) 2 (by simp)
      (by ext; simp [hc]))
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  have h2 : (ModuleCat.ofHom (LinearMap.toSpanSingleton A (C.X 1) c)).hom 1 = c := by simp
  exact h.trans h2

/-- The inclusion of degree-one cycles is injective (tex 4005–4009). PROVED. -/
theorem degOne_iCycles_injective : Function.Injective (C.iCycles 1).hom :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

/-- The cohomology class of a degree-one cocycle (tex 4005–4009). Kind: definition. -/
def degOneClass (c : C.X 1) (hc : (C.d 1 2).hom c = 0) : C.homology 1 :=
  (C.homologyπ 1).hom (degOneCycle C c hc)

/-- Equal cocycles have equal classes (tex 4005–4009). PROVED. -/
theorem degOneClass_congr {c c' : C.X 1} (h : c = c') (hc : (C.d 1 2).hom c = 0)
    (hc' : (C.d 1 2).hom c' = 0) : degOneClass C c hc = degOneClass C c' hc' := by
  subst h
  rfl

/-- The class is additive (tex 4005–4009). PROVED. -/
theorem degOneClass_add (c c' : C.X 1) (hc : (C.d 1 2).hom c = 0) (hc' : (C.d 1 2).hom c' = 0)
    (hcc : (C.d 1 2).hom (c + c') = 0) :
    degOneClass C (c + c') hcc = degOneClass C c hc + degOneClass C c' hc' := by
  have h : degOneCycle C (c + c') hcc = degOneCycle C c hc + degOneCycle C c' hc' := by
    apply degOne_iCycles_injective
    rw [map_add, iCycles_degOneCycle, iCycles_degOneCycle, iCycles_degOneCycle]
  rw [degOneClass, h, map_add]
  rfl

/-- The class is additive, for a cocycle equal to a sum (tex 4005–4009). PROVED. -/
theorem degOneClass_eq_add {c c₁ c₂ : C.X 1} (h : c = c₁ + c₂) (hc : (C.d 1 2).hom c = 0)
    (hc₁ : (C.d 1 2).hom c₁ = 0) (hc₂ : (C.d 1 2).hom c₂ = 0) :
    degOneClass C c hc = degOneClass C c₁ hc₁ + degOneClass C c₂ hc₂ := by
  subst h
  exact degOneClass_add C c₁ c₂ hc₁ hc₂ hc

/-- The class of the zero cocycle is zero (tex 4005–4009). PROVED. -/
theorem degOneClass_eq_zero {c : C.X 1} (h : c = 0) (hc : (C.d 1 2).hom c = 0) :
    degOneClass C c hc = 0 := by
  subst h
  have h0 : degOneCycle C 0 hc = 0 := by
    apply degOne_iCycles_injective
    rw [map_zero, iCycles_degOneCycle]
  rw [degOneClass, h0, map_zero]

/-- **Cocycles differing by a coboundary have the same class** (tex 4005–4009). PROVED. -/
theorem degOneClass_eq_of_sub_eq (c c' : C.X 1) (hc : (C.d 1 2).hom c = 0)
    (hc' : (C.d 1 2).hom c' = 0) (b : C.X 0) (hb : (C.d 0 1).hom b = c - c') :
    degOneClass C c hc = degOneClass C c' hc' := by
  have h : degOneCycle C c hc - degOneCycle C c' hc' = (C.toCycles 0 1).hom b := by
    apply degOne_iCycles_injective
    rw [map_sub, iCycles_degOneCycle, iCycles_degOneCycle, ← hb]
    exact (congrArg (fun f => f.hom b) (C.toCycles_i 0 1)).symm
  have h0 : (C.homologyπ 1).hom ((C.toCycles 0 1).hom b) = 0 :=
    congrArg (fun f => f.hom b) (C.toCycles_comp_homologyπ 0 1)
  rw [← sub_eq_zero, degOneClass, degOneClass, ← map_sub, h, h0]

variable {C} in
/-- **Naturality of the class**: a cochain map sends the class of a cocycle to the class of its
image (tex 3952–3962, 4005–4009: classes are compared along cochain maps). PROVED. -/
theorem homologyMap_degOneClass {C' : CochainComplex (ModuleCat.{0} A) ℤ} (φ : C ⟶ C') (c : C.X 1)
    (hc : (C.d 1 2).hom c = 0) (hc' : (C'.d 1 2).hom ((φ.f 1).hom c) = 0) :
    (HomologicalComplex.homologyMap φ 1).hom (degOneClass C c hc) =
      degOneClass C' ((φ.f 1).hom c) hc' := by
  have h1 : (HomologicalComplex.cyclesMap φ 1).hom (degOneCycle C c hc) =
      degOneCycle C' ((φ.f 1).hom c) hc' := by
    apply degOne_iCycles_injective C'
    rw [iCycles_degOneCycle]
    have h := congrArg (fun f => f.hom (degOneCycle C c hc)) (HomologicalComplex.cyclesMap_i φ 1)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h, iCycles_degOneCycle]
  have h2 := congrArg (fun f => f.hom (degOneCycle C c hc))
    (HomologicalComplex.homologyπ_naturality φ 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [degOneClass, h2, h1]
  rfl

end Cycles

/-! ### The Selmer cocycle and its class -/

section Selmer

variable {K : Type} [Field K] [NumberField K] [DecidableEq K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (W : WeierstrassCurve K) [W.IsElliptic] (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))

/-- **The global Kummer cochain is a closed degree-one global cochain of the genuine Selmer data**
`tateKummerSelData` (tex 4005–4009). PROVED. -/
theorem globalKummerCochain_closed {P : W.toAffine.Point}
    {R : ℕ → (W.baseChange (KS K S)).toAffine.Point} (hR : IsGlobalDivTower W P R) :
    (tateKummerSelData S W hFull).G.d 1 2 rfl (globalKummerCochain hR) = 0 :=
  globalKummerCochain_isCocycle hR

open scoped Classical in
/-- **The restriction map of the Selmer data sends the global Kummer cochain to the local Kummer
cocycles** (tex 3413–3438, 3455–3463). PROVED. -/
theorem res_globalKummerCochain {P : W.toAffine.Point}
    {R : ℕ → (W.baseChange (KS K S)).toAffine.Point} (hR : IsGlobalDivTower W P R)
    (v : Places K S) :
    (tateKummerSelData S W hFull).res.f 1 1 rfl (globalKummerCochain hR) v =
      tateKummerCocycleOf W hFull v.1 (hR.isDivTower_compPt v.1) :=
  resDegOne_globalKummerCochain v.1 hFull hR

open scoped Classical in
/-- **The degree-one Selmer cochain `(a_R, u_R, 0)` of a global tower** (tex 3895–3986,
4005–4009): the global Kummer cochain, and at every `v ∈ S` the local `2`-adic Kummer cocycle of
the local tower as an element of the Kummer condition `Z_v ⊔ B¹`. Kind: definition. -/
def kummerSelmerCochain {P : W.toAffine.Point}
    {R : ℕ → (W.baseChange (KS K S)).toAffine.Point} (hR : IsGlobalDivTower W P R) :
    (selCx (tateKummerSelData S W hFull)).X 1 :=
  show selT (tateKummerSelData S W hFull) 1 from
  (globalKummerCochain hR,
    fun v => ofCondOne (tateKummerZ W hFull v.1) (tateKummerZ_cocycle W hFull v.1)
      ⟨tateKummerCocycleOf W hFull v.1 (hR.isDivTower_compPt v.1),
        tateKummerCocycleOf_mem_sup W hFull v.1 _⟩,
    0)

/-- The global component of the Selmer cochain is the global Kummer cochain. PROVED. -/
theorem kummerSelmerCochain_fst {P : W.toAffine.Point}
    {R : ℕ → (W.baseChange (KS K S)).toAffine.Point} (hR : IsGlobalDivTower W P R) :
    (kummerSelmerCochain S W hFull hR).1 = globalKummerCochain hR :=
  rfl

open scoped Classical in
/-- The local component of the Selmer cochain at `v` is the local Kummer cocycle. PROVED. -/
theorem kummerSelmerCochain_local {P : W.toAffine.Point}
    {R : ℕ → (W.baseChange (KS K S)).toAffine.Point} (hR : IsGlobalDivTower W P R)
    (v : Places K S) :
    ((condOne (tateKummerZ W hFull v.1) (tateKummerZ_cocycle W hFull v.1)
        ((kummerSelmerCochain S W hFull hR).2.1 v) : ↥(tateKummerZ W hFull v.1 ⊔
          contB1 ℤ_[2] (Gloc K v.1) (ResMod (locMap K S v.1) (TateS K S W)))) :
        contCochain ℤ_[2] (Gloc K v.1) (ResMod (locMap K S v.1) (TateS K S W)) 1) =
      tateKummerCocycleOf W hFull v.1 (hR.isDivTower_compPt v.1) :=
  rfl

open scoped Classical in
/-- **The Selmer cochain of a global tower is a cocycle** of the Selmer complex
`selCx (tateKummerSelData S W hFull)` (tex 4005–4009): the global part is a cocycle, the local
conditions have zero differential out of degree one, and `res_v a_R − u_R(v) = 0`. PROVED. -/
theorem kummerSelmerCochain_d {P : W.toAffine.Point}
    {R : ℕ → (W.baseChange (KS K S)).toAffine.Point} (hR : IsGlobalDivTower W P R) :
    (selCx (tateKummerSelData S W hFull)).d 1 2 rfl (kummerSelmerCochain S W hFull hR) = 0 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact globalKummerCochain_isCocycle hR
  · funext v
    exact cocycleCondition_d₁ _ _ _
  · change (tateKummerSelData S W hFull).res.f 1 (2 - 1) (by omega) (globalKummerCochain hR) -
        (tateKummerSelData S W hFull).ι.f 1 (2 - 1) (by omega)
          (kummerSelmerCochain S W hFull hR).2.1 -
        (tateKummerSelData S W hFull).L.d (1 - 1) (2 - 1) (by omega) 0 = 0
    rw [map_zero, sub_zero, sub_eq_zero]
    funext v
    exact resDegOne_globalKummerCochain v.1 hFull hR

/-- The Selmer cochain is a cocycle of the ordinary compact Kummer complex `C_K`. PROVED. -/
theorem kummerSelmerCochain_closed {P : W.toAffine.Point}
    {R : ℕ → (W.baseChange (KS K S)).toAffine.Point} (hR : IsGlobalDivTower W P R) :
    ((compactKummerComplex S W hFull).d 1 2).hom (kummerSelmerCochain S W hFull hR) = 0 :=
  (GCx.toCC_d_hom (selCx (tateKummerSelData S W hFull)) 1 2 rfl _).trans
    (kummerSelmerCochain_d S W hFull hR)

/-- **The `2`-adic Kummer class of a rational point with a global tower**,
`[(a_R, u_R, 0)] ∈ H¹(C_K)` (tex 3895–3986: the Kummer image of the point in the ordinary compact
Kummer complex; tex 4005–4009). Kind: definition. -/
def kummerClassOf (P : W.toAffine.Point) (R : ℕ → (W.baseChange (KS K S)).toAffine.Point)
    (hR : IsGlobalDivTower W P R) : (compactKummerComplex S W hFull).homology 1 :=
  degOneClass (compactKummerComplex S W hFull) (kummerSelmerCochain S W hFull hR)
    (kummerSelmerCochain_closed S W hFull hR)

/-- **The global Kummer class** `[a_R] ∈ H¹_cont(G_{K,S}, T₂E)` of a global tower (tex
3895–3986: the Kummer image of the point in global cohomology). Kind: definition. -/
def globalKummerClass (P : W.toAffine.Point) (R : ℕ → (W.baseChange (KS K S)).toAffine.Point)
    (hR : IsGlobalDivTower W P R) : ((tateKummerSelData S W hFull).G.toCC).homology 1 :=
  degOneClass _ (globalKummerCochain hR)
    ((GCx.toCC_d_hom _ 1 2 rfl _).trans (globalKummerCochain_closed S W hFull hR))

/-- **The class in `H¹(C_K)` lifts the global Kummer class**: the projection
`C_K → C^•_cont(G_{K,S}, T₂E)`, `(a, u, x) ↦ a`, sends `kummerClassOf` to `globalKummerClass`
(tex 3895–3986, 4005–4009). PROVED. -/
theorem homologyMap_projG_kummerClassOf (P : W.toAffine.Point)
    (R : ℕ → (W.baseChange (KS K S)).toAffine.Point) (hR : IsGlobalDivTower W P R) :
    (HomologicalComplex.homologyMap (GHom.toCC (projG (tateKummerSelData S W hFull))) 1).hom
        (kummerClassOf S W hFull P R hR) = globalKummerClass S W hFull P R hR :=
  homologyMap_degOneClass _ _ _ _

/-! ### Independence of the tower -/

open scoped Classical in
/-- **The degree-zero Selmer cochain of the difference of two towers**: the constant `0`-cochain
of `(R n − R' n)_n ∈ T₂E` globally and in every local condition, `0` in the local component
(tex 4005–4009). Kind: definition. -/
def towerDiffSelmer {P : W.toAffine.Point} {R R' : ℕ → (W.baseChange (KS K S)).toAffine.Point}
    (hR : IsGlobalDivTower W P R) (hR' : IsGlobalDivTower W P R') :
    (selCx (tateKummerSelData S W hFull)).X 0 :=
  show selT (tateKummerSelData S W hFull) 0 from
  (constCochain (towerDiffTate hR hR'),
    fun v => ofCondZero (tateKummerZ W hFull v.1) (tateKummerZ_cocycle W hFull v.1)
      (constCochain (show ResMod (locMap K S v.1) (TateS K S W) from towerDiffTate hR hR')),
    0)

open scoped Classical in
/-- **The Selmer cochains of two towers of the same point differ by a coboundary**, that of
`towerDiffSelmer`, globally and locally (tex 4005–4009). PROVED. -/
theorem towerDiffSelmer_d {P : W.toAffine.Point}
    {R R' : ℕ → (W.baseChange (KS K S)).toAffine.Point}
    (hR : IsGlobalDivTower W P R) (hR' : IsGlobalDivTower W P R') :
    (selCx (tateKummerSelData S W hFull)).d 0 1 rfl (towerDiffSelmer S W hFull hR hR') =
      kummerSelmerCochain S W hFull hR - kummerSelmerCochain S W hFull hR' := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply Subtype.ext
    funext g
    change cfun (contD ℤ_[2] (GKS K S) (TateS K S W) 0 (constCochain (towerDiffTate hR hR'))) g =
      globalKummerFun hR (g 0) - globalKummerFun hR' (g 0)
    rw [cfun_contD_constCochain, globalKummerFun_sub]
  · funext v
    apply Subtype.ext
    refine (cocycleCondition_d₀ _ _ _).trans ?_
    change contD ℤ_[2] (Gloc K v.1) (ResMod (locMap K S v.1) (TateS K S W)) 0
        (constCochain (show ResMod (locMap K S v.1) (TateS K S W) from towerDiffTate hR hR')) =
      tateKummerCocycleOf W hFull v.1 (hR.isDivTower_compPt v.1) -
        tateKummerCocycleOf W hFull v.1 (hR'.isDivTower_compPt v.1)
    rw [← resDegOne_globalKummerCochain v.1 hFull hR, ← resDegOne_globalKummerCochain v.1 hFull hR']
    apply Subtype.ext
    funext x
    change cfun (contD ℤ_[2] (Gloc K v.1) (ResMod (locMap K S v.1) (TateS K S W)) 0
        (constCochain (show ResMod (locMap K S v.1) (TateS K S W) from towerDiffTate hR hR'))) x =
      globalKummerFun hR (locMap K S v.1 (x 0)) - globalKummerFun hR' (locMap K S v.1 (x 0))
    rw [cfun_contD_constCochain, globalKummerFun_sub]
    rfl
  · change (tateKummerSelData S W hFull).res.f 0 (1 - 1) (by omega)
        (constCochain (towerDiffTate hR hR')) -
        (tateKummerSelData S W hFull).ι.f 0 (1 - 1) (by omega)
          (towerDiffSelmer S W hFull hR hR').2.1 -
        (tateKummerSelData S W hFull).L.d (0 - 1) (1 - 1) (by omega) 0 = 0 - 0
    rw [map_zero, sub_zero, sub_zero, sub_eq_zero]
    rfl

/-- **The class does not depend on the tower** (tex 4005–4009). PROVED. -/
theorem kummerClassOf_eq {P : W.toAffine.Point}
    {R R' : ℕ → (W.baseChange (KS K S)).toAffine.Point}
    (hR : IsGlobalDivTower W P R) (hR' : IsGlobalDivTower W P R') :
    kummerClassOf S W hFull P R hR = kummerClassOf S W hFull P R' hR' :=
  degOneClass_eq_of_sub_eq _ _ _ _ _ (towerDiffSelmer S W hFull hR hR')
    ((GCx.toCC_d_hom (selCx (tateKummerSelData S W hFull)) 0 1 rfl _).trans
      (towerDiffSelmer_d S W hFull hR hR'))

/-! ### Additivity -/

open scoped Classical in
/-- The Selmer cochain of a sum of towers is the sum of the Selmer cochains. PROVED. -/
theorem kummerSelmerCochain_add {P P' : W.toAffine.Point}
    {R R' : ℕ → (W.baseChange (KS K S)).toAffine.Point}
    (hR : IsGlobalDivTower W P R) (hR' : IsGlobalDivTower W P' R') :
    kummerSelmerCochain S W hFull (hR.add hR') =
      kummerSelmerCochain S W hFull hR + kummerSelmerCochain S W hFull hR' := by
  refine Prod.ext (globalKummerCochain_add hR hR') (Prod.ext ?_ ?_)
  · funext v
    apply Subtype.ext
    change tateKummerCocycleOf W hFull v.1 ((hR.add hR').isDivTower_compPt v.1) =
      tateKummerCocycleOf W hFull v.1 (hR.isDivTower_compPt v.1) +
        tateKummerCocycleOf W hFull v.1 (hR'.isDivTower_compPt v.1)
    rw [← resDegOne_globalKummerCochain v.1 hFull (hR.add hR'),
      ← resDegOne_globalKummerCochain v.1 hFull hR, ← resDegOne_globalKummerCochain v.1 hFull hR',
      globalKummerCochain_add, map_add]
  · exact (add_zero 0).symm

/-- **The class of a sum of towers is the sum of the classes** (tex 4005–4009). PROVED. -/
theorem kummerClassOf_add {P P' : W.toAffine.Point}
    {R R' : ℕ → (W.baseChange (KS K S)).toAffine.Point}
    (hR : IsGlobalDivTower W P R) (hR' : IsGlobalDivTower W P' R') :
    kummerClassOf S W hFull (P + P') (R + R') (hR.add hR') =
      kummerClassOf S W hFull P R hR + kummerClassOf S W hFull P' R' hR' :=
  degOneClass_eq_add _ (kummerSelmerCochain_add S W hFull hR hR') _ _ _

open scoped Classical in
/-- The Selmer cochain of the zero tower is zero. PROVED. -/
theorem kummerSelmerCochain_zero :
    kummerSelmerCochain S W hFull (isGlobalDivTower_zero (S := S) W) = 0 := by
  refine Prod.ext (globalKummerCochain_zero W) (Prod.ext ?_ rfl)
  funext v
  apply Subtype.ext
  change tateKummerCocycleOf W hFull v.1 ((isGlobalDivTower_zero (S := S) W).isDivTower_compPt v.1)
    = 0
  rw [← resDegOne_globalKummerCochain v.1 hFull (isGlobalDivTower_zero (S := S) W),
    globalKummerCochain_zero, map_zero]

/-- **Non-vacuity: the zero tower of the zero point has class zero.** PROVED. -/
theorem kummerClassOf_zero :
    kummerClassOf S W hFull 0 0 (isGlobalDivTower_zero (S := S) W) = 0 :=
  degOneClass_eq_zero _ (kummerSelmerCochain_zero S W hFull) _

end Selmer

/-! ### Global division towers and the class map -/

section ClassMap

variable {K : Type} [Field K] [NumberField K] [DecidableEq K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (W : WeierstrassCurve K)

/-- **Every rational point has a global tower of `2`-power division points in `E(K_S)`**
(tex 3895–3986, 4005–4009). Kind: GLUE (Silverman, *The Arithmetic of Elliptic Curves*,
VIII.1.5(b): `K(2^{-n}P)/K` is unramified outside the places above `2` and of bad reduction),
kept as a `Prop`; it is PROVED from good reduction outside `S` in
`globalDivisionTowers_of_goodReduction`. -/
def GlobalDivisionTowers : Prop :=
  ∀ P : W.toAffine.Point, ∃ R : ℕ → (W.baseChange (KS K S)).toAffine.Point,
    IsGlobalDivTower W P R

omit [NumberField K] in
/-- **Global towers give the finite-level division-point input at every precision**: the level-`i`
point of a tower is a `2^i`-division point of `P` in `E(K_S)`, so `GlobalDivisionTowers` implies
`GlobalDivisionPointsInSupport` of the finite-level packet for every `i` (tex 3895–3986). PROVED. -/
theorem GlobalDivisionTowers.globalDivisionPointsInSupport (hdiv : GlobalDivisionTowers S W)
    (i : ℕ) :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport
      (S0 := S) W i := fun P =>
  ⟨(hdiv P).choose i, (hdiv P).choose_spec.two_pow_smul i⟩

open scoped Classical in
/-- **Global towers from good reduction** (Silverman AEC VIII.1.5(b), tex 3895–3986): if `S`
contains the places above `2` and `E` has good reduction outside `S`, every rational point has a
global tower in `E(K_S)`. The tower is a tower of `2`-power division points over `K̄`
(`divTower`), whose points are defined over `K_S` by the division-point support theorem
`DivisionPoints.exists_supportPoint_map_eq`. PROVED. -/
theorem globalDivisionTowers_of_goodReduction [W.IsElliptic]
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hgood : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ZInQ.Manuscript.RC.DivisionPoints.HasGoodReductionAt W v) :
    GlobalDivisionTowers S W := by
  intro P
  have hT := isDivTower_divTower K W P
  have hdiv : ∀ n, ∃ Q : (W.baseChange (KS K S)).toAffine.Point,
      Affine.Point.map (W' := W) (unramifiedOutside K S).val Q = divTower K W P n := fun n =>
    ZInQ.Manuscript.RC.DivisionPoints.exists_supportPoint_map_eq W (m := 2 ^ n)
      (pow_ne_zero _ two_ne_zero)
      (fun v hv => h2 v (ZInQ.Manuscript.RC.DivisionPoints.natCast_mem_of_two_pow hv)) hgood P
      _ (hT.two_pow_smul n)
  choose R hR using hdiv
  refine ⟨R, ?_, fun n => ?_⟩
  · apply Affine.Point.map_injective (W' := W) (unramifiedOutside K S).val
    rw [hR 0, hT.1]
    exact (ZInQ.Manuscript.RC.DivisionPoints.map_map_ofId W (unramifiedOutside K S).val _).symm
  · apply Affine.Point.map_injective (W' := W) (unramifiedOutside K S).val
    rw [map_nsmul, hR, hR]
    exact hT.2 n

/-- **Non-vacuity of `GlobalDivisionTowers`**: for `S` the set of all finite places, every
elliptic curve has global towers. PROVED. -/
theorem globalDivisionTowers_univ [W.IsElliptic] :
    GlobalDivisionTowers (Set.univ : Set (HeightOneSpectrum (𝓞 K))) W :=
  globalDivisionTowers_of_goodReduction _ W (fun v _ => Set.mem_univ v)
    (fun v hv => absurd (Set.mem_univ v) hv)

/-- **Global towers for `E_ℓ : y² = x(x − ℓ)(x + 3ℓ)`** (tex 3895–3986) when `S` contains the
places above `2` and `3` and `ℓ ≠ 0` is a unit outside `S` (good reduction outside `S`,
`DivisionPoints.hasGoodReductionAt_curveEll`). PROVED. -/
theorem globalDivisionTowers_curveEll {ℓ : K} (hℓ0 : ℓ ≠ 0)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (h3 : ∀ v : HeightOneSpectrum (𝓞 K), (3 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hℓ : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v.valuation K ℓ = 1) :
    GlobalDivisionTowers S (curveEll ℓ) := by
  have := isElliptic_curveEll hℓ0
  exact globalDivisionTowers_of_goodReduction S (curveEll ℓ) h2 fun v hv =>
    ZInQ.Manuscript.RC.DivisionPoints.hasGoodReductionAt_curveEll v (hℓ v hv)
      (fun h => hv (h2 v h)) (fun h => hv (h3 v h))

variable [W.IsElliptic] (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))

/-- **The global `2`-adic Kummer class map** `E(K) →+ H¹(C_K)`, `P ↦ [(a_R, u_R, 0)]` for any
global tower `R` of `P` (tex 3895–3986: `z₀ = i(LmP)` is the Kummer image of a point; tex
4005–4009). Kind: definition. -/
def kummerClass (hdiv : GlobalDivisionTowers S W) :
    W.toAffine.Point →+ (compactKummerComplex S W hFull).homology 1 :=
  AddMonoidHom.mk' (fun P => kummerClassOf S W hFull P (hdiv P).choose (hdiv P).choose_spec)
    fun P Q => (kummerClassOf_eq S W hFull (hdiv (P + Q)).choose_spec
      ((hdiv P).choose_spec.add (hdiv Q).choose_spec)).trans
        (kummerClassOf_add S W hFull (hdiv P).choose_spec (hdiv Q).choose_spec)

/-- **The class map agrees with `kummerClassOf` for every tower** (tex 4005–4009). PROVED. -/
theorem kummerClass_apply (hdiv : GlobalDivisionTowers S W) {P : W.toAffine.Point}
    {R : ℕ → (W.baseChange (KS K S)).toAffine.Point} (hR : IsGlobalDivTower W P R) :
    kummerClass S W hFull hdiv P = kummerClassOf S W hFull P R hR :=
  kummerClassOf_eq S W hFull _ hR

end ClassMap

/-! ### The rational class in `H¹(K₀) = H¹(C_K) ⊗ ℚ₂` -/

section Rational

/-- The element `1 ∈ ℚ₂`, read in `ℚ₂` as a `ℤ₂`-module (tex 3952–3962). Kind: definition. -/
def oneQ2 : (ModuleCat.restrictScalars (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2])).obj
    (ModuleCat.of ℚ_[2] ℚ_[2]) :=
  show ℚ_[2] from 1

/-- **Rationalization** `x ↦ 1 ⊗ x`, `M → ℚ₂ ⊗_{ℤ₂} M` (tex 3952–3962: `K₀ = C_K ⊗ ℚ₂`).
Kind: definition. -/
def rationalize (M : ModuleCat.{0} ℤ_[2]) :
    M →+ (ModuleCat.extendScalars (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2])).obj M :=
  (TensorProduct.mk ℤ_[2] _ M oneQ2).toAddMonoidHom

variable {K : Type} [Field K] [NumberField K] [DecidableEq K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (W : WeierstrassCurve K) [W.IsElliptic] (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))

/-- **The rational Kummer class of a rational point** in `H¹(K₀)`, for the ordinary rational
Kummer complex `K₀ = C_K ⊗ ℚ₂` (`rationalKummerComplex`): `1 ⊗ kummerClass P` transported along
`H¹(K₀) ≅ H¹(C_K) ⊗ ℚ₂` (`rationalKummerHomologyIso`). This is the class `P ∈ H¹(K₀)` of
`z₀ = i(LmP)` (tex 3952–3962, 3895–3986). Kind: definition. -/
def rationalKummerClass (hdiv : GlobalDivisionTowers S W) :
    W.toAffine.Point →+ (rationalKummerComplex S W hFull).homology 1 :=
  (rationalKummerHomologyIso S W hFull 1).inv.hom.toAddMonoidHom.comp
    ((rationalize _).comp (kummerClass S W hFull hdiv))

/-- The rational class is `1 ⊗ kummerClassOf` for every tower (tex 3952–3962). PROVED. -/
theorem rationalKummerClass_apply (hdiv : GlobalDivisionTowers S W) {P : W.toAffine.Point}
    {R : ℕ → (W.baseChange (KS K S)).toAffine.Point} (hR : IsGlobalDivTower W P R) :
    rationalKummerClass S W hFull hdiv P =
      (rationalKummerHomologyIso S W hFull 1).inv.hom
        (TensorProduct.tmul ℤ_[2] oneQ2 (kummerClassOf S W hFull P R hR)) := by
  change (rationalKummerHomologyIso S W hFull 1).inv.hom
      (TensorProduct.tmul ℤ_[2] oneQ2 (kummerClass S W hFull hdiv P)) = _
  rw [kummerClass_apply S W hFull hdiv hR]

/-- **The comparison of input (1) on the rational Kummer class** (tex 3952–3962): for the cochain
map `genuineKummerModelMap S W hFull Dm φ : K₀ → CU ⊗ ℚ₂` built from a degree-one identification
`φ : H¹(K₀) ≃ ker ρ(Dm)`, the image `i(P)` of the rational Kummer class, read in the central
kernel, is `φ(P)`. PROVED (from `twoTermCentralH1_homologyMap_kummerModelMap`). -/
theorem twoTermCentralH1_rationalKummerClass (hdiv : GlobalDivisionTowers S W) {m : ℕ}
    (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT)
    (φ : (rationalKummerComplex S W hFull).homology 1 ≃ₗ[ℚ_[2]]
      LinearMap.ker (Dm.map Rings.rhoT).mulVecLin) (P : W.toAffine.Point) :
    twoTermCentralH1 Dm ((HomologicalComplex.homologyMap (genuineKummerModelMap S W hFull Dm φ)
        1).hom (rationalKummerClass S W hFull hdiv P)) =
      φ (rationalKummerClass S W hFull hdiv P) :=
  twoTermCentralH1_homologyMap_kummerModelMap _ φ _

end Rational

/-! ### Non-vacuity over `ℚ` -/

section Example

/-- The full `2`-power torsion of `y² = x³ − x` over `ℚ` is defined over `ℚ_S` for `S` all
finite places (from good reduction outside `S`; the hypothesis `hFull` of `C_K`, tex 4005–4009).
PROVED. -/
theorem fullTorsion_curveY2X3mX_univ (n : ℕ) :
    FullTorsion ℚ (Set.univ : Set (HeightOneSpectrum (𝓞 ℚ))) curveY2X3mX (2 ^ n) :=
  ZInQ.Manuscript.RC.DivisionPoints.fullTorsion_two_pow_of_goodReduction curveY2X3mX
    (fun v _ => Set.mem_univ v) (fun v hv => absurd (Set.mem_univ v) hv) n

/-- **Non-vacuity of the class map**: for `y² = x³ − x` over `ℚ` and `S` all finite places, both
hypotheses hold and the class map `E(ℚ) →+ H¹(C_K)` is defined (tex 3895–3986, 4005–4009).
Kind: definition. -/
def kummerClassY2X3mX : curveY2X3mX.toAffine.Point →+
    (compactKummerComplex (Set.univ : Set (HeightOneSpectrum (𝓞 ℚ))) curveY2X3mX
      fullTorsion_curveY2X3mX_univ).homology 1 :=
  kummerClass _ curveY2X3mX fullTorsion_curveY2X3mX_univ (globalDivisionTowers_univ curveY2X3mX)

/-- The finite places of `ℚ` above `2` or `3`, a finite support for `E_1 : y² = x(x − 1)(x + 3)`
(the curve `E_ℓ` of tex 1760–1830 at `ℓ = 1`). Kind: definition. -/
def placesTwoThree : Set (HeightOneSpectrum (𝓞 ℚ)) :=
  {v | (2 : 𝓞 ℚ) ∈ v.asIdeal ∨ (3 : 𝓞 ℚ) ∈ v.asIdeal}

/-- A nonzero element of `𝓞 ℚ` lies in finitely many finite places (tex 3455–3463: `S` finite).
PROVED. -/
theorem finite_setOf_mem_ratInt {x : 𝓞 ℚ} (hx : x ≠ 0) :
    {v : HeightOneSpectrum (𝓞 ℚ) | x ∈ v.asIdeal}.Finite :=
  (Ideal.finite_factors (I := Ideal.span {x}) (by simpa using hx)).subset
    fun _ hv => Ideal.dvd_span_singleton.mpr hv

/-- The places above `2` and `3` form a finite set (tex 3455–3463). PROVED. -/
theorem placesTwoThree_finite : placesTwoThree.Finite := by
  have h3 : (3 : 𝓞 ℚ) ≠ 0 := fun h => by
    have := congrArg (algebraMap (𝓞 ℚ) ℚ) h
    rw [map_ofNat, map_zero] at this
    norm_num at this
  exact (finite_setOf_mem_ratInt (x := 2) two_ne_zero).union (finite_setOf_mem_ratInt (x := 3) h3)

/-- `E_1 : y² = x(x − 1)(x + 3)` over `ℚ` is elliptic (tex 1760–1830). PROVED. -/
theorem isElliptic_curveEll_one : (curveEll (1 : ℚ)).IsElliptic :=
  isElliptic_curveEll one_ne_zero

attribute [local instance] isElliptic_curveEll_one

/-- The full `2`-power torsion of `E_1` is defined over `ℚ_S`, `S` the places above `2` and `3`
(good reduction outside `S`; the hypothesis `hFull` of `C_K`, tex 4005–4009). PROVED. -/
theorem fullTorsion_curveEll_one (n : ℕ) :
    FullTorsion ℚ placesTwoThree (curveEll (1 : ℚ)) (2 ^ n) :=
  ZInQ.Manuscript.RC.DivisionPoints.fullTorsion_two_pow_of_goodReduction _
    (fun _ hv => Or.inl hv)
    (fun v hv => ZInQ.Manuscript.RC.DivisionPoints.hasGoodReductionAt_curveEll v (map_one _)
      (fun h => hv (Or.inl h)) (fun h => hv (Or.inr h))) n

/-- **Non-vacuity of `GlobalDivisionTowers` for a finite support**: `E_1` has global towers for
`S` the places above `2` and `3` (tex 3895–3986). PROVED. -/
theorem globalDivisionTowers_curveEll_one :
    GlobalDivisionTowers placesTwoThree (curveEll (1 : ℚ)) :=
  globalDivisionTowers_curveEll placesTwoThree one_ne_zero (fun _ hv => Or.inl hv)
    (fun _ hv => Or.inr hv) (fun _ _ => map_one _)

/-- **The class map of `E_1` over `ℚ`** for `S` the places above `2` and `3`, with both hypotheses
supplied (tex 3895–3986, 4005–4009). Kind: definition. -/
def kummerClassE1 : (curveEll (1 : ℚ)).toAffine.Point →+
    (compactKummerComplex placesTwoThree (curveEll (1 : ℚ)) fullTorsion_curveEll_one).homology 1 :=
  kummerClass _ _ fullTorsion_curveEll_one globalDivisionTowers_curveEll_one

/-- The Kummer data of `E_1` for `S` the places above `2` and `3` are genuine Galois Selmer data
(`IsGaloisSelData`, `S` finite; tex 3455–3463, 4005–4009). PROVED. -/
theorem isGaloisSelData_curveEll_one :
    ZInQ.Manuscript.RC.Wiring.IsGaloisSelData
      (tateKummerSelData placesTwoThree (curveEll (1 : ℚ)) fullTorsion_curveEll_one) :=
  isGaloisSelData_tateKummerSelData _ _ _ placesTwoThree_finite

end Example

end ZInQ.Manuscript.RC.CalPoint
