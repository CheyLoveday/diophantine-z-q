import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitAddressPin

/-!
# Theorem 5.3, Lane RC0 round 19: the pinned height-one leaf over one moving character per family

Proposition `ex:limits-uniform-lower-bound`, height-one regularity (tex 4976–5200), over the
moving characters of tex 2725–2741 and 4255–4280. The pinned leaf `PrimRegularityInputsILP`
(`Wiring/InnerLimitAddressPin.lean`) left the moving exponents `ξ_i` free beyond an open kernel
and triviality above `2N`, and chose the field data, the address family and its retained limit
afresh at each height-one prime. With `ξ_i = 1` the family does not move (`α_i = χ_h`), its
retained limit is the constant twist family, and every prime is terminal. This file restates the
leaf with the text's moving character and quantifier order.

* `FamilyMovingCharacter K ℓ Q` (F1): one moving character per family and stage: the moving
  conductor primes `r_i` (rational primes, injective in `i`, outside `Q` and `2N`), the moving
  supports `Sr i` (finite, containing the places above `r_i`), and `ψ_i : G_{K, Sr i} → ℤ/2^{2i}`
  with open kernel, trivial on the decomposition groups above `2N` (tex 2729, 3430–3432),
  surjective on the inertia group at a place above `r_i` (ramified there; tex 2729–2731,
  4260–4262), and with value `1` on an arithmetic Frobenius lift at a chosen orientation above
  every `q ∈ Q` (tex 2733–2735, 4275–4277). The text's characters satisfy these (Proposition
  `ex:arith-moving-character`; the tree's `moving_character_ecurve_genuineS` through the genuine
  ring-class realization).
* `AddressMovingFamilyR Ψ h W`: the address's moving stage family over the family's character:
  characters `α_i = χ_h · (1 + t)^{ψ_i}` (the family's `ψ_i` inflated to the address's support,
  the same `Ψ_i` for all characters of the family, tex 2737), old supports `S_i` = the places above
  `2N`, the places above `h` and the moving support `Sr i`, and old conditions the actual Kummer
  conditions above `2N` and the full conditions elsewhere (lane RC29's table).
* `LabelFamilyOf ℓ h Fam₀`, `InnerLimitSwitchPinnedOn`: the label families of a base family and
  the linked switches on them (as `AddressLabelFamily`, `InnerLimitSwitchPinned`, for any base).
* `PinnedLimitAt A L u P`: the clause at a height-one prime for a fixed address family and limit.
* `RegularityInputsILQFam`, `RegularityInputsILQ`, `PrimRegularityInputsILQ` (F2): the field data
  and the family's moving character before the addresses; at every address with `u ≠ 0` the
  address family and its retained limit before the primes. PROVED: the consumers
  (`PrimRegularityInputsILQ.toMdl`, `primRegularityInputs_of_ILQ`, `heightOneTarget_of_ILQ`), the
  degenerate case (`primRegularityInputsILQ_of_uPrim_zero`).
* The collapse. PROVED: `AddressMovingFamilyR.inertia_onto` (the address's exponents are surjective
  on inertia at `r_i`), `AddressMovingFamilyR.exponent_ne_one` and
  `AddressMovingFamilyR.character_ne_quad` (so `ξ_i = 1`, the non-moving family `α_i = χ_h`, is
  excluded at every positive stage), and `PinnedLimitAt.terminal_of_stationary` (a stationary
  family forces `dim H¹ = 1` of the finite fibre of the fixed limit, in both branches).

At the quadratic primes `(t)`, `(t + 2)` only the actual fibre is pinned: the switches and
successor fibres of the homology-level data are not tied to the address's families (F3,
documented). The derivative conditions at the previous labels of a label family are not pinned
(in the text the singular side: "all earlier singular conditions", tex 5141–5143, 5168–5170).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Filter NumberField IsDedekindDomain IsLocalRing Matrix Module
open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Manuscript.RC.Uniform (Lambda finPlane lambdaHalfToFrac)
open ZInQ.Manuscript.RC.Limits (stageIdeal stageIdeal_tendsToZero)
open ZInQ.Contrib.RC53Assist.InnerLimit (fibreLimitGlobal finiteLimitSide)
open ZInQ.Manuscript.RC.CoefModules (ActualConj IsOpenKer CondAt Mcoef fullAt FullTorsion KS
  alphaChar quadChar)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.SelmerComplex (GKS Places Gloc locMap inflMap locMap_compat)
open ZInQ.Manuscript.RC.KummerMaps (actualKummerAtS IsLocallyQuadAt)
open ZInQ.Manuscript.RC.Wiring.StageSupport (condToMinS)
open ZInQ.Contrib.RC53Assist.OldOrthogonality.SupportCoefficients (characterAfterSupport)
open ZInQ.Contrib.RC53Assist.InnerLimitMoving (IntegralMatrixStageData selmerStages
  derivativeDiagram retainedRestrictionStages)
open ZInQ.Contrib.CloudB3RC53.CST (newformLevel)
open ZInQ.Manuscript.RC.Rings (isDiscreteValuationRing_atPrime_of_height_one)
open scoped PowerSeries.WithPiTopology

/-! **One moving character per family** -/

section Character

variable (K : Type) [Field K] [NumberField K]

/-- **The family's moving character** (tex 2725–2741, 4255–4280; Proposition
`ex:arith-moving-character`, tex 3500–3702), for the orientation primes `Q` (the union of the
prime supports of the family, tex 2732): at each stage `i`
* `r i`: the moving conductor prime, a rational prime, injective in `i`, outside `Q` and not
  dividing `2N` (tex 2737–2741, 4268–4270);
* `Sr i`: the moving support, finite, containing the places above `r i`;
* `ψ i : G_{K, Sr i} → ℤ/2^{2i}`: the moving exponent (`Ψ_i = (1 + t)^{ψ_i}`), with open kernel;
* `twoN`: trivial on the decomposition groups above `2N` (tex 2729, 3430–3432);
* `placeR`, `inertia_onto`: surjective on the inertia group at a place above `r i`, so ramified
  there (tex 2729–2731, 4260–4262);
* `orient`, `orient_one`: at a chosen orientation above every `q ∈ Q`, value `1` on every
  arithmetic Frobenius lift (tex 2733–2735, 4275–4277);
* `orientBar`, `orientBar_neg`: at the conjugate orientation, value `−1` on every arithmetic
  Frobenius lift (tex 4262–4264).
Kind: definition (data and ELLIOT). -/
structure FamilyMovingCharacter (ℓ : ℕ) (Q : Finset ℕ) where
  /-- The moving conductor primes. -/
  r : ℕ → ℕ
  /-- They are prime. -/
  r_prime : ∀ i, (r i).Prime
  /-- They vary with the stage. -/
  r_injective : Function.Injective r
  /-- They are outside `Q`. -/
  r_notQ : ∀ i, r i ∉ Q
  /-- They do not divide `2N`. -/
  r_not_twoN : ∀ i, ¬ r i ∣ 2 * newformLevel (Ecurve ℓ)
  /-- The moving supports. -/
  Sr : ℕ → Set (HeightOneSpectrum (𝓞 K))
  /-- They are finite. -/
  Sr_finite : ∀ i, (Sr i).Finite
  /-- They contain the places above `r i`. -/
  Sr_r : ∀ i, placesOf K (r i : ℤ) ⊆ Sr i
  /-- The moving exponents. -/
  ψ : ∀ i, GKS K (Sr i) →* Multiplicative (ZMod (2 ^ (2 * i)))
  /-- They have open kernels. -/
  ψ_open : ∀ i, IsOpen ((ψ i).ker : Set (GKS K (Sr i)))
  /-- Trivial on the decomposition groups above `2N`. -/
  twoN : ∀ i, ∀ v ∈ placesTwoN K ℓ, ∀ σ : Gloc K v, ψ i (locMap K (Sr i) v σ) = 1
  /-- A place above `r i`. -/
  placeR : ℕ → HeightOneSpectrum (𝓞 K)
  /-- It lies above `r i`. -/
  placeR_over : ∀ i, placeR i ∈ placesOf K (r i : ℤ)
  /-- Surjective on the inertia group there. -/
  inertia_onto : ∀ i, ∀ y : ZMod (2 ^ (2 * i)),
    ∃ σ ∈ TauCeti.inertiaSubgroup ((placeR i).adicCompletion K),
      ψ i (locMap K (Sr i) (placeR i) σ) = Multiplicative.ofAdd y
  /-- The chosen orientations. -/
  orient : ℕ → HeightOneSpectrum (𝓞 K)
  /-- The orientation of `q` lies above `q`. -/
  orient_over : ∀ q ∈ Q, orient q ∈ placesOf K (q : ℤ)
  /-- Value `1` on every arithmetic Frobenius lift at each orientation. -/
  orient_one : ∀ i, ∀ q ∈ Q, ∀ φ : Gloc K (orient q),
    TauCeti.IsArithFrobeniusLift ((orient q).adicCompletion K) φ →
      ψ i (locMap K (Sr i) (orient q) φ) = Multiplicative.ofAdd 1
  /-- The conjugate orientations. -/
  orientBar : ℕ → HeightOneSpectrum (𝓞 K)
  /-- The conjugate orientation of `q` lies above `q`. -/
  orientBar_over : ∀ q ∈ Q, orientBar q ∈ placesOf K (q : ℤ)
  /-- Value `−1` on every arithmetic Frobenius lift at each conjugate orientation. -/
  orientBar_neg : ∀ i, ∀ q ∈ Q, ∀ φ : Gloc K (orientBar q),
    TauCeti.IsArithFrobeniusLift ((orientBar q).adicCompletion K) φ →
      ψ i (locMap K (Sr i) (orientBar q) φ) = Multiplicative.ofAdd (-1)

variable {K}

/-- **The moving exponent is not trivial at a positive stage** (its inertia image contains
`1 ≠ 0` in `ℤ/2^{2i}`). Kind: PROVED. -/
theorem FamilyMovingCharacter.ψ_ne_one {ℓ : ℕ} {Q : Finset ℕ} (Ψ : FamilyMovingCharacter K ℓ Q)
    {i : ℕ} (hi : 0 < i) : Ψ.ψ i ≠ 1 := by
  intro h1
  obtain ⟨σ, -, hσ⟩ := Ψ.inertia_onto i 1
  rw [h1, MonoidHom.one_apply] at hσ
  have h0 : (1 : ZMod (2 ^ (2 * i))) = 0 := by
    have := congrArg Multiplicative.toAdd hσ
    simpa using this.symm
  have : Fact (1 < 2 ^ (2 * i)) := ⟨Nat.one_lt_two_pow (by omega)⟩
  exact one_ne_zero h0

end Character

/-! **The address's moving family over the family's character** -/

section Address

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
/-- The moving support lies in a support of the address's shape. Kind: PROVED. -/
theorem movingSupport_subset {ℓ : ℕ} {h : ℤ} {T Sr : Set (HeightOneSpectrum (𝓞 K))}
    (hT : T = placesTwoN K ℓ ∪ placesOf K h ∪ Sr) : Sr ⊆ T := by
  rw [hT]
  exact Set.subset_union_right

/-- **The address's moving family over the family's character** (tex 2723–2741, 2748–2760,
3080–3085, 3413–3468, 4255–4280), for the twist `h` (`h = h_x`) and the curve `W` (`W = E_ℓ ⊗ K`):
as `AddressMovingFamily`, but
* `support`: the old support at stage `i` is the places above `2N`, the places above `h` and the
  family's moving support `Sr i` (which contains the places above the moving prime `r i`);
* `character`: the characters are `χ_h (1 + t)^{ψ_i}` with the family's moving exponent `ψ_i`
  inflated to the old support: the same `Ψ_i` for all characters of the family (tex 2737).
The family's character carries the text's ramification at `r_i`, its inertia surjectivity and
its orientation values (`FamilyMovingCharacter`). Kind: definition (data and GLUE). -/
structure AddressMovingFamilyR {ℓ : ℕ} {Q : Finset ℕ} (Ψ : FamilyMovingCharacter K ℓ Q) (h : ℤ)
    (W : WeierstrassCurve K) [W.IsElliptic] where
  /-- The moving stage family. -/
  Fam : MovingStageFamily W
  /-- Full torsion over every old support. -/
  hT : Fam.FullTorsionAt
  /-- The old support: the places above `2N`, the places above `h`, and the moving support. -/
  support : ∀ i, Fam.oldSupport i = placesTwoN K ℓ ∪ placesOf K h ∪ Ψ.Sr i
  /-- A square root of `h` in the field of the old support. -/
  root : ∀ i, KS K (Fam.oldSupport i)
  /-- It squares to `h`. -/
  square : ∀ i, root i ^ 2 = algebraMap K (KS K (Fam.oldSupport i)) (h : K)
  /-- It is nonzero. -/
  nonzero : ∀ i, root i ≠ 0
  /-- The characters are `χ_h Ψ_i` with the family's `Ψ_i`. -/
  character : ∀ i, Fam.α i = alphaChar i (quadChar (root i) (square i) (nonzero i))
    ((Ψ.ψ i).comp (inflMap K (movingSupport_subset (support i))).toMonoidHom)
  /-- A square root of `h` in the field of the enlarged support. -/
  rootS : ∀ i, KS K (Fam.support i)
  /-- It squares to `h`. -/
  squareS : ∀ i, rootS i ^ 2 = algebraMap K (KS K (Fam.support i)) (h : K)
  /-- It is nonzero. -/
  nonzeroS : ∀ i, rootS i ≠ 0
  /-- The enlarged character is quadratic above `2N`. -/
  quadS : ∀ i, ∀ v ∈ placesTwoN K ℓ, IsLocallyQuadAt (S := Fam.support i) i (Fam.character i)
    (quadChar (rootS i) (squareS i) (nonzeroS i)) v
  /-- The old conditions above `2N` are the actual Kummer conditions. -/
  kummer : ∀ i [NeZero i] (v : Places K (Fam.oldSupport i)) (hv : v.1 ∈ placesTwoN K ℓ),
    condToMinS W i (Fam.character i) (Fam.old i v) =
      actualKummerAtS (subset_refl (Fam.support i)) W i (rootS i) (squareS i) (nonzeroS i)
        (Fam.character i) (Fam.fullTorsion hT i) ⟨v.1, Or.inr v.2⟩ (quadS i v.1 hv)
  /-- The other old conditions are the full conditions. -/
  full : ∀ i [NeZero i] (v : Places K (Fam.oldSupport i)), v.1 ∉ placesTwoN K ℓ →
    Fam.old i v = fullAt K (Fam.support i) (Acoef i) (Fam.coefficient i) ⟨v.1, Or.inr v.2⟩

variable {ℓ : ℕ} {Q : Finset ℕ} {Ψ : FamilyMovingCharacter K ℓ Q} {h : ℤ}
  {W : WeierstrassCurve K} [W.IsElliptic]

/-- The address's moving exponent at stage `i`: the family's `ψ_i` inflated to the old support.
Kind: definition. -/
def AddressMovingFamilyR.exponent (A : AddressMovingFamilyR Ψ h W) (i : ℕ) :
    GKS K (A.Fam.oldSupport i) →* Multiplicative (ZMod (2 ^ (2 * i))) :=
  (Ψ.ψ i).comp (inflMap K (movingSupport_subset (A.support i))).toMonoidHom

/-- **The address's exponents are surjective on the inertia group above `r_i`** (tex 2729–2731,
4260–4262): through the compatibility of the localization maps with inflation
(`locMap_compat`). Kind: PROVED. -/
theorem AddressMovingFamilyR.inertia_onto (A : AddressMovingFamilyR Ψ h W) (i : ℕ)
    (y : ZMod (2 ^ (2 * i))) : ∃ σ ∈ TauCeti.inertiaSubgroup ((Ψ.placeR i).adicCompletion K),
      A.exponent i (locMap K (A.Fam.oldSupport i) (Ψ.placeR i) σ) = Multiplicative.ofAdd y := by
  obtain ⟨σ, hσ, hψ⟩ := Ψ.inertia_onto i y
  refine ⟨σ, hσ, ?_⟩
  change Ψ.ψ i (inflMap K _ (locMap K (A.Fam.oldSupport i) (Ψ.placeR i) σ)) = _
  rw [locMap_compat]
  exact hψ

/-- **The address's exponents are not trivial at a positive stage**: the non-moving choice
`ξ_i = 1` is excluded. Kind: PROVED. -/
theorem AddressMovingFamilyR.exponent_ne_one (A : AddressMovingFamilyR Ψ h W) {i : ℕ}
    (hi : 0 < i) : A.exponent i ≠ 1 := by
  intro h1
  obtain ⟨σ, -, hσ⟩ := A.inertia_onto i 1
  rw [h1, MonoidHom.one_apply] at hσ
  have h0 : (1 : ZMod (2 ^ (2 * i))) = 0 := by
    have := congrArg Multiplicative.toAdd hσ
    simpa using this.symm
  have : Fact (1 < 2 ^ (2 * i)) := ⟨Nat.one_lt_two_pow (by omega)⟩
  exact one_ne_zero h0

end Address

/-! **Label families of a base family, and the linked switches on them** -/

section Label

variable {K : Type} [Field K] [NumberField K] {W : WeierstrassCurve K} [W.IsElliptic]

/-- **The label families of a base family** (tex 4255–4280, 5055–5065, 5137–5153): as
`AddressLabelFamily`, for any base family `Fam₀` (the address's family): a moving stage family
whose old support at stage `i` is the base's together with the previous derivative labels, whose
characters are the base's inflated, and whose old conditions at the base's old places are the
actual Kummer conditions above `2N` and the full conditions elsewhere. The derivative conditions
at the previous labels are not pinned (in the text the singular side: "all earlier singular
conditions", tex 5141–5143, 5168–5170). Kind: definition (data and GLUE). -/
structure LabelFamilyOf (ℓ : ℕ) (h : ℤ) (Fam₀ : MovingStageFamily W) where
  /-- The moving stage family. -/
  Fam : MovingStageFamily W
  /-- Full torsion over every old support. -/
  hT : Fam.FullTorsionAt
  /-- The previous derivative labels at each stage. -/
  labels : ℕ → Set (HeightOneSpectrum (𝓞 K))
  /-- The old support: the base's and the previous labels. -/
  support : ∀ i, Fam.oldSupport i = Fam₀.oldSupport i ∪ labels i
  /-- The labels are new places for the base family. -/
  labels_new : ∀ i, Disjoint (Fam₀.oldSupport i) (labels i)
  /-- The base's old support is contained in the old support. -/
  hsub : ∀ i, Fam₀.oldSupport i ⊆ Fam.oldSupport i
  /-- The characters are the base's, inflated. -/
  character : ∀ i, Fam.α i = characterAfterSupport (hsub i) i (Fam₀.α i)
  /-- A square root of `h` in the field of the enlarged support. -/
  rootS : ∀ i, KS K (Fam.support i)
  /-- It squares to `h`. -/
  squareS : ∀ i, rootS i ^ 2 = algebraMap K (KS K (Fam.support i)) (h : K)
  /-- It is nonzero. -/
  nonzeroS : ∀ i, rootS i ≠ 0
  /-- The enlarged character is quadratic above `2N`. -/
  quadS : ∀ i, ∀ v ∈ placesTwoN K ℓ, IsLocallyQuadAt (S := Fam.support i) i (Fam.character i)
    (quadChar (rootS i) (squareS i) (nonzeroS i)) v
  /-- The old conditions above `2N` are the actual Kummer conditions. -/
  kummer : ∀ i [NeZero i] (v : Places K (Fam.oldSupport i)) (hv : v.1 ∈ placesTwoN K ℓ),
    condToMinS W i (Fam.character i) (Fam.old i v) =
      actualKummerAtS (subset_refl (Fam.support i)) W i (rootS i) (squareS i) (nonzeroS i)
        (Fam.character i) (Fam.fullTorsion hT i) ⟨v.1, Or.inr v.2⟩ (quadS i v.1 hv)
  /-- The conditions at the base's other old places are the full conditions. -/
  full : ∀ i [NeZero i] (v : Places K (Fam.oldSupport i)), v.1 ∈ Fam₀.oldSupport i →
    v.1 ∉ placesTwoN K ℓ →
      Fam.old i v = fullAt K (Fam.support i) (Acoef i) (Fam.coefficient i) ⟨v.1, Or.inr v.2⟩

end Label

section Pinned

variable (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F]
  {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) {W : WeierstrassCurve K} (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **Inner-limit switching inputs on the label families of a base family** (tex 4976–5195,
5027–5086): as `InnerLimitSwitchPinned`, with the linked switches on label families of the base
family `Fam₀` (`LabelFamilyOf`). Kind: definition (inputs). -/
structure InnerLimitSwitchPinnedOn (ℓ : ℕ) (h : ℤ) (Fam₀ : MovingStageFamily W)
    (Φ : SwitchFamily (ResAt P) (Localization.AtPrime P))
    (ι : Localization.AtPrime P →+* F) (u : F) extends SwitchModelFrame Φ ι (resAt P) u where
  /-- The linked switches on the label families, with side models. -/
  step : ∀ c, Reach Φ.next Φ.actual c → 1 < (stage c).fiberDim (resAt P) →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      ∃ X : ILStageStepMovingLinked P Cn W hW (stage c) (stage (Φ.next c p)),
        (∃ Lf : LabelFamilyOf ℓ h Fam₀, X.Fam = Lf.Fam) ∧
        Nonempty (HomotopyEquiv (selCx X.stepData.toStep.SF.Dside).toCC
          (selCx (Φ.fibre c)).toCC) ∧
        Nonempty (HomotopyEquiv (selCx X.stepData.toStep.SS.Dside).toCC
          (selCx (Φ.fibre (Φ.next c p))).toCC)

variable {P Cn hW} {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)}
  {ι : Localization.AtPrime P →+* F} {u : F} {ℓ : ℕ} {h : ℤ} {Fam₀ : MovingStageFamily W}

/-- The moving inputs of the pinned inputs (forgetting the label tie). Kind: PROVED. -/
def InnerLimitSwitchPinnedOn.toMoving (X : InnerLimitSwitchPinnedOn P Cn hW ℓ h Fam₀ Φ ι u) :
    InnerLimitSwitchMoving P Cn W hW Φ ι u where
  toSwitchModelFrame := X.toSwitchModelFrame
  step c hc h1 := by
    obtain ⟨p, hcs, Y, -, hF, hS⟩ := X.step c hc h1
    exact ⟨p, hcs, Y, hF, hS⟩

/-- **The actual fibre dimension is the dimension of the pinned fibre**. Kind: PROVED. -/
theorem InnerLimitSwitchPinnedOn.fiberDim_eq_pinned
    (X : InnerLimitSwitchPinnedOn P Cn hW ℓ h Fam₀ Φ ι u)
    (G : GCx (ResAt P)) (e : HomotopyEquiv (selCx (Φ.fibre Φ.actual)).toCC G.toCC) :
    (X.stage Φ.actual).fiberDim (resAt P) = finrank (ResAt P) (G.toCC.homology 1) := by
  rw [X.toSwitchModelFrame.fiberDim_eq Φ.actual]
  exact ((e.toHomologyIso 1).toLinearEquiv).finrank_eq

/-- **A stationary family forces fibre dimension one** (as
`InnerLimitSwitchPinned.fiberDim_eq_one_of_stationary`). Kind: PROVED. -/
theorem InnerLimitSwitchPinnedOn.fiberDim_eq_one_of_stationary (hP : P.height = 1)
    (hι : Function.Injective ι) (X : InnerLimitSwitchPinnedOn P Cn hW ℓ h Fam₀ Φ ι u)
    (hstat : ∀ c p, Φ.next c p = c) : (X.stage Φ.actual).fiberDim (resAt P) = 1 := by
  have := isDiscreteValuationRing_atPrime_of_height_one P hP
  obtain ⟨PK⟩ := exists_primitiveKernelVector hι (resAt P) (X.stage Φ.actual)
    (X.class_ne_zero Φ.actual Reach.start)
  have h1 := one_le_fiberDim_of_primitiveKernel PK
  by_contra hne
  have hlt : 1 < (X.stage Φ.actual).fiberDim (resAt P) := by omega
  obtain ⟨p, -, Y, -, -, -⟩ := X.step Φ.actual Reach.start hlt
  have hd := Y.stepData.toStep.toNonquadDims.drop
  rw [hstat] at hd
  omega

/-- **Outside the terminal case a switch on a label family of the base is required**.
Kind: PROVED. -/
theorem InnerLimitSwitchPinnedOn.switch_required
    (X : InnerLimitSwitchPinnedOn P Cn hW ℓ h Fam₀ Φ ι u)
    {Fam : MovingStageFamily W} (L : MovingRetainedLimit Fam)
    (e : HomotopyEquiv (selCx (Φ.fibre Φ.actual)).toCC (L.finiteFibre P).toCC)
    (hgt : 1 < finrank (ResAt P) ((L.finiteFibre P).toCC.homology 1)) :
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (X.stage Φ.actual).u (X.stage (Φ.next Φ.actual p)).u) ∧
      ∃ Y : ILStageStepMovingLinked P Cn W hW (X.stage Φ.actual) (X.stage (Φ.next Φ.actual p)),
        (∃ Lf : LabelFamilyOf ℓ h Fam₀, Y.Fam = Lf.Fam) ∧
        Nonempty (HomotopyEquiv (selCx Y.stepData.toStep.SF.Dside).toCC
          (selCx (Φ.fibre Φ.actual)).toCC) ∧
        Nonempty (HomotopyEquiv (selCx Y.stepData.toStep.SS.Dside).toCC
          (selCx (Φ.fibre (Φ.next Φ.actual p))).toCC) :=
  X.step Φ.actual Reach.start (by rw [X.fiberDim_eq_pinned _ e]; exact hgt)

end Pinned

/-! **The leaf: the family's character and the address's limit before the primes** -/

section Leaf

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {Cn : ActualConj K S} {W : WeierstrassCurve K} {hW : W.map (Cn.κ : K →+* K) = W}
  [W.IsElliptic] [HasFullTwoTorsion K S W] {ℓ : ℕ} {Q : Finset ℕ}

variable (Cn hW) in
/-- **The clause at a height-one prime for a fixed address family and limit** (tex 4976–5200):
a configuration family genuine at `𝔭` (GLUE), an integral model `Dfin` of the finite side at `𝔭`
of the limit `L` of the address's family `A` (the actual finite-side class and functional), THE
PIN (the actual fibre homotopy equivalent to `L.finiteFibre P`), and the nonquadratic linked
switches on the label families of `A` (`InnerLimitSwitchPinnedOn`) or, at a quadratic prime, the
homology-level data, in both cases with actual stage `Dfin.stage`. At a quadratic prime only the
actual fibre is pinned; the switches and successor fibres are not tied to the address's families.
Kind: definition. -/
def PinnedLimitAt {Ψ : FamilyMovingCharacter K ℓ Q} {h : ℤ} (A : AddressMovingFamilyR Ψ h W)
    (L : MovingRetainedLimit A.Fam) (u : FractionRing Lambda) (P : Ideal Lambda) [P.IsPrime] :
    Prop :=
  ∃ Φ : SwitchFamily (ResAt P) (Localization.AtPrime P), IsGenuineFamilyAt P Φ ∧
    ∃ Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
        (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
        (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite)),
      Nonempty (HomotopyEquiv (selCx (Φ.fibre Φ.actual)).toCC (L.finiteFibre P).toCC) ∧
      ((∃ X : InnerLimitSwitchPinnedOn P Cn hW ℓ h A.Fam Φ (UniformSwitch.toFracAt P) u,
          X.stage Φ.actual = Dfin.stage) ∨
        (Φ.quadratic (resAt P) ∧
          ∃ G : HomologySwitchDataPK Φ (UniformSwitch.toFracAt P) (resAt P) u,
            G.stage Φ.actual = Dfin.stage))

variable (Cn hW) in
/-- **The address clause over the family's character** (tex 4976–5200): `u = 0` (tex 5196–5197;
ELLIOT), or the address's moving family `A` over `Ψ` and a retained limit `L` of it, chosen
before the primes, with the pinned clause at every height-one prime `𝔭 ≠ (2)`.
Kind: definition. -/
def RegularityInputsILQFam (Ψ : FamilyMovingCharacter K ℓ Q) (h : ℤ) (u : FractionRing Lambda) :
    Prop :=
  u = 0 ∨ ∃ (A : AddressMovingFamilyR Ψ h W) (L : MovingRetainedLimit A.Fam),
    ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
      PinnedLimitAt Cn hW A L u P

/-- **The address clause gives the model-level inputs**. Kind: PROVED. -/
theorem RegularityInputsILQFam.toMdl {Ψ : FamilyMovingCharacter K ℓ Q} {h : ℤ}
    {u : FractionRing Lambda} (hI : RegularityInputsILQFam Cn hW Ψ h u) :
    RegularityInputsMdl u := by
  rcases hI with hI | ⟨A, L, hI⟩
  · exact Or.inl hI
  · refine Or.inr fun P _ hP hne => ?_
    obtain ⟨Φ, hΦ, Dfin, -, hb⟩ := hI P hP hne
    refine ⟨Φ, hΦ, ?_⟩
    rcases hb with ⟨X, -⟩ | ⟨hq, G, -⟩
    · exact Or.inl ⟨X.toMoving.toInner.toModelInputs⟩
    · exact Or.inr ⟨hq, ⟨G⟩⟩

/-- **The collapse is the terminal case of the fixed limit** (tex 4976–4980, 5154–5159): if the
clause holds at `𝔭` for a family without proper successors, the finite fibre at `𝔭` of the fixed
limit `L` of the address's moving family has `dim H¹ = 1`; both branches. Kind: PROVED. -/
theorem PinnedLimitAt.terminal_of_stationary {Ψ : FamilyMovingCharacter K ℓ Q} {h : ℤ}
    {A : AddressMovingFamilyR Ψ h W} {L : MovingRetainedLimit A.Fam} {u : FractionRing Lambda}
    {P : Ideal Lambda} [P.IsPrime] (hP : P.height = 1) (hI : PinnedLimitAt Cn hW A L u P)
    (hstat : ∀ (Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)) c p, Φ.next c p = c) :
    finrank (ResAt P) ((L.finiteFibre P).toCC.homology 1) = 1 := by
  obtain ⟨Φ, -, Dfin, ⟨e⟩, hb⟩ := hI
  have hA : finrank (ResAt P) ((selCx (Φ.fibre Φ.actual)).toCC.homology 1) = 1 := by
    rcases hb with ⟨X, -⟩ | ⟨-, G, -⟩
    · rw [← X.toSwitchModelFrame.fiberDim_eq Φ.actual]
      exact X.fiberDim_eq_one_of_stationary hP (UniformSwitch.toFracAt_injective P) (hstat Φ)
    · rw [← fiberDim_eq_h1 (ResAt P) (Localization.AtPrime P) (FractionRing Lambda)
        (UniformSwitch.toFracAt P) (resAt P) (G.stage Φ.actual) (Φ.fibre Φ.actual)
        ⟨G.model Φ.actual⟩]
      exact G.fiberDim_eq_one_of_stationary hP (hstat Φ)
  rw [← hA]
  exact ((e.toHomologyIso 1).toLinearEquiv).finrank_eq.symm

end Leaf

section LeafForms

/-- **The per-instance form** (F2 per address; for the ring instances of (3.5)): `u = 0`, or the
field `K` (quadratic, containing `√k`), places `S`, the actual conjugation, `W = E_ℓ ⊗ K` with full
two-torsion and the instance's moving character over the primes of `h` (`FamilyMovingCharacter`),
chosen once, with the address clause. Kind: definition. -/
def RegularityInputsILQ (ℓ : ℕ) (h k : ℤ) (u : FractionRing Lambda) : Prop :=
  u = 0 ∨ ∃ (K : Type) (_ : Field K) (_ : NumberField K) (S : Set (HeightOneSpectrum (𝓞 K)))
    (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
    (_ : W.IsElliptic) (_ : HasFullTwoTorsion K S W),
    W = (Ecurve ℓ).baseChange K ∧ Module.finrank ℚ K = 2 ∧ (∃ sk : K, sk ^ 2 = (k : K)) ∧
    ∃ Ψ : FamilyMovingCharacter K ℓ h.natAbs.primeFactors, RegularityInputsILQFam Cn hW Ψ h u

/-- The per-instance form gives the model-level inputs. Kind: PROVED. -/
theorem RegularityInputsILQ.toMdl {ℓ : ℕ} {h k : ℤ} {u : FractionRing Lambda}
    (hI : RegularityInputsILQ ℓ h k u) : RegularityInputsMdl u := by
  rcases hI with hI | ⟨K, _, _, S, Cn, W, hW, _, _, -, -, -, Ψ, hF⟩
  · exact Or.inl hI
  · exact hF.toMdl

variable {ℓ : ℕ} (D : RCData ℓ)

/-- **The height-one leaf over one moving character per family** (tex 4976–5200, at the final
families; F1 and F2): for every final family `F` coordinates `U x` with
`IsTExpansion (U x) (D.uPrim F x)` (tex 3877–3892; GLUE) and either all zero, or the field `K`
(quadratic, containing `√k` for the final companion `k`), places `S`, the actual conjugation,
`W = E_ℓ ⊗ K` with full two-torsion and the family's moving character over `F.Q`, chosen once for
the family, with the address clause at every address (its moving family and limit chosen before
the primes). Kind: definition. -/
def PrimRegularityInputsILQ : Prop :=
  ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∃ U : Addr F.b → FractionRing Lambda, (∀ x, IsTExpansion (U x) (D.uPrim F x)) ∧
      ((∀ x, U x = 0) ∨
        ∃ (K : Type) (_ : Field K) (_ : NumberField K) (S : Set (HeightOneSpectrum (𝓞 K)))
          (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
          (_ : W.IsElliptic) (_ : HasFullTwoTorsion K S W),
          W = (Ecurve ℓ).baseChange K ∧ Module.finrank ℚ K = 2 ∧
          (∃ sk : K, sk ^ 2 = (D.kfin : K)) ∧
          ∃ Ψ : FamilyMovingCharacter K ℓ F.Q, ∀ x, RegularityInputsILQFam Cn hW Ψ (F.h x) (U x))

/-- The leaf gives the model-level leaf. Kind: PROVED. -/
theorem PrimRegularityInputsILQ.toMdl (hI : PrimRegularityInputsILQ D) :
    PrimRegularityInputsMdl D := by
  intro Co Ce F hF x
  obtain ⟨U, hT, hU⟩ := hI Co Ce F hF
  refine ⟨U x, hT x, ?_⟩
  rcases hU with hU | ⟨K, _, _, S, Cn, W, hW, _, _, -, -, -, Ψ, hx⟩
  · exact Or.inl (hU x)
  · exact (hx x).toMdl

/-- **`PrimRegularityInputs` from the leaf** (the form consumed by the base-zero step).
Kind: PROVED. -/
theorem primRegularityInputs_of_ILQ (hI : PrimRegularityInputsILQ D) : PrimRegularityInputs D :=
  primRegularityInputs_of_Mdl D hI.toMdl

/-- **`RCSteps.height_one`** from the leaf and (4.7). Kind: PROVED (from the inputs). -/
theorem heightOneTarget_of_ILQ (hI : PrimRegularityInputsILQ D) (h47 : CommonCoordinateTarget D) :
    HeightOneTarget D :=
  heightOneTarget_of_inputs D (primRegularityInputs_of_ILQ D hI) h47

/-- **Degenerate satisfiability**: the leaf holds when the primitive coordinates vanish.
Kind: PROVED. -/
theorem primRegularityInputsILQ_of_uPrim_zero (hD : ∀ F x, D.uPrim F x = 0) :
    PrimRegularityInputsILQ D :=
  fun _ _ F _ => ⟨fun _ => 0, fun x => by rw [hD F x]; exact isTExpansion_zero,
    Or.inl fun _ => rfl⟩

end LeafForms

end ZInQ.Manuscript.RC.Wiring
