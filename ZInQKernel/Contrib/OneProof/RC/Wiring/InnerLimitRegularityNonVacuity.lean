import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitRegularity
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineOuterTies
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.LimitNonVacuity
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.StageEndNonVacuity

/-!
**Theorem 5.3, Lane RC0 round 11: non-vacuity of the inner-limit regularity inputs**

Proposition `ex:limits-uniform-lower-bound`, height-one regularity (tex 4976–5200), with the switch
taken on the inner-limit objects (tex 5027–5086) and Lemma `ex:limits-inner-limit` (tex
4385–4451). The structures of `InnerLimitRegularity.lean` are satisfiable by concrete data.

**1. A full `ILStageStep`, a LABELLED TOY** (`ilToyStep`, for any curve with an actual
conjugation, any prime `𝔭` and any nonprincipal ultrafilter; at `E₁ : y² = x(x−1)(x+3)` over `ℚ`,
`S = Set.univ`, `actualConjQ`, the prime `(t)` and the hyperfilter: `ilToyStepE1`). It is NOT the
realized Galois diagram. Per field:
* `U`, `hU`: any nonprincipal ultrafilter (genuine).
* `G`, `hflat`, `Uc`, `res`, `ιc` (TOY): the stage complexes `ilCx (A_i)` (`A_i²` in degrees `1`,
  `2`, zero differentials; free), the localization `ilRes` (`x ↦ (x, 0)` onto the finite plane,
  the identity onto `D²`); the local condition is the zero complex (degenerate).
* `Q`, `tr`, `htr` (TOY): `ilSel`, global target and global cup product zero (degenerate), local
  cup product the image at `A_i` of lane RC31's toy local pairing `toyLoc (Ω J_Λ)ᵀ` (perfect on
  `D⁰ × D²` and on `F ⊕ S`), zero isotropy homotopy; the trace `(e, l) ↦ l`.
* `hdual` (genuine proof for the toy data): `ilSel_globalDuality`, an explicit stage matrix
  diagram whose identities are the images at `A_i` of lane RC31's exact identities over `Λ`.
* `hres`, `lo = 1`, `hi = 2`, `hbdd`, `B = 2`, `hB`: genuine for the toy; the residual ranks are
  exactly `2, 2` in degrees `1, 2` (`ilCx_finrank_residual`).
* `C`, `D`, `E` (TOY): lane RC31's retained data `toyStages`, `toyPairing`, `toyDuality` (constant
  stages, identities exact over `Λ`); `hlift`, `hrank`, `hrankB` hold exactly.
* `ε₀ = ε₂ = ε = σ = 1`, `hloc`: lane RC31's `toy_hloc`; `J = conjMatrix Cn W hW 𝔭` is the ACTUAL
  conjugation matrix of the given curve, the retained local pairing is built from it.
* `hdet` (genuine computation on the toy limit diagram): the relaxed localization image contains
  the finite plane (`il_hdet`); with the duality of the step it is equal to it
  (`il_relaxedImage_eq`).
* `φ`, `φ'` (genuine computations, TOY stages): `H¹` of the finite limit side is `k²`
  (`ilFinSideEquiv`), `H¹` of the singular limit side vanishes (`ilSingSide_subsingleton`); the
  stages `S₀ = [Λ_𝔭² --0--> Λ_𝔭²]`, `S₁ = [Λ_𝔭 --1--> Λ_𝔭]` are chosen to match (`ilStage0`,
  `ilStage1`; not the stages of a configuration family).

**2. The leaf, degenerately** (the `u = 0` branch): `primRegularityInputsIL_of_uPrim_zero`, and
concrete interface data `ilZeroData` satisfying the leaf (`primRegularityInputsIL_ilZeroData`).

**3. The step is not forced to be degenerate**: every `ILStageStep` drops the fibre dimension by
two (`ilStageStep_drop`, through `toStepData` and the RC53 group's `QuasiNonquadStep`), so there
is none from a stage to itself (`ilStageStep_isEmpty_self`); the toy realizes the drop `2 → 0`
(`ilToyStep_drop`), with source fibre dimension `2 > 1`, as the family's `step` field requires.

Not attempted here: an `ILSwitchInputs` family (it needs a switching family whose fibres are the
limit sides with homotopy equivalences to the stages), and a nondegenerate `RegularityInputsIL`
(its families must be genuine at `𝔭`, which needs genuine Galois Selmer data over `k(𝔭)` with
nonzero `H¹`, not in the tree).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Filter Matrix IsLocalRing TensorProduct NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch (TwoTermStage)
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (fiberH1 fiberH1_finite
  finrank_h1_twoTermFiberComplex)
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex Vec2 ComplexStages fibreLimitGlobal
  limitRelaxed finiteLimitSide singularLimitSide)
open ZInQ.Contrib.RC53Assist.InnerLimitArith (ResidualCohomologyFinite gcxBaseChange)
open ZInQ.Manuscript.RC.Limits (matCx GradedModel residualCohomologyAt residualDiff StageA stageMap
  stageIdeal)
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.Uniform (Lambda finPlane)
open ZInQ.Manuscript.RC.CoefModules (ActualConj)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion curveE1 Pt0)
open ZInQ.Manuscript.RC.Central (IsClassFunctionalCoord)

/-! **The stage complex of the toy shape and its residual ranks** -/

section Residual

variable (R : Type) [CommRing R]

/-- **The stage complex of the toy shape**: `R²` in degrees `1` and `2`, zero differentials.
Kind: definition. -/
abbrev ilCx : GCx R := matCx toyRank (fun _ _ _ => 0) (fun _ _ _ _ _ => Matrix.zero_mul _)

/-- Its residual differentials vanish. Kind: PROVED. -/
theorem ilCx_residualDiff_eq_zero [IsLocalRing R] (a b : ℤ) (h : a + 1 = b) :
    residualDiff (ilCx R) a b h = 0 := by
  change ((Matrix.toLin' (0 : Matrix (Fin (toyRank b)) (Fin (toyRank a)) R)).baseChange
    (ResidueField R)) = 0
  rw [map_zero, LinearMap.baseChange_zero]

/-- A subquotient of zero maps is the middle space. Kind: PROVED. -/
theorem il_subquotient_zero_finrank {k V W Z : Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup Z] [Module k Z] :
    Module.finrank k (ZInQ.Manuscript.RC.Limits.subquotientOf (0 : V →ₗ[k] W) (0 : W →ₗ[k] Z)) =
      Module.finrank k W := by
  unfold ZInQ.Manuscript.RC.Limits.subquotientOf
  rw [LinearMap.range_zero, Submodule.comap_bot, Submodule.ker_subtype, LinearMap.ker_zero,
    (Submodule.quotEquivOfEqBot _ rfl).finrank_eq, finrank_top]

/-- **The residual ranks of the stage complex are the toy ranks.** Kind: PROVED. -/
theorem ilCx_finrank_residual [IsLocalRing R] (n : ℤ) :
    Module.finrank (ResidueField R) (residualCohomologyAt (ilCx R) n) = toyRank n := by
  have : Module.Finite R ((ilCx R).X n) := inferInstanceAs (Module.Finite R (Fin (toyRank n) → R))
  have : Module.Free R ((ilCx R).X n) := inferInstanceAs (Module.Free R (Fin (toyRank n) → R))
  unfold residualCohomologyAt
  rw [ilCx_residualDiff_eq_zero R (n - 1) n, ilCx_residualDiff_eq_zero R n (n + 1),
    il_subquotient_zero_finrank]
  calc Module.finrank (ResidueField R) (ResidueField R ⊗[R] (ilCx R).X n)
      = Module.finrank R ((ilCx R).X n) := Module.finrank_baseChange
    _ = toyRank n := Module.finrank_fin_fun R

/-- **The stage complex has finite residual cohomology.** Kind: PROVED. -/
theorem ilCx_residualCohomologyFinite [IsLocalRing R] : ResidualCohomologyFinite (ilCx R) :=
  fun n => (moduleFinite_homology_iff (gcxBaseChange (ResidueField R) (ilCx R)) n).2
    (matCx_residual_finite R toyRank _ _ n)

end Residual

/-- The toy ranks are at most `2`. Kind: PROVED. -/
theorem ilToyRank_le_two (n : ℤ) : toyRank n ≤ 2 := by
  rcases n with ((_ | _ | _ | n) | n)
  all_goals first
    | exact le_refl 2
    | exact Nat.zero_le 2

/-! **The stage Selmer data of the toy shape** -/

section Stage

variable (R : Type) [CommRing R]

/-- The graded model of `ilCx` (identity retract). Kind: definition. -/
abbrev ilModel : GradedModel (ilCx R) := ZInQ.Manuscript.RC.Limits.matCx.gradedModel _ _ _

/-- Components of the localization: degree `1` `x ↦ (x, 0)`, degree `2` the identity. -/
def ilResLin : ∀ n : ℤ, (Fin (toyRank n) → R) →ₗ[R] (splitLocalComplex R).X n
  | .ofNat 1 => LinearMap.inl R (Vec2 R) (Vec2 R)
  | .ofNat 2 => LinearMap.id
  | _ => 0

/-- The localization of the toy-shape stage complex into the split model. -/
def ilRes : GHom (ilCx R) (splitLocalComplex R) where
  f a b h := by
    subst h
    exact ilResLin R a
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj h₁
    exact (congrArg (ilResLin R (i + 1))
      (Matrix.zero_mulVec (x : Fin (toyRank i) → R))).trans (map_zero _)

/-- The toy-shape stage complex is flat. -/
theorem ilCx_flat (n : ℤ) : Module.Flat R ((ilCx R).X n) :=
  inferInstanceAs (Module.Flat R (Fin (toyRank n) → R))

/-- The toy-shape stage complex vanishes outside degrees `1`, `2`. -/
theorem ilCx_eq_zero (n : ℤ) (h1 : n ≠ 1) (h2 : n ≠ 2) (x : (ilCx R).X n) : x = 0 := by
  have := toyRank_isEmpty n h1 h2
  exact funext fun i => isEmptyElim i

/-- The (zero) global cup product. -/
def ilCupG : GPair (ilCx R) (ilCx R) (exZero R) where
  P _ _ _ _ := 0
  leib _ _ _ _ _ _ _ _ _ _ _ _ := rfl

variable {R} (f : Lambda →+* R) (A : Matrix (Fin 2) (Fin 2) Lambda)

/-- The toy local pairing vanishes outside total degree `2`. -/
theorem ilToyLoc_eq_zero (a b : ℤ) (h : a + b ≠ 2) : toyLoc A a b = 0 := by
  rcases a with (_ | _ | _ | m) | m <;> rcases b with (_ | _ | _ | n) | n
  all_goals first
    | rfl
    | exact absurd rfl h

/-- The finite plane is isotropic for the mapped toy pairing. -/
theorem ilIso11 (x y : Fin 2 → R) :
    Sum.elim x 0 ⬝ᵥ ((toyLocOne A).map f *ᵥ Sum.elim y 0) = 0 := by
  simp [toyLocOne, dotProduct, Fintype.sum_sum_type, Matrix.mulVec, fromBlocks]

/-- The localization is isotropic for the mapped toy pairing in total degree `2`. -/
theorem ilLoc_res (a b : ℤ) (h : a + b = 2) (x : (ilCx R).X a) (y : (ilCx R).X b) :
    locForm (fun a b => (toyLoc A a b).map f) a b ((ilRes R).f a a rfl x)
      ((ilRes R).f b b rfl y) = 0 := by
  rcases (show a = 1 ∨ a ≠ 1 ∧ a ≠ 2 ∨ a = 2 by omega) with rfl | ha | rfl
  · obtain rfl : b = 1 := by omega
    rw [locForm_apply]
    exact ilIso11 f A x y
  · rw [ilCx_eq_zero R a ha.1 ha.2 x, map_zero, map_zero, LinearMap.zero_apply]
  · rw [ilCx_eq_zero R b (by omega) (by omega) y, map_zero, map_zero]

/-- The local cup product: the mapped toy pairing into degree `2`, zero elsewhere. -/
def ilCupL (a b : ℤ) : ∀ k : ℤ,
    (splitLocalComplex R).X a →ₗ[R] (splitLocalComplex R).X b →ₗ[R] (exEL R).X k
  | .ofNat 2 => locForm (fun a b => (toyLoc A a b).map f) a b
  | .ofNat 0 => 0
  | .ofNat 1 => 0
  | .ofNat (_ + 3) => 0
  | .negSucc _ => 0

/-- The local cup product vanishes outside target degree `2`. -/
theorem ilCupL_ne (a b k : ℤ) (hk : k ≠ 2) : ilCupL f A a b k = 0 := by
  rcases k with (_ | _ | _ | m) | m
  · rfl
  · rfl
  · exact absurd rfl hk
  · rfl
  · rfl

/-- The local cup product as a pairing of complexes. -/
def ilCupLPair : GPair (splitLocalComplex R) (splitLocalComplex R) (exEL R) where
  P a b k _ := ilCupL f A a b k
  leib i i₁ j j₁ k k₁ h hi hj hk x y := by
    change (0 : (exEL R).X k →ₗ[R] (exEL R).X k₁) _ =
      ilCupL f A i₁ j k₁ ((0 : (splitLocalComplex R).X i →ₗ[R] (splitLocalComplex R).X i₁) x) y +
        sgn i • ilCupL f A i j₁ k₁ x
          ((0 : (splitLocalComplex R).X j →ₗ[R] (splitLocalComplex R).X j₁) y)
    simp

/-- The Selmer pairing datum of the toy shape. -/
def ilSel : SelPairData (splitSelData (ilCx R) (ilRes R) (exZero R) (exIota R))
    (splitSelData (ilCx R) (ilRes R) (exZero R) (exIota R)) where
  E := exZero R
  EL := exEL R
  resE := exResE R
  cupG := ilCupG R
  cupL := ilCupLPair f A
  compat i j k i' j' k' h h' hi hj hk a b := by
    subst hi hj hk
    change (0 : (exEL R).X k) = ilCupL f A i j k ((ilRes R).f i i rfl a) ((ilRes R).f j j rfl b)
    rcases eq_or_ne k 2 with rfl | hk2
    · exact (ilLoc_res f A i j h' a b).symm
    · rw [ilCupL_ne f A i j k hk2, LinearMap.zero_apply, LinearMap.zero_apply]
  hU _ _ _ _ := 0
  isotropy i i₁ j j₁ k k₁ h hi hj hk u v := by
    change (0 : (exEL R).X k₁) + 0 + sgn i • 0 =
      ilCupL f A i j k₁ ((0 : (exZero R).X i →ₗ[R] (splitLocalComplex R).X i) u)
        ((0 : (exZero R).X j →ₗ[R] (splitLocalComplex R).X j) v)
    simp

/-- The trace `(e, l) ↦ l` on degree `3` of the target cone. -/
def ilTr : (coneCx (ilSel f A).resE).X 3 →ₗ[R] R := LinearMap.snd R PUnit R

/-- The trace kills coboundaries. -/
theorem ilHtr (z : (coneCx (ilSel f A).resE).X 2) :
    ilTr f A ((coneCx (ilSel f A).resE).d 2 3 rfl z) = 0 :=
  sub_zero (0 : R)

/-- The coordinate local pairing of the toy-shape Selmer datum is the mapped toy pairing. -/
theorem ilStageLocMat : stageLocMat (ilSel f A) (ilTr f A) = fun a b => (toyLoc A a b).map f := by
  funext a b
  by_cases h : a + b = 2
  · refine locMat_eq_of_form R (stageLocMat (ilSel f A) (ilTr f A))
      (fun a b => (toyLoc A a b).map f) a b fun u v => ?_
    rw [locForm_stageLocMat _ _ a b h]
    rfl
  · rw [stageLocMat, dite_eq_right_iff.mpr (fun h' => absurd h' h), ilToyLoc_eq_zero A a b h,
      Matrix.map_zero _ (map_zero f)]

/-- The stage pairing input of the toy-shape Selmer datum. -/
abbrev ilP : StagePairingInput (ilCx R) :=
  stagePairingInputOfSel (ilSel f A) (ilTr f A) (ilHtr f A)

/-- The model localization is the mapped toy localization. -/
theorem ilModelRes_eq : modelRes (ilModel R) (ilP f A) = fun n => (toyRes n).map f := by
  funext n
  by_cases h1 : n = 1
  · subst h1
    refine Matrix.ext fun (i : Fin 2 ⊕ Fin 2) (j : Fin 2) => ?_
    rcases i with i | i
    · change (Pi.single j 1 : Fin 2 → R) i = f ((1 : Matrix (Fin 2) (Fin 2) Lambda) i j)
      rw [Matrix.one_apply, Pi.single_apply]
      split_ifs <;> simp
    · change (0 : R) = f 0
      exact (map_zero f).symm
  · by_cases h2 : n = 2
    · subst h2
      refine Matrix.ext fun (i : Fin 2) (j : Fin 2) => ?_
      change (Pi.single j 1 : Fin 2 → R) i = f ((1 : Matrix (Fin 2) (Fin 2) Lambda) i j)
      rw [Matrix.one_apply, Pi.single_apply]
      split_ifs <;> simp
    · ext i j
      exact ((toyRank_isEmpty n h1 h2).false j).elim

/-- The model trace pairing is zero. -/
theorem ilModelGlob_eq : modelGlob (ilModel R) (ilP f A) =
    fun a b _ => (0 : Matrix (Fin (toyRank a)) (Fin (toyRank b)) Lambda).map f := by
  funext a b h
  ext i j
  exact (map_zero f).symm

/-- The model differentials are zero. -/
theorem ilModel_dC : (ilModel R).dC =
    fun a b _ => (0 : Matrix (Fin (toyRank b)) (Fin (toyRank a)) Lambda).map f := by
  funext a b h
  exact (Matrix.map_zero _ (map_zero f)).symm

/-- The mapped toy reverse map. -/
def ilRev (B : Matrix (Fin 2) (Fin 2) Lambda) (a : ℤ) :
    Matrix (Fin (toyRank a)) (cIdxOf toyRank (3 - a)) R := (toyRev B a).map f

/-- The (zero) source homotopy. -/
def ilSrc (a b : ℤ) (_ : b + 1 = a) : Matrix (Fin (toyRank b)) (Fin (toyRank a)) R :=
  (0 : Matrix (Fin (toyRank b)) (Fin (toyRank a)) Lambda).map f

/-- The mapped toy target homotopy. -/
def ilTgt (a b : ℤ) (_ : b + 1 = a) : Matrix (cIdxOf toyRank (3 - b)) (cIdxOf toyRank (3 - a)) R :=
  (toyTgt a b).map f

/-- The mapped toy reverse map is a chain map. -/
theorem il_chain (B : Matrix (Fin 2) (Fin 2) Lambda)
    (D : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (toyRank b)) (Fin (toyRank a)) R)
    (hD : D = fun a b _ => (0 : Matrix (Fin (toyRank b)) (Fin (toyRank a)) Lambda).map f)
    (Rk : ∀ n : ℤ, Matrix (lIdx n) (Fin (toyRank n)) R) (hRk : Rk = fun n => (toyRes n).map f)
    (a : ℤ) :
    ilRev f B (a + 1) * dualDiffMatOf D Rk a (a + 1) rfl - D a (a + 1) rfl * ilRev f B a = 0 := by
  subst hD hRk
  have h := congrArg (fun M => M.map f) (toy_chain B a)
  simp only [matrix_map_sub, Matrix.map_mul, dualDiffMatOf_map] at h
  exact h.trans (Matrix.map_zero _ (map_zero f))

/-- The mapped first homotopy-inverse identity. -/
theorem il_src (B : Matrix (Fin 2) (Fin 2) Lambda) (hBA : B * A = 1)
    (D : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (toyRank b)) (Fin (toyRank a)) R)
    (hD : D = fun a b _ => (0 : Matrix (Fin (toyRank b)) (Fin (toyRank a)) Lambda).map f)
    (Mbg : ∀ a b : ℤ, a + b = 3 → Matrix (Fin (toyRank a)) (Fin (toyRank b)) R)
    (hMbg : Mbg = fun a b _ => (0 : Matrix (Fin (toyRank a)) (Fin (toyRank b)) Lambda).map f)
    (Mbl : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) R) (hMbl : Mbl = fun a b => (toyLoc A a b).map f)
    (Rk : ∀ n : ℤ, Matrix (lIdx n) (Fin (toyRank n)) R) (hRk : Rk = fun n => (toyRes n).map f)
    (a : ℤ) :
    ilRev f B a * forwardMatOf Mbg Mbl Rk a - ilSrc f (a + 1) a rfl * D a (a + 1) rfl -
      D (a - 1) a (by omega) * ilSrc f a (a - 1) (by omega) - 1 = 0 := by
  subst hD hMbg hMbl hRk
  have h := congrArg (fun M => M.map f) (toy_src A B hBA a)
  simp only [matrix_map_sub, Matrix.map_mul, forwardMatOf_map,
    Matrix.map_one _ (map_zero f) (map_one f)] at h
  exact h.trans (Matrix.map_zero _ (map_zero f))

/-- The mapped second homotopy-inverse identity. -/
theorem il_tgt (B : Matrix (Fin 2) (Fin 2) Lambda) (hAB : A * B = 1)
    (D : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (toyRank b)) (Fin (toyRank a)) R)
    (hD : D = fun a b _ => (0 : Matrix (Fin (toyRank b)) (Fin (toyRank a)) Lambda).map f)
    (Mbg : ∀ a b : ℤ, a + b = 3 → Matrix (Fin (toyRank a)) (Fin (toyRank b)) R)
    (hMbg : Mbg = fun a b _ => (0 : Matrix (Fin (toyRank a)) (Fin (toyRank b)) Lambda).map f)
    (Mbl : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) R) (hMbl : Mbl = fun a b => (toyLoc A a b).map f)
    (Rk : ∀ n : ℤ, Matrix (lIdx n) (Fin (toyRank n)) R) (hRk : Rk = fun n => (toyRes n).map f)
    (a : ℤ) :
    forwardMatOf Mbg Mbl Rk a * ilRev f B a -
      ilTgt f (a + 1) a rfl * dualDiffMatOf D Rk a (a + 1) rfl -
      dualDiffMatOf D Rk (a - 1) a (by omega) * ilTgt f a (a - 1) (by omega) - 1 = 0 := by
  subst hD hMbg hMbl hRk
  have h := congrArg (fun M => M.map f) (toy_tgt A B hAB a)
  simp only [matrix_map_sub, Matrix.map_mul, forwardMatOf_map, dualDiffMatOf_map,
    Matrix.map_one _ (map_zero f) (map_one f)] at h
  exact h.trans (Matrix.map_zero _ (map_zero f))

/-- The stagewise matrix diagram of the toy-shape Selmer datum. -/
def ilDiagram (B : Matrix (Fin 2) (Fin 2) Lambda) (hAB : A * B = 1) (hBA : B * A = 1) :
    StageMatrixDiagram R toyRank where
  dC := (ilModel R).dC
  dC_sq := (ilModel R).dC_sq
  res := modelRes (ilModel R) (ilP f A)
  res_comm := modelRes_comm (ilModel R) (ilP f A)
  glob := modelGlob (ilModel R) (ilP f A)
  loc := (ilP f A).loc
  recip := modelRecip (ilModel R) (ilP f A)
  rev := ilRev f B
  srcHom := ilSrc f
  tgtHom := ilTgt f
  chain := il_chain f B _ (ilModel_dC f) _ (ilModelRes_eq f A)
  src := il_src f A B hBA _ (ilModel_dC f) _ (ilModelGlob_eq f A) _ (ilStageLocMat f A) _
    (ilModelRes_eq f A)
  tgt := il_tgt f A B hAB _ (ilModel_dC f) _ (ilModelGlob_eq f A) _ (ilStageLocMat f A) _
    (ilModelRes_eq f A)

/-- The global duality map of the toy-shape Selmer datum is a quasi-isomorphism. -/
theorem ilSel_globalDuality (B : Matrix (Fin 2) (Fin 2) Lambda) (hAB : A * B = 1)
    (hBA : B * A = 1) :
    QuasiIso (GHom.toCC (globalDualityMap (ilSel f A) (ilTr f A) (ilHtr f A))) := by
  have e := quasiIso_stageDualityMap_of_diagram (ilModel R) (ilP f A) (ilDiagram f A B hAB hBA)
    rfl rfl rfl rfl
  rwa [stageDualityMap_eq_globalDualityMap] at e

end Stage

/-! **The inner-limit switch objects of the toy retained data** -/

section Side

open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.RC53Assist.InnerLimit
open ZInQ.Manuscript.RC.Uniform (mem_finPlane singPlane mem_singPlane)
open ZInQ.Manuscript.RC.SelmerComplex (clsAt clsAt_surjective clsAt_boundary clsAt_eq_zero
  homologyMap_clsAt exists_factor_of_surjective)
open scoped PowerSeries.WithPiTopology

section Generic

variable {k : Type} [Field k] (G : GCx k) (res : GHom G (splitLocalComplex k))
  (Q : Submodule k (Coords k))

/-- For a complex concentrated in degree one, `H¹(W) ≃ W¹` sends a class to its cocycle. -/
theorem il_h1Equiv_clsAt (W : GCx k) (hW : ConcDegOne W) (x : LinearMap.ker (W.d 1 2 rfl)) :
    h1Equiv W hW (clsAt W 1 2 rfl x) = x.1 := by
  rw [h1Equiv_apply]
  change ((W.toCC.homologyπ 1) ≫ (h1Iso W hW).hom).hom
    ((ZInQ.Manuscript.RC.SelmerComplex.liftCycAt W.toCC 1 2 rfl).hom
      (ZInQ.Manuscript.RC.SelmerComplex.kerToCC W 1 2 rfl x)) = x.1
  rw [homologyπ_h1Iso]
  exact ZInQ.Manuscript.RC.SelmerComplex.iCycles_clsAt W 1 2 rfl x

/-- The side Selmer data with condition `Q` inside the relaxed one. -/
abbrev ilSideD : SelData k :=
  ZInQ.Contrib.CloudB3RC53.SelmerDuality.restrictData (limitRelaxedData G res)
    (conditionIncl (le_top : Q ≤ ⊤))

/-- The global part of a side cochain. -/
abbrev ilA (x : (selCx (ilSideD G res Q)).X 1) : G.X 1 :=
  (show selT (ilSideD G res Q) 1 from x).1

/-- The condition part of a side cochain. -/
abbrev ilU (x : (selCx (ilSideD G res Q)).X 1) : Q := (show selT (ilSideD G res Q) 1 from x).2.1

/-- The local part of a side cochain. -/
abbrev ilL (x : (selCx (ilSideD G res Q)).X 1) : Vec2 k :=
  (show selT (ilSideD G res Q) 1 from x).2.2

/-- The cocycle condition of a side: `res a = u` in the coordinates. -/
theorem ilSide_cocycle (m : LinearMap.ker ((selCx (ilSideD G res Q)).d 1 2 rfl)) :
    res.f 1 1 rfl (ilA G res Q m.1) = ((ilU G res Q m.1 : Q) : Coords k) := by
  have hc := congrArg (fun z : (selCx (ilSideD G res Q)).X 2 =>
    (show selT (ilSideD G res Q) 2 from z).2.2) (LinearMap.mem_ker.mp m.2)
  change (show Coords k from res.f 1 1 rfl (ilA G res Q m.1)) -
    ((ilU G res Q m.1 : Q) : Coords k) - 0 = 0 at hc
  rw [sub_zero, sub_eq_zero] at hc
  exact hc

/-- A side cocycle with vanishing global part has trivial class. -/
theorem ilSide_cls_zero (m : LinearMap.ker ((selCx (ilSideD G res Q)).d 1 2 rfl))
    (h : ilA G res Q m.1 = 0) :
    clsAt (selCx (ilSideD G res Q)) 1 2 rfl m = 0 := by
  have hu : ilU G res Q m.1 = 0 := by
    have hc := ilSide_cocycle G res Q m
    rw [h, map_zero] at hc
    exact Subtype.ext hc.symm
  let y : (selCx (ilSideD G res Q)).X 0 :=
    show selT (ilSideD G res Q) 0 from (0, (-ilL G res Q m.1 : Vec2 k), 0)
  have e : (selCx (ilSideD G res Q)).d 0 1 rfl y = m.1 := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · change G.d 0 1 rfl 0 = ilA G res Q m.1
      rw [map_zero, h]
    · change (0 : Q) = ilU G res Q m.1
      exact hu.symm
    · change (show Vec2 k from res.f 0 0 rfl 0) - (-ilL G res Q m.1) - 0 = ilL G res Q m.1
      rw [map_zero]
      change (0 : Vec2 k) - -ilL G res Q m.1 - 0 = ilL G res Q m.1
      simp
  have hm : m = ⟨_, LinearMap.mem_ker.2 ((selCx (ilSideD G res Q)).d_d 0 1 2 rfl rfl y)⟩ :=
    Subtype.ext e.symm
  rw [hm]
  exact clsAt_boundary (selCx (ilSideD G res Q)) 0 1 2 rfl rfl y

/-- A relaxed cocycle `(a, res a, 0)` maps to `res a` in the relaxed coordinates. -/
theorem il_res_mem_U (a : G.X 1) (ha : G.d 1 2 rfl a = 0) :
    res.f 1 1 rfl a ∈ (limitRelaxed G res).U := by
  let c : (selCx (limitRelaxedData G res)).X 1 := show selT (limitRelaxedData G res) 1 from
    (a, (⟨res.f 1 1 rfl a, Submodule.mem_top⟩ : (⊤ : Submodule k (Coords k))), 0)
  have hc : (selCx (limitRelaxedData G res)).d 1 2 rfl c = 0 := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · exact ha
    · exact Subsingleton.elim (α := PUnit) _ _
    · change (show Coords k from res.f 1 1 rfl a) - (show Coords k from res.f 1 1 rfl a) - 0 = 0
      exact (sub_zero _).trans (sub_self _)
  refine ⟨_, ⟨clsAt (selCx (limitRelaxedData G res)) 1 2 rfl ⟨c, LinearMap.mem_ker.2 hc⟩, rfl⟩, ?_⟩
  change h1Equiv (oneComplex k (Coords k)) (oneComplex_concentrated _)
    ((HomologicalComplex.homologyMap (GHom.toCC (quotMap (limitRelaxedData G res)
      (conditionProj (⊤ : Submodule k (Coords k)).subtype))) 1).hom
        (clsAt (selCx (limitRelaxedData G res)) 1 2 rfl ⟨c, LinearMap.mem_ker.2 hc⟩)) = _
  rw [homologyMap_clsAt _ 1 2 rfl ⟨c, LinearMap.mem_ker.2 hc⟩ (by
    rw [LinearMap.mem_ker]
    exact Subsingleton.elim (α := PUnit) _ _), il_h1Equiv_clsAt]
  rfl

end Generic

variable (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
  (A : Matrix (Fin 2) (Fin 2) Lambda) (P : Ideal Lambda) [P.IsPrime]

/-- The toy global differentials vanish. -/
theorem il_Gd (a b : ℤ) (h : a + 1 = b) (x : (fibreLimitGlobal U hU P (toyStages U)).X a) :
    (fibreLimitGlobal U hU P (toyStages U)).d a b h x = 0 := by
  change Matrix.toLin' ((ZInQ.Manuscript.RC.Limits.ulimMat U
    (fun _ => (0 : Matrix (Fin (toyRank b)) (Fin (toyRank a)) Lambda))).map
      (algebraMap Lambda (ResAt P))) x = 0
  rw [ZInQ.Manuscript.RC.Limits.ulimMat_const]
  simp only [Matrix.map_zero _ (map_zero _), map_zero]
  rfl

/-- The toy localization in degree one is `x ↦ (x, 0)`. -/
theorem il_res1 (x : Fin 2 → ResAt P) :
    (((toyPairing U A).resLimit hU P).f 1 1 rfl x : Coords (ResAt P)) = (x, 0) := by
  change (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 2) (ResAt P) (ResAt P))
    (((ZInQ.Manuscript.RC.Limits.ulimMat U (fun _ => toyResOne)).map
      (algebraMap Lambda (ResAt P))) *ᵥ x) = (x, 0)
  rw [ZInQ.Manuscript.RC.Limits.ulimMat_const]
  ext i
  · simp [toyResOne, Matrix.mulVec, dotProduct, Matrix.one_apply]
  · simp [toyResOne, Matrix.mulVec, dotProduct]

/-- **Detection for the toy**: the relaxed localization image contains the finite plane (it is
equal to it: `il_relaxedImage_eq`). Kind: PROVED. -/
theorem il_hdet : finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) ≤
    (limitRelaxed (fibreLimitGlobal U hU P (toyStages U)) ((toyPairing U A).resLimit hU P)).U := by
  intro z hz
  have h2 : z.2 = 0 := mem_finPlane.mp hz
  have := il_res_mem_U (fibreLimitGlobal U hU P (toyStages U)) ((toyPairing U A).resLimit hU P)
    (z.1 : Fin 2 → ResAt P) (il_Gd U hU P 1 2 rfl _)
  rw [il_res1] at this
  have hz : z = (z.1, 0) := Prod.ext rfl h2
  rw [hz]
  exact this

/-- The finite plane over the residue field. -/
abbrev ilFP : Submodule (ResAt P) (Coords (ResAt P)) :=
  finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P))

/-- The singular plane over the residue field. -/
abbrev ilSP : Submodule (ResAt P) (Coords (ResAt P)) :=
  singPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P))

/-- The finite side Selmer data of the toy. -/
abbrev ilFinD : SelData (ResAt P) :=
  ilSideD (fibreLimitGlobal U hU P (toyStages U)) ((toyPairing U A).resLimit hU P) (ilFP P)

/-- The singular side Selmer data of the toy. -/
abbrev ilSingD : SelData (ResAt P) :=
  ilSideD (fibreLimitGlobal U hU P (toyStages U)) ((toyPairing U A).resLimit hU P) (ilSP P)

/-- The global part of a finite side cocycle. -/
def ilFinPsi0 : LinearMap.ker ((selCx (ilFinD U hU A P)).d 1 2 rfl) →ₗ[ResAt P] Vec2 (ResAt P)
    where
  toFun m := (show Vec2 (ResAt P) from ilA _ _ _ m.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The global part of a finite side cocycle descends to cohomology. -/
theorem ilFin_desc : ∃ ψ : (selCx (ilFinD U hU A P)).toCC.homology 1 →ₗ[ResAt P] Vec2 (ResAt P),
    ∀ m, ψ (clsAt _ 1 2 rfl m) = ilFinPsi0 U hU A P m :=
  exists_factor_of_surjective _ (clsAt_surjective _ 1 2 rfl) _ (fun m hm => by
    obtain ⟨y, hy⟩ := clsAt_eq_zero _ 0 1 2 rfl rfl m hm
    change ilA _ _ _ m.1 = 0
    rw [← hy]
    exact il_Gd U hU P 0 1 rfl _)

/-- The descended map `[(g, f, l)] ↦ g` on the finite side. -/
def ilFinPsi : (selCx (ilFinD U hU A P)).toCC.homology 1 →ₗ[ResAt P] Vec2 (ResAt P) :=
  Classical.choose (ilFin_desc U hU A P)

/-- The descended map on the class of a cocycle. -/
theorem ilFinPsi_spec (m : LinearMap.ker ((selCx (ilFinD U hU A P)).d 1 2 rfl)) :
    ilFinPsi U hU A P (clsAt _ 1 2 rfl m) = ilFinPsi0 U hU A P m :=
  Classical.choose_spec (ilFin_desc U hU A P) m

/-- The descended map is bijective. -/
theorem ilFinPsi_bijective : Function.Bijective (ilFinPsi U hU A P) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro v hv
    obtain ⟨m, rfl⟩ := clsAt_surjective _ 1 2 rfl v
    rw [ilFinPsi_spec] at hv
    exact ilSide_cls_zero _ _ _ m hv
  · intro g
    let x : (selCx (ilFinD U hU A P)).X 1 := show selT (ilFinD U hU A P) 1 from
      (g, (⟨(g, 0), mem_finPlane.2 rfl⟩ : ilFP P), 0)
    have hx : (selCx (ilFinD U hU A P)).d 1 2 rfl x = 0 := by
      refine Prod.ext (il_Gd U hU P 1 2 rfl g) (Prod.ext (Subsingleton.elim (α := PUnit) _ _) ?_)
      have hr := il_res1 U hU A P g
      change (show Coords (ResAt P) from ((toyPairing U A).resLimit hU P).f 1 1 rfl g) -
        ((g, 0) : Coords (ResAt P)) - 0 = 0
      rw [hr]
      simp
    exact ⟨clsAt _ 1 2 rfl ⟨x, LinearMap.mem_ker.2 hx⟩, (ilFinPsi_spec U hU A P _).trans rfl⟩

/-- **`H¹` of the finite limit side of the toy is the plane `k²`** (`[(g, f, l)] ↦ g`). Kind:
definition (PROVED bijectivity). -/
def ilFinSideEquiv : (selCx (finiteLimitSide (fibreLimitGlobal U hU P (toyStages U))
    ((toyPairing U A).resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] Vec2 (ResAt P) :=
  LinearEquiv.ofBijective (ilFinPsi U hU A P) (ilFinPsi_bijective U hU A P)

/-- Every singular side class vanishes. -/
theorem ilSing_eq_zero (v : (selCx (ilSingD U hU A P)).toCC.homology 1) : v = 0 := by
  obtain ⟨m, rfl⟩ := clsAt_surjective _ 1 2 rfl v
  apply ilSide_cls_zero
  have hc := ilSide_cocycle _ _ _ m
  have hr := il_res1 U hU A P (ilA _ _ _ m.1)
  rw [hr] at hc
  have h1 := mem_singPlane.mp (ilU _ _ _ m.1).2
  rw [← hc] at h1
  exact h1

/-- **`H¹` of the singular limit side of the toy vanishes.** Kind: PROVED. -/
theorem ilSingSide_subsingleton : Subsingleton ((selCx (singularLimitSide
    (fibreLimitGlobal U hU P (toyStages U))
      ((toyPairing U A).resLimit hU P)).Dside).toCC.homology 1) :=
  ⟨fun a b => (ilSing_eq_zero U hU A P a).trans (ilSing_eq_zero U hU A P b).symm⟩

end Side

/-! **Two two-term stages: fibre dimensions `2` and `0`** -/

section Stages

variable (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F] (ι : Localization.AtPrime P →+* F)

/-- **The source stage** `[A² --0--> A²]` (`A = Λ_𝔭`), cycle `(1, 1)`, functional `0`, coordinate
`0`. Kind: definition. -/
def ilStage0 : TwoTermStage ι where
  n := 1
  D := 0
  z := fun _ => 1
  w := 0
  u := 0
  hz := Matrix.zero_mulVec _
  hw := Matrix.vecMul_zero _
  hu := by
    ext i j
    simp [Matrix.vecMulVec_apply]

/-- **The target stage** `[A --1--> A]`, cycle, functional and coordinate `0`. Kind:
definition. -/
def ilStage1 : TwoTermStage ι where
  n := 0
  D := 1
  z := 0
  w := 0
  u := 0
  hz := Matrix.mulVec_zero _
  hw := Matrix.zero_vecMul _
  hu := by
    ext i j
    simp [Matrix.vecMulVec_apply]

/-- The source stage has fibre dimension `2`. Kind: PROVED. -/
theorem ilStage0_fiberDim : (ilStage0 P ι).fiberDim (resAt P) = 2 := by
  unfold TwoTermStage.fiberDim
  have h0 : (ilStage0 P ι).D.map (resAt P) = 0 := Matrix.map_zero _ (map_zero _)
  rw [h0, Matrix.mulVecLin_zero, LinearMap.ker_zero, finrank_top, Module.finrank_fin_fun]
  rfl

/-- The target stage has fibre dimension `0`. Kind: PROVED. -/
theorem ilStage1_fiberDim : (ilStage1 P ι).fiberDim (resAt P) = 0 := by
  unfold TwoTermStage.fiberDim
  have h1 : (ilStage1 P ι).D.map (resAt P) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  rw [h1, Matrix.mulVecLin_one, LinearMap.ker_id, finrank_bot]

/-- The fibre `H¹` of the source stage is the plane. Kind: definition (PROVED dimensions). -/
def ilFiber0Equiv : Vec2 (ResAt P) ≃ₗ[ResAt P] fiberH1 (resAt P) (ilStage0 P ι) :=
  haveI := fiberH1_finite (resAt P) (ilStage0 P ι)
  LinearEquiv.ofFinrankEq _ _ (by
    rw [finrank_h1_twoTermFiberComplex, ilStage0_fiberDim, Module.finrank_fin_fun])

/-- The fibre `H¹` of the target stage vanishes. Kind: PROVED. -/
theorem ilFiber1_subsingleton : Subsingleton (fiberH1 (resAt P) (ilStage1 P ι)) := by
  have := fiberH1_finite (resAt P) (ilStage1 P ι)
  rw [← Module.finrank_zero_iff (R := ResAt P)]
  rw [finrank_h1_twoTermFiberComplex, ilStage1_fiberDim]

end Stages

/-! **Every inner-limit switch drops the fibre dimension by two** -/

section Drop

variable {P : Ideal Lambda} [P.IsPrime] {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}
  {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {Cn : ActualConj K S} {W : WeierstrassCurve K} {hW : W.map (Cn.κ : K →+* K) = W}
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **An inner-limit switch drops the fibre dimension by two** (`ILStageStep.toStepData`, then
the RC53 group's `QuasiNonquadStep.toNonquadDims`). Kind: PROVED. -/
theorem ilStageStep_drop {S₀ S₁ : TwoTermStage ι} (X : ILStageStep P Cn W hW S₀ S₁) :
    S₁.fiberDim (resAt P) + 2 = S₀.fiberDim (resAt P) :=
  X.toStepData.toStep.toNonquadDims.drop

/-- **No inner-limit switch from a stage to itself.** Kind: PROVED. -/
theorem ilStageStep_isEmpty_self (S₀ : TwoTermStage ι) : IsEmpty (ILStageStep P Cn W hW S₀ S₀) :=
  ⟨fun X => by have := ilStageStep_drop X; omega⟩

end Drop

/-! **The toy switch** -/

section Toy

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F] (ι : Localization.AtPrime P →+* F)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)

/-- **A TOY instance of one inner-limit switch.** Kind: definition (PROVED fields). -/
def ilToyStep : ILStageStep P Cn W hW (ilStage0 P ι) (ilStage1 P ι) where
  U := U
  hU := hU
  G i := ilCx (StageA i)
  hflat i n := ilCx_flat (StageA i) n
  Uc i := exZero (StageA i)
  res i := ilRes (StageA i)
  ιc i := exIota (StageA i)
  Q i := ilSel (stageMap i) (toyA Cn W hW)
  tr i := ilTr (stageMap i) (toyA Cn W hW)
  htr i := ilHtr (stageMap i) (toyA Cn W hW)
  hdual i := ilSel_globalDuality (stageMap i) (toyA Cn W hW) (toyB Cn W hW)
    (toyA_mul_toyB Cn W hW) (toyB_mul_toyA Cn W hW)
  hres i _ := ilCx_residualCohomologyFinite (StageA i)
  lo := 1
  hi := 2
  hbdd i _ n hn := by
    rw [ilCx_finrank_residual]
    exact toyRank_bounded n hn
  B := 2
  hB i _ n := by
    rw [ilCx_finrank_residual]
    exact ilToyRank_le_two n
  C := toyStages U
  D := toyPairing U (toyA Cn W hW)
  E := toyDuality U _ _ (toyA_mul_toyB Cn W hW) (toyB_mul_toyA Cn W hW)
  hlift i _ a b := (congrFun (congrFun (ilStageLocMat (stageMap i) (toyA Cn W hW)) a) b).symm
  hrank := Filter.Eventually.of_forall fun i _ n => (ilCx_finrank_residual (StageA i) n).symm
  hrankB n := ilToyRank_le_two n
  ε₀ := 1
  ε₂ := 1
  ε := 1
  σ := 1
  hε₂ := one_ne_zero
  hε := one_ne_zero
  hσ := one_ne_zero
  hloc := toy_hloc Cn W hW U P
  hdet := il_hdet U hU (toyA Cn W hW) P
  φ := (ilFinSideEquiv U hU (toyA Cn W hW) P).trans (ilFiber0Equiv P ι)
  φ' :=
    haveI := ilSingSide_subsingleton U hU (toyA Cn W hW) P
    haveI := ilFiber1_subsingleton P ι
    LinearEquiv.ofSubsingleton _ _

/-- **The relaxed localization image of the toy limit diagram is the finite plane**: the field
`hU` of the dimensions derived from `ilToyStep` (`U = U^⊥` from the duality, with the detection).
Kind: PROVED. -/
theorem il_relaxedImage_eq :
    (limitRelaxed (fibreLimitGlobal U hU P (toyStages U))
      ((toyPairing U (toyA Cn W hW)).resLimit hU P)).U =
        finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) :=
  (ilToyStep Cn W hW P (ZInQ.Contrib.CloudB3RC53.UniformSwitch.toFracAt P) U
    hU).toStepData.toStep.toNonquadDims.hU

include Cn W hW U hU in
/-- **The toy step is not degenerate**: its source has fibre dimension `2 > 1` and the step drops
it to `0` (`ilStageStep_drop` applied to `ilToyStep`, checked against the direct computation).
Kind: PROVED. -/
theorem ilToyStep_drop :
    (ilStage1 P ι).fiberDim (resAt P) + 2 = (ilStage0 P ι).fiberDim (resAt P) ∧
      (ilStage0 P ι).fiberDim (resAt P) = 2 ∧ (ilStage1 P ι).fiberDim (resAt P) = 0 ∧
        1 < (ilStage0 P ι).fiberDim (resAt P) :=
  ⟨ilStageStep_drop (ilToyStep Cn W hW P ι U hU), ilStage0_fiberDim P ι, ilStage1_fiberDim P ι,
    by rw [ilStage0_fiberDim]; omega⟩

end Toy

/-- The toy step at `E₁ : y² = x(x−1)(x+3)` over `ℚ`, the prime `(t)` and the hyperfilter. -/
def ilToyStepE1 : ILStageStep Pt0 (actualConjQ Set.univ) curveE1 (curveE1_map_conj Set.univ)
    (ilStage0 Pt0 (ZInQ.Contrib.CloudB3RC53.UniformSwitch.toFracAt Pt0))
    (ilStage1 Pt0 (ZInQ.Contrib.CloudB3RC53.UniformSwitch.toFracAt Pt0)) :=
  ilToyStep _ _ _ Pt0 _ (Filter.hyperfilter ℕ) Filter.hyperfilter_le_cofinite

/-! **Degenerate satisfiability of the leaf** -/

/-- **`PrimRegularityInputsIL D` holds when the primitive coordinates vanish** (the `u = 0`
branch). Kind: PROVED. -/
theorem primRegularityInputsIL_of_uPrim_zero {ℓ : ℕ} (D : RCData ℓ)
    (hD : ∀ F x, D.uPrim F x = 0) : PrimRegularityInputsIL D :=
  fun _ _ F _ x => ⟨0, by rw [hD F x]; exact isTExpansion_zero, Or.inl rfl⟩

/-- Interface data with vanishing primitive and corrected coordinates. Kind: definition. -/
def ilZeroData (ℓ : ℕ) : RCData ℓ where
  S := ∅
  prepared := fun _ => True
  Lstar := fun _ => 1
  jgen := fun _ => 0
  jrc := fun _ _ => 0
  hstar := -7
  stages := Filter.hyperfilter ℕ
  Mθ := fun θ => θ + 3
  aθ := fun _ _ => 1
  admissible := fun _ D => D = 1
  δo := 0
  kfin := -7
  uPrim := fun _ _ => 0
  uTilde := fun _ _ => 0

/-- **The leaf is satisfiable by concrete data.** Kind: PROVED. -/
theorem primRegularityInputsIL_ilZeroData (ℓ : ℕ) : PrimRegularityInputsIL (ilZeroData ℓ) :=
  primRegularityInputsIL_of_uPrim_zero _ fun _ _ => rfl

end ZInQ.Manuscript.RC.Wiring
