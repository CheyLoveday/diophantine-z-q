import ZInQKernel.Contrib.OneProof.RC.BaseZeroAssembly.Assembly

/-!
# Lane RC25 (base zero), part 4: the new inputs are satisfiable and do not force the conclusion

Every declaration here is `PROVED`.

* `trivialStage`: a `SplitNormStage` (the trivial ring-class group, `a_r = 3`, `m_r = 1`): the
  hypotheses of `SplitNormStage.weightedPoint_eq` are consistent with a nonzero weighted point.
* `boundary45Base_nonvacuous`: a `Boundary45Base` whose central cycle `z̄` is nonzero (for a
  non-torsion specified point): the inputs of (4.5) at the base do not force `z̄ = 0`; `z̄ = 0`
  follows only for a torsion point (`Boundary45Base.central_eq_zero_of_torsion`).
* `baseZeroCore_nonvacuous`: for every interface data `D` and family `F` whose base coordinate
  `D.uPrim F 0` is (the image of) an element `f ∈ Λ`, there is a `BaseZeroCore D F 1` (over the
  group `ℤ` with the non-torsion point `1`) with generic coordinate `f` and central cycle `f(0)`.
  With `f = 1` the central cycle and the central coordinate are `1 ≠ 0`: without the height formula
  (a torsion specified point) the inputs do not imply the conclusion of the lemma. For a torsion
  specified point the core is equivalent to the conclusion `u_{prim,0}(0) = 0`; the non-vacuity
  examples use a non-torsion point.
* `baseTail_hypotheses_of_lambda`: the hypotheses of `baseTail_of_targets` hold when
  `ũ₀ = u_{prim,0}` is (the image of) an element of `Λ` (with `ε = 1`).

The conductor-one Heegner data (`HeegnerData`: a newform, a lattice, the modular parametrization
and a CM point) are not constructed here; they are unchanged from lane RC0's `BaseZeroModelCST`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.BaseZeroAssembly

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Uniform
  ZInQ.Manuscript.RC.Rings ZInQ.Contrib.CloudB3RC53
open Filter Topology Matrix

/-! ## A stage and a boundary -/

/-- The trivial stage: `Δ` trivial, `E(H_r) = E(K) = ℤ`, `y_1 = y_r = 1`, `a_r = 3`; (4.1) reads
`1 = 3 − 1 − 1`, and the weighted point is `W = 1 = (3 − 2) • 1`. -/
def trivialStage : SplitNormStage (1 : ℤ) where
  Pt := ℤ
  Δ := Unit
  act := 1
  N := ⊤
  decN := fun x => isTrue (Subgroup.mem_top x)
  T := Finset.univ
  hT := fun _ => ⟨(), ⟨Finset.mem_univ _, Subgroup.mem_top _⟩, fun y _ => Subsingleton.elim y ()⟩
  y1 := 1
  hy1 := fun _ _ => rfl
  yr := 1
  a := 3
  σ := 1
  hnorm := by
    simp only [Finset.sum_filter, Subgroup.mem_top, ite_true, Finset.univ_unique,
      Finset.sum_singleton, MonoidHom.one_apply, Module.End.one_apply]
    norm_num
  incl := AddMonoidHom.id ℤ
  hincl := Function.injective_id
  hP := by simp
  W := 1
  hW := by simp

/-- The weighted point of the trivial stage is the point itself (`m_r = 1`). PROVED. -/
theorem trivialStage_weightedPoint : trivialStage.W = (trivialStage.a - 2) • (1 : ℤ) :=
  trivialStage.weightedPoint_eq

/-- The additive map `x ↦ (x c)` from `ℤ` to `ℚ₂¹`. -/
def constKappa (c : ℚ_[2]) : ℤ →+ (Fin 1 → ℚ_[2]) where
  toFun x := fun _ => (x : ℚ_[2]) * c
  map_zero' := by
    funext i
    simp
  map_add' x y := by
    funext i
    push_cast
    simp only [Pi.add_apply]
    ring

/-- The boundary of the constant stages with `L = 1` and `κ(x) = x c`: the central cycle is `c`. -/
def constBoundary (c : ℚ_[2]) : Boundary45Base (1 : ℤ) 1 (fun _ => c) where
  stage := fun _ => trivialStage
  L := 1
  hL := one_ne_zero
  kappa := constKappa c
  hlim := by
    have h : (fun _ : ℕ => ((1 : ℤ) : ℚ_[2]) • constKappa c trivialStage.W) =
        fun _ => fun _ => c := by
      funext i j
      simp [constKappa, trivialStage]
    rw [h]
    exact tendsto_const_nhds

/-- **The inputs of (4.5) at the base do not force the central cycle to vanish** (PROVED): the
boundary of the constant stages with central cycle `1 ≠ 0`. -/
theorem boundary45Base_nonvacuous :
    ∃ _ : Boundary45Base (1 : ℤ) 1 (fun _ => (1 : ℚ_[2])), (fun _ : Fin 1 => (1 : ℚ_[2])) ≠ 0 :=
  ⟨constBoundary 1, fun h => one_ne_zero (congrFun h 0)⟩

/-! ## The core of the base model -/

/-- **The core of the base model is satisfiable, with any integral base coordinate** (PROVED): if
`D.uPrim F 0` is the image of `f ∈ Λ`, there is a `BaseZeroCore D F 1` with the two-term model
`[A --0--> A]`, the cycle `z = f`, the functional `1`, generic coordinate `f` and central cycle
`f(0)`. -/
theorem baseZeroCore_nonvacuous {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) (f : Lambda)
    (hf : D.uPrim Fam 0 = lamIncl f) :
    ∃ M : BaseZeroCore D Fam (1 : ℤ),
      M.uprim = algebraMap Lambda (FractionRing Lambda) f ∧
        ∀ i, Rings.rhoT (M.z i) = lambdaEvalZero f := by
  classical
  refine ⟨{
    m := 0
    Dm := 0
    hcentral := by rw [Matrix.map_zero _ (map_zero _), Matrix.rank_zero]
    z := fun _ => algebraMap Lambda LambdaT f
    hz := by simp
    CU := PairedFunctional.threeTermComplex (M := Fin 1 → Rings.LambdaT)
      (N := Fin 1 → Rings.LambdaT) (M' := Fin 1 → Rings.LambdaT) 0 0 (by simp)
    e1 := LinearEquiv.refl _ _
    e2 := LinearEquiv.refl _ _
    hd := by
      intro y
      simp only [PairedFunctional.threeTermComplex_d_one_two, Matrix.zero_mulVec]
      rfl
    lam := LinearMap.proj 0
    hlam := by
      intro y
      simp only [PairedFunctional.threeTermComplex_d_one_two]
      rfl
    uprim := algebraMap LambdaT (FractionRing Lambda) (algebraMap Lambda LambdaT f)
    hu := ?_
    boundary := ?_
    hprimId := by
      rw [hf]
      exact isTExpansion_algebraMap_lambdaT f }, ?_, ?_⟩
  · intro w _ hrep
    have hw0 : w 0 = 1 := by
      have h := hrep (Pi.single 0 1)
      rw [dotProduct_single, mul_one] at h
      exact h.symm.trans (by rfl)
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.vecMulVec_apply, Matrix.adjugate_fin_one, hw0]
  · have hz : (fun i : Fin (0 + 1) => Rings.rhoT (algebraMap Lambda LambdaT f)) =
        fun _ => lambdaEvalZero f := by
      funext i
      exact rhoT_algebraMap f
    exact hz ▸ constBoundary (lambdaEvalZero f)
  · exact algebraMap_lambdaT_lambda f
  · intro i
    exact rhoT_algebraMap f

/-- **The core does not force the conclusion** (PROVED): with `f = 1` the generic coordinate is
`1` and the central cycle is `1`, both nonzero; base zero's `ũ₀(0) = 0` needs the height formula
(a torsion specified point, `Boundary45Base.central_eq_zero_of_torsion`), and here the specified
point `1 ∈ ℤ` has infinite order. -/
theorem baseZeroCore_not_forced {ℓ : ℕ} (D : RCData ℓ) (Fam : Family)
    (hf : D.uPrim Fam 0 = lamIncl 1) :
    ∃ M : BaseZeroCore D Fam (1 : ℤ), M.uprim ≠ 0 ∧ ∀ i, Rings.rhoT (M.z i) ≠ 0 := by
  obtain ⟨M, hu, hz⟩ := baseZeroCore_nonvacuous D Fam 1 hf
  refine ⟨M, ?_, fun i => ?_⟩
  · rw [hu, map_one]
    exact one_ne_zero
  · rw [hz i, map_one]
    exact one_ne_zero

/-- **The hypotheses of `baseTail_of_targets` are satisfiable** (PROVED): if `ũ₀ = u_{prim,0}` is
the image of `f ∈ Λ`, then `u_{prim,0} = f ∈ Frac Λ` has `t`-expansion `D.uPrim F 0`, (4.7) holds
with `ε = 1`, and `ũ₀ ∈ Λ[1/2]`. -/
theorem baseTail_hypotheses_of_lambda {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) (f : Lambda)
    (hp : D.uPrim Fam 0 = lamIncl f) (ht : D.uTilde Fam 0 = lamIncl f) :
    IsTExpansion (algebraMap Lambda (FractionRing Lambda) f) (D.uPrim Fam 0) ∧
      (∃ ε : PowerSeries ℚ_[2], LamUnit ε ∧ D.uTilde Fam 0 = ε * D.uPrim Fam 0) ∧
      InLamHalf (D.uTilde Fam 0) := by
  refine ⟨by rw [hp]; exact isTExpansion_algebraMap f, ⟨1, ⟨1, by simp⟩, by rw [ht, hp, one_mul]⟩,
    ?_⟩
  rw [ht]
  exact ⟨0, fun n => PowerSeries.coeff n f, fun n => by simp [lamIncl]⟩

end ZInQ.Manuscript.RC.BaseZeroAssembly
