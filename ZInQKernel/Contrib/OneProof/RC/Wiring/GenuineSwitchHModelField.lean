import ZInQKernel.Contrib.OneProof.RC.Limits.FieldSplitting
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchHModelAssembly

/-!
**Theorem 5.3: two-term models over a field, and the switch models of `HomologySwitchDataPK`**

Lemma `ex:limits-inner-limit` (tex 4391–4451) in the field case (lane RC29's `FieldSplitting.lean`:
every complex of `k`-vector spaces with finite-dimensional cohomology has a graded finite free
model with zero differential and ranks the cohomology dimensions, `fsplitModelOfHomology`), and the
two-term models of the height-one switching argument (Proposition
`ex:limits-uniform-lower-bound`, tex 4976–4996).

The text's model (tex 4986–4988): "Cancel the degree-zero and degree-three disks and then the unit
disks. Write `C = [R^s --d--> R^s]` in degrees one and two, with `d ⊗ k = 0`" — over the residue
field this is `[k^s --0--> k^s]`, the normal form `twoTermModel` below; cancelling the degree-zero
and degree-three disks is the concentration of the cohomology in degrees one and two, and the
square shape is `dim H¹ = dim H²`.

**What a two-term model needs** (`exists_twoTerm_model_iff`): a complex `C` of `k`-vector spaces
with finite-dimensional cohomology is homotopy equivalent to the fibre `[k^{n+1} --D̄--> k^{n+1}]`
of a stage of fibre dimension `s` if and only if its cohomology vanishes outside degrees one and
two and `dim H¹ = dim H² = s`. The direction "if" is `stageModel_of_concentrated` (and in normal
form `twoTermModel`: `C ≃ [k^s --0--> k^s]`; `exists_twoTerm_model`: a square two-term complex of
size at least one); "only if" is `tmod_homology_zero_of_equiv`, `tmod_h1_of_equiv`,
`tmod_h2_of_equiv` (`GenuineSwitchHModelAssembly.lean`: the two-term complex vanishes outside
degrees one and two, `H¹ = ker D̄`, `H² = coker D̄`, of the same dimension since `D̄` is square).

**The `model` field of `HomologySwitchDataPK`** (`HomologySwitchDataPK.ofConcentrated`): for a
configuration family whose fibres' Selmer complexes have finite-dimensional cohomology concentrated
in degrees one and two with `dim H¹ = dim H² = (stage c).fiberDim ρ`, the field `model` is DERIVED
(`fibreModels_of_concentrated`, then `FibreModels.model`). The remaining inputs are listed at
`HomologySwitchDataPK.ofFibreModels`: `hz0`, `hw0` (through the derived model), `hu0`, `σ`, `h2`,
`hσ`, `class_ne_zero`, the switch fields, and the stages themselves (integral data over `A`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Module Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SwitchInputs
  ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Manuscript.RC.Limits (fsplitModelOfHomology fsplit_hfin_of_homology
  fsplitModel_rank_eq_homology)

variable {k : Type} [Field k]

/-- **The two-term model in normal form** (tex 4391–4451, 4976–4996): a complex `X` of `k`-vector
spaces with finite-dimensional cohomology concentrated in degrees one and two and
`dim H² = dim H¹ = s` is homotopy equivalent to `[k^s --0--> k^s]` (lane RC29's field splitting,
then `tmodOfModel`). This is the fibre of the text's minimal model (tex 4986–4988: "Cancel the
degree-zero and degree-three disks and then the unit disks. Write `C = [R^s --d--> R^s]` in degrees
one and two, with `d ⊗ k = 0`"), over the residue field only. Kind: definition (PROVED). -/
def twoTermModel (X : GCx k) (hfin : ∀ n, FiniteDimensional k (X.toCC.homology n))
    (hconc : ∀ n, n ≠ 1 → n ≠ 2 → finrank k (X.toCC.homology n) = 0)
    (hsq : finrank k (X.toCC.homology 2) = finrank k (X.toCC.homology 1)) :
    HomotopyEquiv X.toCC (tmodCx (0 : Matrix (Fin (finrank k (X.toCC.homology 1)))
      (Fin (finrank k (X.toCC.homology 1))) k)) :=
  tmodOfModel X (fsplitModelOfHomology X hfin) (fun _ _ _ => rfl)
    (fun n h1 h2 => (fsplitModel_rank_eq_homology X (fsplit_hfin_of_homology X hfin) n).trans
      (hconc n h1 h2))
    (fsplitModel_rank_eq_homology X (fsplit_hfin_of_homology X hfin) 1)
    ((fsplitModel_rank_eq_homology X (fsplit_hfin_of_homology X hfin) 2).trans hsq)

/-- PROVED. The kernel of the `1 × 1` identity matrix is zero. -/
theorem tmod_finrank_ker_one : finrank k (LinearMap.ker (1 : Matrix (Fin 1) (Fin 1) k).mulVecLin) = 0 := by
  rw [Matrix.mulVecLin_one, LinearMap.ker_id, finrank_bot]

/-- PROVED. The kernel of a zero square matrix is everything. -/
theorem tmod_finrank_ker_zero (m : ℕ) :
    finrank k (LinearMap.ker (0 : Matrix (Fin m) (Fin m) k).mulVecLin) = m := by
  have : (0 : Matrix (Fin m) (Fin m) k).mulVecLin = 0 :=
    LinearMap.ext fun x => Matrix.zero_mulVec x
  rw [this, LinearMap.ker_zero, finrank_top, Module.finrank_fin_fun]

/-- PROVED. **`exists_twoTerm_model`** (tex 4391–4451, 4983–4987: "the two-term model"): a complex
of `k`-vector spaces with finite-dimensional cohomology concentrated in degrees one and two and
`dim H¹ = dim H²` is homotopy equivalent to a square two-term complex `[k^{n+1} --D--> k^{n+1}]`
(the shape `twoTermFiberComplex` of a `TwoTermStage`), with `dim ker D = dim H¹`. -/
theorem exists_twoTerm_model (X : GCx k) (hfin : ∀ n, FiniteDimensional k (X.toCC.homology n))
    (hconc : ∀ n, n ≠ 1 → n ≠ 2 → finrank k (X.toCC.homology n) = 0)
    (hsq : finrank k (X.toCC.homology 2) = finrank k (X.toCC.homology 1)) :
    ∃ (n : ℕ) (D : Matrix (Fin (n + 1)) (Fin (n + 1)) k),
      finrank k (LinearMap.ker D.mulVecLin) = finrank k (X.toCC.homology 1) ∧
        Nonempty (HomotopyEquiv X.toCC (tmodCx D)) := by
  obtain h | ⟨m, hm⟩ : finrank k (X.toCC.homology 1) = 0 ∨
      ∃ m, finrank k (X.toCC.homology 1) = m + 1 := by
    rcases Nat.eq_zero_or_pos (finrank k (X.toCC.homology 1)) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
  · refine ⟨0, 1, tmod_finrank_ker_one.trans h.symm, ⟨(twoTermModel X hfin hconc hsq).trans
      (tmodEquiv_of_finrank _ _ ?_)⟩⟩
    rw [tmod_finrank_ker_zero, tmod_finrank_ker_one, h]
  · refine ⟨m, 0, (tmod_finrank_ker_zero _).trans hm.symm, ⟨(twoTermModel X hfin hconc hsq).trans
      (tmodEquiv_of_finrank _ _ ?_)⟩⟩
    rw [tmod_finrank_ker_zero, tmod_finrank_ker_zero, hm]

/-- **The stage model** (tex 4976–4996): under the same hypotheses, `X ≃ [k^{n+1} --D̄--> k^{n+1}]`
for every stage `S` of fibre dimension `dim H¹`. Kind: definition (PROVED). -/
def stageModel_of_concentrated {A F : Type} [CommRing A] [Field F] {ι : A →+* F} (ρ : A →+* k)
    (X : GCx k) (hfin : ∀ n, FiniteDimensional k (X.toCC.homology n))
    (hconc : ∀ n, n ≠ 1 → n ≠ 2 → finrank k (X.toCC.homology n) = 0)
    (hsq : finrank k (X.toCC.homology 2) = finrank k (X.toCC.homology 1)) (S : TwoTermStage ι)
    (hS : S.fiberDim ρ = finrank k (X.toCC.homology 1)) :
    HomotopyEquiv X.toCC (twoTermFiberComplex ρ S) :=
  (twoTermModel X hfin hconc hsq).trans ((tmodZeroCast hS.symm).trans (tmodNormal (S.D.map ρ)))

/-- PROVED. **What a two-term model needs** (tex 4976–4996): a complex `X` of `k`-vector spaces with
finite-dimensional cohomology is homotopy equivalent to the fibre of a stage `S` if and only if its
cohomology vanishes outside degrees one and two and `dim H¹ = dim H² = s`, the fibre dimension of
`S`. -/
theorem exists_twoTerm_model_iff {A F : Type} [CommRing A] [Field F] {ι : A →+* F} (ρ : A →+* k)
    (X : GCx k) (hfin : ∀ n, FiniteDimensional k (X.toCC.homology n)) (S : TwoTermStage ι) :
    Nonempty (HomotopyEquiv X.toCC (twoTermFiberComplex ρ S)) ↔
      (∀ n, n ≠ 1 → n ≠ 2 → finrank k (X.toCC.homology n) = 0) ∧
        finrank k (X.toCC.homology 1) = S.fiberDim ρ ∧
          finrank k (X.toCC.homology 2) = S.fiberDim ρ := by
  constructor
  · rintro ⟨e⟩
    exact ⟨fun n h1 h2 => tmod_homology_zero_of_equiv (S.D.map ρ) e n h1 h2,
      tmod_h1_of_equiv ρ S e, tmod_h2_of_equiv ρ S e⟩
  · rintro ⟨hconc, h1, h2⟩
    exact ⟨stageModel_of_concentrated ρ X hfin hconc (h2.trans h1.symm) S h1.symm⟩

section Switch

variable {A F : Type} [CommRing A] [Field F] {ι : A →+* F}

/-- **Fibre models from the cohomology of the fibres** (tex 4391–4451, 4976–4996): if the Selmer
complex of every configuration's fibre has finite-dimensional cohomology concentrated in degrees
one and two with `dim H¹ = dim H² = (stage c).fiberDim ρ`, the field splitting gives graded finite
free models adapted to the stages. Kind: definition (PROVED fields). -/
def fibreModels_of_concentrated (Φ : SwitchFamily k A) (ρ : A →+* k)
    (stage : Φ.Config → TwoTermStage ι)
    (hfin : ∀ c n, FiniteDimensional k ((selCx (Φ.fibre c)).toCC.homology n))
    (hconc : ∀ c n, n ≠ 1 → n ≠ 2 → finrank k ((selCx (Φ.fibre c)).toCC.homology n) = 0)
    (h1 : ∀ c, finrank k ((selCx (Φ.fibre c)).toCC.homology 1) = (stage c).fiberDim ρ)
    (h2 : ∀ c, finrank k ((selCx (Φ.fibre c)).toCC.homology 2) = (stage c).fiberDim ρ) :
    FibreModels Φ ρ stage where
  R c := fsplitModelOfHomology (selCx (Φ.fibre c)) (hfin c)
  hdC _ _ _ _ := rfl
  h0 c n hn1 hn2 := (fsplitModel_rank_eq_homology _ (fsplit_hfin_of_homology _ (hfin c)) n).trans
    (hconc c n hn1 hn2)
  h1 c := (fsplitModel_rank_eq_homology _ (fsplit_hfin_of_homology _ (hfin c)) 1).trans (h1 c)
  h2 c := (fsplitModel_rank_eq_homology _ (fsplit_hfin_of_homology _ (hfin c)) 2).trans (h2 c)

/-- PROVED. **The `model` field of `HomologySwitchDataPK` exists** under the concentration
hypothesis: for every configuration, the fibre's Selmer complex is homotopy equivalent to the
fibre of its stage. -/
theorem model_of_concentrated (Φ : SwitchFamily k A) (ρ : A →+* k)
    (stage : Φ.Config → TwoTermStage ι)
    (hfin : ∀ c n, FiniteDimensional k ((selCx (Φ.fibre c)).toCC.homology n))
    (hconc : ∀ c n, n ≠ 1 → n ≠ 2 → finrank k ((selCx (Φ.fibre c)).toCC.homology n) = 0)
    (h1 : ∀ c, finrank k ((selCx (Φ.fibre c)).toCC.homology 1) = (stage c).fiberDim ρ)
    (h2 : ∀ c, finrank k ((selCx (Φ.fibre c)).toCC.homology 2) = (stage c).fiberDim ρ)
    (c : Φ.Config) :
    Nonempty (HomotopyEquiv (selCx (Φ.fibre c)).toCC (twoTermFiberComplex ρ (stage c))) :=
  ⟨(fibreModels_of_concentrated Φ ρ stage hfin hconc h1 h2).model c⟩

/-- **The homology-level switching data with the model derived from the concentration
hypothesis** (tex 4391–4451, 4976–5195): `HomologySwitchDataPK.ofFibreModels` with the fibre models
of `fibreModels_of_concentrated`. Kind: definition. -/
def HomologySwitchDataPK.ofConcentrated {Φ : SwitchFamily k A} {ρ : A →+* k} {u : F}
    (stage : Φ.Config → TwoTermStage ι)
    (hfin : ∀ c n, FiniteDimensional k ((selCx (Φ.fibre c)).toCC.homology n))
    (hconc : ∀ c n, n ≠ 1 → n ≠ 2 → finrank k ((selCx (Φ.fibre c)).toCC.homology n) = 0)
    (h1 : ∀ c, finrank k ((selCx (Φ.fibre c)).toCC.homology 1) = (stage c).fiberDim ρ)
    (h2 : ∀ c, finrank k ((selCx (Φ.fibre c)).toCC.homology 2) = (stage c).fiberDim ρ)
    (hz0 : (((fibreModels_of_concentrated Φ ρ stage hfin hconc h1 h2).model Φ.actual).hom.f 1).hom
      Φ.zAct = fun i => ρ ((stage Φ.actual).z i))
    (hw0 : ∀ y, Φ.lamAct y = (fun i => ρ ((stage Φ.actual).w i)) ⬝ᵥ
      ((((fibreModels_of_concentrated Φ ρ stage hfin hconc h1 h2).model Φ.actual).hom.f 2).hom y :
        Fin _ → k))
    (hu0 : (stage Φ.actual).u = u)
    (σ : ∀ c, fiberH1 ρ (stage c) →ₗ[k] fiberH1 ρ (stage c))
    (h2' : Φ.quadratic ρ → (2 : k) ≠ 0)
    (hσ : Φ.quadratic ρ → ∀ c, σ c ∘ₗ σ c = LinearMap.id)
    (class_ne_zero : ∀ c, Reach Φ.next Φ.actual c → ∃ i, (stage c).z i ≠ 0)
    (switch_mixed : ∀ c, Reach Φ.next Φ.actual c → (¬ Φ.quadratic ρ ∨
      (0 < finrank k ↥(signPart (σ c) (1 : k)) ∧ 0 < finrank k ↥(signPart (σ c) (-1 : k)))) →
      1 < (stage c).fiberDim ρ →
      ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
        (Φ.quadratic ρ → ∃ M : QuasiMixedStep ρ (stage c) (stage (Φ.next c p)) (σ c)
            (σ (Φ.next c p)), M.X.SF.Dside = Φ.fibre c ∧ M.X.SS.Dside = Φ.fibre (Φ.next c p)) ∧
        (¬ Φ.quadratic ρ → ∃ N : QuasiNonquadStep ρ (stage c) (stage (Φ.next c p)),
            N.SF.Dside = Φ.fibre c ∧ N.SS.Dside = Φ.fibre (Φ.next c p)))
    (switch_single : ∀ c, Reach Φ.next Φ.actual c → Φ.quadratic ρ →
      ¬ (0 < finrank k ↥(signPart (σ c) (1 : k)) ∧ 0 < finrank k ↥(signPart (σ c) (-1 : k))) →
      1 < (stage c).fiberDim ρ →
      ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
        ∃ M : QuasiSingleStep ρ (stage c) (stage (Φ.next c p)) (σ (Φ.next c p)),
          M.X.SF.Dside = Φ.fibre c ∧ M.X.SS.Dside = Φ.fibre (Φ.next c p)) :
    HomologySwitchDataPK Φ ι ρ u :=
  HomologySwitchDataPK.ofFibreModels (fibreModels_of_concentrated Φ ρ stage hfin hconc h1 h2) hz0
    hw0 hu0 σ h2' hσ class_ne_zero switch_mixed switch_single

end Switch

/-! ### `hz0` and `hw0` through a model -/

section ClassFunctional

variable {A F : Type} [CommRing A] [Field F] {ι : A →+* F}

/-- PROVED. **A model is the identity on cocycles of the stage's fibre after a round trip**: for
every homotopy equivalence `e : C ≃ [k^{n+1} --D̄--> k^{n+1}]` and every `v` with `D̄ v = 0`,
`e.hom (e.inv v) = v` in degree one (the homotopy `inv ≫ hom ≃ 1` factors through `D̄` there, the
fibre being zero in degree zero). -/
theorem tmod_hom_inv_cocycle (ρ : A →+* k) (S : TwoTermStage ι)
    {C : CochainComplex (ModuleCat.{0} k) ℤ} (e : HomotopyEquiv C (twoTermFiberComplex ρ S))
    (v : (twoTermFiberComplex ρ S).X 1) (hv : ((twoTermFiberComplex ρ S).d 1 2).hom v = 0) :
    (e.hom.f 1).hom ((e.inv.f 1).hom v) = v := by
  have h := e.homotopyInvHomId.comm 1
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 1 2 from rfl),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel 0 1 from rfl)] at h
  have h' := congrArg (fun f => ModuleCat.Hom.hom f v) h
  have hd01 : (twoTermFiberComplex ρ S).d 0 1 = 0 :=
    (threeTermComplex_d_zero_one _ _ _).trans ModuleCat.ofHom_zero
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_add, LinearMap.add_apply, HomologicalComplex.id_f, ModuleCat.hom_id,
    LinearMap.id_apply, hv, map_zero, hd01, ModuleCat.hom_zero, LinearMap.zero_apply,
    zero_add] at h'
  exact h'

/-- PROVED. The reduction of the stage's cycle is a cycle of the fibre: `D̄ z̄ = 0`. -/
theorem tmod_reduce_cycle (ρ : A →+* k) (S : TwoTermStage ι) :
    (S.D.map ρ) *ᵥ (fun i => ρ (S.z i)) = 0 := by
  have h := S.hz
  ext i
  have hi := congrArg (fun x => ρ (x i)) h
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at hi
  simpa [Matrix.mulVec, dotProduct, Matrix.map_apply] using hi

/-- PROVED. The reduction of the stage's functional is closed: `w̄ D̄ = 0`. -/
theorem tmod_reduce_functional (ρ : A →+* k) (S : TwoTermStage ι) :
    (fun i => ρ (S.w i)) ᵥ* (S.D.map ρ) = 0 := by
  have h := S.hw
  ext i
  have hi := congrArg (fun x => ρ (x i)) h
  simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at hi
  simpa [Matrix.vecMul, dotProduct, Matrix.map_apply] using hi

/-- **A family re-anchored at a model** (tex 4986–4992: "the actual class `z`", "the paired
functional"): the same configurations and fibres, with the actual class `e⁻¹(z̄)` and the
functional `y ↦ w̄ · e(y)` transported from a stage `S` through a homotopy equivalence `e` of the
actual fibre with the fibre of `S`. Kind: definition (PROVED fields). -/
def tmodAnchor (Φ : SwitchFamily k A) (ρ : A →+* k) (S : TwoTermStage ι)
    (e : HomotopyEquiv (selCx (Φ.fibre Φ.actual)).toCC (twoTermFiberComplex ρ S)) :
    SwitchFamily k A where
  Config := Φ.Config
  Prime := Φ.Prime
  actual := Φ.actual
  next := Φ.next
  fibre := Φ.fibre
  t := Φ.t
  zAct := (e.inv.f 1).hom fun i => ρ (S.z i)
  hzAct := by
    have hv : (S.D.map ρ) *ᵥ (fun i => ρ (S.z i)) = 0 := tmod_reduce_cycle ρ S
    have h0 : ((twoTermFiberComplex ρ S).d 1 2).hom (fun i => ρ (S.z i)) = 0 := hv
    have := congrArg (fun f => ModuleCat.Hom.hom f (fun i => ρ (S.z i))) (e.inv.comm 1 2)
    simp only [ModuleCat.hom_comp] at this
    exact this.trans ((congrArg (fun x => (e.inv.f 2).hom x) h0).trans (map_zero _))
  lamAct :=
    { toFun := fun y => (fun i => ρ (S.w i)) ⬝ᵥ ((e.hom.f 2).hom y : Fin (S.n + 1) → k)
      map_add' := fun y y' => by
        rw [map_add]
        exact dotProduct_add _ _ _
      map_smul' := fun c y => by
        change (fun i => ρ (S.w i)) ⬝ᵥ ((e.hom.f 2).hom (c • y) : Fin (S.n + 1) → k) = _
        rw [map_smul]
        exact dotProduct_smul _ _ _ }
  hlamAct y := by
    change (fun i => ρ (S.w i)) ⬝ᵥ ((e.hom.f 2).hom
      (((selCx (Φ.fibre Φ.actual)).toCC.d 1 2).hom y) : Fin (S.n + 1) → k) = 0
    have := congrArg (fun f => ModuleCat.Hom.hom f y) (e.hom.comm 1 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    have h2 : ((e.hom.f 2).hom (((selCx (Φ.fibre Φ.actual)).toCC.d 1 2).hom y) :
        Fin (S.n + 1) → k) = (S.D.map ρ) *ᵥ ((e.hom.f 1).hom y : Fin (S.n + 1) → k) :=
      this.symm
    rw [h2]
    exact (Matrix.dotProduct_mulVec _ _ _).trans (by
      rw [tmod_reduce_functional ρ S]
      exact zero_dotProduct _)

/-- PROVED. **`hz0` holds for the re-anchored family**: the model sends its actual class to the
reduction of the stage's cycle. -/
theorem tmodAnchor_hz0 (Φ : SwitchFamily k A) (ρ : A →+* k) (S : TwoTermStage ι)
    (e : HomotopyEquiv (selCx (Φ.fibre Φ.actual)).toCC (twoTermFiberComplex ρ S)) :
    (e.hom.f 1).hom (tmodAnchor Φ ρ S e).zAct = fun i => ρ (S.z i) :=
  tmod_hom_inv_cocycle ρ S e _ (tmod_reduce_cycle ρ S)

/-- PROVED. **`hw0` holds for the re-anchored family** (by definition of its functional). -/
theorem tmodAnchor_hw0 (Φ : SwitchFamily k A) (ρ : A →+* k) (S : TwoTermStage ι)
    (e : HomotopyEquiv (selCx (Φ.fibre Φ.actual)).toCC (twoTermFiberComplex ρ S))
    (y : (selCx (Φ.fibre Φ.actual)).toCC.X 2) :
    (tmodAnchor Φ ρ S e).lamAct y = (fun i => ρ (S.w i)) ⬝ᵥ ((e.hom.f 2).hom y : Fin (S.n + 1) → k) :=
  rfl

end ClassFunctional

end ZInQ.Manuscript.RC.Wiring
