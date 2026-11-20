import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchHModel

/-!
**Theorem 5.3: the switch models of `HomologySwitchDataPK` from finite models of the fibres**

Lemma `ex:limits-inner-limit` (tex 4391–4451) in the field case, and the two-term models of the
height-one switching argument (Proposition `ex:limits-uniform-lower-bound`, tex 4976–4996).

**What a two-term model needs.** A complex `C` of `k`-vector spaces is homotopy equivalent to the
fibre `[k^{n+1} --D̄--> k^{n+1}]` of a stage of fibre dimension `s` if and only if its cohomology is
finite-dimensional, concentrated in degrees one and two, with `dim H¹ = dim H² = s`. Necessity of
`dim H¹ = s` and of the vanishing outside degrees `0, 1, 2`: `tmod_h1_of_equiv`,
`tmod_homology_zero_of_equiv`. Sufficiency: a graded finite free model of `C` with zero differential
(lane RC31's `GradedModel`, whose ranks are the cohomology dimensions) gives
`tmodOfModel : C ≃ [k^s --0--> k^s]`, and then `tmodStageOfModel : C ≃ twoTermFiberComplex ρ S` for
every stage `S` of fibre dimension `s` (`tmodNormal`, `GenuineSwitchHModel.lean`). Such a model
exists over a field by lane RC29's field splitting (`FieldSplitting.lean`, the field case of RC31's
`exists_gradedModel`, where the residual cohomology is the cohomology and the perturbation `ε`
vanishes).

**The `model` field of `HomologySwitchDataPK`.** `HomologySwitchDataPK.ofGradedModels` builds the
switching data from graded finite free models of the configurations' fibres with zero differential
and cohomology concentrated in degrees one and two of equal dimension, the stages' fibre dimensions
being the `H¹`-dimensions: the field `model` is then DERIVED (`tmodStageOfModel`), not an input.
The fields that remain inputs: `hz0`, `hw0` (they tie the actual class and functional of the family
to the starting stage's cycle and functional THROUGH the derived model), `hu0`, the signs `σ`, `h2`,
`hσ`, `class_ne_zero` and the two switch fields; and the stages themselves (their integral matrix,
cycle, functional and coordinate over `A`), which a model over the residue field does not supply:
the integral finite free model over `R = Λ_𝔭` with these reductions is the inner-limit construction
(tex 4391–4451 over the Artin quotients, then the limit), not formalized here.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory CategoryTheory.Limits Module Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SwitchInputs
  ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Manuscript.RC.Limits (GradedModel matCx subquotientOf)

variable {k : Type} [Field k]

/-! ### Cohomology as cocycles modulo coboundaries -/

/-- Subquotients along equal maps. Kind: definition. -/
def tmodSubqCongr {V W Z : Type} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [AddCommGroup Z] [Module k Z] {f f' : V →ₗ[k] W} {g g' : W →ₗ[k] Z} (hf : f = f')
    (hg : g = g') : subquotientOf f g ≃ₗ[k] subquotientOf f' g' := by
  subst hf hg
  exact LinearEquiv.refl k _

/-- **The cohomology of a relation-indexed complex is its cocycles modulo coboundaries** (as a
linear equivalence; the finiteness form is lane RC31's `moduleFinite_homology_iff`). Kind:
definition. -/
def tmodHomologyEquiv (C : GCx k) (n : ℤ) :
    C.toCC.homology n ≃ₗ[k] subquotientOf (C.d (n - 1) n (by omega)) (C.d n (n + 1) rfl) := by
  have e := C.toCC.homologyIsoSc' (n - 1) n (n + 1) (CochainComplex.prev ℤ n)
    (CochainComplex.next ℤ n)
  have hr : LinearMap.range (C.toCC.sc' (n - 1) n (n + 1)).moduleCatToCycles =
      (LinearMap.range (C.toCC.sc' (n - 1) n (n + 1)).f.hom).comap
        (LinearMap.ker (C.toCC.sc' (n - 1) n (n + 1)).g.hom).subtype :=
    LinearMap.range_codRestrict _ _ _
  have hf : (C.toCC.sc' (n - 1) n (n + 1)).f.hom = C.d (n - 1) n (by omega) :=
    LinearMap.ext fun x => GCx.toCC_d_hom C (n - 1) n (by omega) x
  have hg : (C.toCC.sc' (n - 1) n (n + 1)).g.hom = C.d n (n + 1) rfl :=
    LinearMap.ext fun x => GCx.toCC_d_hom C n (n + 1) rfl x
  exact ((e.toLinearEquiv.trans
    (C.toCC.sc' (n - 1) n (n + 1)).moduleCatHomologyIso.toLinearEquiv).trans
      (Submodule.quotEquivOfEq _ _ hr)).trans (tmodSubqCongr hf hg)

/-! ### Necessity -/

/-- PROVED. **A complex homotopy equivalent to the fibre of a stage has `dim H¹ = s`**, the stage's
fibre dimension. -/
theorem tmod_h1_of_equiv {A F : Type} [CommRing A] [Field F] {ι : A →+* F} (ρ : A →+* k)
    (S : TwoTermStage ι) {C : CochainComplex (ModuleCat.{0} k) ℤ}
    (e : HomotopyEquiv C (twoTermFiberComplex ρ S)) :
    finrank k (C.homology 1) = S.fiberDim ρ := by
  rw [← finrank_h1_twoTermFiberComplex ρ S]
  exact ((e.toHomologyIso 1).toLinearEquiv).finrank_eq

/-- PROVED. **A complex homotopy equivalent to a square two-term complex has no cohomology outside
degrees one and two** (the objects of the two-term complex vanish in degree zero and outside
`0, 1, 2`). -/
theorem tmod_homology_zero_of_equiv {m : ℕ} (D : Matrix (Fin m) (Fin m) k)
    {C : CochainComplex (ModuleCat.{0} k) ℤ} (e : HomotopyEquiv C (tmodCx D)) (n : ℤ)
    (h1 : n ≠ 1) (h2 : n ≠ 2) : finrank k (C.homology n) = 0 := by
  have hX : Subsingleton ((tmodCx D).X n) := by
    by_cases h0 : n = 0
    · subst h0
      exact (inferInstance : Subsingleton PUnit)
    · exact threeTermX_subsingleton n h0 h1 h2
  have hZ : IsZero ((tmodCx D).X n) := ModuleCat.isZero_of_subsingleton _
  have hH : IsZero ((tmodCx D).homology n) :=
    ShortComplex.isZero_homology_of_isZero_X₂ ((tmodCx D).sc n) hZ
  have := ((e.toHomologyIso n).toLinearEquiv).finrank_eq
  rw [this]
  have : Subsingleton ((tmodCx D).homology n) := ModuleCat.subsingleton_of_isZero hH
  exact Module.finrank_zero_of_subsingleton


/-- PROVED. **`dim H²` of a square two-term complex is `dim ker D`** (`H² = coker D`, rank–nullity). -/
theorem tmod_finrank_h2 {m : ℕ} (D : Matrix (Fin m) (Fin m) k) :
    finrank k ((tmodCx D).homology 2) = finrank k (LinearMap.ker D.mulVecLin) := by
  set K := tmodCx D
  have hd23 : K.d 2 3 = 0 :=
    threeTermD_eq_zero (0 : PUnit.{1} →ₗ[k] (Fin m → k)) D.mulVecLin 2 3
      (fun h => absurd h.1 (by decide)) (fun h => absurd h.1 (by decide))
  have e1 := K.isoHomologyι 2 3 (by simp) hd23
  have e2 := K.opcyclesIsoSc' 1 2 3 (by simp) (by simp)
  have e3 := (K.sc' 1 2 3).moduleCatOpcyclesIso
  rw [((e1 ≪≫ e2 ≪≫ e3).toLinearEquiv).finrank_eq]
  change finrank k ((Fin m → k) ⧸ LinearMap.range D.mulVecLin) = _
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range D.mulVecLin)
  have hrn := LinearMap.finrank_range_add_finrank_ker D.mulVecLin
  omega

/-- PROVED. **A complex homotopy equivalent to the fibre of a stage has `dim H² = s`**, the stage's
fibre dimension. -/
theorem tmod_h2_of_equiv {A F : Type} [CommRing A] [Field F] {ι : A →+* F} (ρ : A →+* k)
    (S : TwoTermStage ι) {C : CochainComplex (ModuleCat.{0} k) ℤ}
    (e : HomotopyEquiv C (twoTermFiberComplex ρ S)) :
    finrank k (C.homology 2) = S.fiberDim ρ :=
  (((e.toHomologyIso 2).toLinearEquiv).finrank_eq).trans (tmod_finrank_h2 (S.D.map ρ))

/-! ### Sufficiency, from a graded finite free model with zero differential -/

omit [Field k] in
/-- PROVED. `matCx` along equal differentials. -/
theorem tmod_matCx_congr {k : Type} [Field k] (r : ℤ → ℕ)
    {dC dC' : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (r b)) (Fin (r a)) k} (h : dC = dC')
    (hsq : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c), dC b c hbc * dC a b hab = 0)
    (hsq' : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c), dC' b c hbc * dC' a b hab = 0) :
    matCx r dC hsq = matCx r dC' hsq' := by
  subst h
  rfl

/-- **A complex with a graded finite free model with zero differential, of ranks concentrated in
degrees one and two and equal there, is homotopy equivalent to `[k^s --0--> k^s]`.** Kind:
definition (PROVED). -/
def tmodOfModel (X : GCx k) (R : GradedModel X) (hdC : ∀ a b h, R.dC a b h = 0) {s : ℕ}
    (h0 : ∀ n, n ≠ 1 → n ≠ 2 → R.rank n = 0) (h1 : R.rank 1 = s) (h2 : R.rank 2 = s) :
    HomotopyEquiv X.toCC (tmodCx (0 : Matrix (Fin s) (Fin s) k)) :=
  have hz : R.dC = fun a b _ => (0 : Matrix (Fin (R.rank b)) (Fin (R.rank a)) k) :=
    funext fun a => funext fun b => funext fun h => hdC a b h
  have hsq0 : ∀ a b c (_ : a + 1 = b) (_ : b + 1 = c),
      (0 : Matrix (Fin (R.rank c)) (Fin (R.rank b)) k) *
        (0 : Matrix (Fin (R.rank b)) (Fin (R.rank a)) k) = 0 :=
    fun _ _ _ _ _ => Matrix.zero_mul _
  (R.retract.homotopyEquiv.symm.trans (HomotopyEquiv.ofIso
    (eqToIso (congrArg GCx.toCC (tmod_matCx_congr R.rank hz R.dC_sq hsq0))))).trans
    (tmodMatEquiv R.rank hsq0 h0 h1 h2)

/-- **The stage model from a graded finite free model** (tex 4976–4996): for every stage `S` whose
fibre dimension is the common rank `s` of the model in degrees one and two, `X ≃ [k^{n+1} --D̄-->
k^{n+1}]`. Kind: definition (PROVED). -/
def tmodStageOfModel {A F : Type} [CommRing A] [Field F] {ι : A →+* F} (ρ : A →+* k)
    (X : GCx k) (R : GradedModel X) (hdC : ∀ a b h, R.dC a b h = 0)
    (h0 : ∀ n, n ≠ 1 → n ≠ 2 → R.rank n = 0) (S : TwoTermStage ι) (h1 : R.rank 1 = S.fiberDim ρ)
    (h2 : R.rank 2 = S.fiberDim ρ) : HomotopyEquiv X.toCC (twoTermFiberComplex ρ S) :=
  (tmodOfModel X R hdC h0 h1 h2).trans (tmodNormal (S.D.map ρ))

/-! ### The `model` field of the homology-level switching data -/

section Switch

variable {A F : Type} [CommRing A] [Field F]

/-- **Graded finite free models of the configurations' fibres, adapted to stages** (tex
4976–4996, 4391–4451): for every configuration a graded finite free model of its fibre's Selmer
complex with zero differential, ranks concentrated in degrees one and two and both equal to the
stage's fibre dimension. Kind: definition (data). -/
structure FibreModels (Φ : SwitchFamily k A) {ι : A →+* F} (ρ : A →+* k)
    (stage : Φ.Config → TwoTermStage ι) where
  /-- The graded model of every fibre. -/
  R : ∀ c, GradedModel (selCx (Φ.fibre c))
  /-- Zero differential. -/
  hdC : ∀ c a b h, (R c).dC a b h = 0
  /-- Ranks vanish outside degrees one and two. -/
  h0 : ∀ c n, n ≠ 1 → n ≠ 2 → (R c).rank n = 0
  /-- The rank in degree one is the stage's fibre dimension. -/
  h1 : ∀ c, (R c).rank 1 = (stage c).fiberDim ρ
  /-- The rank in degree two is the stage's fibre dimension. -/
  h2 : ∀ c, (R c).rank 2 = (stage c).fiberDim ρ

variable {Φ : SwitchFamily k A} {ι : A →+* F} {ρ : A →+* k} {stage : Φ.Config → TwoTermStage ι}

/-- **The switch model derived from the fibre models**: the homotopy equivalence of every
configuration's fibre with the fibre of its stage. Kind: definition (PROVED). -/
def FibreModels.model (M : FibreModels Φ ρ stage) (c : Φ.Config) :
    HomotopyEquiv (selCx (Φ.fibre c)).toCC (twoTermFiberComplex ρ (stage c)) :=
  tmodStageOfModel ρ _ (M.R c) (M.hdC c) (M.h0 c) (stage c) (M.h1 c) (M.h2 c)

/-- **The homology-level switching data with the derived model** (tex 4976–5195): from fibre
models adapted to the stages, the field `model` of `HomologySwitchDataPK` is `M.model`; the
remaining fields are the inputs listed (`hz0` and `hw0` through the derived model). Kind:
definition. -/
def HomologySwitchDataPK.ofFibreModels {u : F} (M : FibreModels Φ ρ stage)
    (hz0 : ((M.model Φ.actual).hom.f 1).hom Φ.zAct = fun i => ρ ((stage Φ.actual).z i))
    (hw0 : ∀ y, Φ.lamAct y =
      (fun i => ρ ((stage Φ.actual).w i)) ⬝ᵥ (((M.model Φ.actual).hom.f 2).hom y : Fin _ → k))
    (hu0 : (stage Φ.actual).u = u)
    (σ : ∀ c, fiberH1 ρ (stage c) →ₗ[k] fiberH1 ρ (stage c))
    (h2 : Φ.quadratic ρ → (2 : k) ≠ 0)
    (hσ : Φ.quadratic ρ → ∀ c, σ c ∘ₗ σ c = LinearMap.id)
    (class_ne_zero : ∀ c, Reach Φ.next Φ.actual c → ∃ i, (stage c).z i ≠ 0)
    (switch_mixed : ∀ c, Reach Φ.next Φ.actual c → (¬ Φ.quadratic ρ ∨
      (0 < finrank k ↥(signPart (σ c) (1 : k)) ∧
        0 < finrank k ↥(signPart (σ c) (-1 : k)))) →
      1 < (stage c).fiberDim ρ →
      ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
        (Φ.quadratic ρ → ∃ M : QuasiMixedStep ρ (stage c) (stage (Φ.next c p)) (σ c)
            (σ (Φ.next c p)), M.X.SF.Dside = Φ.fibre c ∧ M.X.SS.Dside = Φ.fibre (Φ.next c p)) ∧
        (¬ Φ.quadratic ρ → ∃ N : QuasiNonquadStep ρ (stage c) (stage (Φ.next c p)),
            N.SF.Dside = Φ.fibre c ∧ N.SS.Dside = Φ.fibre (Φ.next c p)))
    (switch_single : ∀ c, Reach Φ.next Φ.actual c → Φ.quadratic ρ →
      ¬ (0 < finrank k ↥(signPart (σ c) (1 : k)) ∧
        0 < finrank k ↥(signPart (σ c) (-1 : k))) →
      1 < (stage c).fiberDim ρ →
      ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
        ∃ M : QuasiSingleStep ρ (stage c) (stage (Φ.next c p)) (σ (Φ.next c p)),
          M.X.SF.Dside = Φ.fibre c ∧ M.X.SS.Dside = Φ.fibre (Φ.next c p)) :
    HomologySwitchDataPK Φ ι ρ u where
  stage := stage
  model := M.model
  hz0 := hz0
  hw0 := hw0
  hu0 := hu0
  σ := σ
  h2 := h2
  hσ := hσ
  class_ne_zero := class_ne_zero
  switch_mixed := switch_mixed
  switch_single := switch_single

/-- PROVED. **The fibre models force the cohomology of every fibre**: `dim H¹(fibre c) = s(c)`,
the stage's fibre dimension (through the derived model). -/
theorem FibreModels.finrank_h1 (M : FibreModels Φ ρ stage) (c : Φ.Config) :
    finrank k ((selCx (Φ.fibre c)).toCC.homology 1) = (stage c).fiberDim ρ :=
  tmod_h1_of_equiv ρ (stage c) (M.model c)

end Switch

end ZInQ.Manuscript.RC.Wiring
