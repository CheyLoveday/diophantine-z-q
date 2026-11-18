import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineEq35Leaf
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchNonVacuity

/-!
**Theorem 5.3, Lane RC0 round 4: ties of the outer part of `Eq35InputsGenuineGG`**

The outer part of the new (3.5) leaf asks that every switched minimal model `model i l` of the fixed
family be a two-term model of genuine Galois Selmer data over `𝒪` (`IsGenuineInstanceModel`). This
file records what that asks of the genuine objects (PROVED):

* `integralTwoTerm_h1_nontrivial`: the two-term complex `[R^{n+1} --M--> R^{n+1}]` of a matrix with a
  nonzero kernel vector has nonzero `H¹`.
* `IsGenuineInstanceModel.h1_nontrivial`: a genuine instance model forces the genuine Galois Selmer
  complex over `𝒪` it models to have nonzero `H¹` (the actual class of the model is primitive, hence
  a nonzero cycle, and the homotopy equivalence identifies the cohomology).
* `zeroSelData_not_model`: the zero genuine Galois data over any coefficient ring (`K = ℚ`, `S = ∅`,
  `M = 0`) model no instance model: the pin cannot be met by trivial genuine data.
* `primRegularityInputsG_of_uPrim_zero`, `eq35InputsGenuineGG_of_not_prepared`: the new leaves are
  satisfiable (degenerate witnesses: vanishing coordinates; no ring instances).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 Module NumberField IsDedekindDomain CategoryTheory
  Matrix

open ZInQ.Contrib.CloudB3RC53.PairedFunctional (SelData selCx)
open ZInQ.Manuscript.RC.Determinant (OO)
open ZInQ.Manuscript.RC.SelmerComplex (GKS galoisSelData GaloisLocalConditions strictConditions)

/-- **The two-term complex of a matrix with a nonzero kernel vector has nonzero `H¹`**: degree zero
is `0`, so `H¹ = ker M`. Kind: PROVED. -/
theorem integralTwoTerm_h1_nontrivial {R : Type} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (z : Fin (n + 1) → R) (hz : M *ᵥ z = 0)
    (hz0 : z ≠ 0) : Nontrivial ((integralTwoTerm M).homology 1) := by
  set K := integralTwoTerm M
  have hd0 : K.d 0 1 = 0 := by
    change ModuleCat.ofHom (0 : PUnit.{1} →ₗ[R] (Fin (n + 1) → R)) = 0
    rfl
  let e := ((K.isoHomologyπ 0 1 (by simp) hd0).symm ≪≫ K.cyclesIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    (K.sc' 0 1 2).moduleCatCyclesIso).toLinearEquiv
  have hmem : z ∈ LinearMap.ker (K.sc' 0 1 2).g.hom := by
    change M.mulVecLin z = 0
    rw [Matrix.mulVecLin_apply]
    exact hz
  refine ⟨⟨e.symm ⟨z, hmem⟩, 0, fun h => hz0 ?_⟩⟩
  have h' : (⟨z, hmem⟩ : LinearMap.ker (K.sc' 0 1 2).g.hom) = 0 :=
    e.symm.injective (h.trans (map_zero e.symm).symm)
  exact congrArg Subtype.val h'

/-- **A genuine instance model forces nonzero genuine `H¹`**: the genuine Galois Selmer data over
`𝒪` modelled by an instance model have `H¹ ≠ 0` (the primitive actual class is a nonzero cycle of
the model). Kind: PROVED. -/
theorem IsGenuineInstanceModel.h1_nontrivial {n : ℕ}
    {X : SwitchInputs.InstanceModel (2 : OO) (FractionRing OO) n} (h : IsGenuineInstanceModel X) :
    ∃ D : SelData OO, IsGaloisSelData D ∧ Nontrivial ((selCx D).toCC.homology 1) := by
  obtain ⟨D, hD, ⟨e⟩⟩ := h
  have hz0 : X.zR ≠ 0 := by
    obtain ⟨i, hi⟩ := X.hprim
    intro h0
    exact hi (by rw [h0]; exact dvd_zero _)
  have := integralTwoTerm_h1_nontrivial X.M X.zR X.hz hz0
  exact ⟨D, hD, ((e.toHomologyIso 1).toLinearEquiv.toEquiv).nontrivial⟩

section Zero

variable (k : Type) [CommRing k]

/-- Scalar multiplication on the zero module is continuous. -/
instance continuousConstSMul_punit : ContinuousConstSMul k PUnit := ⟨fun _ => continuous_const⟩

/-- **The zero genuine Galois data over `k`**: `galoisSelData ℚ ∅ k 0 Δ` with strict conditions. -/
def zeroSelData : SelData k :=
  galoisSelData ℚ emptySupport k PUnit (strictConditions _ _ _ _ PUnit)

/-- The zero data are genuine Galois Selmer data. Kind: PROVED. -/
theorem zeroSelData_isGalois : IsGaloisSelData (zeroSelData k) :=
  ⟨ℚ, inferInstance, inferInstance, emptySupport, PUnit, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    strictConditions _ _ _ _ PUnit, Set.finite_empty,
    fun v => ((Set.mem_empty_iff_false _).mp v.2).elim, rfl⟩

/-- The degree-one term of the zero data's Selmer complex is zero. Kind: PROVED. -/
theorem zeroSelData_X1_subsingleton : Subsingleton ((selCx (zeroSelData k)).toCC.X 1) := by
  constructor
  intro a b
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  have h1 : a1 = b1 := by
    obtain ⟨f, hf⟩ := a1
    obtain ⟨g, hg⟩ := b1
    have hfg : f = g := by
      change ((Fin 1 → GKS ℚ emptySupport) → PUnit) at f g
      exact funext fun x => rfl
    subst hfg
    rfl
  have he : IsEmpty (ZInQ.Manuscript.RC.SelmerComplex.Places ℚ emptySupport) :=
    ⟨fun v => (Set.mem_empty_iff_false _).mp v.2⟩
  have h2 : a2 = b2 := by
    change (∀ v : ZInQ.Manuscript.RC.SelmerComplex.Places ℚ emptySupport, _) at a2 b2
    exact funext fun v => (he.false v).elim
  have h3 : a3 = b3 := by
    change (∀ v : ZInQ.Manuscript.RC.SelmerComplex.Places ℚ emptySupport, _) at a3 b3
    exact funext fun v => (he.false v).elim
  rw [h1, h2, h3]

end Zero

/-- **The zero genuine data model no instance model**: no homotopy equivalence from the Selmer
complex of the zero genuine Galois data over `𝒪` to the two-term complex of any instance model (its
`H¹` is zero, that of a model is not). Kind: PROVED. -/
theorem zeroSelData_not_model {n : ℕ} (X : SwitchInputs.InstanceModel (2 : OO) (FractionRing OO) n) :
    IsEmpty (HomotopyEquiv (selCx (zeroSelData OO)).toCC (integralTwoTerm X.M)) := by
  refine ⟨fun e => ?_⟩
  have hz0 : X.zR ≠ 0 := by
    obtain ⟨i, hi⟩ := X.hprim
    intro h0
    exact hi (by rw [h0]; exact dvd_zero _)
  have hn := integralTwoTerm_h1_nontrivial X.M X.zR X.hz hz0
  have hs := homology_subsingleton_of_X _ 1 (zeroSelData_X1_subsingleton OO)
  have hn' : Nontrivial ((selCx (zeroSelData OO)).toCC.homology 1) :=
    ((e.toHomologyIso 1).toLinearEquiv.toEquiv).nontrivial
  exact (not_nontrivial_iff_subsingleton.mpr hs) hn'

/-! **Satisfiability of the new leaves** -/

/-- The `t`-expansion of `0` is `0`. -/
theorem isTExpansion_zero : IsTExpansion 0 0 :=
  ⟨0, 1, one_ne_zero, by simp, by simp⟩

/-- **`PrimRegularityInputsG D` is satisfiable**: it holds (through its `u = 0` branch) whenever the
primitive coordinates vanish. Kind: PROVED. -/
theorem primRegularityInputsG_of_uPrim_zero {ℓ : ℕ} (D : RCData ℓ) (hD : ∀ F x, D.uPrim F x = 0) :
    PrimRegularityInputsG D :=
  fun _ _ F _ x => ⟨0, by rw [hD F x]; exact isTExpansion_zero, Or.inl rfl⟩

/-- **`Eq35InputsGenuineGG W` is satisfiable**: it holds when the prepared filter is empty (no ring
instances; the model family over the empty instance type). Kind: PROVED. -/
theorem eq35InputsGenuineGG_of_not_prepared {ℓ : ℕ} (W : WData ℓ) (hW : ∀ h, ¬ W.prepared h) :
    Eq35InputsGenuineGG W :=
  ⟨fun _ _ => 0, 0, fun h _ hp _ _ => (hW h hp).elim, fun h _ hp _ _ _ _ => (hW h hp).elim,
    Empty, ⟨fun _ => 0, fun i _ => (hW _ i.2.1).elim⟩, fun i _ => (hW _ i.2.1).elim,
    fun i => (hW _ i.2.1).elim, fun _ inst => (hW _ (inst 0).prepared).elim⟩

end ZInQ.Manuscript.RC.Wiring
