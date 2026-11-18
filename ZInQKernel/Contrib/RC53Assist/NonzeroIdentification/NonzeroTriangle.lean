import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.ActualOnePlace

/-!
# Nonzero coefficients for the full-condition triangle

The number field is `CyclotomicField 4 ℚ`. The old support consists of the
places above two, and one place above three is added. The family coefficient
module is the regular module over `MonoidAlgebra OO (SignGroup b)`, with
trivial Galois action and the discrete topology. The augmentation coefficient
module is `ZMod 2`, again with trivial Galois action.

The coefficient modules and every nonnegative global and local cochain term
are nonzero. The full local conditions, the finite coefficient setting, the
nonempty set of new places, the cancellation core, and the genuine short exact
sequence of triangle (5.6) are constructed without additional hypotheses.

This is a partial non-vacuity result, NOT an instance of `Identification3`.
The finite-model comparisons `ψf`, `ψ0`, `ψold`, the compatibility square, and
the tame comparison have not been constructed. In particular, the
subsingleton-cochain argument used for zero coefficients cannot be reused.

Locators: `diophantine_zq.tex`, triangle (5.6), lines 5234–5238; singular
quotients, lines 3479–3481; local blocks, lines 5455–5463;
`ClearingComplex/FullConditionIdentification.lean`, fields 220–297;
`ClearingComplex/FullConditionSelmer.lean`, lines 198–261.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.NonzeroIdentification

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup)
open ActualQEmpty (KA ρA)
open ActualOnePlace (S₂ S₂' hS₂ ψurB hψurB)

/-- Definition: the nonzero family coefficient module; triangle (5.6),
`FullConditionIdentification.lean`, fields 222–231. -/
abbrev FamilyCoefficient (b : ℕ) : Type :=
  TrivMod (GKS KA S₂') (MonoidAlgebra OO (SignGroup b))

/-- Definition: the nonzero finite augmentation coefficient module;
`FullConditionIdentification.lean`, fields 249–258. -/
abbrev AugmentationCoefficient : Type := TrivMod (GKS KA S₂) (ZMod 2)

/-- Definition: the discrete topology on the family coefficient module;
`FullConditionIdentification.lean`, field `Mf_top`. -/
instance familyCoefficient_topology (b : ℕ) : TopologicalSpace (FamilyCoefficient b) := ⊥

/-- Proved instance: the chosen family topology is discrete;
`FullConditionIdentification.lean`, field `Mf_top`. -/
instance familyCoefficient_discrete (b : ℕ) : DiscreteTopology (FamilyCoefficient b) := ⟨rfl⟩

/-- Proved instance: the trivial Galois action is jointly continuous;
`FullConditionIdentification.lean`, field `Mf_cact`. -/
instance familyCoefficient_continuousAction (b : ℕ) :
    ContinuousSMul (GKS KA S₂') (FamilyCoefficient b) where
  continuous_smul := continuous_snd

/-- Proved instance: the regular family coefficient module is nontrivial;
`FullConditionIdentification.lean`, field `Mf`. -/
instance familyCoefficient_nontrivial (b : ℕ) : Nontrivial (FamilyCoefficient b) :=
  inferInstanceAs (Nontrivial (MonoidAlgebra OO (SignGroup b)))

/-- Proved instance: the finite augmentation coefficient module is nontrivial;
`FullConditionIdentification.lean`, field `M₀`. -/
instance augmentationCoefficient_nontrivial : Nontrivial AugmentationCoefficient :=
  inferInstanceAs (Nontrivial (ZMod 2))

section Constant

variable {k G M : Type} [CommRing k] [Group G] [TopologicalSpace G]
  [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M]

/-- Definition: a coefficient as a constant continuous cochain in degree `n`;
`SelmerComplex/Cochains.lean`, lines 247–254. -/
def constantCochain (n : ℕ) : M →ₗ[k] contCochain k G M n where
  toFun m := ⟨fun _ => m, continuous_const⟩
  map_add' _ _ := Subtype.ext (funext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (funext fun _ => rfl)

/-- Proved: constant cochains retain the coefficient, by evaluation at the
identity tuple; `SelmerComplex/Cochains.lean`, lines 247–254. -/
theorem constantCochain_injective (n : ℕ) :
    Function.Injective (constantCochain (k := k) (G := G) (M := M) n) := by
  intro x y h
  exact congrFun (congrArg Subtype.val h) (fun _ => 1)

/-- Proved: a nonzero coefficient module has nonzero continuous cochain terms
in every nonnegative degree; `SelmerComplex/Cochains.lean`, lines 300–306. -/
theorem cochainTerm_nontrivial [Nontrivial M] [ContinuousMul G]
    [ContinuousSMul G M] (n : ℕ) : Nontrivial ((contCochains k G M).X n) := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne M
  exact ⟨⟨constantCochain (k := k) (G := G) n x,
    constantCochain (k := k) (G := G) n y,
    fun h => hxy (constantCochain_injective n h)⟩⟩

end Constant

/-- Definition: the full family local conditions on nonzero coefficients;
`SelmerComplex/Selmer.lean`, lines 478–480. -/
def familyConditions (b : ℕ) :
    GaloisLocalConditions KA S₂' (MonoidAlgebra OO (SignGroup b)) (FamilyCoefficient b) :=
  relaxedConditions _ _ _ _ _

/-- Definition: the full old local conditions on the nonzero finite module;
`FullConditionIdentification.lean`, field `Δ₀`, and `SelmerComplex/Selmer.lean`,
lines 478–480. -/
def augmentationConditions :
    GaloisLocalConditions KA S₂ (ZMod 2) AugmentationCoefficient :=
  relaxedConditions _ _ _ _ _

/-- Proved: the family conditions are full at every new place, with an actual
identity map on nonzero cochain terms; `FullConditionIdentification.lean`,
lines 384–394. -/
theorem familyConditions_full (b : ℕ) :
    ∀ v : Places KA S₂', v.1 ∉ S₂ → ∀ n : ℤ,
      Function.Bijective (((familyConditions b).i v).f n n rfl) :=
  hfull_relaxed S₂ S₂' (MonoidAlgebra OO (SignGroup b)) (FamilyCoefficient b)

/-- Proved: every nonnegative global family cochain term is nonzero;
`SelmerComplex/Selmer.lean`, lines 274–275, and (5.6). -/
theorem family_global_nontrivial (b n : ℕ) :
    Nontrivial ((galoisSelData KA S₂' _ (FamilyCoefficient b)
      (familyConditions b)).G.X (n : ℤ)) :=
  cochainTerm_nontrivial n

/-- Proved: every nonnegative local family cochain term is nonzero;
`SelmerComplex/Selmer.lean`, lines 277–278, and (5.6). -/
theorem family_local_nontrivial (b n : ℕ) (v : Places KA S₂') :
    Nontrivial ((localCx (MonoidAlgebra OO (SignGroup b)) (GKS KA S₂')
      (fun w : Places KA S₂' => Gloc KA w.1) (fun w => locMap KA S₂' w.1)
      (FamilyCoefficient b) v).X (n : ℤ)) := by
  have : Nontrivial (ResMod (locMap KA S₂' v.1) (FamilyCoefficient b)) :=
    inferInstanceAs (Nontrivial (FamilyCoefficient b))
  exact cochainTerm_nontrivial n

/-- Proved: the full-condition global augmentation cochains are nonzero in
all nonnegative degrees; `FullConditionSelmer.lean`, lines 198–204. -/
theorem augmentation_global_nontrivial (n : ℕ) :
    Nontrivial ((galoisFullData KA hS₂ (ZMod 2) AugmentationCoefficient
      augmentationConditions).G.X (n : ℤ)) := by
  have : Nontrivial (ResMod (inflMap KA hS₂) AugmentationCoefficient) :=
    inferInstanceAs (Nontrivial AugmentationCoefficient)
  exact cochainTerm_nontrivial n

/-- Proved: the degreewise-zero global premise of the zero-coefficient
construction is false for this nonzero family module;
`ClearingComplex/ActualZero.lean`, lines 45–59. -/
theorem family_not_degreewise_zero (b : ℕ) :
    ¬ ∀ n : ℤ, Subsingleton ((galoisSelData KA S₂' _ (FamilyCoefficient b)
      (familyConditions b)).G.X n) := by
  intro hall
  have := family_global_nontrivial b 0
  obtain ⟨x, y, hxy⟩ := exists_pair_ne
    ((galoisSelData KA S₂' _ (FamilyCoefficient b) (familyConditions b)).G.X 0)
  exact hxy ((hall 0).elim x y)

/-- Proved: the degreewise-zero global premise also fails for the nonzero
augmentation module; `ClearingComplex/ActualZero.lean`, lines 45–59. -/
theorem augmentation_not_degreewise_zero :
    ¬ ∀ n : ℤ, Subsingleton ((galoisFullData KA hS₂ (ZMod 2) AugmentationCoefficient
      augmentationConditions).G.X n) := by
  intro hall
  have := augmentation_global_nontrivial 0
  obtain ⟨x, y, hxy⟩ := exists_pair_ne
    ((galoisFullData KA hS₂ (ZMod 2) AugmentationCoefficient augmentationConditions).G.X 0)
  exact hxy ((hall 0).elim x y)

/-- Proved: triangle (5.6) is short exact on the genuine nonzero finite
coefficient module; `FullConditionSelmer.lean`, lines 252–261. -/
theorem nonzero_full_triangle :
    (galoisFullSES KA hS₂ (ZMod 2) AugmentationCoefficient ψurB hψurB
      augmentationConditions).ShortExact :=
  galoisFullSES_shortExact KA hS₂ (ZMod 2) AugmentationCoefficient ψurB hψurB
    augmentationConditions

/-- Proved: the cancellation core, two nonzero coefficient modules, the
finite setting, a nonempty new-place set, and the genuine full-condition
triangle coexist. This does not assert the finite-model identifications;
`FullConditionIdentification.lean`, fields 220–297. -/
theorem nonzero_data_witness (b : ℕ) :
    Nonempty (FullCore (NewPlaces KA S₂ S₂') b 0 0 0 0) ∧
    Nontrivial (FamilyCoefficient b) ∧ Nontrivial AugmentationCoefficient ∧
    NekovarFiniteSetting KA S₂ 2 (ZMod 2) ∧ Nonempty (NewPlaces KA S₂ S₂') ∧
    (galoisFullSES KA hS₂ (ZMod 2) AugmentationCoefficient ψurB hψurB
      augmentationConditions).ShortExact :=
  ⟨⟨fullCoreEx b (NewPlaces KA S₂ S₂')⟩, inferInstance, inferInstance,
    ActualOnePlace.hsetB, ActualOnePlace.nonempty_new, nonzero_full_triangle⟩

end ZInQ.Contrib.RC53Assist.NonzeroIdentification
