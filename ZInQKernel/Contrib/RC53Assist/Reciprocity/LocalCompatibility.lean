import ZInQKernel.Contrib.RC53Assist.HswResidual.Residual
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Weil
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.UnramifiedFactorization
import ZInQKernel.Contrib.CloudB3RC53.TameModel.UnramifiedQIso
import ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.ClassFieldTheory.Global.Brauer.SumFormula

/-!
# Square roots of unity and the localization embedding

The coefficient identifications below are identifications of actual roots of unity.
They are normalized by the unique nonidentity square root, namely minus one.
The embedding of separable closures is obtained from the embedding of algebraic
closures defining the localization homomorphism. No compatibility of localization
on cohomology is assumed.
-/

set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.Reciprocity

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory
open ZInQ.Contrib.RC53Assist.HswResidual

section Roots

variable {F L : Type} [Field F] [Field L]

/-- An additive identification with the square roots of unity sends one to minus one. -/
theorem twoRoots_one (e : ZMod 2 ≃+ Additive (rootsOfUnity 2 F)) :
    ((e 1).toMul : Fˣ) = -1 := by
  have hne : (e 1).toMul ≠ 1 := by
    intro h
    have hzero : e 1 = 0 := Additive.toMul.injective h
    have h10 : (1 : ZMod 2) = 0 := e.injective (hzero.trans (map_zero e).symm)
    exact one_ne_zero h10
  have hsq : (((e 1).toMul : Fˣ) : F) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp (e 1).toMul.2, Units.val_one]
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact False.elim (hne (Subtype.ext (Units.ext h)))
  · exact Units.ext h

/-- Every additive identification with the square roots is compatible with a field embedding. -/
theorem twoRoots_naturality (f : F →+* L)
    (eF : ZMod 2 ≃+ Additive (rootsOfUnity 2 F))
    (eL : ZMod 2 ≃+ Additive (rootsOfUnity 2 L)) (t : ZMod 2) :
    (restrictRootsOfUnity f 2).toAdditive (eF t) = eL t := by
  fin_cases t
  · change (restrictRootsOfUnity f 2).toAdditive (eF 0) = eL 0
    simp only [map_zero]
  · apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    change f ((((eF 1).toMul : Fˣ) : F)) = (((eL 1).toMul : Lˣ) : L)
    rw [twoRoots_one, twoRoots_one]
    simp only [Units.val_neg, Units.val_one, map_neg, map_one]

/-- The square-root dictionary is independent of the choice of additive equivalence. -/
theorem twoRoots_unique (e e' : ZMod 2 ≃+ Additive (rootsOfUnity 2 F)) : e = e' := by
  apply AddEquiv.ext
  intro t
  have h := twoRoots_naturality (RingHom.id F) e e' t
  have hid : (restrictRootsOfUnity (RingHom.id F) 2).toAdditive (e t) = e t := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    rfl
  exact hid.symm.trans h

end Roots

section CoefficientNaturality

variable {K L M : Type} [Field K] [Field L] [Algebra K L] [AddCommGroup M]

/-- A roots inclusion commutes with the local coefficient inclusion through every field embedding. -/
theorem localCoefficient_square (τ : SeparableClosure K →ₐ[K] SeparableClosure L)
    (d : ZMod 2 ≃+ M) (ι : M →+ UnitsCoeff K)
    (hι : (ι (d 1)).toMul = -1) (e : ZMod 2 ≃+ KummerCoeff L 2) (t : ZMod 2) :
    unitsCoeffBaseChange τ (ι (d t)) = kummerCoeffIncl L 2 (e t) := by
  fin_cases t
  · change unitsCoeffBaseChange τ (ι (d 0)) = kummerCoeffIncl L 2 (e 0)
    simp only [map_zero]
  · change unitsCoeffBaseChange τ (ι (d 1)) = kummerCoeffIncl L 2 (e 1)
    apply Additive.toMul.injective
    rw [toMul_unitsCoeffBaseChange, hι, toMul_kummerCoeffIncl, twoRoots_one]
    apply Units.ext
    change τ (-1 : SeparableClosure K) = (-1 : SeparableClosure L)
    exact (map_neg τ (1 : SeparableClosure K)).trans (congrArg Neg.neg (map_one τ))

end CoefficientNaturality

section CoefficientDictionary

variable (K : Type) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K)))

/-- An actual coefficient module of square roots, including its Galois action. -/
structure SquareRootCoefficients (M : Type) [AddCommGroup M]
    [DistribMulAction (GKS K S) M] where
  roots : M ≃+ Additive (rootsOfUnity 2 (KS K S))
  equivariant : ∀ (g : GKS K S) (m : M),
    roots (g • m) = (restrictRootsOfUnity (galS K S g) 2).toAdditive (roots m)

/-- The trivial two-element module as the actual square roots of unity of the global extension. -/
def squareRootCoordinates :
    TrivMod (GKS K S) (ZMod 2) ≃+ Additive (rootsOfUnity 2 (KS K S)) := by
  have h : IsPrimitiveRoot (-1 : (KS K S)ˣ) 2 := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    change IsPrimitiveRoot (-1 : KS K S) 2
    exact IsPrimitiveRoot.neg_one 0 (by norm_num)
  exact h.zmodEquivRootsOfUnity

/-- The coordinate dictionary agrees with every additive identification of these square roots. -/
theorem squareRootCoordinates_unique
    (e : TrivMod (GKS K S) (ZMod 2) ≃+ Additive (rootsOfUnity 2 (KS K S))) :
    squareRootCoordinates K S = e := twoRoots_unique _ _

/-- The coordinate dictionary is equivariant for the genuine action on roots. -/
theorem squareRootCoordinates_smul (g : GKS K S) (t : TrivMod (GKS K S) (ZMod 2)) :
    squareRootCoordinates K S (g • t) =
      (restrictRootsOfUnity (galS K S g) 2).toAdditive (squareRootCoordinates K S t) :=
  (twoRoots_naturality (galS K S g).toRingHom
    (squareRootCoordinates K S) (squareRootCoordinates K S) t).symm

variable {M : Type} [AddCommGroup M] [DistribMulAction (GKS K S) M]
  (D : SquareRootCoefficients K S M)

/-- The coefficient dictionary to an actual square-root coefficient module. -/
def muTwoDictionary : TrivMod (GKS K S) (ZMod 2) ≃+ M :=
  (squareRootCoordinates K S).trans D.roots.symm

/-- The dictionary identifies the underlying roots, not merely their abstract group names. -/
theorem muTwoDictionary_roots (t : TrivMod (GKS K S) (ZMod 2)) :
    D.roots (muTwoDictionary K S D t) = squareRootCoordinates K S t :=
  D.roots.apply_symm_apply _

/-- The nonzero residual coefficient is the genuine root minus one. -/
theorem muTwoDictionary_one :
    ((D.roots (muTwoDictionary K S D (show TrivMod (GKS K S) (ZMod 2) from (1 : ZMod 2)))).toMul :
      (KS K S)ˣ) = -1 := by
  rw [muTwoDictionary_roots]
  exact twoRoots_one (squareRootCoordinates K S)

/-- The genuine coefficient dictionary is Galois-equivariant. -/
theorem muTwoDictionary_smul (g : GKS K S) (t : TrivMod (GKS K S) (ZMod 2)) :
    muTwoDictionary K S D (g • t) = g • muTwoDictionary K S D t := by
  apply D.roots.injective
  rw [D.equivariant, muTwoDictionary_roots, muTwoDictionary_roots,
    squareRootCoordinates_smul]

variable [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]

/-- The actual coefficient dictionary induces the corresponding degree-two cohomology equivalence. -/
def muTwoH2Dictionary :
    H2 (GKS K S) (TrivMod (GKS K S) (ZMod 2)) ≃+ H2 (GKS K S) M :=
  explicitCoeff2Equiv (GKS K S) (TrivMod (GKS K S) (ZMod 2)) (muTwoDictionary K S D)
    continuous_of_discreteTopology continuous_of_discreteTopology (muTwoDictionary_smul K S D)

end CoefficientDictionary

section Embeddings

variable (K : Type) [Field K] [NumberField K]

/-- The embedding of separable closures inducing the given finite-place localization. -/
def decompSeparableEmbedding (v : HeightOneSpectrum (𝓞 K)) :
    SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K) where
  toRingHom :=
    { toFun := fun x => ⟨decompLift K v x.1,
        mem_separableClosure_iff.mpr (Algebra.IsSeparable.isSeparable (v.adicCompletion K) _)⟩
      map_one' := Subtype.ext (map_one (decompLift K v))
      map_mul' := fun x y => Subtype.ext (map_mul (decompLift K v) x.1 y.1)
      map_zero' := Subtype.ext (map_zero (decompLift K v))
      map_add' := fun x y => Subtype.ext (map_add (decompLift K v) x.1 y.1) }
  commutes' c := by
    apply Subtype.ext
    change decompLift K v (algebraMap K (AlgebraicClosure K) c) =
      algebraMap K (AlgebraicClosure (v.adicCompletion K)) c
    exact decompLift_algebraMap K v c

/-- The separable-closure embedding is the restriction of the chosen algebraic-closure embedding. -/
theorem decompSeparableEmbedding_coe (v : HeightOneSpectrum (𝓞 K)) (x : SeparableClosure K) :
    (decompSeparableEmbedding K v x : AlgebraicClosure (v.adicCompletion K)) =
      decompLift K v (x : AlgebraicClosure K) := rfl

/-- The decomposition homomorphism agrees in the algebraic and separable closure descriptions. -/
theorem decompSeparableEmbedding_galois (v : HeightOneSpectrum (𝓞 K))
    (g : Field.absoluteGaloisGroup (v.adicCompletion K)) :
    absoluteGaloisGroupMap (decompSeparableEmbedding K v)
        (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K) g) =
      absoluteGaloisGroupRestrictEquiv K (decompMap K v g) := by
  apply (absoluteGaloisGroupMap_eq_iff (decompSeparableEmbedding K v)).mpr
  intro x
  apply Subtype.ext
  calc
    _ = @id (Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) g
        (decompSeparableEmbedding K v x : AlgebraicClosure (v.adicCompletion K)) :=
      coe_absoluteGaloisGroupRestrictEquiv_apply (v.adicCompletion K)
        (@id (Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) g) _
    _ = decompLift K v (@id (Gal(AlgebraicClosure K/K)) (decompMap K v g) x.1) :=
      (decompLift_decompMap K v g x.1).symm
    _ = _ := congrArg (decompLift K v)
      (coe_absoluteGaloisGroupRestrictEquiv_apply K
        (@id (Gal(AlgebraicClosure K/K)) (decompMap K v g)) x).symm

/-- Localization is restriction after the compatible separable-closure decomposition map. -/
theorem locMap_via_separable (S : Set (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) (g : AbsoluteGaloisGroup (v.adicCompletion K)) :
    resAbsCont K S ((absoluteGaloisGroupRestrictEquiv K).symm
      (absoluteGaloisGroupMap (decompSeparableEmbedding K v) g)) =
        locMap K S v ((absoluteGaloisGroupRestrictEquiv (v.adicCompletion K)).symm g) := by
  have h := decompSeparableEmbedding_galois K v
    ((absoluteGaloisGroupRestrictEquiv (v.adicCompletion K)).symm g)
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  rw [h, ContinuousMulEquiv.symm_apply_apply]
  rfl

end Embeddings

section LocalSquare

variable (K : Type) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K)))

/-- Degree-two localization of the actual continuous cochains with residual coefficients. -/
def localizeMuTwoH2 (v : HeightOneSpectrum (𝓞 K)) :
    H2 (GKS K S) (TrivMod (GKS K S) (ZMod 2)) →+
      H2 (Gloc K v) (ResMod (locMap K S v) (TrivMod (GKS K S) (ZMod 2))) :=
  explicitMap2 (GKS K S) (TrivMod (GKS K S) (ZMod 2)) (Gloc K v)
    (ResMod (locMap K S v) (TrivMod (GKS K S) (ZMod 2))) (locMap K S v)
    (toResMod (k := ZMod 2) (M := TrivMod (GKS K S) (ZMod 2)) (locMap K S v)).toAddMonoidHom
    (continuous_toResMod (k := ZMod 2) (M := TrivMod (GKS K S) (ZMod 2)) (locMap K S v))
    (toResMod_compat (k := ZMod 2) (M := TrivMod (GKS K S) (ZMod 2)) (locMap K S v))

variable {M : Type} [AddCommGroup M] [DistribMulAction (GKS K S) M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  (D : SquareRootCoefficients K S M)

/-- The actual restriction of a continuous global two-cocycle. -/
def localizedMuTwoCycle (v : HeightOneSpectrum (𝓞 K))
    (c : LinearMap.ker ((contCochains (ZMod 2) (GKS K S)
      (TrivMod (GKS K S) (ZMod 2))).d 2 3).hom) :
    LinearMap.ker ((contCochains (ZMod 2) (Gloc K v)
      (ResMod (locMap K S v) (TrivMod (GKS K S) (ZMod 2)))).d 2 3).hom :=
  ⟨((resCochains (k := ZMod 2) (M := TrivMod (GKS K S) (ZMod 2))
      (locMap K S v)).f 2).hom c.1, by
    have h := congrArg (fun f => f.hom c.1)
      ((resCochains (k := ZMod 2) (M := TrivMod (GKS K S) (ZMod 2))
        (locMap K S v)).comm 2 3)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    have hc : ((contCochains (ZMod 2) (GKS K S)
      (TrivMod (GKS K S) (ZMod 2))).d 2 3).hom c.1 = 0 := c.2
    rw [hc, map_zero] at h
    exact h⟩

/-- Explicit degree-two localization is the restriction of the genuine continuous cochains. -/
theorem localizeMuTwoH2_kerToH2 (v : HeightOneSpectrum (𝓞 K))
    (c : LinearMap.ker ((contCochains (ZMod 2) (GKS K S)
      (TrivMod (GKS K S) (ZMod 2))).d 2 3).hom) :
    localizeMuTwoH2 K S v (kerToH2 c) = kerToH2 (localizedMuTwoCycle K S v c) := by
  rw [localizeMuTwoH2, kerToH2_apply, kerToH2_apply]
  erw [explicitMap2_mk]
  apply congrArg (fun z : Z2 (Gloc K v)
    (ResMod (locMap K S v) (TrivMod (GKS K S) (ZMod 2))) =>
      (z : H2 (Gloc K v) (ResMod (locMap K S v) (TrivMod (GKS K S) (ZMod 2)))))
  apply Subtype.ext
  funext p
  obtain ⟨g, h⟩ := p
  change contFun c.1 ![locMap K S v g, locMap K S v h] =
    contFun (((resCochains (k := ZMod 2) (M := TrivMod (GKS K S) (ZMod 2))
      (locMap K S v)).f 2).hom c.1) ![g, h]
  have hv : (locMap K S v : Gloc K v → GKS K S) ∘ ![g, h] =
      ![locMap K S v g, locMap K S v h] := by
    funext i
    fin_cases i <;> rfl
  exact (congrArg (contFun c.1) hv).symm

/-- The defining construction property of a global Brauer map: inflation along restriction,
followed by the normalized actual roots inclusion and the continuous Brauer comparison.
This property assumes neither a localization square nor any vanishing statement. -/
def GlobalBrauerConstruction (toBrauer : H2 (GKS K S) M →+ Br K) : Prop :=
  ∃ (ι : M →+ UnitsCoeff K)
    (hι : ∀ (g : AbsoluteGaloisGroup K) (m : M),
      ι (resAbsCont K S ((absoluteGaloisGroupRestrictEquiv K).symm g) • m) = g • ι m),
    (ι (muTwoDictionary K S D (show TrivMod (GKS K S) (ZMod 2) from (1 : ZMod 2)))).toMul = -1 ∧
    ∀ x : H2 (GKS K S) M, toBrauer x =
      unitsRepH2Equiv K (explicitMap2 (GKS K S) M (AbsoluteGaloisGroup K) (UnitsCoeff K)
        ((resAbsCont K S).comp
          ((absoluteGaloisGroupRestrictEquiv K).symm : AbsoluteGaloisGroup K →ₜ* Field.absoluteGaloisGroup K))
        ι continuous_of_discreteTopology hι x)

/-- The genuine local square for residual square-root coefficients.
The local leg uses restriction of continuous cochains, the existing local coefficient transport,
and the existing Kummer-to-Brauer map. -/
theorem localBrauer_square (toBrauer : H2 (GKS K S) M →+ Br K)
    (hconstruction : GlobalBrauerConstruction K S D toBrauer)
    (v : HeightOneSpectrum (𝓞 K))
    (eμ : ResMod (locMap K S v) (TrivMod (GKS K S) (ZMod 2)) ≃+
      KummerCoeff (v.adicCompletion K) 2)
    (heμ : ∀ (g : AbsoluteGaloisGroup (v.adicCompletion K))
      (t : ResMod (locMap K S v) (TrivMod (GKS K S) (ZMod 2))),
      eμ ((absoluteGaloisGroupRestrictEquiv (v.adicCompletion K)).symm g • t) = g • eμ t)
    (x : H2 (GKS K S) (TrivMod (GKS K S) (ZMod 2))) :
    ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := v.adicCompletion K) 2
        (kummerH2Transport eμ heμ (localizeMuTwoH2 K S v x)) =
      brBaseChange K (v.adicCompletion K) (toBrauer (muTwoH2Dictionary K S D x)) := by
  obtain ⟨ι, hι, hιone, hdef⟩ := hconstruction
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [hdef, brBaseChange_apply K (v.adicCompletion K) (decompSeparableEmbedding K v),
      AddEquiv.symm_apply_apply]
    change unitsRepH2Equiv (v.adicCompletion K)
      (explicitCoeff2 (AbsoluteGaloisGroup (v.adicCompletion K))
        (KummerCoeff (v.adicCompletion K) 2)
        (kummerCoeffInclHom (v.adicCompletion K) 2) continuous_of_discreteTopology
        (kummerH2Transport eμ heμ (localizeMuTwoH2 K S v (c : H2 _ _)))) = _
    rw [kummerH2Transport, explicitMap2Equiv_apply, localizeMuTwoH2,
      muTwoH2Dictionary, explicitCoeff2Equiv_apply]
    erw [explicitCoeff2_eq_explicitMap2, explicitCoeff2_eq_explicitMap2]
    erw [explicitMap2_mk, explicitMap2_mk]
    apply congrArg (unitsRepH2Equiv (v.adicCompletion K))
    apply congrArg (fun z : Z2 (AbsoluteGaloisGroup (v.adicCompletion K))
      (UnitsCoeff (v.adicCompletion K)) =>
        (z : H2 (AbsoluteGaloisGroup (v.adicCompletion K)) (UnitsCoeff (v.adicCompletion K))))
    apply Subtype.ext
    funext p
    obtain ⟨g, h⟩ := p
    change kummerCoeffIncl (v.adicCompletion K) 2
      (eμ ((c : GKS K S × GKS K S → TrivMod (GKS K S) (ZMod 2))
        (locMap K S v ((absoluteGaloisGroupRestrictEquiv (v.adicCompletion K)).symm g),
          locMap K S v ((absoluteGaloisGroupRestrictEquiv (v.adicCompletion K)).symm h)))) =
      unitsCoeffBaseChange (decompSeparableEmbedding K v)
        (ι (muTwoDictionary K S D ((c : GKS K S × GKS K S → TrivMod (GKS K S) (ZMod 2))
          (resAbsCont K S ((absoluteGaloisGroupRestrictEquiv K).symm
              (absoluteGaloisGroupMap (decompSeparableEmbedding K v) g)),
            resAbsCont K S ((absoluteGaloisGroupRestrictEquiv K).symm
              (absoluteGaloisGroupMap (decompSeparableEmbedding K v) h))))))
    rw [locMap_via_separable, locMap_via_separable]
    exact (localCoefficient_square (decompSeparableEmbedding K v)
      (muTwoDictionary K S D) ι hιone eμ _).symm

end LocalSquare

section Reductions

open ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.TameModel

variable (K : Type) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The local residual coefficient is the actual square-root module of the local separable closure. -/
def localMuTwoEquiv (v : HeightOneSpectrum (𝓞 K)) :
    ResMod (locMap K S v) (TrivMod (GKS K S) (ZMod 2)) ≃+ KummerCoeff (v.adicCompletion K) 2 :=
  (kummerCoeffAddEquivZMod (K := v.adicCompletion K) (n := 2)
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by decide)))).symm

/-- The local coefficient dictionary is equivariant; the two actions on square roots are trivial. -/
theorem localMuTwoEquiv_smul (v : HeightOneSpectrum (𝓞 K))
    (g : AbsoluteGaloisGroup (v.adicCompletion K))
    (t : ResMod (locMap K S v) (TrivMod (GKS K S) (ZMod 2))) :
    localMuTwoEquiv K S v ((absoluteGaloisGroupRestrictEquiv (v.adicCompletion K)).symm g • t) =
      g • localMuTwoEquiv K S v t :=
  (smul_kummerCoeff_eq_self
    (IsPrimitiveRoot.neg_one 0 (by norm_num) : IsPrimitiveRoot (-1 : v.adicCompletion K) 2) g _).symm

/-- Unramified degree-two cohomology with the actual residual coefficients vanishes. -/
theorem unramifiedMuTwoH2_subsingleton (v : HeightOneSpectrum (𝓞 K)) :
    Subsingleton (H2 (GUr K v) (TrivMod (GUr K v) (ZMod 2))) := by
  have : ContinuousSMul (ZMod 2) (TrivMod (GUr K v) (ZMod 2)) :=
    inferInstanceAs (ContinuousSMul (ZMod 2) (ZMod 2))
  have : Finite (TrivMod (GUr K v) (ZMod 2)) := inferInstanceAs (Finite (ZMod 2))
  have : Subsingleton (contCohomology (ZMod 2) (GUr K v)
      (TrivMod (GUr K v) (ZMod 2)) 2) :=
    ur_subsingleton_contCohomology_ge_two K v (ZMod 2)
      (TrivMod (GUr K v) (ZMod 2)) 2 (by decide)
  exact (contH2AddEquiv (ZMod 2) (GUr K v) (TrivMod (GUr K v) (ZMod 2))).symm.injective.subsingleton

/-- A genuine unramified factorization kills the localized residual degree-two class. -/
theorem localizeMuTwoH2_eq_zero_of_factorization (v : HeightOneSpectrum (𝓞 K))
    (ψ : GUr K v →ₜ* GKS K S) (hψ : ∀ g, locMap K S v g = ψ (urRes K v g))
    (x : H2 (GKS K S) (TrivMod (GKS K S) (ZMod 2))) :
    localizeMuTwoH2 K S v x = 0 := by
  let U := TrivMod (GUr K v) (ZMod 2)
  have : IsTopologicalAddGroup U := inferInstanceAs (IsTopologicalAddGroup (ZMod 2))
  have : IsTopologicalAddGroup (ResMod (locMap K S v) (TrivMod (GKS K S) (ZMod 2))) :=
    inferInstanceAs (IsTopologicalAddGroup (ZMod 2))
  let R : H2 (GKS K S) (TrivMod (GKS K S) (ZMod 2)) →+ H2 (GUr K v) U :=
    explicitMap2 (GKS K S) (TrivMod (GKS K S) (ZMod 2)) (GUr K v) U ψ
      (AddMonoidHom.id (ZMod 2)) continuous_id (fun _ _ => rfl)
  let L : H2 (GUr K v) U →+
      H2 (Gloc K v) (ResMod (locMap K S v) (TrivMod (GKS K S) (ZMod 2))) :=
    explicitMap2 (GUr K v) U (Gloc K v)
      (ResMod (locMap K S v) (TrivMod (GKS K S) (ZMod 2))) (urRes K v)
      (AddMonoidHom.id (ZMod 2)) continuous_id (fun _ _ => rfl)
  have heq : localizeMuTwoH2 K S v x = L (R x) := by
    induction x using QuotientAddGroup.induction_on with
    | H c =>
      dsimp only [L, R]
      rw [localizeMuTwoH2]
      erw [explicitMap2_mk, explicitMap2_mk]
      apply congrArg (fun z : Z2 (Gloc K v)
        (ResMod (locMap K S v) (TrivMod (GKS K S) (ZMod 2))) =>
          (z : H2 (Gloc K v) (ResMod (locMap K S v) (TrivMod (GKS K S) (ZMod 2)))))
      apply Subtype.ext
      funext p
      obtain ⟨g, h⟩ := p
      change (c : GKS K S × GKS K S → TrivMod (GKS K S) (ZMod 2))
          (locMap K S v g, locMap K S v h) =
        (c : GKS K S × GKS K S → TrivMod (GKS K S) (ZMod 2))
          (ψ (urRes K v g), ψ (urRes K v h))
      rw [hψ, hψ]
  have : Subsingleton (H2 (GUr K v) U) := unramifiedMuTwoH2_subsingleton K v
  have hR : R x = 0 := Subsingleton.elim _ _
  rw [heq, hR, map_zero]

/-- Outside the designated finite places, the actual localized residual degree-two class vanishes. -/
theorem localizeMuTwoH2_eq_zero_of_notMem (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (x : H2 (GKS K S) (TrivMod (GKS K S) (ZMod 2))) :
    localizeMuTwoH2 K S v x = 0 := by
  obtain ⟨ψ, hψ⟩ := unramifiedAtFactorization K S v hv
  exact localizeMuTwoH2_eq_zero_of_factorization K S v ψ hψ x

omit [NumberField K] in
/-- The Brauer localization at a complex place vanishes. -/
theorem brBaseChange_eq_zero_of_complex (w : InfinitePlace K) (hw : w.IsComplex) (b : Br K) :
    brBaseChange K w.Completion b = 0 :=
  brCompletion_eq_zero_of_isComplex w hw _

/-- At a place outside the designated set, restriction of an actual continuous two-cocycle is a boundary. -/
theorem localizedMuTwoCycle_isBoundary_of_notMem (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (c : LinearMap.ker ((contCochains (ZMod 2) (GKS K S)
      (TrivMod (GKS K S) (ZMod 2))).d 2 3).hom) :
    ∃ y : (contCochains (ZMod 2) (Gloc K v)
      (ResMod (locMap K S v) (TrivMod (GKS K S) (ZMod 2)))).X 1,
      ((contCochains (ZMod 2) (Gloc K v)
        (ResMod (locMap K S v) (TrivMod (GKS K S) (ZMod 2)))).d 1 2).hom y =
          (localizedMuTwoCycle K S v c).1 := by
  apply (kerToH2_eq_zero_iff _).mp
  rw [← localizeMuTwoH2_kerToH2]
  exact localizeMuTwoH2_eq_zero_of_notMem K S v hv _

variable {M : Type} [AddCommGroup M] [DistribMulAction (GKS K S) M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  (D : SquareRootCoefficients K S M)

/-- The global Brauer image of residual coefficients has no localization outside the designated places. -/
theorem globalBrauer_outsideS (toBrauer : H2 (GKS K S) M →+ Br K)
    (hconstruction : GlobalBrauerConstruction K S D toBrauer)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (x : H2 (GKS K S) (TrivMod (GKS K S) (ZMod 2))) :
    brBaseChange K (v.adicCompletion K) (toBrauer (muTwoH2Dictionary K S D x)) = 0 := by
  rw [← localBrauer_square K S D toBrauer hconstruction v
    (localMuTwoEquiv K S v) (localMuTwoEquiv_smul K S v) x,
    localizeMuTwoH2_eq_zero_of_notMem K S v hv x, map_zero, map_zero]

/-- A totally complex field has no archimedean Brauer localization terms. -/
theorem brLocalization_infinite_eq_zero (hK : IsTotallyComplex K) (b : Br K) :
    (brLocalization K b).2 = 0 := by
  funext w
  exact brBaseChange_eq_zero_of_complex K w (hK.isComplex w) b

end Reductions

section CanonicalConstruction

attribute [local instance] TopRep.distribMulAction

variable (K : Type) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K)))
  {M : Type} [AddCommGroup M] [DistribMulAction (GKS K S) M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  (D : SquareRootCoefficients K S M)

omit [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M] in
/-- A literal roots inclusion has the required normalization on the nonzero residual coefficient. -/
theorem rootsInclusion_normalization (j : KS K S →+* SeparableClosure K)
    (ι : M →+ (unitsRep K).V)
    (hformula : ∀ m : M, (((unitsCoeffEquivUnitsRep K).symm (ι m)).toMul : SeparableClosure K) =
      j (((D.roots m).toMul : (KS K S)ˣ) : KS K S)) :
    ((unitsCoeffEquivUnitsRep K).symm
      (ι (muTwoDictionary K S D (show TrivMod (GKS K S) (ZMod 2) from (1 : ZMod 2))))).toMul = -1 := by
  apply Units.ext
  erw [hformula, muTwoDictionary_roots, twoRoots_one (squareRootCoordinates K S)]
  change j (-1 : KS K S) = (-1 : SeparableClosure K)
  exact (map_neg j (1 : KS K S)).trans (congrArg Neg.neg (map_one j))

/-- The defining global construction on the algebraic-closure Galois group and the canonical
Brauer coefficient object. This is a defining formula, not a localization assumption. -/
def GlobalBrauerConstructionCanonical (toBrauer : H2 (GKS K S) M →+ Br K) : Prop :=
  ∃ (ι : M →+ (unitsRep K).V)
    (hι : ∀ (g : Field.absoluteGaloisGroup K) (m : M),
      ι (resAbsCont K S g • m) = g • ι m),
    ((unitsCoeffEquivUnitsRep K).symm
      (ι (muTwoDictionary K S D (show TrivMod (GKS K S) (ZMod 2) from (1 : ZMod 2))))).toMul = -1 ∧
    ∀ x : H2 (GKS K S) M, toBrauer x =
      (unitsRep K).explicitH2AddEquivContinuousCohomologyOfDiscrete
        (explicitMap2 (GKS K S) M (Field.absoluteGaloisGroup K) (unitsRep K).V
          (resAbsCont K S) ι continuous_of_discreteTopology hι x)

/-- The algebraic-closure defining construction gives the separable-closure construction property. -/
theorem globalConstruction_of_canonical (toBrauer : H2 (GKS K S) M →+ Br K)
    (hcanonical : GlobalBrauerConstructionCanonical K S D toBrauer) :
    GlobalBrauerConstruction K S D toBrauer := by
  obtain ⟨ι, hι, hnorm, hdef⟩ := hcanonical
  let j : M →+ UnitsCoeff K := (unitsCoeffEquivUnitsRep K).symm.toAddMonoidHom.comp ι
  have hjval (m : M) : unitsCoeffEquivUnitsRep K (j m) = ι m :=
    (unitsCoeffEquivUnitsRep K).apply_symm_apply _
  have hj : ∀ (g : AbsoluteGaloisGroup K) (m : M),
      j (resAbsCont K S ((absoluteGaloisGroupRestrictEquiv K).symm g) • m) = g • j m := by
    intro g m
    apply (unitsCoeffEquivUnitsRep K).injective
    rw [hjval, hι]
    have h := unitsCoeffEquivUnitsRep_smul K ((absoluteGaloisGroupRestrictEquiv K).symm g) (j m)
    rw [ContinuousMulEquiv.apply_symm_apply, hjval] at h
    exact (TopRep.distribMulAction_smul _ _ _).trans h.symm
  refine ⟨j, hj, hnorm, fun x => ?_⟩
  rw [hdef, unitsRepH2Equiv_apply]
  apply congrArg (unitsRep K).explicitH2AddEquivContinuousCohomologyOfDiscrete
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    erw [explicitMap2_mk, explicitMap2_mk]
    apply congrArg (fun z : Z2 (Field.absoluteGaloisGroup K) (unitsRep K).V =>
      (z : H2 (Field.absoluteGaloisGroup K) (unitsRep K).V))
    apply Subtype.ext
    funext p
    obtain ⟨g, h⟩ := p
    change ι ((c : GKS K S × GKS K S → M) (resAbsCont K S g, resAbsCont K S h)) =
      unitsCoeffEquivUnitsRep K (j ((c : GKS K S × GKS K S → M)
        (resAbsCont K S ((absoluteGaloisGroupRestrictEquiv K).symm
            (absoluteGaloisGroupRestrictEquiv K g)),
          resAbsCont K S ((absoluteGaloisGroupRestrictEquiv K).symm
            (absoluteGaloisGroupRestrictEquiv K h)))))
    rw [ContinuousMulEquiv.symm_apply_apply, ContinuousMulEquiv.symm_apply_apply, hjval]

/-- The global construction property follows from the actual cocycle readback.
The readback specifies every cocycle value as the roots inclusion of the restricted value. -/
theorem canonicalConstruction_of_cocycleReadback (toBrauer : H2 (GKS K S) M →+ Br K)
    (ι : M →+ (unitsRep K).V)
    (hι : ∀ (g : Field.absoluteGaloisGroup K) (m : M), ι (resAbsCont K S g • m) = g • ι m)
    (hnorm : ((unitsCoeffEquivUnitsRep K).symm
      (ι (muTwoDictionary K S D (show TrivMod (GKS K S) (ZMod 2) from (1 : ZMod 2))))).toMul = -1)
    (toUnitsCocycle : Z2 (GKS K S) M → Z2 (Field.absoluteGaloisGroup K) (unitsRep K).V)
    (happly : ∀ (c : Z2 (GKS K S) M) (g h : Field.absoluteGaloisGroup K),
      (toUnitsCocycle c).1 (g, h) = ι (c.1 (resAbsCont K S g, resAbsCont K S h)))
    (hrep : ∀ c : Z2 (GKS K S) M, toBrauer (c : H2 (GKS K S) M) =
      (unitsRep K).explicitH2AddEquivContinuousCohomologyOfDiscrete
        (toUnitsCocycle c : H2 (Field.absoluteGaloisGroup K) (unitsRep K).V)) :
    GlobalBrauerConstructionCanonical K S D toBrauer := by
  refine ⟨ι, hι, hnorm, fun x => ?_⟩
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [hrep]
    erw [explicitMap2_mk]
    apply congrArg (unitsRep K).explicitH2AddEquivContinuousCohomologyOfDiscrete
    apply congrArg (fun z : Z2 (Field.absoluteGaloisGroup K) (unitsRep K).V =>
      (z : H2 (Field.absoluteGaloisGroup K) (unitsRep K).V))
    apply Subtype.ext
    funext p
    obtain ⟨g, h⟩ := p
    exact (happly c g h).trans (cocyclesMap2_apply _ _ _ _ _ _ _ _ c g h).symm

/-- The local square also holds against the defining construction on the canonical Brauer carrier. -/
theorem localBrauer_square_canonical (toBrauer : H2 (GKS K S) M →+ Br K)
    (hcanonical : GlobalBrauerConstructionCanonical K S D toBrauer)
    (v : HeightOneSpectrum (𝓞 K))
    (x : H2 (GKS K S) (TrivMod (GKS K S) (ZMod 2))) :
    ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := v.adicCompletion K) 2
        (kummerH2Transport (localMuTwoEquiv K S v) (localMuTwoEquiv_smul K S v)
          (localizeMuTwoH2 K S v x)) =
      brBaseChange K (v.adicCompletion K) (toBrauer (muTwoH2Dictionary K S D x)) :=
  localBrauer_square K S D toBrauer (globalConstruction_of_canonical K S D toBrauer hcanonical)
    v (localMuTwoEquiv K S v) (localMuTwoEquiv_smul K S v) x

end CanonicalConstruction

section SumFormulaAssembly

variable (K : Type) [Field K] [NumberField K]

/-- The sum formula kills a lone finite-place localization over a totally complex number field. -/
theorem brauerLocalization_zero_of_singleSupport (hK : IsTotallyComplex K)
    (q : HeightOneSpectrum (𝓞 K)) (b : Br K)
    (hsum : sumLocalInv K (brLocalization K b) = 0)
    (hother : ∀ v : HeightOneSpectrum (𝓞 K), v ≠ q → brBaseChange K (v.adicCompletion K) b = 0) :
    brBaseChange K (q.adicCompletion K) b = 0 := by
  classical
  have heq : brLocalization K b =
      (DFinsupp.single q (brBaseChange K (q.adicCompletion K) b), 0) := by
    apply Prod.ext
    · apply DFinsupp.ext
      intro v
      rw [brLocalization_fst_apply]
      by_cases hv : v = q
      · subst v
        rw [DFinsupp.single_eq_same]
      · rw [DFinsupp.single_eq_of_ne hv]
        exact hother v hv
    · exact brLocalization_infinite_eq_zero K hK b
  have hinv : invMap (q.adicCompletion K) (brBaseChange K (q.adicCompletion K) b) = 0 := by
    rwa [heq, sumLocalInv_single] at hsum
  exact (invMap (q.adicCompletion K)).injective (hinv.trans (map_zero _).symm)

variable (S : Set (HeightOneSpectrum (𝓞 K)))
  {M : Type} [AddCommGroup M] [DistribMulAction (GKS K S) M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  (D : SquareRootCoefficients K S M)

/-- The all-place Brauer sum is the finite sum over the designated set, after the proved
outside-set and complex-place reductions. -/
theorem allPlaceSum_eq_finiteSum (hK : IsTotallyComplex K) (hS : S.Finite)
    (toBrauer : H2 (GKS K S) M →+ Br K)
    (hconstruction : GlobalBrauerConstruction K S D toBrauer)
    (x : H2 (GKS K S) (TrivMod (GKS K S) (ZMod 2))) :
    sumLocalInv K (brLocalization K (toBrauer (muTwoH2Dictionary K S D x))) =
      ∑ v ∈ hS.toFinset, invMap (v.adicCompletion K)
        (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := v.adicCompletion K) 2
          (kummerH2Transport (localMuTwoEquiv K S v) (localMuTwoEquiv_smul K S v)
            (localizeMuTwoH2 K S v x))) := by
  classical
  let b := toBrauer (muTwoH2Dictionary K S D x)
  have hsupport : ∀ v ∉ hS.toFinset, (brLocalization K b).1 v = 0 := by
    intro v hv
    rw [brLocalization_fst_apply]
    exact globalBrauer_outsideS K S D toBrauer hconstruction v
      (fun h => hv (hS.mem_toFinset.mpr h)) x
  have h := sumLocalInv_eq_sum K (brLocalization K b) hsupport
  rw [brLocalization_infinite_eq_zero K hK b] at h
  simp only [Pi.zero_apply, map_zero, Finset.sum_const_zero, add_zero, brLocalization_fst_apply] at h
  calc
    _ = ∑ v ∈ hS.toFinset, invMap (v.adicCompletion K) (brBaseChange K (v.adicCompletion K) b) := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      apply congrArg (invMap (v.adicCompletion K))
      exact (localBrauer_square K S D toBrauer hconstruction v
        (localMuTwoEquiv K S v) (localMuTwoEquiv_smul K S v) x).symm

/-- The finite sum of residual local Brauer invariants vanishes by the proved all-place sum formula. -/
theorem finiteSum_eq_zero (hK : IsTotallyComplex K) (hS : S.Finite)
    (toBrauer : H2 (GKS K S) M →+ Br K)
    (hconstruction : GlobalBrauerConstruction K S D toBrauer)
    (x : H2 (GKS K S) (TrivMod (GKS K S) (ZMod 2))) :
    ∑ v ∈ hS.toFinset, invMap (v.adicCompletion K)
      (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := v.adicCompletion K) 2
        (kummerH2Transport (localMuTwoEquiv K S v) (localMuTwoEquiv_smul K S v)
          (localizeMuTwoH2 K S v x))) = 0 :=
  (allPlaceSum_eq_finiteSum K S D hK hS toBrauer hconstruction x).symm.trans
    (sumLocalInv_brLocalization_eq_zero K _)

/-- Residual reciprocity in cohomology follows from the defining global construction and its sum formula.
The local injectivity input is the existing Kummer-to-Brauer comparison at the selected place. -/
theorem localizeMuTwoH2_eq_zero_of_globalConstruction (hK : IsTotallyComplex K)
    (toBrauer : H2 (GKS K S) M →+ Br K)
    (hconstruction : GlobalBrauerConstruction K S D toBrauer)
    (hsum : ∀ x : H2 (GKS K S) M, sumLocalInv K (brLocalization K (toBrauer x)) = 0)
    (q : Places K S)
    (hInjective : Function.Injective
      (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := q.1.adicCompletion K) 2))
    (x : H2 (GKS K S) (TrivMod (GKS K S) (ZMod 2)))
    (hlocal : ∀ v : Places K S, v ≠ q → localizeMuTwoH2 K S v.1 x = 0) :
    localizeMuTwoH2 K S q.1 x = 0 := by
  let b := toBrauer (muTwoH2Dictionary K S D x)
  have hother : ∀ v : HeightOneSpectrum (𝓞 K), v ≠ q.1 →
      brBaseChange K (v.adicCompletion K) b = 0 := by
    intro v hvq
    by_cases hv : v ∈ S
    · let w : Places K S := ⟨v, hv⟩
      have hw : w ≠ q := fun h => hvq (congrArg Subtype.val h)
      have hclass := hlocal w hw
      change brBaseChange K (v.adicCompletion K) (toBrauer (muTwoH2Dictionary K S D x)) = 0
      rw [← localBrauer_square K S D toBrauer hconstruction v
        (localMuTwoEquiv K S v) (localMuTwoEquiv_smul K S v) x,
        hclass, map_zero, map_zero]
    · exact globalBrauer_outsideS K S D toBrauer hconstruction v hv x
  have hbq : brBaseChange K (q.1.adicCompletion K) b = 0 :=
    brauerLocalization_zero_of_singleSupport K hK q.1 b (hsum _) hother
  have hbr := (localBrauer_square K S D toBrauer hconstruction q.1
    (localMuTwoEquiv K S q.1) (localMuTwoEquiv_smul K S q.1) x).trans hbq
  have hclass : kummerH2Transport (localMuTwoEquiv K S q.1) (localMuTwoEquiv_smul K S q.1)
      (localizeMuTwoH2 K S q.1 x) = 0 :=
    hInjective (hbr.trans (map_zero _).symm)
  exact (kummerH2Transport (localMuTwoEquiv K S q.1) (localMuTwoEquiv_smul K S q.1)).injective
    (hclass.trans (map_zero _).symm)

/-- The proved Brauer sum formula supplies the sum hypothesis in residual reciprocity. -/
theorem localizeMuTwoH2_eq_zero_of_sumFormula (hK : IsTotallyComplex K)
    (toBrauer : H2 (GKS K S) M →+ Br K)
    (hconstruction : GlobalBrauerConstruction K S D toBrauer)
    (q : Places K S)
    (hInjective : Function.Injective
      (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := q.1.adicCompletion K) 2))
    (x : H2 (GKS K S) (TrivMod (GKS K S) (ZMod 2)))
    (hlocal : ∀ v : Places K S, v ≠ q → localizeMuTwoH2 K S v.1 x = 0) :
    localizeMuTwoH2 K S q.1 x = 0 :=
  localizeMuTwoH2_eq_zero_of_globalConstruction K S D hK toBrauer hconstruction
    (fun x => sumLocalInv_brLocalization_eq_zero K (toBrauer x)) q hInjective x hlocal

/-- The elementwise reciprocity statement for the actual continuous global and local complexes.
Only the coefficient model, the defining global construction, its sum formula, and the existing
local Kummer injectivity at the selected place are used. -/
theorem reciprocityAt_from_globalConstruction (hK : IsTotallyComplex K)
    (toBrauer : H2 (GKS K S) M →+ Br K)
    (hconstruction : GlobalBrauerConstruction K S D toBrauer)
    (hsum : ∀ x : H2 (GKS K S) M, sumLocalInv K (brLocalization K (toBrauer x)) = 0)
    (q : Places K S)
    (hInjective : Function.Injective
      (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := q.1.adicCompletion K) 2)) :
    ∀ e : (globalCx (ZMod 2) (GKS K S) (TrivMod (GKS K S) (ZMod 2))).X 2,
      (globalCx (ZMod 2) (GKS K S) (TrivMod (GKS K S) (ZMod 2))).d 2 3 rfl e = 0 →
      (∀ v : Places K S, v ≠ q →
        ∃ y : (localCx (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
            (fun v => locMap K S v.1) (TrivMod (GKS K S) (ZMod 2)) v).X 1,
          (localCx (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
            (fun v => locMap K S v.1) (TrivMod (GKS K S) (ZMod 2)) v).d 1 2 rfl y =
              (resS (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
                (fun v => locMap K S v.1) (TrivMod (GKS K S) (ZMod 2))).f 2 2 rfl e v) →
      ∃ y : (localCx (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (TrivMod (GKS K S) (ZMod 2)) q).X 1,
        (localCx (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (TrivMod (GKS K S) (ZMod 2)) q).d 1 2 rfl y =
            (resS (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
              (fun v => locMap K S v.1) (TrivMod (GKS K S) (ZMod 2))).f 2 2 rfl e q := by
  intro e he hloc
  let c : LinearMap.ker ((contCochains (ZMod 2) (GKS K S)
    (TrivMod (GKS K S) (ZMod 2))).d 2 3).hom := ⟨e, he⟩
  have hclass : localizeMuTwoH2 K S q.1 (kerToH2 c) = 0 :=
    localizeMuTwoH2_eq_zero_of_globalConstruction K S D hK toBrauer hconstruction hsum q
      hInjective (kerToH2 c) (fun v hv => by
        rw [localizeMuTwoH2_kerToH2]
        apply (kerToH2_eq_zero_iff _).mpr
        obtain ⟨y, hy⟩ := hloc v hv
        exact ⟨y, hy⟩)
  have hzero : kerToH2 (localizedMuTwoCycle K S q.1 c) = 0 :=
    (localizeMuTwoH2_kerToH2 K S q.1 c).symm.trans hclass
  obtain ⟨y, hy⟩ := (kerToH2_eq_zero_iff _).mp hzero
  exact ⟨y, hy⟩

/-- The elementwise reciprocity assembly against the canonical defining global construction. -/
theorem reciprocityAt_from_canonicalConstruction (hK : IsTotallyComplex K)
    (toBrauer : H2 (GKS K S) M →+ Br K)
    (hcanonical : GlobalBrauerConstructionCanonical K S D toBrauer)
    (hsum : ∀ x : H2 (GKS K S) M, sumLocalInv K (brLocalization K (toBrauer x)) = 0)
    (q : Places K S)
    (hInjective : Function.Injective
      (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := q.1.adicCompletion K) 2)) :
    let T := TrivMod (GKS K S) (ZMod 2)
    let E := globalCx (ZMod 2) (GKS K S) T
    let A := localCx (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T
    let R := resS (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T
    ∀ e : E.X 2, E.d 2 3 rfl e = 0 →
      (∀ v : Places K S, v ≠ q → ∃ y : (A v).X 1, (A v).d 1 2 rfl y = R.f 2 2 rfl e v) →
      ∃ y : (A q).X 1, (A q).d 1 2 rfl y = R.f 2 2 rfl e q :=
  reciprocityAt_from_globalConstruction K S D hK toBrauer
    (globalConstruction_of_canonical K S D toBrauer hcanonical) hsum q hInjective

/-- The proved all-place sum formula eliminates a separate sum hypothesis from the elementwise assembly. -/
theorem reciprocityAt_from_sumFormula (hK : IsTotallyComplex K)
    (toBrauer : H2 (GKS K S) M →+ Br K)
    (hcanonical : GlobalBrauerConstructionCanonical K S D toBrauer)
    (q : Places K S)
    (hInjective : Function.Injective
      (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := q.1.adicCompletion K) 2)) :
    let T := TrivMod (GKS K S) (ZMod 2)
    let E := globalCx (ZMod 2) (GKS K S) T
    let A := localCx (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T
    let R := resS (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T
    ∀ e : E.X 2, E.d 2 3 rfl e = 0 →
      (∀ v : Places K S, v ≠ q → ∃ y : (A v).X 1, (A v).d 1 2 rfl y = R.f 2 2 rfl e v) →
      ∃ y : (A q).X 1, (A q).d 1 2 rfl y = R.f 2 2 rfl e q :=
  reciprocityAt_from_canonicalConstruction K S D hK toBrauer hcanonical
    (fun x => sumLocalInv_brLocalization_eq_zero K (toBrauer x)) q hInjective

section ReadbackAssembly

attribute [local instance] TopRep.distribMulAction

/-- The complete elementwise assembly from the defining cocycle readback of the global map.
No local square, outside-set vanishing, or finite-sum identification is an input. -/
theorem reciprocityAt_from_cocycleReadback (hK : IsTotallyComplex K)
    (toBrauer : H2 (GKS K S) M →+ Br K)
    (ι : M →+ (unitsRep K).V)
    (hι : ∀ (g : Field.absoluteGaloisGroup K) (m : M), ι (resAbsCont K S g • m) = g • ι m)
    (hnorm : ((unitsCoeffEquivUnitsRep K).symm
      (ι (muTwoDictionary K S D (show TrivMod (GKS K S) (ZMod 2) from (1 : ZMod 2))))).toMul = -1)
    (toUnitsCocycle : Z2 (GKS K S) M → Z2 (Field.absoluteGaloisGroup K) (unitsRep K).V)
    (happly : ∀ (c : Z2 (GKS K S) M) (g h : Field.absoluteGaloisGroup K),
      (toUnitsCocycle c).1 (g, h) = ι (c.1 (resAbsCont K S g, resAbsCont K S h)))
    (hrep : ∀ c : Z2 (GKS K S) M, toBrauer (c : H2 (GKS K S) M) =
      (unitsRep K).explicitH2AddEquivContinuousCohomologyOfDiscrete
        (toUnitsCocycle c : H2 (Field.absoluteGaloisGroup K) (unitsRep K).V))
    (hsum : ∀ x : H2 (GKS K S) M, sumLocalInv K (brLocalization K (toBrauer x)) = 0)
    (q : Places K S)
    (hInjective : Function.Injective
      (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := q.1.adicCompletion K) 2)) :
    let T := TrivMod (GKS K S) (ZMod 2)
    let E := globalCx (ZMod 2) (GKS K S) T
    let A := localCx (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T
    let R := resS (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T
    ∀ e : E.X 2, E.d 2 3 rfl e = 0 →
      (∀ v : Places K S, v ≠ q → ∃ y : (A v).X 1, (A v).d 1 2 rfl y = R.f 2 2 rfl e v) →
      ∃ y : (A q).X 1, (A q).d 1 2 rfl y = R.f 2 2 rfl e q :=
  reciprocityAt_from_canonicalConstruction K S D hK toBrauer
    (canonicalConstruction_of_cocycleReadback K S D toBrauer ι hι hnorm toUnitsCocycle happly hrep)
    hsum q hInjective

end ReadbackAssembly

end SumFormulaAssembly

end ZInQ.Contrib.RC53Assist.Reciprocity
