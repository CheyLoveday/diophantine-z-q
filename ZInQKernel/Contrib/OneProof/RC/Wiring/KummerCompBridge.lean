import ZInQKernel.Contrib.RC53Assist.CentralUniversal.GenuineObjects
import ZInQKernel.Contrib.OneProof.RC.Wiring.CalPointKummerClass
import ZInQKernel.Contrib.RC53Assist.DiskOrders.Limit.CocycleLimit

/-!
# Lane RC37: the field, Galois and point comparison between `K_S` and `ℚˢ`

For `K = ℚ(√k)` (the intermediate field `QuadraticField k` of `ℚˢ / ℚ`) and a set `S` of finite
primes of `K`, this file compares the objects of the compact side (the field `K_S` inside an
algebraic closure `K̄` of `K`, the group `G_{K,S} = Gal(K_S/K)`, the points `E(K_S)` of
`W = E_K` and their `2`-power torsion, with the coordinatewise action) with the objects of the
discrete side (the separable closure `ℚˢ`, the stabilizer `G_K = galK (sqrtK k)` of `√k` in
`G_ℚ`, the coefficient modules `E(ℚˢ)`, `E(ℚˢ)[2^m]`, `E(ℚˢ)[2^∞]` of the curve `E/ℚ`):

* `kcClosureEquiv`: a `K`-isomorphism `K̄ ≃ ℚˢ` (`ℚˢ` is an algebraic closure of `K`, since `ℚ`
  is perfect); `kcEmb`: its restriction `K_S → ℚˢ`.
* `kcGal : G_K →ₜ* G_{K,S}`: `σ ↦` the restriction to `K_S` of the transport of `σ` to `K̄`;
  `kcEmb_kcGal`: `kcEmb (kcGal σ x) = σ (kcEmb x)`; continuous and surjective.
* `kcPt : E(K_S) →+ E(ℚˢ)` (the point map along `kcEmb`), injective and equivariant along
  `kcGal`; `kcLev`, `kcLevInf`: its restrictions to `E(K_S)[2^m]` with values in `E(ℚˢ)[2^m]`
  and `E(ℚˢ)[2^∞]`, equivariant, and bijective onto `E(ℚˢ)[2^m]` under full `2^m`-torsion.
* `kcInfl`, `kcInflInf`: the induced maps of continuous cochain complexes
  `C^•(G_{K,S}, E(K_S)[2^m]) → C^•(G_K, E(ℚˢ)[2^m])` and `→ C^•(G_K, E(ℚˢ)[2^∞])`.
* `kcPointsEquiv : E(K) ≃+ H⁰(G_K, E(ℚˢ))` (Galois descent along `K ⊂ ℚˢ`) and its
  compatibility `kcPt_pointToKS` with the image `E(K) → E(K_S)`.

Kinds: definitions and PROVED. No hypothesis beyond those stated (`IsElliptic` and full
`2^m`-torsion for the bijectivity).
-/

noncomputable section

namespace ZInQ.Manuscript.RC

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC53Assist.CentralUniversal ZInQ.Manuscript.RC53Assist.QuadraticDescent
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside resAbs resAbs_apply_coe
  resAbs_surjective)
open ZInQ.Manuscript.RC.KummerMaps (some_eq_some)
open ZInQ.Manuscript.SelmerTwoPower
open TauCeti TauCeti.ContCohomology

/-- The `K`-algebra structure of `K_S`: the instance of the general theory, recorded once so that
it is found directly for `K = ℚ(√k)`. Kind: definition. -/
abbrev kcAlgKS (K : Type) [Field K] (S : Set (HeightOneSpectrum (𝓞 K))) : Algebra K (KS K S) :=
  inferInstance

attribute [local instance high] kcAlgKS

/-- Every module over `K = ℚ(√k)` is torsion-free (recorded for direct instance search).
Kind: PROVED. -/
theorem kcTorsionFree (k : ℤ) (M : Type*) [AddCommGroup M] [Module (QuadraticField k) M] :
    Module.IsTorsionFree (QuadraticField k) M :=
  DivisionSemiring.to_moduleIsTorsionFree

attribute [local instance high] kcTorsionFree

/-! ### The algebraic closure and the embedding `K_S → ℚˢ` -/

section Closure

variable (k : ℤ)

/-- The separable closure `ℚˢ` is algebraic over `K = ℚ(√k)`. Kind: PROVED. -/
theorem kc_isAlgebraic : Algebra.IsAlgebraic (QuadraticField k) (SeparableClosure ℚ) :=
  Algebra.IsAlgebraic.tower_top (K := ℚ) (QuadraticField k)

/-- `ℚˢ` is an algebraic closure of `K = ℚ(√k)` (it is algebraically closed, `ℚ` being
perfect). Kind: PROVED. -/
theorem kc_isAlgClosure : IsAlgClosure (QuadraticField k) (SeparableClosure ℚ) :=
  haveI := kc_isAlgebraic k
  ⟨inferInstance, inferInstance⟩

/-- **A `K`-isomorphism `K̄ ≃ ℚˢ`** for `K = ℚ(√k)`: both are algebraic closures of `K`.
Kind: definition. -/
def kcClosureEquiv :
    AlgebraicClosure (QuadraticField k) ≃ₐ[QuadraticField k] SeparableClosure ℚ :=
  haveI := kc_isAlgClosure k
  IsAlgClosure.equiv (QuadraticField k) (AlgebraicClosure (QuadraticField k))
    (SeparableClosure ℚ)

variable (S : Set (HeightOneSpectrum (𝓞 (QuadraticField k))))

/-- **The embedding `K_S → ℚˢ`**: the restriction of `kcClosureEquiv` to `K_S ⊂ K̄`.
Kind: definition. -/
def kcEmb : KS (QuadraticField k) S →ₐ[QuadraticField k] SeparableClosure ℚ :=
  (kcClosureEquiv k).toAlgHom.comp (inclS (QuadraticField k) S)

/-- `kcEmb` on elements: `kcClosureEquiv` applied to the element of `K̄`. Kind: PROVED. -/
theorem kcEmb_apply (x : KS (QuadraticField k) S) :
    kcEmb k S x = kcClosureEquiv k (x : AlgebraicClosure (QuadraticField k)) :=
  rfl

/-- `kcEmb` is injective. Kind: PROVED. -/
theorem kcEmb_injective : Function.Injective (kcEmb k S) :=
  RingHom.injective (kcEmb k S).toRingHom

end Closure

/-! ### The Galois comparison `G_K → G_{K,S}` -/

section Galois

variable (k : ℤ)

/-- **Elements of `G_K` fix `K = ℚ(√k)` pointwise** (they fix `√k`). Kind: PROVED. -/
theorem kc_fix (σ : galK (sqrtK k)) (x : QuadraticField k) :
    (σ : AbsoluteGaloisGroup ℚ) (x : SeparableClosure ℚ) = x := by
  obtain ⟨x, hx⟩ := x
  show (σ : AbsoluteGaloisGroup ℚ) x = x
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact mem_galK.mp σ.2
  | algebraMap q => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz]
  | inv y _ hy => rw [map_inv₀, hy]
  | mul y z _ _ hy hz => rw [map_mul, hy, hz]

/-- **`G_K` acting `K`-linearly on `ℚˢ`**: an element of `G_K` as a `K`-automorphism of `ℚˢ`.
Kind: definition. -/
def kcAutK : galK (sqrtK k) →* (SeparableClosure ℚ ≃ₐ[QuadraticField k] SeparableClosure ℚ) where
  toFun σ := { (σ : AbsoluteGaloisGroup ℚ).toRingEquiv with commutes' := fun x => kc_fix k σ x }
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

/-- `kcAutK` on elements. Kind: PROVED. -/
theorem kcAutK_apply (σ : galK (sqrtK k)) (x : SeparableClosure ℚ) :
    kcAutK k σ x = (σ : AbsoluteGaloisGroup ℚ) x :=
  rfl

/-- The transport `κ⁻¹ ∘ σ ∘ κ ∈ Gal(K̄/K)` of `σ ∈ G_K`, for `κ = kcClosureEquiv`.
Kind: definition. -/
def kcAbs : galK (sqrtK k) →* (AlgebraicClosure (QuadraticField k) ≃ₐ[QuadraticField k]
    AlgebraicClosure (QuadraticField k)) :=
  (kcClosureEquiv k).symm.autCongr.toMonoidHom.comp (kcAutK k)

/-- `κ (kcAbs σ y) = σ (κ y)`. Kind: PROVED. -/
theorem kcClosureEquiv_kcAbs (σ : galK (sqrtK k)) (y : AlgebraicClosure (QuadraticField k)) :
    kcClosureEquiv k (kcAbs k σ y) = (σ : AbsoluteGaloisGroup ℚ) (kcClosureEquiv k y) := by
  simp [kcAbs, AlgEquiv.autCongr_apply, kcAutK_apply]

variable (S : Set (HeightOneSpectrum (𝓞 (QuadraticField k))))

/-- The comparison `G_K → G_{K,S}` as a monoid homomorphism: the restriction of `kcAbs σ` to
`K_S`. Kind: definition. -/
def kcGalHom : galK (sqrtK k) →* GKS (QuadraticField k) S where
  toFun σ := resAbs (QuadraticField k) S (kcAbs k σ)
  map_one' := (congrArg (resAbs _ S) (map_one (kcAbs k))).trans (map_one (resAbs _ S))
  map_mul' σ τ := (congrArg (resAbs _ S) (map_mul (kcAbs k) σ τ)).trans (map_mul (resAbs _ S) _ _)

/-- `kcGalHom` on elements: the restriction of `kcAbs σ`. Kind: PROVED. -/
theorem kcGalHom_apply (σ : galK (sqrtK k)) :
    kcGalHom k S σ = resAbs (QuadraticField k) S (kcAbs k σ) :=
  rfl

/-- **`kcEmb (kcGalHom σ x) = σ (kcEmb x)`.** Kind: PROVED. -/
theorem kcEmb_kcGalHom (σ : galK (sqrtK k)) (x : KS (QuadraticField k) S) :
    kcEmb k S (galS _ S (kcGalHom k S σ) x) = (σ : AbsoluteGaloisGroup ℚ) (kcEmb k S x) := by
  rw [kcEmb_apply, kcEmb_apply, ← kcClosureEquiv_kcAbs]
  congr 1
  exact resAbs_apply_coe (QuadraticField k) S (kcAbs k σ) x

/-- A finite subextension `E` of `L/K` has a finite family of elements such that every
automorphism fixing the family lies in the fixing subgroup of `E` (a spanning family).
Kind: PROVED. -/
theorem kc_exists_fix {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [FiniteDimensional K E] :
    ∃ (n : ℕ) (s : Fin n → L),
      ∀ g : L ≃ₐ[K] L, (∀ i, g (s i) = s i) → g ∈ E.fixingSubgroup := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := K) (M := E)
  refine ⟨n, fun i => (s i : L), fun g hg => ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have key := LinearMap.ext_on_range hs
    (f := (g.toAlgHom.comp E.val).toLinearMap) (g := E.val.toLinearMap) hg
  exact LinearMap.congr_fun key ⟨x, hx⟩

/-- **`kcGalHom` is continuous** (Krull topologies): the preimage of the fixing subgroup of a
finite subextension of `K_S` contains the stabilizer in `G_K` of the images in `ℚˢ` of a finite
spanning family. Kind: PROVED. -/
theorem kcGalHom_continuous : Continuous (kcGalHom k S) := by
  refine continuous_of_continuousAt_one (kcGalHom k S) ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨E, hE, hEU⟩ :=
    (krullTopology_mem_nhds_one_iff (QuadraticField k) (KS (QuadraticField k) S) U).mp hU
  obtain ⟨n, s, hs⟩ := kc_exists_fix E
  let V : Set (galK (sqrtK k)) := ⋂ i, Subtype.val ⁻¹'
    (MulAction.stabilizer (AbsoluteGaloisGroup ℚ) (kcEmb k S (s i)) :
      Set (AbsoluteGaloisGroup ℚ))
  have hVo : IsOpen V := isOpen_iInter_of_finite fun i =>
    (stabilizer_isOpen_of_isIntegral _).preimage continuous_subtype_val
  have h1V : (1 : galK (sqrtK k)) ∈ V :=
    Set.mem_iInter.mpr fun i => (MulAction.stabilizer _ _).one_mem
  refine Filter.mem_map.mpr (Filter.mem_of_superset (hVo.mem_nhds h1V) fun σ hσ => hEU ?_)
  refine hs (galS _ S (kcGalHom k S σ)) fun i => kcEmb_injective k S ?_
  rw [kcEmb_kcGalHom]
  exact MulAction.mem_stabilizer_iff.mp (Set.mem_iInter.mp hσ i)

/-- **The Galois comparison `G_K →ₜ* G_{K,S}`**: `σ ↦` the restriction to `K_S` of the transport
of `σ` to `K̄` along `kcClosureEquiv` (`σ` fixes `K` since it fixes `√k`). Kind: definition. -/
def kcGal : galK (sqrtK k) →ₜ* GKS (QuadraticField k) S :=
  { kcGalHom k S with continuous_toFun := kcGalHom_continuous k S }

/-- `kcGal` is `kcGalHom`. Kind: PROVED. -/
theorem kcGal_apply (σ : galK (sqrtK k)) : kcGal k S σ = kcGalHom k S σ :=
  rfl

/-- **`kcEmb (kcGal σ x) = σ (kcEmb x)`** for `σ ∈ G_K`, `x ∈ K_S`. Kind: PROVED. -/
theorem kcEmb_kcGal (σ : galK (sqrtK k)) (x : KS (QuadraticField k) S) :
    kcEmb k S (galS _ S (kcGal k S σ) x) = (σ : AbsoluteGaloisGroup ℚ) (kcEmb k S x) :=
  kcEmb_kcGalHom k S σ x

/-- `kcGal` is continuous. Kind: PROVED. -/
theorem kcGal_continuous : Continuous (kcGal k S) :=
  (kcGal k S).continuous

/-- **`kcGal` is surjective**: an element of `G_{K,S}` lifts to `Gal(K̄/K)`, whose transport to
`ℚˢ` fixes `√k`. Kind: PROVED. -/
theorem kcGal_surjective : Function.Surjective (kcGal k S) := by
  intro g
  obtain ⟨τ, hτ⟩ := resAbs_surjective (QuadraticField k) S g
  let σ' : SeparableClosure ℚ ≃ₐ[QuadraticField k] SeparableClosure ℚ :=
    (kcClosureEquiv k).autCongr τ
  let σ : AbsoluteGaloisGroup ℚ :=
    { σ'.toRingEquiv with commutes' := fun q => by simp }
  have hσ : σ ∈ galK (sqrtK k) :=
    mem_galK.mpr (σ'.commutes ⟨sqrtK k, IntermediateField.mem_adjoin_simple_self ℚ (sqrtK k)⟩)
  refine ⟨⟨σ, hσ⟩, ?_⟩
  rw [kcGal_apply, kcGalHom_apply, ← hτ]
  congr 1
  ext y
  simp [kcAbs, AlgEquiv.autCongr_apply, kcAutK_apply, σ, σ']

end Galois

/-! ### Points and torsion -/

section Points

variable (k : ℤ) (S : Set (HeightOneSpectrum (𝓞 (QuadraticField k)))) (E : WeierstrassCurve ℚ)

/-- **The points of `E_K` over `ℚˢ` are the coefficient module `E(ℚˢ)`**: the base change of
`E_K = E ×_ℚ K` to `ℚˢ` along `K ⊂ ℚˢ` is the base change of `E` to `ℚˢ` (definitionally), so
this is `E.pointCoeffEquiv`. Kind: definition. -/
def kcCoeffEquiv :
    ((E.baseChange (QuadraticField k)).baseChange (SeparableClosure ℚ)).toAffine.Point ≃+
      E.PointCoeff :=
  E.pointCoeffEquiv

/-- **The action of `σ ∈ G_K` on `E(ℚˢ)`** is the point map along the `K`-automorphism
`kcAutK σ`. Kind: PROVED. -/
theorem kcCoeffEquiv_smul (σ : galK (sqrtK k))
    (Q : ((E.baseChange (QuadraticField k)).baseChange (SeparableClosure ℚ)).toAffine.Point) :
    (σ : AbsoluteGaloisGroup ℚ) • kcCoeffEquiv k E Q =
      kcCoeffEquiv k E (Affine.Point.map (W' := E.baseChange (QuadraticField k))
        (kcAutK k σ).toAlgHom Q) := by
  rcases Q with _ | ⟨x, y, h⟩ <;> rfl

/-- **The point map `E(K_S) → E(ℚˢ)`** along `kcEmb`, read in the coefficient module
`E.PointCoeff` (the base change of `E_K` to `ℚˢ` along `K ⊂ ℚˢ` is the base change of `E`).
Kind: definition. -/
def kcPt : Pt (QuadraticField k) S (E.baseChange (QuadraticField k)) →+ E.PointCoeff :=
  (kcCoeffEquiv k E).toAddMonoidHom.comp
    (Affine.Point.map (W' := E.baseChange (QuadraticField k)) (kcEmb k S))

/-- `kcPt` is the point map along `kcEmb`, read through `kcCoeffEquiv`. Kind: PROVED. -/
theorem kcPt_apply (P : Pt (QuadraticField k) S (E.baseChange (QuadraticField k))) :
    kcPt k S E P = kcCoeffEquiv k E
      (Affine.Point.map (W' := E.baseChange (QuadraticField k)) (kcEmb k S) P) :=
  rfl

/-- `kcPt` on coordinates. Kind: PROVED. -/
theorem kcPt_some {x y : KS (QuadraticField k) S}
    (h : ((E.baseChange (QuadraticField k)).baseChange
      (KS (QuadraticField k) S)).toAffine.Nonsingular x y) :
    kcPt k S E (.some x y h) = E.pointCoeffEquiv (.some (kcEmb k S x) (kcEmb k S y)
      (((E.baseChange (QuadraticField k)).toAffine.baseChange_nonsingular
        (kcEmb_injective k S) x y).mpr h)) :=
  rfl

/-- `kcPt` is injective. Kind: PROVED. -/
theorem kcPt_injective : Function.Injective (kcPt k S E) :=
  (kcCoeffEquiv k E).injective.comp (Affine.Point.map_injective (kcEmb k S))

/-- **Equivariance of the point map** along `kcGal`: `kcPt (kcGal σ • P) = σ • kcPt P`.
Kind: PROVED. -/
theorem kcPt_smul (σ : galK (sqrtK k))
    (P : Pt (QuadraticField k) S (E.baseChange (QuadraticField k))) :
    kcPt k S E (Affine.Point.map (galS _ S (kcGal k S σ)).toAlgHom P) =
      (σ : AbsoluteGaloisGroup ℚ) • kcPt k S E P := by
  rcases P with _ | ⟨x, y, hxy⟩
  · rw [← Affine.Point.zero_def, map_zero, map_zero, smul_zero]
  · rw [Affine.Point.map_some, kcPt_some, kcPt_some, smul_pointCoeffEquiv]
    congr 1
    exact some_eq_some (kcEmb_kcGal k S σ x) (kcEmb_kcGal k S σ y) _ _

variable (m : ℕ)

/-- **The torsion comparison `E(K_S)[2^m] → E(ℚˢ)[2^m]`**, the restriction of `kcPt`.
Kind: definition. -/
def kcLev :
    Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m →+ E.TorsionCoeff (2 ^ m) where
  toFun P := ⟨kcPt k S E (P : Pt _ S _), by
    rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul, two_pow_nsmul_lev P, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add (kcPt k S E) _ _)

/-- `kcLev` on underlying points. Kind: PROVED. -/
theorem coe_kcLev (P : Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m) :
    ((kcLev k S E m P : E.TorsionCoeff (2 ^ m)) : E.PointCoeff) = kcPt k S E (P : Pt _ S _) :=
  rfl

/-- **`kcLev` is equivariant along `kcGal`**: `kcLev (kcGal σ • P) = σ • kcLev P`.
Kind: PROVED. -/
theorem kcLev_smul (σ : galK (sqrtK k))
    (P : Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m) :
    kcLev k S E m (kcGal k S σ • P) = σ • kcLev k S E m P := by
  apply Subtype.ext
  rw [coe_kcLev, smul_lev_coe, kcPt_smul, Subgroup.smul_def, coe_smul_torsionCoeff, coe_kcLev]

/-- `kcLev` is injective. Kind: PROVED. -/
theorem kcLev_injective : Function.Injective (kcLev k S E m) := fun _ _ h =>
  Subtype.ext (kcPt_injective k S E (congrArg Subtype.val h))

/-- **Under full `2^m`-torsion over `K_S`, `kcLev` is bijective**: both sides have `4^m`
points. Kind: PROVED. -/
theorem kcLev_bijective [E.IsElliptic]
    (hFull : FullTorsion (QuadraticField k) S (E.baseChange (QuadraticField k)) (2 ^ m)) :
    Function.Bijective (kcLev k S E m) := by
  have hu : IsUnit ((2 ^ m : ℕ) : ℚ) := isUnit_iff_ne_zero.mpr (by positivity)
  exact (kcLev_injective k S E m).bijective_of_nat_card_le
    (by rw [E.natCard_torsionCoeff hu, hFull])

/-- **The identification `E(K_S)[2^m] ≃ E(ℚˢ)[2^m]`** under full `2^m`-torsion over `K_S`.
Kind: definition. -/
def kcLevEquiv [E.IsElliptic]
    (hFull : FullTorsion (QuadraticField k) S (E.baseChange (QuadraticField k)) (2 ^ m)) :
    Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m ≃+ E.TorsionCoeff (2 ^ m) :=
  AddEquiv.ofBijective (kcLev k S E m) (kcLev_bijective k S E m hFull)

/-- `kcLevEquiv` is `kcLev`. Kind: PROVED. -/
theorem kcLevEquiv_apply [E.IsElliptic]
    (hFull : FullTorsion (QuadraticField k) S (E.baseChange (QuadraticField k)) (2 ^ m))
    (P : Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m) :
    kcLevEquiv k S E m hFull P = kcLev k S E m P :=
  rfl

/-- **The inverse identification is equivariant**: `kcLev⁻¹ (σ • t) = kcGal σ • kcLev⁻¹ t`.
Kind: PROVED. -/
theorem kcLevEquiv_symm_smul [E.IsElliptic]
    (hFull : FullTorsion (QuadraticField k) S (E.baseChange (QuadraticField k)) (2 ^ m))
    (σ : galK (sqrtK k)) (t : E.TorsionCoeff (2 ^ m)) :
    (kcLevEquiv k S E m hFull).symm (σ • t) = kcGal k S σ • (kcLevEquiv k S E m hFull).symm t := by
  apply (kcLevEquiv k S E m hFull).injective
  rw [AddEquiv.apply_symm_apply, kcLevEquiv_apply, kcLev_smul, ← kcLevEquiv_apply k S E m hFull,
    AddEquiv.apply_symm_apply]

/-- **The comparison `E(K_S)[2^m] → E(ℚˢ)[2^∞]`**: `kcLev` followed by the inclusion
`levelCoeffToInfinite`. Kind: definition. -/
def kcLevInf :
    Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m →+ TwoPowerCoeff E :=
  (ZInQ.Contrib.RC53Assist.DiskOrders.Limit.levelCoeffToInfinite (sqrtK k) E m).toAddMonoidHom.comp
    (kcLev k S E m)

/-- `kcLevInf` on underlying points. Kind: PROVED. -/
theorem coe_kcLevInf (P : Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m) :
    ((kcLevInf k S E m P : TwoPowerCoeff E) : E.PointCoeff) = kcPt k S E (P : Pt _ S _) :=
  rfl

/-- `kcLevInf` is `levelCoeffToInfinite ∘ kcLev`. Kind: PROVED. -/
theorem kcLevInf_eq (P : Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m) :
    kcLevInf k S E m P =
      ZInQ.Contrib.RC53Assist.DiskOrders.Limit.levelCoeffToInfinite (sqrtK k) E m
        (kcLev k S E m P) :=
  rfl

/-- **`kcLevInf` is equivariant along `kcGal`**. Kind: PROVED. -/
theorem kcLevInf_smul (σ : galK (sqrtK k))
    (P : Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m) :
    kcLevInf k S E m (kcGal k S σ • P) = σ • kcLevInf k S E m P := by
  rw [kcLevInf_eq, kcLevInf_eq, kcLev_smul, map_smul]

end Points

/-! ### The cochain maps -/

section Cochains

attribute [local instance] levTop continuousSMul_lev

variable (k : ℤ) (S : Set (HeightOneSpectrum (𝓞 (QuadraticField k)))) (E : WeierstrassCurve ℚ)
  (m : ℕ)

/-- **The cochain map `C^•(G_{K,S}, E(K_S)[2^m]) → C^•(G_K, E(ℚˢ)[2^m])`** of the compatible
pair `(kcGal, kcLev)`: `c ↦ kcLev ∘ c ∘ kcGalⁿ`. Kind: definition. -/
def kcInfl :
    contCochains ℤ (GKS (QuadraticField k) S)
        (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m) ⟶
      contCochains ℤ (galK (sqrtK k)) (E.TorsionCoeff (2 ^ m)) :=
  contCochainsMap (kcGal k S) (kcLev k S E m).toIntLinearMap continuous_of_discreteTopology
    (fun σ P => kcLev_smul k S E m σ P)

/-- `kcInfl` on cochains: `kcInfl c (x) = kcLev (c (kcGal ∘ x))`. Kind: PROVED. -/
theorem kcInfl_apply (n : ℕ)
    (c : (contCochains ℤ (GKS (QuadraticField k) S)
      (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m)).X n)
    (x : Fin n → galK (sqrtK k)) :
    asFun ℤ (galK (sqrtK k)) (E.TorsionCoeff (2 ^ m))
        (((contSubCx ℤ (galK (sqrtK k)) (E.TorsionCoeff (2 ^ m))).el
          (((kcInfl k S E m).f n).hom c) : contCochain ℤ _ _ n) :
          (groupCohomology.inhomogeneousCochains (rep ℤ _ _)).X n) x =
      kcLev k S E m (asFun ℤ (GKS (QuadraticField k) S)
        (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m)
        ((contSubCx ℤ (GKS (QuadraticField k) S)
          (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m)).el c :
            contCochain ℤ _ _ n) (kcGal k S ∘ x)) :=
  rfl

/-- **The cochain map `C^•(G_{K,S}, E(K_S)[2^m]) → C^•(G_K, E(ℚˢ)[2^∞])`** of the compatible
pair `(kcGal, kcLevInf)`. Kind: definition. -/
def kcInflInf :
    contCochains ℤ (GKS (QuadraticField k) S)
        (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m) ⟶
      contCochains ℤ (galK (sqrtK k)) (TwoPowerCoeff E) :=
  contCochainsMap (kcGal k S) (kcLevInf k S E m).toIntLinearMap continuous_of_discreteTopology
    (fun σ P => kcLevInf_smul k S E m σ P)

/-- `kcInflInf` on cochains: `kcInflInf c (x) = kcLevInf (c (kcGal ∘ x))`. Kind: PROVED. -/
theorem kcInflInf_apply (n : ℕ)
    (c : (contCochains ℤ (GKS (QuadraticField k) S)
      (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m)).X n)
    (x : Fin n → galK (sqrtK k)) :
    asFun ℤ (galK (sqrtK k)) (TwoPowerCoeff E)
        (((contSubCx ℤ (galK (sqrtK k)) (TwoPowerCoeff E)).el
          (((kcInflInf k S E m).f n).hom c) : contCochain ℤ _ _ n) :
          (groupCohomology.inhomogeneousCochains (rep ℤ _ _)).X n) x =
      kcLevInf k S E m (asFun ℤ (GKS (QuadraticField k) S)
        (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m)
        ((contSubCx ℤ (GKS (QuadraticField k) S)
          (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m)).el c :
            contCochain ℤ _ _ n) (kcGal k S ∘ x)) :=
  rfl

open CategoryTheory in
/-- **`kcInflInf` factors through `kcInfl`**: it is `kcInfl` followed by the coefficient
inclusion `E(ℚˢ)[2^m] → E(ℚˢ)[2^∞]` (`levelCoeffToInfinite`). Kind: PROVED. -/
theorem kcInflInf_eq_comp : kcInfl k S E m ≫
      (contCochainsMap (ContinuousMonoidHom.id (galK (sqrtK k)))
        (ZInQ.Contrib.RC53Assist.DiskOrders.Limit.levelCoeffToInfinite (sqrtK k) E
          m).toAddMonoidHom.toIntLinearMap continuous_of_discreteTopology
        (fun g P => (ZInQ.Contrib.RC53Assist.DiskOrders.Limit.levelCoeffToInfinite (sqrtK k) E
          m).map_smul g P)) = kcInflInf k S E m := by
  ext n c
  rfl

end Cochains

/-! ### Rational points: Galois descent along `K ⊂ ℚˢ` -/

section Rational

variable (k : ℤ) (E : WeierstrassCurve ℚ)

/-- A ring automorphism of `ℚˢ` fixing `√k`, as an element of `G_K`. Kind: definition. -/
def kcOfRingEquiv (f : SeparableClosure ℚ ≃+* SeparableClosure ℚ) (hf : f (sqrtK k) = sqrtK k) :
    galK (sqrtK k) :=
  ⟨{ f with commutes' := fun q => by simp }, mem_galK.mpr hf⟩

/-- `kcOfRingEquiv` on elements. Kind: PROVED. -/
theorem kcOfRingEquiv_apply (f : SeparableClosure ℚ ≃+* SeparableClosure ℚ)
    (hf : f (sqrtK k) = sqrtK k) (x : SeparableClosure ℚ) :
    (kcOfRingEquiv k f hf : AbsoluteGaloisGroup ℚ) x = f x :=
  rfl

/-- **Galois descent for elements**: an element of `ℚˢ` fixed by `G_K` lies in `K = ℚ(√k)`
(infinite Galois correspondence: the fixed field of the fixing subgroup of `ℚ(√k)` is `ℚ(√k)`).
Kind: PROVED. -/
theorem kc_mem_of_fixed {x : SeparableClosure ℚ}
    (hx : ∀ σ : galK (sqrtK k), (σ : AbsoluteGaloisGroup ℚ) x = x) :
    x ∈ IntermediateField.adjoin ℚ {sqrtK k} := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin ℚ {sqrtK k}),
    IntermediateField.mem_fixedField_iff]
  intro f hf
  exact hx (kcOfRingEquiv k f.toRingEquiv ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hf _
    (IntermediateField.mem_adjoin_simple_self ℚ (sqrtK k))))

/-- **The image `E(K) → E(ℚˢ)` of rational points**, the point map along `K ⊂ ℚˢ`.
Kind: definition. -/
def kcBasePt : (E.baseChange (QuadraticField k)).toAffine.Point →+ E.PointCoeff :=
  (kcCoeffEquiv k E).toAddMonoidHom.comp
    ((Affine.Point.map (W' := E.baseChange (QuadraticField k))
        (Algebra.ofId (QuadraticField k) (SeparableClosure ℚ))).comp
      (Affine.Point.equivBaseChangeSelf (E.baseChange (QuadraticField k)).toAffine).toAddMonoidHom)

/-- `kcBasePt` on points: the point map along `K ⊂ ℚˢ`. Kind: PROVED. -/
theorem kcBasePt_apply (P : (E.baseChange (QuadraticField k)).toAffine.Point) :
    kcBasePt k E P = kcCoeffEquiv k E (Affine.Point.map (W' := E.baseChange (QuadraticField k))
      (Algebra.ofId (QuadraticField k) (SeparableClosure ℚ))
      (Affine.Point.equivBaseChangeSelf (E.baseChange (QuadraticField k)).toAffine P)) :=
  rfl

/-- `kcBasePt` is injective. Kind: PROVED. -/
theorem kcBasePt_injective : Function.Injective (kcBasePt k E) :=
  (kcCoeffEquiv k E).injective.comp ((Affine.Point.map_injective _).comp
    (Affine.Point.equivBaseChangeSelf (E.baseChange (QuadraticField k)).toAffine).injective)

/-- **Rational points are fixed by `G_K`.** Kind: PROVED. -/
theorem kcBasePt_mem (P : (E.baseChange (QuadraticField k)).toAffine.Point) :
    kcBasePt k E P ∈ ZInQ.Contrib.RC53Assist.DiskOrders.Limit.pointsK (sqrtK k) E := by
  refine (FixedPoints.mem_addSubgroup _ _ _).mpr fun σ => ?_
  rw [Subgroup.smul_def, kcBasePt_apply, kcCoeffEquiv_smul, Affine.Point.map_map,
    Subsingleton.elim ((kcAutK k σ).toAlgHom.comp
      (Algebra.ofId (QuadraticField k) (SeparableClosure ℚ)))
      (Algebra.ofId (QuadraticField k) (SeparableClosure ℚ))]

/-- **Points of `E(ℚˢ)` fixed by `G_K` are rational over `K`** (Galois descent on the two
coordinates). Kind: PROVED. -/
theorem kcBasePt_surjective (P : E.PointCoeff)
    (hP : P ∈ ZInQ.Contrib.RC53Assist.DiskOrders.Limit.pointsK (sqrtK k) E) :
    ∃ Q : (E.baseChange (QuadraticField k)).toAffine.Point, kcBasePt k E Q = P := by
  obtain ⟨P, rfl⟩ := (kcCoeffEquiv k E).surjective P
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨0, map_zero _⟩
  · have hfix : ∀ σ : galK (sqrtK k),
        (σ : AbsoluteGaloisGroup ℚ) x = x ∧ (σ : AbsoluteGaloisGroup ℚ) y = y := fun σ => by
      have h1 := (FixedPoints.mem_addSubgroup _ _ _).mp hP σ
      rw [Subgroup.smul_def, kcCoeffEquiv_smul, Affine.Point.map_some] at h1
      have h2 := (kcCoeffEquiv k E).injective h1
      simp only [Affine.Point.some.injEq] at h2
      exact ⟨h2.1, h2.2⟩
    let x₀ : QuadraticField k := ⟨x, kc_mem_of_fixed k fun σ => (hfix σ).1⟩
    let y₀ : QuadraticField k := ⟨y, kc_mem_of_fixed k fun σ => (hfix σ).2⟩
    have h₀ : ((E.baseChange (QuadraticField k)).baseChange
        (QuadraticField k)).toAffine.Nonsingular x₀ y₀ :=
      ((E.baseChange (QuadraticField k)).toAffine.baseChange_nonsingular
        (Algebra.ofId (QuadraticField k) (SeparableClosure ℚ)).injective x₀ y₀).mp h
    refine ⟨(Affine.Point.equivBaseChangeSelf (E.baseChange (QuadraticField k)).toAffine).symm
      (.some x₀ y₀ h₀), ?_⟩
    change kcCoeffEquiv k E (Affine.Point.map _ (Affine.Point.equivBaseChangeSelf _
      ((Affine.Point.equivBaseChangeSelf _).symm _))) = _
    rw [AddEquiv.apply_symm_apply, Affine.Point.map_some]
    rfl

/-- **`E(K) ≃ H⁰(G_K, E(ℚˢ))`**: the point map along `K ⊂ ℚˢ` onto the `G_K`-fixed points
(Galois descent). Kind: definition. -/
def kcPointsEquiv : (E.baseChange (QuadraticField k)).toAffine.Point ≃+
    ZInQ.Contrib.RC53Assist.DiskOrders.Limit.pointsK (sqrtK k) E :=
  AddEquiv.ofBijective ((kcBasePt k E).codRestrict _ (kcBasePt_mem k E))
    ⟨fun _ _ h => kcBasePt_injective k E (congrArg Subtype.val h), fun P => by
      obtain ⟨Q, hQ⟩ := kcBasePt_surjective k E P P.2
      exact ⟨Q, Subtype.ext hQ⟩⟩

/-- `kcPointsEquiv` is `kcBasePt`. Kind: PROVED. -/
theorem coe_kcPointsEquiv (P : (E.baseChange (QuadraticField k)).toAffine.Point) :
    ((kcPointsEquiv k E P : ZInQ.Contrib.RC53Assist.DiskOrders.Limit.pointsK (sqrtK k) E) :
      E.PointCoeff) = kcBasePt k E P :=
  rfl

/-- **Compatibility with the image `E(K) → E(K_S)`**: `kcPt (pointToKS P) = kcPointsEquiv P`.
Kind: PROVED. -/
theorem kcPt_pointToKS (S : Set (HeightOneSpectrum (𝓞 (QuadraticField k))))
    (P : (E.baseChange (QuadraticField k)).toAffine.Point) :
    kcPt k S E (CalPoint.pointToKS S (E.baseChange (QuadraticField k)) P) =
      ((kcPointsEquiv k E P : ZInQ.Contrib.RC53Assist.DiskOrders.Limit.pointsK (sqrtK k) E) :
        E.PointCoeff) := by
  have hP : CalPoint.pointToKS S (E.baseChange (QuadraticField k)) P =
      Affine.Point.map (W' := E.baseChange (QuadraticField k))
        (Algebra.ofId (QuadraticField k) (KS (QuadraticField k) S))
        (Affine.Point.equivBaseChangeSelf (E.baseChange (QuadraticField k)).toAffine P) :=
    rfl
  rw [coe_kcPointsEquiv, kcBasePt_apply, kcPt_apply, hP, Affine.Point.map_map,
    Subsingleton.elim ((kcEmb k S).comp
    (Algebra.ofId (QuadraticField k) (KS (QuadraticField k) S)))
    (Algebra.ofId (QuadraticField k) (SeparableClosure ℚ))]

end Rational

end ZInQ.Manuscript.RC
