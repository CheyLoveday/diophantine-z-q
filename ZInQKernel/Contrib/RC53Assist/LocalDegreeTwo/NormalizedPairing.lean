import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.StageInputs
import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.StageFlat
import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.Conjugation
import ZInQKernel.Contrib.RC53Assist.DerivedKummer.LocalDuality
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TauCetiComparison
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Brauer.CharacterFormula
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Local.Unramified
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.StageArith
import ZInQKernel.Contrib.OneProof.RC.Limits.GradedConeDual
import ZInQKernel.Contrib.OneProof.RC.Limits.GradedFiniteFree
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.DualQuasiIso
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.CompKummer

/-!
# Normalized arithmetic and the retained split-stage pairing

This is a standalone expanded edition. It retains the earlier declarations
and adds the local invariant formula, Hilbert 90 elimination, and cochain
pairing and trace transport. The earlier source edition is not altered.

The Kummer--Brauer injectivity elimination was found in an independent review.
The same chosen tame orientation is retained in degrees one and two.
-/

/-!
# Normalized degree-two coordinates at derivative primes

The coordinate is obtained from the local Brauer invariant. Its orientation is
fixed by the cup product of the arithmetic unramified character and the Kummer
character of a uniformizer. Finite coefficient extension is performed on the
continuous cochains themselves, not on an unrelated finite complex.

The coefficient rings are the finite Frobenius rings
`(ℤ/2^iℤ)[t]/t^i`. Self-injectivity extends the scalar invariant from cocycles
to all degree-two cochains. No splitting of a module over a field is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.LocalDegreeTwo

open CategoryTheory Module
open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open scoped TensorProduct

/-- A scalar coefficient module with trivial Galois action. -/
def ScalarCoeff (S : Type) : Type := S

instance (S : Type) [CommRing S] : AddCommGroup (ScalarCoeff S) :=
  inferInstanceAs (AddCommGroup S)

instance (S : Type) [CommRing S] : Module S (ScalarCoeff S) :=
  inferInstanceAs (Module S S)

instance (S : Type) : TopologicalSpace (ScalarCoeff S) := ⊥

instance (S : Type) : DiscreteTopology (ScalarCoeff S) := ⟨rfl⟩

instance (S : Type) [CommRing S] : ContinuousAdd (ScalarCoeff S) :=
  ⟨continuous_of_discreteTopology⟩

instance (S : Type) [CommRing S] : ContinuousConstSMul S (ScalarCoeff S) :=
  ⟨fun _ => continuous_of_discreteTopology⟩

instance (G S : Type) [Group G] [CommRing S] : DistribMulAction G (ScalarCoeff S) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

instance (G S : Type) [Group G] [CommRing S] : SMulCommClass G S (ScalarCoeff S) :=
  ⟨fun _ _ _ => rfl⟩

instance (G S : Type) [Group G] [TopologicalSpace G] [CommRing S] :
    ContinuousSMul G (ScalarCoeff S) := ⟨continuous_snd⟩

/-- Forgetting the scalar coefficient tag preserves the scalar module. -/
def ScalarCoeff.equiv (S : Type) [CommRing S] : ScalarCoeff S ≃ₗ[S] S :=
  LinearEquiv.refl S S

section CoefficientExtension

variable {S R G M : Type} [CommRing S] [CommRing R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [Module R M] [Module S M]
  [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- Evaluation of a continuous cochain at a tuple. -/
def cochainEval {n : ℕ} (v : Fin n → G) : (contCochains R G M).X n →ₗ[R] M where
  toFun z := contFun z v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A scalar coordinate of a continuous cochain. -/
def scalarCochain {n : ℕ} (f : M →ₗ[S] S) (z : (contCochains R G M).X n) :
    (contCochains S G (ScalarCoeff S)).X n :=
  (contSubCx S G (ScalarCoeff S)).ofSub
    ⟨fun v => (show ScalarCoeff S from f (contFun z v)),
      (continuous_of_discreteTopology : Continuous (fun m : M =>
        (show ScalarCoeff S from f m))).comp ((contSubCx R G M).el z).2⟩

/-- The scalar cochain applies the coefficient functional pointwise. -/
theorem scalarCochain_eval {n : ℕ} (f : M →ₗ[S] S) (z : (contCochains R G M).X n)
    (v : Fin n → G) :
    (show S from contFun (k := S) (G := G) (M := ScalarCoeff S)
      (scalarCochain f z) v) = f (contFun z v) := rfl

/-- Scalar coordinates respect addition of cochains. -/
theorem scalarCochain_add {n : ℕ} (f : M →ₗ[S] S)
    (z w : (contCochains R G M).X n) :
    scalarCochain f (z + w) = scalarCochain f z + scalarCochain f w := by
  apply contCochains_ext
  intro v
  exact map_add f _ _

/-- Scalar coordinates of the zero cochain vanish. -/
theorem scalarCochain_zero {n : ℕ} (f : M →ₗ[S] S) :
    scalarCochain f (0 : (contCochains R G M).X n) = 0 := by
  apply contCochains_ext
  intro v
  exact map_zero f

variable {ι : Type} [Fintype ι] (b : Basis ι S M)

/-- Finite coefficient decomposition of a scalar functional on cochains. -/
theorem scalarCochain_basis_expansion {n : ℕ} (f : M →ₗ[S] S)
    (z : (contCochains R G M).X n) :
    scalarCochain f z = ∑ j, f (b j) • scalarCochain (b.coord j) z := by
  apply contCochains_ext
  intro v
  change f (contFun z v) = (show S from cochainEval (R := S) (M := ScalarCoeff S) v
    (∑ j, f (b j) • scalarCochain (b.coord j) z))
  rw [map_sum]
  simp only [map_smul]
  change f (contFun z v) = ∑ j, f (b j) * b.coord j (contFun z v)
  conv_lhs => rw [← b.sum_repr (contFun z v)]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, smul_eq_mul, Basis.coord_apply, mul_comm]

variable (c : (contCochains S G (ScalarCoeff S)).X 2 →ₗ[S] S)

/-- Applying the scalar invariant in every finite coefficient coordinate. -/
def coefficientValue (z : (contCochains R G M).X 2) : M :=
  ∑ j, c (scalarCochain (b.coord j) z) • b j

/-- Every scalar functional reads the same invariant of the corresponding
scalar-valued cochain. -/
theorem coefficientValue_functional (f : M →ₗ[S] S)
    (z : (contCochains R G M).X 2) :
    f (coefficientValue b c z) = c (scalarCochain f z) := by
  rw [coefficientValue, map_sum, scalarCochain_basis_expansion b, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]

/-- In a chosen basis the vector invariant is the scalar invariant of each
coordinate. -/
theorem coefficientValue_coord (j : ι) (z : (contCochains R G M).X 2) :
    b.coord j (coefficientValue b c z) = c (scalarCochain (b.coord j) z) :=
  coefficientValue_functional b c (b.coord j) z

variable [SMulCommClass R S M]

/-- Finite coefficient extension is linear over the full coefficient ring,
not merely over the residue scalars. -/
def coefficientCoordinate : (contCochains R G M).X 2 →ₗ[R] M where
  toFun := coefficientValue b c
  map_add' z w := by
    apply b.repr.injective
    ext j
    change b.coord j (coefficientValue b c (z + w)) =
      b.coord j (coefficientValue b c z + coefficientValue b c w)
    rw [map_add, coefficientValue_coord, coefficientValue_coord, coefficientValue_coord,
      scalarCochain_add, map_add]
  map_smul' r z := by
    apply b.repr.injective
    ext j
    let f : M →ₗ[S] S :=
      { toFun := fun m => b.coord j (r • m)
        map_add' := fun x y => by rw [smul_add, map_add]
        map_smul' := fun a m => by rw [smul_comm r a, map_smul]; rfl }
    change b.coord j (coefficientValue b c (r • z)) = f (coefficientValue b c z)
    rw [coefficientValue_coord, coefficientValue_functional]
    congr 1

variable (htriv : ∀ (g : G) (m : M), g • m = m)

omit [SMulCommClass R S M] in
include htriv in
/-- A scalar coordinate commutes with the differential in degree one. -/
theorem scalarCochain_d12 (f : M →ₗ[S] S) (a : (contCochains R G M).X 1) :
    scalarCochain f (((contCochains R G M).d 1 2).hom a) =
      ((contCochains S G (ScalarCoeff S)).d 1 2).hom (scalarCochain f a) := by
  apply contCochains_ext
  intro v
  have hv : v = ![v 0, v 1] := by funext j; fin_cases j <;> rfl
  rw [hv]
  change f (contFun (((contCochains R G M).d 1 2).hom a) ![v 0, v 1]) = _
  rw [contFun_d12, contFun_d12]
  change f (v 0 • contFun a (fun _ => v 1) - contFun a (fun _ => v 0 * v 1) +
      contFun a (fun _ => v 0)) =
    f (contFun a (fun _ => v 1)) - f (contFun a (fun _ => v 0 * v 1)) +
      f (contFun a (fun _ => v 0))
  rw [htriv, map_add, map_sub]

omit [SMulCommClass R S M] in
include htriv in
/-- A scalar coordinate commutes with the differential in degree two. -/
theorem scalarCochain_d23 (f : M →ₗ[S] S) (z : (contCochains R G M).X 2) :
    scalarCochain f (((contCochains R G M).d 2 3).hom z) =
      ((contCochains S G (ScalarCoeff S)).d 2 3).hom (scalarCochain f z) := by
  apply contCochains_ext
  intro v
  have hv : v = ![v 0, v 1, v 2] := by funext j; fin_cases j <;> rfl
  rw [hv]
  change f (contFun (((contCochains R G M).d 2 3).hom z) ![v 0, v 1, v 2]) = _
  rw [contFun_d23, contFun_d23]
  change f (v 0 • contFun z ![v 1, v 2] - contFun z ![v 0 * v 1, v 2] +
      contFun z ![v 0, v 1 * v 2] - contFun z ![v 0, v 1]) =
    f (contFun z ![v 1, v 2]) - f (contFun z ![v 0 * v 1, v 2]) +
      f (contFun z ![v 0, v 1 * v 2]) - f (contFun z ![v 0, v 1])
  rw [htriv, map_sub, map_add, map_sub]

omit [Fintype ι] [SMulCommClass R S M] in
/-- Scalar coordinates in a finite basis detect equality of cochains. -/
theorem cochain_eq_of_scalar_coordinates {n : ℕ} {z w : (contCochains R G M).X n}
    (h : ∀ j, scalarCochain (b.coord j) z = scalarCochain (b.coord j) w) : z = w := by
  apply contCochains_ext
  intro v
  apply b.repr.injective
  ext j
  exact congrArg (fun a => (show S from contFun (k := S) (G := G)
    (M := ScalarCoeff S) a v)) (h j)

/-- Reconstructing a cochain from its finite scalar coordinates. -/
def expandCochain {n : ℕ}
    (a : ι → (contCochains S G (ScalarCoeff S)).X n) : (contCochains R G M).X n :=
  (contSubCx R G M).ofSub
    ⟨fun v => ∑ j, ScalarCoeff.equiv S
        (contFun (k := S) (G := G) (M := ScalarCoeff S) (a j) v) • b j,
      continuous_finsetSum _ fun j _ =>
        (continuous_of_discreteTopology : Continuous (fun s : ScalarCoeff S =>
          ScalarCoeff.equiv S s • b j)).comp ((contSubCx S G (ScalarCoeff S)).el (a j)).2⟩

omit [SMulCommClass R S M] in
/-- A scalar coordinate of the reconstruction is the original cochain. -/
theorem scalarCochain_expand {n : ℕ}
    (a : ι → (contCochains S G (ScalarCoeff S)).X n) (j : ι) :
    scalarCochain (b.coord j) (expandCochain (R := R) b a) = a j := by
  classical
  apply contCochains_ext
  intro v
  apply (ScalarCoeff.equiv S).injective
  change b.coord j (∑ k, ScalarCoeff.equiv S
    (contFun (k := S) (G := G) (M := ScalarCoeff S) (a k) v) • b k) =
      ScalarCoeff.equiv S (contFun (k := S) (G := G) (M := ScalarCoeff S) (a j) v)
  simp [map_smul, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, smul_eq_mul]

include htriv in
/-- The scalar coordinate induces the full finite-coefficient degree-two
coordinate, including both kernel exactness and surjectivity. -/
theorem coefficientCoordinate_isCoordinate
    (hc : LocalDegreeTwoCoordinate (M := ScalarCoeff S) c) :
    LocalDegreeTwoCoordinate (coefficientCoordinate (R := R) b c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    apply b.repr.injective
    ext j
    change b.coord j (coefficientValue b c (((contCochains R G M).d 1 2).hom a)) =
      b.coord j (0 : M)
    rw [map_zero, coefficientValue_coord, scalarCochain_d12 htriv]
    exact hc.1 _
  · intro z hz hcz
    have hzj : ∀ j, ((contCochains S G (ScalarCoeff S)).d 2 3).hom
        (scalarCochain (b.coord j) z) = 0 := by
      intro j
      rw [← scalarCochain_d23 htriv, hz, scalarCochain_zero]
    have hczj : ∀ j, c (scalarCochain (b.coord j) z) = 0 := by
      intro j
      rw [← coefficientValue_coord]
      change b.coord j (coefficientCoordinate b c z) = 0
      rw [hcz, map_zero]
    choose a ha using fun j => hc.2.1 _ (hzj j) (hczj j)
    refine ⟨expandCochain b a, cochain_eq_of_scalar_coordinates b fun j => ?_⟩
    rw [scalarCochain_d12 htriv, scalarCochain_expand, ha]
  · intro m
    choose z hz hzm using fun j => hc.2.2 (show ScalarCoeff S from b.coord j m)
    refine ⟨expandCochain b z, ?_, ?_⟩
    · apply cochain_eq_of_scalar_coordinates b
      intro j
      rw [scalarCochain_d23 htriv, scalarCochain_expand, hz, scalarCochain_zero]
    · apply b.repr.injective
      ext j
      change b.coord j (coefficientValue b c (expandCochain b z)) = b.coord j m
      rw [coefficientValue_coord, scalarCochain_expand]
      exact hzm j

variable [Algebra S R] [IsScalarTower S R M]

/-- The scalar tame-symbol orientation is preserved by extension to the full
coefficient module. -/
theorem coefficientCoordinate_normalized (u κ : G → S)
    (hc : LocalDegreeTwoNormalized (M := ScalarCoeff S) c u κ) :
    LocalDegreeTwoNormalized (coefficientCoordinate (R := R) b c)
      (fun g => algebraMap S R (u g)) (fun g => algebraMap S R (κ g)) := by
  intro m z hz
  apply b.repr.injective
  ext j
  change b.coord j (coefficientValue b c z) = b.coord j m
  rw [coefficientValue_coord]
  apply hc (show ScalarCoeff S from b.coord j m) (scalarCochain (b.coord j) z)
  intro g h
  change b.coord j (evalTwo R M g h z) = (u g * κ h) * b.coord j m
  rw [hz, ← map_mul, algebraMap_smul, map_smul, smul_eq_mul]

end CoefficientExtension

/-- Scalar multiplication as a biadditive pairing. -/
def scalarPairing (n : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod n) M] :
    ScalarCoeff (ZMod n) →+ M →+ M where
  toFun a :=
    { toFun := fun m => ScalarCoeff.equiv (ZMod n) a • m
      map_zero' := smul_zero _
      map_add' := smul_add _ }
  map_zero' := by ext m; exact zero_smul (ZMod n) m
  map_add' a b := by ext m; exact add_smul _ _ m

section TameSymbol

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (n : ℕ) [NeZero n]

/-- The arithmetic unramified character, read on the separable closure. -/
def unramifiedCharacter (g : AbsoluteGaloisGroup F) : ZMod n :=
  urCharN F n ((absoluteGaloisGroupRestrictEquiv F).symm g)

/-- The unramified character is additive. -/
theorem unramifiedCharacter_mul (g h : AbsoluteGaloisGroup F) :
    unramifiedCharacter n (g * h) = unramifiedCharacter n g + unramifiedCharacter n h := by
  rw [unramifiedCharacter, map_mul, urCharN_mul]
  rfl

/-- The unramified character is continuous. -/
theorem unramifiedCharacter_continuous : Continuous (unramifiedCharacter (F := F) n) :=
  (continuous_urCharN (K := F) (n := n)).comp (absoluteGaloisGroupRestrictEquiv F).symm.continuous

/-- The unramified character as a scalar-valued continuous one-cocycle. -/
def unramifiedCocycle : Z1 (AbsoluteGaloisGroup F) (ScalarCoeff (ZMod n)) :=
  ⟨fun g => (ScalarCoeff.equiv (ZMod n)).symm (unramifiedCharacter n g),
    mem_Z1_iff.mpr ⟨(continuous_of_discreteTopology : Continuous
        (ScalarCoeff.equiv (ZMod n)).symm).comp (unramifiedCharacter_continuous n),
      fun g h => by
        change unramifiedCharacter n (g * h) = unramifiedCharacter n h + unramifiedCharacter n g
        rw [unramifiedCharacter_mul, add_comm]⟩⟩

/-- The associated rational-circle character. -/
def unramifiedCircleCharacter : Additive (AbsoluteGaloisGroup F) →+ AddCircle (1 : ℚ) :=
  (ZMod.toRatAddCircle n).comp
    { toFun := fun g => unramifiedCharacter n g.toMul
      map_zero' := by
        change urCharN F n ((absoluteGaloisGroupRestrictEquiv F).symm 1) = 0
        rw [map_one, urCharN_inertia (inertiaSubgroup F).one_mem]
      map_add' := fun g h => unramifiedCharacter_mul n g.toMul h.toMul }

/-- The rational-circle character has open kernel. -/
theorem unramifiedCircleCharacter_open :
    IsOpen ((unramifiedCircleCharacter (F := F) n).ker : Set (Additive (AbsoluteGaloisGroup F)))
      := by
  have hzero : IsOpen ({0} : Set (ZMod n)) := isOpen_discrete _
  have hcont : Continuous (fun g : Additive (AbsoluteGaloisGroup F) =>
      unramifiedCharacter n g.toMul) :=
    (unramifiedCharacter_continuous n).comp continuous_toMul
  have heq : ((unramifiedCircleCharacter (F := F) n).ker : Set (Additive (AbsoluteGaloisGroup F))) =
      (fun g => unramifiedCharacter n g.toMul) ⁻¹' {0} := by
    ext g
    simp [unramifiedCircleCharacter, AddMonoidHom.mem_ker, ZMod.toRatAddCircle_eq_zero]
  rw [heq]
  exact hzero.preimage hcont

/-- The carry of the circle character is the integral defect of the canonical
residue representatives. -/
theorem unramified_characterCarry (g h : AbsoluteGaloisGroup F) :
    (n : ℤ) * characterCarry (unramifiedCircleCharacter n) g h =
      (unramifiedCharacter n g).val + (unramifiedCharacter n h).val -
        (unramifiedCharacter n (g * h)).val := by
  have hn : (0 : ℚ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hrep (g : AbsoluteGaloisGroup F) :
      (AddCircle.equivIco 1 0 (unramifiedCircleCharacter n (Additive.ofMul g)) : ℚ) =
        (unramifiedCharacter n g).val / n := by
    change (AddCircle.equivIco 1 0 (ZMod.toRatAddCircle n (unramifiedCharacter n g)) : ℚ) = _
    rw [ZMod.toRatAddCircle_apply]
    apply AddCircle.equivIco_coe_of_mem
    refine ⟨by positivity, ?_⟩
    rw [zero_add, div_lt_one hn]
    exact_mod_cast ZMod.val_lt (unramifiedCharacter n g)
  have hc := intCast_characterCarry (unramifiedCircleCharacter n) g h
  rw [hrep, hrep, hrep] at hc
  have hq : (n : ℚ) * characterCarry (unramifiedCircleCharacter n) g h =
      (unramifiedCharacter n g).val + (unramifiedCharacter n h).val -
        (unramifiedCharacter n (g * h)).val := by
    rw [hc]
    field_simp
  exact_mod_cast hq

variable {n} (a : Fˣ) (β : (SeparableClosure F)ˣ)
  (hβ : β ^ n = Units.map (algebraMap F (SeparableClosure F)).toMonoidHom a)
  (hμ : ∀ (g : AbsoluteGaloisGroup F) (x : KummerCoeff F n), g • x = x)

/-- The unramified character cupped with the Kummer character of the chosen
root, through scalar multiplication. -/
def unramifiedKummerCup : Z2 (AbsoluteGaloisGroup F) (KummerCoeff F n) :=
  ZInQ.Contrib.CloudB3RC53.Duality.cupZ (scalarPairing n (KummerCoeff F n))
    (fun g x y => by rw [hμ g y, hμ g _]; rfl)
    (unramifiedCocycle n) ⟨kummerCocycle hβ, kummerCocycle_mem_Z1 hβ⟩

/-- The cup has the usual inhomogeneous formula with the unramified character
in the first argument. -/
theorem unramifiedKummerCup_apply (g h : AbsoluteGaloisGroup F) :
    (unramifiedKummerCup a β hβ hμ : AbsoluteGaloisGroup F × AbsoluteGaloisGroup F →
      KummerCoeff F n) (g, h) = (unramifiedCharacter n g).val • kummerCocycle hβ h := by
  change unramifiedCharacter n g • (g • kummerCocycle hβ h) = _
  rw [hμ]
  conv_lhs => rw [← ZMod.natCast_zmod_val (unramifiedCharacter n g)]
  exact Nat.cast_smul_eq_nsmul (ZMod n) _ _

/-- An explicit continuous primitive comparing the Kummer cup with the carry
class. The conjugated root is used to preserve the positive orientation. -/
def cupCarryPrimitive (g : AbsoluteGaloisGroup F) : UnitsCoeff F :=
  (unramifiedCharacter n g).val • (g • (Additive.ofMul β : UnitsCoeff F))

/-- The comparison primitive is continuous. -/
theorem cupCarryPrimitive_continuous : Continuous (cupCarryPrimitive (n := n) β) := by
  exact (continuous_of_discreteTopology : Continuous (fun p : ZMod n × UnitsCoeff F =>
    p.1.val • p.2)).comp
      ((unramifiedCharacter_continuous n).prodMk (continuous_id.smul continuous_const))

/-- The coefficient inclusion of the cup and the coboundary of the primitive
sum to the positively oriented carry cocycle. -/
theorem cupCarryPrimitive_identity (g h : AbsoluteGaloisGroup F) :
    d1 (AbsoluteGaloisGroup F) (UnitsCoeff F) (cupCarryPrimitive (n := n) β) (g, h) +
      kummerCoeffIncl F n
        ((unramifiedKummerCup a β hβ hμ : AbsoluteGaloisGroup F × AbsoluteGaloisGroup F →
          KummerCoeff F n) (g, h)) =
      characterCarry (unramifiedCircleCharacter n) g h •
        (baseUnitsEquivInvariants F (Additive.ofMul a) : UnitsCoeff F) := by
  let B : UnitsCoeff F := Additive.ofMul β
  let A : UnitsCoeff F := baseUnitsEquivInvariants F (Additive.ofMul a)
  have hnB : n • B = A := by
    apply Additive.toMul.injective
    change β ^ n = Units.map (algebraMap F (SeparableClosure F)).toMonoidHom a
    exact hβ
  have hfix : g • (h • B - B) = h • B - B := by
    rw [← kummerCoeffIncl_kummerCocycle hβ h, ← kummerCoeffIncl_equivariant, hμ]
  have hdiff : (g * h) • B - g • B = h • B - B := by
    rw [mul_smul, ← smul_sub]
    exact hfix
  have hngh : n • ((g * h) • B) = A := by
    rw [smul_comm, hnB]
    exact (FixedPoints.mem_addSubgroup _ _ _).mp
      (baseUnitsEquivInvariants F (Additive.ofMul a)).2 (g * h)
  rw [unramifiedKummerCup_apply, map_nsmul, kummerCoeffIncl_kummerCocycle, ← hdiff]
  change g • ((unramifiedCharacter n h).val • (h • B)) -
      (unramifiedCharacter n (g * h)).val • ((g * h) • B) +
      (unramifiedCharacter n g).val • (g • B) +
      (unramifiedCharacter n g).val • ((g * h) • B - g • B) =
        characterCarry (unramifiedCircleCharacter n) g h • A
  rw [smul_comm, ← mul_smul, nsmul_sub]
  simp only [← natCast_zsmul]
  calc
    _ = ((unramifiedCharacter n g).val + (unramifiedCharacter n h).val -
        (unramifiedCharacter n (g * h)).val : ℤ) • ((g * h) • B) := by
      rw [sub_smul, add_smul]
      abel
    _ = ((n : ℤ) * characterCarry (unramifiedCircleCharacter n) g h) • ((g * h) • B) := by
      rw [unramified_characterCarry]
    _ = characterCarry (unramifiedCircleCharacter n) g h • A := by
      rw [mul_comm, mul_zsmul, natCast_zsmul, hngh]

/-- The Kummer cup maps to the positively oriented carry class in the Brauer
coefficient module. -/
theorem unramifiedKummerCup_carry :
    explicitCoeff2 (AbsoluteGaloisGroup F) (KummerCoeff F n) (kummerCoeffInclHom F n)
        continuous_of_discreteTopology (H2pi _ _ (unramifiedKummerCup a β hβ hμ)) =
      H2pi (AbsoluteGaloisGroup F) (UnitsCoeff F)
        (characterCarryCocycle (unramifiedCircleCharacter n)
          (unramifiedCircleCharacter_open n) (baseUnitsEquivInvariants F (Additive.ofMul a))) := by
  change explicitCoeff2 (AbsoluteGaloisGroup F) (KummerCoeff F n) (kummerCoeffInclHom F n)
      continuous_of_discreteTopology (unramifiedKummerCup a β hβ hμ : H2 _ _) =
    (characterCarryCocycle (unramifiedCircleCharacter n)
      (unramifiedCircleCharacter_open n) (baseUnitsEquivInvariants F (Additive.ofMul a)) : H2 _ _)
  rw [explicitCoeff2_mk]
  apply H2pi_eq_iff.mpr
  apply mem_B2_iff.mpr
  refine ⟨fun g => -cupCarryPrimitive (n := n) β g,
    (cupCarryPrimitive_continuous (n := n) β).neg, ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  have hid := cupCarryPrimitive_identity a β hβ hμ g h
  simp only [Pi.sub_apply, cocyclesMap2_apply, characterCarryCocycle_apply]
  change d1 (AbsoluteGaloisGroup F) (UnitsCoeff F) (-cupCarryPrimitive (n := n) β) (g, h) =
    kummerCoeffIncl F n
      ((unramifiedKummerCup a β hβ hμ : AbsoluteGaloisGroup F × AbsoluteGaloisGroup F →
        KummerCoeff F n) (g, h)) -
      characterCarry (unramifiedCircleCharacter n) g h •
        (baseUnitsEquivInvariants F (Additive.ofMul a) : UnitsCoeff F)
  rw [map_neg, Pi.neg_apply, eq_sub_of_add_eq hid, neg_sub]

/-- The cup of the arithmetic unramified character and the Kummer character
of a uniformizer has invariant `1/n`. -/
theorem unramifiedKummerCup_invariant (ha : IsUniformizer F a) :
    invMap F (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr n
      (H2pi _ _ (unramifiedKummerCup a β hβ hμ))) =
        ((1 / n : ℚ) : AddCircle (1 : ℚ)) := by
  change invMap F (unitsRepH2Equiv F
    (explicitCoeff2 (AbsoluteGaloisGroup F) (KummerCoeff F n) (kummerCoeffInclHom F n)
      continuous_of_discreteTopology (H2pi _ _ (unramifiedKummerCup a β hβ hμ)))) = _
  rw [unramifiedKummerCup_carry]
  change invMap F (unitsRepH2Equiv F
    (characterCarryCocycle (unramifiedCircleCharacter n)
      (unramifiedCircleCharacter_open n) (baseUnitsEquivInvariants F (Additive.ofMul a)) : H2 _
        _)) = _
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk'_surjective
    (commutator ((Field.absoluteGaloisGroup F))).topologicalClosure (artinMap F a)
  rw [invMap_characterCarryCocycle_of_mk_eq_artinMap _ _ a σ hσ]
  change ZMod.toRatAddCircle n
    (urCharN F n ((absoluteGaloisGroupRestrictEquiv F).symm
      (absoluteGaloisGroupRestrictEquiv F σ))) = _
  rw [(absoluteGaloisGroupRestrictEquiv F).symm_apply_apply,
    urCharN_frobenius (isArithFrobeniusLift_of_mk_eq_artinMap_uniformizer F ha σ hσ)]
  simpa using ZMod.toRatAddCircle_natCast n 1

end TameSymbol

section ScalarCups

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (n : ℕ) [NeZero n] (u κ : G → ZMod n) (hu : Continuous u) (hκ : Continuous κ)

/-- The scalar two-cochain `(g,h) ↦ u(g)κ(h)`. -/
def scalarCup : (contCochains (ZMod n) G (ScalarCoeff (ZMod n))).X 2 :=
  mkCochain2 (fun p => (ScalarCoeff.equiv (ZMod n)).symm (u p.1 * κ p.2))
    ((continuous_of_discreteTopology : Continuous (fun p : ZMod n × ZMod n =>
      (ScalarCoeff.equiv (ZMod n)).symm (p.1 * p.2))).comp
        ((hu.comp continuous_fst).prodMk (hκ.comp continuous_snd)))

omit [NeZero n] in
/-- Evaluation of the scalar cup. -/
theorem scalarCup_eval (g h : G) :
    evalTwo (ZMod n) (ScalarCoeff (ZMod n)) g h (scalarCup n u κ hu hκ) =
      (ScalarCoeff.equiv (ZMod n)).symm (u g * κ h) := rfl

omit [NeZero n] in
/-- The scalar cup of additive characters is a continuous two-cocycle. -/
theorem scalarCup_cycle (huadd : ∀ g h, u (g * h) = u g + u h)
    (hκadd : ∀ g h, κ (g * h) = κ g + κ h) :
    ((contCochains (ZMod n) G (ScalarCoeff (ZMod n))).d 2 3).hom
      (scalarCup n u κ hu hκ) = 0 := by
  apply contCochains_ext
  intro v
  have hv : v = ![v 0, v 1, v 2] := by funext j; fin_cases j <;> rfl
  rw [hv, contFun_d23]
  apply (ScalarCoeff.equiv (ZMod n)).injective
  change u (v 1) * κ (v 2) - u (v 0 * v 1) * κ (v 2) +
    u (v 0) * κ (v 1 * v 2) - u (v 0) * κ (v 1) = 0
  rw [huadd, hκadd]
  ring

end ScalarCups

section ScalarInvariant

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ} [NeZero n]
  (η : ZMod n ≃+ KummerCoeff F n)
  (hμ : ∀ (g : AbsoluteGaloisGroup F) (x : KummerCoeff F n), g • x = x)

/-- The coefficient and Galois-group dictionary for scalar degree-two
cohomology and Kummer degree-two cohomology. -/
def scalarKummerEquiv :
    H2 (Field.absoluteGaloisGroup F) (ScalarCoeff (ZMod n)) ≃+
      H2 (AbsoluteGaloisGroup F) (KummerCoeff F n) :=
  explicitMap2Equiv (Field.absoluteGaloisGroup F) (ScalarCoeff (ZMod n))
    (AbsoluteGaloisGroup F) (KummerCoeff F n) (absoluteGaloisGroupRestrictEquiv F).symm
    ((ScalarCoeff.equiv (ZMod n)).toAddEquiv.trans η)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (fun g x => by rw [hμ]; rfl)

/-- The actual local invariant of a scalar degree-two class. -/
def scalarInvariant : H2 (Field.absoluteGaloisGroup F) (ScalarCoeff (ZMod n)) →+ AddCircle (1 :
  ℚ) :=
  (invMap F).toAddMonoidHom.comp
    ((ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr n).comp
      (scalarKummerEquiv η hμ).toAddMonoidHom)

omit [NeZero n] in
/-- Scalar invariants lie in the exact `n`-torsion subgroup of the rational
circle. -/
theorem scalarInvariant_torsion
    (q : H2 (Field.absoluteGaloisGroup F) (ScalarCoeff (ZMod n))) :
    n • scalarInvariant η hμ q = 0 := by
  have hkill : ∀ x : ScalarCoeff (ZMod n), n • x = 0 := by
    intro x
    apply (ScalarCoeff.equiv (ZMod n)).injective
    rw [map_nsmul, map_zero]
    simp
  rw [← map_nsmul, nsmul_H2_eq_zero hkill, map_zero]

/-- The scalar degree-two invariant, with values in `ℤ/nℤ` rather than
`(1/n)ℤ/ℤ`. -/
def scalarH2Value : H2 (Field.absoluteGaloisGroup F) (ScalarCoeff (ZMod n)) →+ ZMod n :=
  (ZInQ.Contrib.RC53Assist.DerivedKummer.circleTorsionEquiv n).toAddMonoidHom.comp
    ((scalarInvariant η hμ).codRestrict (AddSubgroup.torsionBy (AddCircle (1 : ℚ)) n)
      (fun q => AddSubgroup.torsionBy.nsmul_iff.mpr (scalarInvariant_torsion η hμ q)))

/-- Converting the scalar value back to the rational circle recovers the
actual Brauer invariant. -/
theorem scalarH2Value_invariant
    (q : H2 (Field.absoluteGaloisGroup F) (ScalarCoeff (ZMod n))) :
    ZMod.toRatAddCircle n (scalarH2Value η hμ q) = scalarInvariant η hμ q :=
  ZInQ.Contrib.RC53Assist.DerivedKummer.circleTorsionEquiv_toRat n _

/-- The generic scalar argument uses the Kummer--Brauer injection. At the
actual stages it is discharged by the existing Hilbert 90 theorem. -/
theorem scalarH2Value_injective
    (hKB : Function.Injective (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := F) n)) :
    Function.Injective (scalarH2Value η hμ) := by
  intro q q' h
  apply (scalarKummerEquiv η hμ).injective
  apply hKB
  apply (invMap F).injective
  change scalarInvariant η hμ q = scalarInvariant η hμ q'
  rw [← scalarH2Value_invariant, ← scalarH2Value_invariant, h]

variable (a : Fˣ) (β : (SeparableClosure F)ˣ)
  (hβ : β ^ n = Units.map (algebraMap F (SeparableClosure F)).toMonoidHom a)

/-- The fundamental scalar class determined by the unramified Kummer cup. -/
def scalarFundamentalClass : H2 (Field.absoluteGaloisGroup F) (ScalarCoeff (ZMod n)) :=
  (scalarKummerEquiv η hμ).symm (H2pi _ _ (unramifiedKummerCup a β hβ hμ))

/-- The fundamental scalar class has coordinate one. -/
theorem scalarFundamentalClass_value (ha : IsUniformizer F a) :
    scalarH2Value η hμ (scalarFundamentalClass η hμ a β hβ) = 1 := by
  apply ZMod.toRatAddCircle_injective n
  rw [scalarH2Value_invariant]
  change invMap F (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr n
    (scalarKummerEquiv η hμ ((scalarKummerEquiv η hμ).symm
      (H2pi _ _ (unramifiedKummerCup a β hβ hμ))))) = _
  rw [(scalarKummerEquiv η hμ).apply_symm_apply, unramifiedKummerCup_invariant a β hβ hμ ha]
  simpa using (ZMod.toRatAddCircle_natCast n 1).symm

include hβ in
/-- The scalar invariant is onto because the normalized uniformizer cup
supplies its generator. -/
theorem scalarH2Value_surjective (ha : IsUniformizer F a) :
    Function.Surjective (scalarH2Value η hμ) := by
  intro x
  refine ⟨x.val • scalarFundamentalClass η hμ a β hβ, ?_⟩
  rw [map_nsmul, scalarFundamentalClass_value η hμ a β hβ ha]
  simp

/-- The tame Kummer character, in the chosen primitive-root coordinate. -/
def tameKummerCharacter (g : (Field.absoluteGaloisGroup F)) : ZMod n :=
  η.symm (kummerCocycle hβ (absoluteGaloisGroupRestrictEquiv F g))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [NeZero n] in
/-- The Kummer character is continuous. -/
theorem tameKummerCharacter_continuous : Continuous (tameKummerCharacter η a β hβ) :=
  (continuous_of_discreteTopology : Continuous η.symm).comp
    (((mem_Z1_iff.mp (kummerCocycle_mem_Z1 hβ)).1).comp (absoluteGaloisGroupRestrictEquiv
      F).continuous)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [NeZero n] in
include hμ in
/-- With fixed roots of unity the Kummer character is additive. -/
theorem tameKummerCharacter_mul (g h : (Field.absoluteGaloisGroup F)) :
    tameKummerCharacter η a β hβ (g * h) =
      tameKummerCharacter η a β hβ g + tameKummerCharacter η a β hβ h := by
  have hk := (mem_Z1_iff.mp (kummerCocycle_mem_Z1 hβ)).2
    (absoluteGaloisGroupRestrictEquiv F g) (absoluteGaloisGroupRestrictEquiv F h)
  change η.symm (kummerCocycle hβ (absoluteGaloisGroupRestrictEquiv F (g * h))) = _
  rw [map_mul, hk, hμ, map_add, add_comm]
  rfl

/-- The scalar unramified--Kummer cup as a cochain on the actual local
Galois group. -/
def normalizedScalarCup :
    (contCochains (ZMod n) (Field.absoluteGaloisGroup F) (ScalarCoeff (ZMod n))).X 2 :=
  scalarCup n (urCharN F n) (tameKummerCharacter η a β hβ)
    (continuous_urCharN (K := F) (n := n)) (tameKummerCharacter_continuous η a β hβ)

include hμ in
/-- The normalized scalar cup is a two-cocycle. -/
theorem normalizedScalarCup_cycle :
    ((contCochains (ZMod n) (Field.absoluteGaloisGroup F) (ScalarCoeff (ZMod n))).d 2 3).hom
      (normalizedScalarCup η a β hβ) = 0 :=
  scalarCup_cycle n _ _ _ _ (urCharN_mul (K := F) (n := n))
    (tameKummerCharacter_mul η hμ a β hβ)

/-- The coefficient dictionary identifies the scalar cup with the actual
Kummer cup, fixing the orientation at the level of cocycle representatives. -/
theorem scalarKummerEquiv_cup :
    scalarKummerEquiv η hμ
      (kerToH2 ⟨normalizedScalarCup η a β hβ, normalizedScalarCup_cycle η hμ a β hβ⟩) =
        H2pi _ _ (unramifiedKummerCup a β hβ hμ) := by
  rw [scalarKummerEquiv, explicitMap2Equiv_apply]
  change explicitMap2 (Field.absoluteGaloisGroup F) (ScalarCoeff (ZMod n))
      (AbsoluteGaloisGroup F) (KummerCoeff F n) (absoluteGaloisGroupRestrictEquiv F).symm
      ((ScalarCoeff.equiv (ZMod n)).toAddEquiv.trans η).toAddMonoidHom
      continuous_of_discreteTopology _
      (H2pi _ _ ⟨_, mem_Z2_of_d_eq_zero _ (normalizedScalarCup_cycle η hμ a β hβ)⟩) = _
  erw [explicitMap2_mk]
  congr 1
  apply Subtype.ext
  funext p
  obtain ⟨g, h⟩ := p
  rw [cocyclesMap2_apply, unramifiedKummerCup_apply]
  change η (unramifiedCharacter n g * η.symm
      (kummerCocycle hβ (absoluteGaloisGroupRestrictEquiv F
        ((absoluteGaloisGroupRestrictEquiv F).symm h)))) =
    (unramifiedCharacter n g).val • kummerCocycle hβ h
  rw [(absoluteGaloisGroupRestrictEquiv F).apply_symm_apply]
  have hη (x y : ZMod n) : η (x * y) = x • η y :=
    (η.toAddMonoidHom.toZModLinearMap n).map_smul x y
  rw [hη, η.apply_symm_apply]
  conv_lhs => rw [← ZMod.natCast_zmod_val (unramifiedCharacter n g)]
  exact Nat.cast_smul_eq_nsmul (ZMod n) _ _

/-- The scalar cocycle with formula `u(g)κ(h)` has invariant `1/n`. -/
theorem normalizedScalarCup_invariant (ha : IsUniformizer F a) :
    scalarInvariant η hμ
      (kerToH2 ⟨normalizedScalarCup η a β hβ, normalizedScalarCup_cycle η hμ a β hβ⟩) =
        ((1 / n : ℚ) : AddCircle (1 : ℚ)) := by
  change invMap F (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr n
    (scalarKummerEquiv η hμ _)) = _
  rw [scalarKummerEquiv_cup]
  exact unramifiedKummerCup_invariant a β hβ hμ ha

/-- The local scalar invariant restricted to the two-cocycles of the actual
continuous cochain complex. -/
def scalarCycleValue :
    LinearMap.ker ((contCochains (ZMod n) (Field.absoluteGaloisGroup F)
      (ScalarCoeff (ZMod n))).d 2 3).hom →ₗ[ZMod n] ZMod n :=
  ((scalarH2Value η hμ).comp
    (kerToH2 (k := ZMod n) (G := Field.absoluteGaloisGroup F)
      (M := ScalarCoeff (ZMod n)))).toZModLinearMap n

/-- Self-injectivity of the residue ring extends the scalar invariant to
all degree-two cochains. -/
theorem scalarCoordinate_extension_exists :
    ∃ c : (contCochains (ZMod n) (Field.absoluteGaloisGroup F)
        (ScalarCoeff (ZMod n))).X 2 →ₗ[ZMod n] ZMod n,
      ∀ z : LinearMap.ker ((contCochains (ZMod n) (Field.absoluteGaloisGroup F)
          (ScalarCoeff (ZMod n))).d 2 3).hom,
        c (z : (contCochains (ZMod n) (Field.absoluteGaloisGroup F)
          (ScalarCoeff (ZMod n))).X 2) = scalarCycleValue η hμ z := by
  have : Module.Injective (ZMod n) (ZMod n) :=
    ZInQ.Contrib.CloudB3RC53.SelmerDuality.selfInjective_of_frobeniusForm
      (ZMod.toRatAddCircle n) (fun x hx => by
        have h := hx 1
        rw [mul_one, ZMod.toRatAddCircle_eq_zero] at h
        exact h)
  exact Module.Injective.out
    (LinearMap.ker ((contCochains (ZMod n) (Field.absoluteGaloisGroup F)
      (ScalarCoeff (ZMod n))).d 2 3).hom).subtype Subtype.val_injective (scalarCycleValue η hμ)

/-- A cochain-level scalar coordinate extending the actual local invariant.
Its value on cocycles is independent of the chosen extension. -/
def scalarCoordinate :
    (contCochains (ZMod n) (Field.absoluteGaloisGroup F)
      (ScalarCoeff (ZMod n))).X 2 →ₗ[ZMod n] ZMod n :=
  Classical.choose (scalarCoordinate_extension_exists η hμ)

/-- On cycles the cochain coordinate is exactly the local Brauer invariant
read in `ℤ/nℤ`. -/
theorem scalarCoordinate_cycles
    (z : LinearMap.ker ((contCochains (ZMod n) (Field.absoluteGaloisGroup F)
      (ScalarCoeff (ZMod n))).d 2 3).hom) :
    scalarCoordinate η hμ (z : (contCochains (ZMod n) (Field.absoluteGaloisGroup F)
      (ScalarCoeff (ZMod n))).X 2) = scalarH2Value η hμ (kerToH2 z) :=
  Classical.choose_spec (scalarCoordinate_extension_exists η hμ) z

include hβ in
/-- The actual scalar coordinate kills coboundaries, detects their kernel
on cocycles, and is onto. The generic formulation keeps the Kummer--Brauer
injection explicit; the actual-stage corollary discharges it. -/
theorem scalarCoordinate_isCoordinate
    (hKB : Function.Injective (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := F) n))
    (ha : IsUniformizer F a) :
    LocalDegreeTwoCoordinate (M := ScalarCoeff (ZMod n)) (scalarCoordinate η hμ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hd : ((contCochains (ZMod n) (Field.absoluteGaloisGroup F)
        (ScalarCoeff (ZMod n))).d 2 3).hom
        (((contCochains (ZMod n) (Field.absoluteGaloisGroup F)
          (ScalarCoeff (ZMod n))).d 1 2).hom x) = 0 := by
      have h := congrArg (fun f => ModuleCat.Hom.hom f x)
        ((contCochains (ZMod n) (Field.absoluteGaloisGroup F)
          (ScalarCoeff (ZMod n))).d_comp_d 1 2 3)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] using h
    change scalarCoordinate η hμ
      (((contCochains (ZMod n) (Field.absoluteGaloisGroup F)
        (ScalarCoeff (ZMod n))).d 1 2).hom x) = (0 : ZMod n)
    have he := scalarCoordinate_cycles η hμ ⟨_, hd⟩
    rw [he]
    have hq : kerToH2 ⟨_, hd⟩ = 0 := (kerToH2_eq_zero_iff ⟨_, hd⟩).mpr ⟨x, rfl⟩
    rw [hq, map_zero]
  · intro z hz hcz
    change scalarCoordinate η hμ z = (0 : ZMod n) at hcz
    apply (kerToH2_eq_zero_iff ⟨z, hz⟩).mp
    apply scalarH2Value_injective η hμ hKB
    rw [map_zero, ← scalarCoordinate_cycles η hμ ⟨z, hz⟩]
    exact hcz
  · intro m
    obtain ⟨q, hq⟩ := scalarH2Value_surjective η hμ a β hβ ha
      (ScalarCoeff.equiv (ZMod n) m)
    obtain ⟨z, hz⟩ := kerToH2_surjective
      (k := ZMod n) (G := Field.absoluteGaloisGroup F) (M := ScalarCoeff (ZMod n)) q
    refine ⟨z, z.2, ?_⟩
    change scalarCoordinate η hμ
      (z : (contCochains (ZMod n) (Field.absoluteGaloisGroup F)
        (ScalarCoeff (ZMod n))).X 2) = ScalarCoeff.equiv (ZMod n) m
    rw [scalarCoordinate_cycles, hz, hq]

/-- The scalar coordinate is oriented by the actual unramified--Kummer
cup, with no nonzero normalization factor left unspecified. -/
theorem scalarCoordinate_normalized (ha : IsUniformizer F a) :
    LocalDegreeTwoNormalized (M := ScalarCoeff (ZMod n)) (scalarCoordinate η hμ)
      (urCharN F n) (tameKummerCharacter η a β hβ) := by
  have ht : scalarCoordinate η hμ (normalizedScalarCup η a β hβ) = 1 := by
    calc
      _ = scalarH2Value η hμ
          (kerToH2 ⟨normalizedScalarCup η a β hβ, normalizedScalarCup_cycle η hμ a β hβ⟩) :=
        scalarCoordinate_cycles η hμ _
      _ = 1 := by
        apply ZMod.toRatAddCircle_injective n
        rw [scalarH2Value_invariant, normalizedScalarCup_invariant η hμ a β hβ ha]
        simpa using (ZMod.toRatAddCircle_natCast n 1).symm
  intro m z hz
  have he : z = ScalarCoeff.equiv (ZMod n) m • normalizedScalarCup η a β hβ := by
    apply contCochains_ext
    intro v
    have hv : v = ![v 0, v 1] := by funext j; fin_cases j <;> rfl
    rw [hv]
    change evalTwo (ZMod n) (ScalarCoeff (ZMod n)) (v 0) (v 1) z =
      evalTwo (ZMod n) (ScalarCoeff (ZMod n)) (v 0) (v 1)
        (ScalarCoeff.equiv (ZMod n) m • normalizedScalarCup η a β hβ)
    rw [hz, map_smul]
    apply (ScalarCoeff.equiv (ZMod n)).injective
    change (urCharN F n (v 0) * tameKummerCharacter η a β hβ (v 1)) *
        ScalarCoeff.equiv (ZMod n) m =
      ScalarCoeff.equiv (ZMod n) m *
        (urCharN F n (v 0) * tameKummerCharacter η a β hβ (v 1))
    ring
  change scalarCoordinate η hμ z = ScalarCoeff.equiv (ZMod n) m
  rw [he, map_smul, ht]
  exact mul_one _

end ScalarInvariant

section LocalCoefficients

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ} [NeZero n]
  {R M : Type} [CommRing R] [Algebra (ZMod n) R]
  [AddCommGroup M] [Module R M] [Module (ZMod n) M] [IsScalarTower (ZMod n) R M]
  [DistribMulAction (Field.absoluteGaloisGroup F) M]
  [SMulCommClass (Field.absoluteGaloisGroup F) R M] [SMulCommClass R (ZMod n) M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup F) M]
  {ι : Type} [Fintype ι] (b : Basis ι (ZMod n) M)
  (η : ZMod n ≃+ KummerCoeff F n)
  (hμ : ∀ (g : AbsoluteGaloisGroup F) (x : KummerCoeff F n), g • x = x)

/-- The full coefficient-valued local degree-two coordinate, obtained by
finite coefficient extension of the actual scalar Brauer invariant. -/
def normalizedCoefficientCoordinate :
    (contCochains R (Field.absoluteGaloisGroup F) M).X 2 →ₗ[R] M :=
  coefficientCoordinate b (scalarCoordinate η hμ)

/-- The produced coordinate has the two required properties at the actual
local Galois group. -/
theorem normalizedCoefficientCoordinate_spec
    (htriv : ∀ (g : Field.absoluteGaloisGroup F) (m : M), g • m = m)
    (hKB : Function.Injective (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := F) n))
    (a : Fˣ) (β : (SeparableClosure F)ˣ)
    (hβ : β ^ n = Units.map (algebraMap F (SeparableClosure F)).toMonoidHom a)
    (ha : IsUniformizer F a) :
    LocalDegreeTwoCoordinate (normalizedCoefficientCoordinate (R := R) b η hμ) ∧
      LocalDegreeTwoNormalized (normalizedCoefficientCoordinate (R := R) b η hμ)
        (fun g => algebraMap (ZMod n) R (urCharN F n g))
        (fun g => algebraMap (ZMod n) R (tameKummerCharacter η a β hβ g)) :=
  ⟨coefficientCoordinate_isCoordinate (R := R) b (scalarCoordinate η hμ) htriv
      (scalarCoordinate_isCoordinate η hμ a β hβ hKB ha),
    coefficientCoordinate_normalized (R := R) b (scalarCoordinate η hμ) _ _
      (scalarCoordinate_normalized η hμ a β hβ ha)⟩

end LocalCoefficients

section StageAlgebra

variable {n : ℕ} [NeZero n] {T : Type} [AddCommGroup T]

/-- Extending a rank-two residue coefficient module to an arbitrary
coefficient algebra. -/
def coefficientTensorEquiv (A : Type) [CommRing A] [Algebra (ZMod n) A]
    (φ : T ≃+ ZMod n × ZMod n) :
    (A ⊗[ℤ] T) ≃ₗ[A] A × A :=
  (LinearEquiv.baseChange ℤ A T (ZMod n × ZMod n) φ.toIntLinearEquiv).trans
    ((TensorProduct.prodRight ℤ A A (ZMod n) (ZMod n)).trans
      ((ZInQ.Manuscript.RC.CoefModules.mulZModEquiv A n).prodCongr
        (ZInQ.Manuscript.RC.CoefModules.mulZModEquiv A n)))

/-- Residue scalar multiplication commutes with the coefficient-ring
multiplication on every residue coefficient module. -/
theorem residueScalarComm (R M : Type) [CommRing R] [AddCommGroup M]
    [Module R M] [Module (ZMod n) M] : SMulCommClass R (ZMod n) M := by
  refine ⟨fun r s m => ?_⟩
  rw [← ZMod.natCast_zmod_val s, Nat.cast_smul_eq_nsmul (ZMod n),
    Nat.cast_smul_eq_nsmul (ZMod n)]
  exact smul_comm r s.val m

/-- The canonical residue module structure is compatible with extension
of scalars to the full coefficient ring. -/
theorem residueScalarTower (R M : Type) [CommRing R] [Algebra (ZMod n) R]
    [AddCommGroup M] [Module R M] [Module (ZMod n) M] :
    IsScalarTower (ZMod n) R M := by
  refine ⟨fun s r m => ?_⟩
  rw [Algebra.smul_def]
  rw [ZInQ.Manuscript.RC.CoefModules.algebraMap_zmod_eq_val R n s, mul_smul,
    Nat.cast_smul_eq_nsmul R]
  conv_rhs => rw [← ZMod.natCast_zmod_val s, Nat.cast_smul_eq_nsmul (ZMod n)]

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.HeegnerAlgebra ZInQ.Manuscript.RC.CoefModules

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (α : GKS K S →* (Acoef i)ˣ) (q : HeightOneSpectrum (𝓞 K))

omit [W.IsElliptic] [NeZero i] in
/-- The actual localized coefficient module is killed by the stage
power of two, independently of any local duality assertion. -/
theorem localizedMcoef_nsmul (m : ResMod (locMap K S q) (Mcoef K S W i α)) :
    (2 ^ i) • m = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (Acoef i)]
  have hzero : ((2 ^ i : ℕ) : Acoef i) = 0 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, acoef_two_pow_eq_zero]
  rw [hzero]
  exact zero_smul (Acoef i) m

/-- A finite residue basis of the actual localized stage module. The
basis is constructed from elliptic torsion and the polynomial power basis. -/
theorem localizedMcoef_basis
    [Module (ZMod (2 ^ i)) (ResMod (locMap K S q) (Mcoef K S W i α))]
    (hW : FullTorsion K S W (2 ^ i)) :
    Nonempty (Basis (Fin i ⊕ Fin i) (ZMod (2 ^ i))
      (ResMod (locMap K S q) (Mcoef K S W i α))) := by
  have : NeZero (2 ^ i) := ⟨pow_ne_zero i two_ne_zero⟩
  obtain ⟨φ⟩ := torsS_addEquiv_prod W hW
  let eA : Mcoef K S W i α ≃ₗ[Acoef i] Acoef i × Acoef i :=
    (CoefMod.equiv (Acoef i) α (TorsS K S W ((2 ^ i : ℕ) : ℤ))).symm.trans
      (coefficientTensorEquiv (Acoef i) φ)
  let e : ResMod (locMap K S q) (Mcoef K S W i α) ≃+ Acoef i × Acoef i := eA.toAddEquiv
  let eS := LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap (2 ^ i)) e.bijective
  let pb : PowerBasis (ZMod (2 ^ i)) (Acoef i) :=
    AdjoinRoot.powerBasis' (Polynomial.monic_X_pow i)
  have hdim : pb.dim = i := Polynomial.natDegree_X_pow i
  let bA : Basis (Fin i) (ZMod (2 ^ i)) (Acoef i) := pb.basis.reindex (finCongr hdim)
  exact ⟨(bA.prod bA).map eS.symm⟩

end StageAlgebra

section CharacterDictionary

variable {F : Type} [Field F] {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- Fixed algebraic roots of unity give the actual trivial action on the
Kummer coefficients of the separable closure. -/
theorem kummerCoefficients_fixed
    (hμ : ∀ (g : Gal(AlgebraicClosure F/F)) (ζ : AlgebraicClosure F),
      ζ ^ n = 1 → g ζ = ζ)
    (g : AbsoluteGaloisGroup F) (x : KummerCoeff F n) : g • x = x := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply Subtype.val_injective
  let z : SeparableClosure F := (x.toMul : (SeparableClosure F)ˣ)
  change (g z : AlgebraicClosure F) = (z : AlgebraicClosure F)
  have hz : z ^ n = 1 := by
    have h := (mem_rootsOfUnity n _).mp x.toMul.2
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun u : (SeparableClosure F)ˣ => (u : SeparableClosure F)) h
  have hza : (z : AlgebraicClosure F) ^ n = 1 := by exact_mod_cast hz
  have he := coe_absoluteGaloisGroupRestrictEquiv_apply (K := F)
    ((absoluteGaloisGroupRestrictEquiv F).symm g) z
  rw [(absoluteGaloisGroupRestrictEquiv F).apply_symm_apply] at he
  exact he.trans (hμ _ _ hza)

variable (a : Fˣ) (β : (SeparableClosure F)ˣ)
  (hβ : β ^ n = Units.map (algebraMap F (SeparableClosure F)).toMonoidHom a)

omit [NeZero n] in
include hβ in
/-- The chosen separable root, read in the algebraic closure, has the same
power equation. -/
theorem algebraicRoot_pow :
    ((β : SeparableClosure F) : AlgebraicClosure F) ^ n =
      algebraMap F (AlgebraicClosure F) (a : F) := by
  have hs : (β : SeparableClosure F) ^ n = algebraMap F (SeparableClosure F) (a : F) := by
    calc
      _ = ((β ^ n : (SeparableClosure F)ˣ) : SeparableClosure F) := by
        rw [Units.val_pow_eq_pow_val]
      _ = ((Units.map (algebraMap F (SeparableClosure F)).toMonoidHom a :
          (SeparableClosure F)ˣ) : SeparableClosure F) :=
        congrArg (fun u : (SeparableClosure F)ˣ => (u : SeparableClosure F)) hβ
      _ = algebraMap F (SeparableClosure F) (a : F) := rfl
  have hv : algebraMap (SeparableClosure F) (AlgebraicClosure F) (β : SeparableClosure F) =
      ((β : SeparableClosure F) : AlgebraicClosure F) := rfl
  have ht : (algebraMap (SeparableClosure F) (AlgebraicClosure F) (β : SeparableClosure F)) ^ n =
      algebraMap F (AlgebraicClosure F) (a : F) := by
    simpa only [map_pow, ← IsScalarTower.algebraMap_apply] using
      congrArg (algebraMap (SeparableClosure F) (AlgebraicClosure F)) hs
  exact (congrArg (fun z : AlgebraicClosure F => z ^ n) hv).symm.trans ht

/-- Reading a nonzero root in the algebraic closure preserves nonvanishing. -/
theorem algebraicRoot_ne_zero : ((β : SeparableClosure F) : AlgebraicClosure F) ≠ 0 :=
  fun h => β.ne_zero (Subtype.val_injective h)

omit [NeZero n] in
/-- The actual Kummer cocycle and the algebraic-closure ratio agree. -/
theorem kummerCocycle_algebraicValue (g : Gal(AlgebraicClosure F/F)) :
    (((kummerCocycle hβ (absoluteGaloisGroupRestrictEquiv F g)).toMul :
      (SeparableClosure F)ˣ) : AlgebraicClosure F) =
        ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal
          ((β : SeparableClosure F) : AlgebraicClosure F) g := by
  let s : SeparableClosure F ≃ₐ[F] SeparableClosure F := absoluteGaloisGroupRestrictEquiv F g
  rw [toMul_kummerCocycle]
  change ((Units.map (s : SeparableClosure F →* SeparableClosure F) β * β⁻¹ :
    (SeparableClosure F)ˣ) : AlgebraicClosure F) = _
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_ofClass]
  change (algebraMap (SeparableClosure F) (AlgebraicClosure F))
      (s (β : SeparableClosure F) * (β : SeparableClosure F)⁻¹) = _
  rw [map_mul]
  have hs : (s (β : SeparableClosure F) : AlgebraicClosure F) =
      g ((β : SeparableClosure F) : AlgebraicClosure F) :=
    coe_absoluteGaloisGroupRestrictEquiv_apply (K := F) g (β : SeparableClosure F)
  change (s (β : SeparableClosure F) : AlgebraicClosure F) *
      ((β : SeparableClosure F) : AlgebraicClosure F)⁻¹ = _
  rw [hs]
  rfl

/-- A residue coefficient equivalence reads every value as a power of its
chosen primitive root. -/
theorem kummerEquiv_algebraicPower (η : ZMod n ≃+ KummerCoeff F n) (x : ZMod n) :
    (((η x).toMul : (SeparableClosure F)ˣ) : AlgebraicClosure F) =
      (((η 1).toMul : (SeparableClosure F)ˣ) : AlgebraicClosure F) ^ x.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x,
    show ((x.val : ℕ) : ZMod n) = x.val • (1 : ZMod n) by simp, map_nsmul]
  simp

/-- The character used in the invariant construction is the exact tame
Kummer logarithm used by the degree-one coordinates. -/
theorem tameKummerCharacter_eq_log (η : ZMod n ≃+ KummerCoeff F n)
    {σ : Field.absoluteGaloisGroup F}
    (hζ : IsPrimitiveRoot (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal
      ((β : SeparableClosure F) : AlgebraicClosure F) σ) n)
    (hη : (((η 1).toMul : (SeparableClosure F)ˣ) : AlgebraicClosure F) =
      ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal
        ((β : SeparableClosure F) : AlgebraicClosure F) σ)
    (g : Field.absoluteGaloisGroup F) :
    tameKummerCharacter η a β hβ g =
      kummerLog (algebraicRoot_pow a β hβ) (algebraicRoot_ne_zero β) hζ g := by
  symm
  apply (kummerLog_eq_iff (algebraicRoot_pow a β hβ) (algebraicRoot_ne_zero β) hζ g _).mpr
  rw [← hη, ← kummerEquiv_algebraicPower η]
  change (((η (η.symm (kummerCocycle hβ (absoluteGaloisGroupRestrictEquiv F g)))).toMul :
    (SeparableClosure F)ˣ) : AlgebraicClosure F) = _
  rw [η.apply_symm_apply]
  exact kummerCocycle_algebraicValue a β hβ g

end CharacterDictionary

/-- A uniformizer, a tame root, and compatible arithmetic Frobenius and
inertia generators. This contains no cohomological coordinate hypothesis. -/
structure TameOrientation (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) [NeZero n] where
  uniformizer : Fˣ
  uniformizer_is : IsUniformizer F uniformizer
  root : AlgebraicClosure F
  root_pow : root ^ n = algebraMap F (AlgebraicClosure F) (uniformizer : F)
  root_ne_zero : root ≠ 0
  frobenius : Gal(AlgebraicClosure F/F)
  frobenius_is : IsArithFrobeniusLift F frobenius
  frobenius_fix : frobenius root = root
  inertia : Gal(AlgebraicClosure F/F)
  inertia_mem : inertia ∈ inertiaSubgroup F
  primitive : IsPrimitiveRoot
    (ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal root inertia) n

namespace TameOrientation

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ} [NeZero n] (D : TameOrientation F n)

/-- The arithmetic unramified character in the chosen orientation. -/
def unramified (_D : TameOrientation F n) : Gal(AlgebraicClosure F/F) → ZMod n := urCharN F n

/-- The exact tame Kummer character of the chosen uniformizer root. -/
def kummer : Gal(AlgebraicClosure F/F) → ZMod n :=
  kummerLog D.root_pow D.root_ne_zero D.primitive

/-- The degree-one coordinates are oriented as the finite and singular
axes: `(1,0)` at Frobenius and `(0,1)` at inertia. -/
theorem character_values [Fact (1 < n)] :
    D.unramified D.frobenius = 1 ∧ D.unramified D.inertia = 0 ∧
      D.kummer D.frobenius = 0 ∧ D.kummer D.inertia = 1 :=
  ⟨urCharN_frobenius D.frobenius_is, urCharN_inertia D.inertia_mem,
    kummerLog_of_fix D.root_pow D.root_ne_zero D.primitive D.frobenius_fix,
    kummerLog_self D.root_pow D.root_ne_zero D.primitive⟩

end TameOrientation

section Existence

open _root_.ValuativeRel
open ZInQ.Contrib.CloudB3RC53.TameQuotient

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ} [NeZero n]
  {R M : Type} [CommRing R] [Algebra (ZMod n) R]
  [AddCommGroup M] [Module R M] [Module (ZMod n) M] [IsScalarTower (ZMod n) R M]
  [DistribMulAction (Field.absoluteGaloisGroup F) M]
  [SMulCommClass (Field.absoluteGaloisGroup F) R M] [SMulCommClass R (ZMod n) M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup F) M]
  {ι : Type} [Fintype ι] (b : Basis ι (ZMod n) M)

include b in
/-- The normalized local degree-two coordinate exists for the actual local
Galois group and any finite free residue coefficient module. The tame symbol
and surjectivity are proved. The characteristic-zero stage corollary
discharges the Kummer--Brauer injection by Hilbert 90. -/
theorem exists_normalizedLocalCoordinate
    (hn : n.Coprime (ringChar 𝓀[F]))
    (htriv : ∀ (g : Field.absoluteGaloisGroup F) (m : M), g • m = m)
    (hμ : ∀ (g : Gal(AlgebraicClosure F/F)) (ζ : AlgebraicClosure F), ζ ^ n = 1 → g ζ = ζ)
    (hKB : Function.Injective (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := F) n)) :
    ∃ (D : TameOrientation F n)
      (c₂ : (contCochains R (Field.absoluteGaloisGroup F) M).X 2 →ₗ[R] M),
      LocalDegreeTwoCoordinate c₂ ∧ LocalDegreeTwoNormalized c₂
        (fun g => algebraMap (ZMod n) R (D.unramified g))
        (fun g => algebraMap (ZMod n) R (D.kummer g)) := by
  have hnF : IsUnit (n : F) := isUnit_iff_ne_zero.mpr (natCast_ne_zero_of_coprime_ringChar hn)
  have : NeZero (n : SeparableClosure F) := ⟨hnF.natCast_ne_zero_of_algebra⟩
  obtain ⟨π, hπ⟩ := exists_isUniformizer F
  obtain ⟨β, hβ⟩ := exists_pow_eq_units_map hnF π
  let βbar : AlgebraicClosure F := (β : SeparableClosure F)
  have hβbar : βbar ^ n = algebraMap F (AlgebraicClosure F) (π : F) := algebraicRoot_pow π β hβ
  have hβ0 : βbar ≠ 0 := algebraicRoot_ne_zero β
  have hπv : (normalizedValuation F π).toAdd = 1 := by
    rw [(isUniformizer_def π).mp hπ, toAdd_ofAdd]
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (SeparableClosure F) n
  let ζu : (SeparableClosure F)ˣ := (hζ.isUnit (NeZero.ne n)).unit
  have hζu : IsPrimitiveRoot ζu n := hζ.isUnit_unit (NeZero.ne n)
  let η : ZMod n ≃+ KummerCoeff F n := hζu.zmodEquivRootsOfUnity
  have hη1 : ((η 1).toMul : (SeparableClosure F)ˣ) = ζu := by
    simpa using hζu.coe_zmodEquivRootsOfUnity_apply_natCast 1
  let ζbar : rootsOfUnity n (AlgebraicClosure F) :=
    restrictRootsOfUnity (algebraMap (SeparableClosure F) (AlgebraicClosure F)) n (η 1).toMul
  have hζbar : ((ζbar : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) =
      algebraMap (SeparableClosure F) (AlgebraicClosure F) (ζu : SeparableClosure F) := by
    change algebraMap (SeparableClosure F) (AlgebraicClosure F)
      (((η 1).toMul : (SeparableClosure F)ˣ) : SeparableClosure F) = _
    rw [hη1]
  obtain ⟨σ, hσ⟩ := tameChar_surjective hn hβbar hβ0 π.ne_zero hπv ζbar
  have hσval : kummerVal βbar σ.1 = ((ζbar : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) := by
    simpa only [coe_tameChar] using congrArg
      (fun x : rootsOfUnity n (AlgebraicClosure F) => ((x : (AlgebraicClosure F)ˣ) :
        AlgebraicClosure F)) hσ
  have hζuf : IsPrimitiveRoot (ζu : SeparableClosure F) n := by
    change IsPrimitiveRoot ((hζ.isUnit (NeZero.ne n)).unit : SeparableClosure F) n
    rw [IsUnit.unit_spec]
    exact hζ
  have hζσ : IsPrimitiveRoot (kummerVal βbar σ.1) n := by
    rw [hσval, hζbar]
    exact hζuf.map_of_injective (algebraMap (SeparableClosure F) (AlgebraicClosure F)).injective
  have hησ : (((η 1).toMul : (SeparableClosure F)ˣ) : AlgebraicClosure F) =
      kummerVal βbar σ.1 := by
    have hval : ((ζbar : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) =
        (((η 1).toMul : (SeparableClosure F)ˣ) : AlgebraicClosure F) := rfl
    exact hval.symm.trans hσval.symm
  obtain ⟨φ, hφ, hφβ⟩ := exists_frobeniusLift_fix hn hβbar hβ0 π.ne_zero hπv
  let D : TameOrientation F n :=
    { uniformizer := π
      uniformizer_is := hπ
      root := βbar
      root_pow := hβbar
      root_ne_zero := hβ0
      frobenius := φ
      frobenius_is := hφ
      frobenius_fix := hφβ
      inertia := σ.1
      inertia_mem := σ.2
      primitive := hζσ }
  let hμs := kummerCoefficients_fixed hμ
  obtain ⟨hc, hnorm⟩ := normalizedCoefficientCoordinate_spec (R := R) b η hμs htriv hKB π β hβ hπ
  refine ⟨D, normalizedCoefficientCoordinate (R := R) b η hμs, hc, ?_⟩
  intro m z hz
  apply hnorm m z
  intro g h
  have hl : tameKummerCharacter η π β hβ h = D.kummer h :=
    tameKummerCharacter_eq_log π β hβ η hζσ hησ h
  exact (hz g h).trans (congrArg (fun x : ZMod n =>
    (algebraMap (ZMod n) R (D.unramified g) * algebraMap (ZMod n) R x) • m) hl.symm)

end Existence

section DerivativeStage

open NumberField IsDedekindDomain _root_.ValuativeRel
open ZInQ.Manuscript.RC.HeegnerAlgebra ZInQ.Manuscript.RC.CoefModules

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α] (q : HeightOneSpectrum (𝓞 K))

/-- The normalized degree-two coordinate at an odd derivative stage prime,
for the actual localized stage coefficient module. The full-torsion,
derivative-action and fixed-root inputs have their exact arithmetic types. -/
theorem exists_stageCoordinate (h2 : (2 : 𝓞 K) ∉ q.asIdeal)
    (hW : FullTorsion K S W (2 ^ i))
    (htriv : ∀ (g : Gloc K q) (m : ResMod (locMap K S q) (Mcoef K S W i α)), g • m = m)
    (hμ : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K)/q.adicCompletion K))
      (ζ : AlgebraicClosure (q.adicCompletion K)), ζ ^ (2 ^ i) = 1 → g ζ = ζ)
    (hKB : Function.Injective
      (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr (F := q.adicCompletion K) (2 ^ i))) :
    ∃ (D : TameOrientation (q.adicCompletion K) (2 ^ i))
      (c₂ : (contCochains (Acoef i) (Gloc K q)
        (ResMod (locMap K S q) (Mcoef K S W i α))).X 2 →ₗ[Acoef i]
          ResMod (locMap K S q) (Mcoef K S W i α)),
      LocalDegreeTwoCoordinate c₂ ∧ LocalDegreeTwoNormalized c₂
        (fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (D.unramified g))
        (fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (D.kummer g)) := by
  have : NeZero (2 ^ i) := ⟨pow_ne_zero i two_ne_zero⟩
  let M := ResMod (locMap K S q) (Mcoef K S W i α)
  let : Module (ZMod (2 ^ i)) M := AddCommGroup.zmodModule (localizedMcoef_nsmul W i α q)
  let : SMulCommClass (Acoef i) (ZMod (2 ^ i)) M := residueScalarComm (Acoef i) M
  let : IsScalarTower (ZMod (2 ^ i)) (Acoef i) M := residueScalarTower (Acoef i) M
  let : DistribMulAction (Field.absoluteGaloisGroup (q.adicCompletion K)) M :=
    inferInstanceAs (DistribMulAction (Gloc K q) M)
  let : SMulCommClass (Field.absoluteGaloisGroup (q.adicCompletion K)) (Acoef i) M :=
    inferInstanceAs (SMulCommClass (Gloc K q) (Acoef i) M)
  let : ContinuousSMul (Field.absoluteGaloisGroup (q.adicCompletion K)) M :=
    inferInstanceAs (ContinuousSMul (Gloc K q) M)
  obtain ⟨b⟩ := localizedMcoef_basis W i α q hW
  have hp : (ringChar 𝓀[q.adicCompletion K]).Prime :=
    (CharP.char_is_prime_or_zero 𝓀[q.adicCompletion K] _).resolve_right
      (CharP.char_ne_zero_of_finite 𝓀[q.adicCompletion K] _)
  have hnd : ¬ ringChar 𝓀[q.adicCompletion K] ∣ 2 := by
    rw [HeightOneSpectrum.ringChar_residueField_adicCompletion_dvd_iff]
    exact_mod_cast h2
  have hn : (2 ^ i).Coprime (ringChar 𝓀[q.adicCompletion K]) :=
    Nat.Coprime.pow_left i ((hp.coprime_iff_not_dvd.mpr hnd).symm)
  obtain ⟨D, c₂, hc, hnorm⟩ := exists_normalizedLocalCoordinate (R := Acoef i) b hn htriv hμ hKB
  exact ⟨D, c₂, hc, hnorm⟩

end DerivativeStage

end ZInQ.Contrib.RC53Assist.LocalDegreeTwo

namespace ZInQ.Contrib.RC53Assist.LocalDegreeTwo

open CategoryTheory Module
open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.HeegnerAlgebra ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.InnerLimit (Vec2)

section InvariantExport

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ} [NeZero n]
  {R M : Type} [CommRing R] [Algebra (ZMod n) R]
  [AddCommGroup M] [Module R M] [Module (ZMod n) M]
  [IsScalarTower (ZMod n) R M]
  [DistribMulAction (Field.absoluteGaloisGroup F) M]
  [SMulCommClass (Field.absoluteGaloisGroup F) R M]
  [SMulCommClass R (ZMod n) M]
  [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (Field.absoluteGaloisGroup F) M]
  (η : ZMod n ≃+ KummerCoeff F n)
  (hμ : ∀ (g : AbsoluteGaloisGroup F) (x : KummerCoeff F n), g • x = x)
  (htriv : ∀ (g : Field.absoluteGaloisGroup F) (m : M), g • m = m)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [NeZero n] [Algebra (ZMod n) R] [IsScalarTower (ZMod n) R M]
  [SMulCommClass R (ZMod n) M] in
include htriv in
/-- Applying a scalar coefficient functional to a local two-cocycle
preserves its cocycle identity. -/
theorem scalarCochain_cycle (f : M →ₗ[ZMod n] ZMod n)
    (z : (contCochains R (Field.absoluteGaloisGroup F) M).X 2)
    (hz : ((contCochains R (Field.absoluteGaloisGroup F) M).d 2 3).hom z = 0) :
    ((contCochains (ZMod n) (Field.absoluteGaloisGroup F)
      (ScalarCoeff (ZMod n))).d 2 3).hom (scalarCochain f z) = 0 := by
  rw [← scalarCochain_d23 htriv f, hz, scalarCochain_zero]

/-- The coefficient coordinate is the actual Brauer invariant in every
scalar coefficient functional, on every continuous local two-cocycle. -/
def BrauerCoordinateFormula
    (c₂ : (contCochains R (Field.absoluteGaloisGroup F) M).X 2 →ₗ[R] M) : Prop :=
  ∀ (f : M →ₗ[ZMod n] ZMod n)
    (z : (contCochains R (Field.absoluteGaloisGroup F) M).X 2)
    (hz : ((contCochains R (Field.absoluteGaloisGroup F) M).d 2 3).hom z = 0),
    ZMod.toRatAddCircle n (f (c₂ z)) =
      invMap F (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr n
        (scalarKummerEquiv η hμ (kerToH2
          ⟨scalarCochain f z, scalarCochain_cycle htriv f z hz⟩)))

omit [Algebra (ZMod n) R] [IsScalarTower (ZMod n) R M] in
/-- The finite coefficient extension agrees with the local invariant on
cocycles. This exports the scalar invariant identity, not only uniqueness
of a normalized coordinate. -/
theorem normalizedCoefficientCoordinate_brauerFormula
    {ι : Type} [Fintype ι] (b : Basis ι (ZMod n) M) :
    BrauerCoordinateFormula η hμ htriv
      (normalizedCoefficientCoordinate (R := R) b η hμ) := by
  intro f z hz
  change ZMod.toRatAddCircle n (f (coefficientValue b (scalarCoordinate η hμ) z)) = _
  rw [coefficientValue_functional]
  rw [scalarCoordinate_cycles η hμ
    ⟨scalarCochain f z, scalarCochain_cycle htriv f z hz⟩,
    scalarH2Value_invariant]
  rfl

end InvariantExport

section ReviewedStageCorollaries

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α]
  (q : HeightOneSpectrum (𝓞 K))

/-- Hilbert 90 removes the Kummer--Brauer injectivity hypothesis at the
actual characteristic-zero stage. This elimination was found in an
independent review. -/
theorem exists_stageCoordinate_without_hKB
    (h2 : (2 : 𝓞 K) ∉ q.asIdeal) (hW : FullTorsion K S W (2 ^ i))
    (htriv : ∀ (g : Gloc K q)
      (m : ResMod (locMap K S q) (Mcoef K S W i α)), g • m = m)
    (hμ : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K)/q.adicCompletion K))
      (ζ : AlgebraicClosure (q.adicCompletion K)), ζ ^ (2 ^ i) = 1 → g ζ = ζ) :
    ∃ (D : TameOrientation (q.adicCompletion K) (2 ^ i))
      (c₂ : (contCochains (Acoef i) (Gloc K q)
        (ResMod (locMap K S q) (Mcoef K S W i α))).X 2 →ₗ[Acoef i]
          ResMod (locMap K S q) (Mcoef K S W i α)),
      LocalDegreeTwoCoordinate c₂ ∧ LocalDegreeTwoNormalized c₂
        (fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (D.unramified g))
        (fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (D.kummer g)) := by
  have : CharZero (q.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (q.adicCompletion K)).injective
  exact exists_stageCoordinate W i α q h2 hW htriv hμ
    (ZInQ.Manuscript.RC.KummerMaps.compKummerToBr_injective _ _
      (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (pow_ne_zero _ two_ne_zero))))

omit [NeZero i] in
/-- The actual coefficient rings used by the arithmetic and the split
stage consumer are definitionally the same. -/
theorem acoef_eq_stageA : Acoef i = ZInQ.Manuscript.RC.Limits.StageA i := rfl

/-- The scalar invariant formula for the actual localized stage module,
with its canonical residue-module and local-action dictionaries. -/
def StageBrauerCoordinateFormula
    (η : ZMod (2 ^ i) ≃+ KummerCoeff (q.adicCompletion K) (2 ^ i))
    (hμ : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K)/q.adicCompletion K))
      (ζ : AlgebraicClosure (q.adicCompletion K)), ζ ^ (2 ^ i) = 1 → g ζ = ζ)
    (htriv : ∀ (g : Gloc K q)
      (m : ResMod (locMap K S q) (Mcoef K S W i α)), g • m = m)
    (c₂ : (contCochains (Acoef i) (Gloc K q)
      (ResMod (locMap K S q) (Mcoef K S W i α))).X 2 →ₗ[Acoef i]
        ResMod (locMap K S q) (Mcoef K S W i α)) : Prop := by
  have : NeZero (2 ^ i) := ⟨pow_ne_zero i two_ne_zero⟩
  let M := ResMod (locMap K S q) (Mcoef K S W i α)
  let : Module (ZMod (2 ^ i)) M :=
    AddCommGroup.zmodModule (localizedMcoef_nsmul W i α q)
  let : SMulCommClass (Acoef i) (ZMod (2 ^ i)) M := residueScalarComm (Acoef i) M
  let : IsScalarTower (ZMod (2 ^ i)) (Acoef i) M := residueScalarTower (Acoef i) M
  let : DistribMulAction (Field.absoluteGaloisGroup (q.adicCompletion K)) M :=
    inferInstanceAs (DistribMulAction (Gloc K q) M)
  let : SMulCommClass (Field.absoluteGaloisGroup (q.adicCompletion K)) (Acoef i) M :=
    inferInstanceAs (SMulCommClass (Gloc K q) (Acoef i) M)
  let : ContinuousSMul (Field.absoluteGaloisGroup (q.adicCompletion K)) M :=
    inferInstanceAs (ContinuousSMul (Gloc K q) M)
  exact BrauerCoordinateFormula (R := Acoef i) (M := M)
    η (kummerCoefficients_fixed hμ) htriv c₂

/-- Writing a rank-two coefficient pair as its two coordinate entries. -/
def pairVectorEquiv (A : Type) [CommRing A] : (A × A) ≃ₗ[A] Vec2 A where
  toFun x := ![x.1, x.2]
  invFun v := (v 0, v 1)
  left_inv _ := rfl
  right_inv v := by funext j; fin_cases j <;> rfl
  map_add' x y := by funext j; fin_cases j <;> rfl
  map_smul' r x := by funext j; fin_cases j <;> rfl

omit [NeZero i] [IsOpenKer α] in
/-- The rank-two basis over the full stage ring is constructed from full
elliptic torsion, independently of the local invariant or the orientation. -/
theorem exists_localizedMcoef_equiv (hW : FullTorsion K S W (2 ^ i)) :
    Nonempty (ResMod (locMap K S q) (Mcoef K S W i α) ≃ₗ[Acoef i] Vec2 (Acoef i)) := by
  have : NeZero (2 ^ i) := ⟨pow_ne_zero i two_ne_zero⟩
  obtain ⟨φ⟩ := torsS_addEquiv_prod W hW
  let eA : Mcoef K S W i α ≃ₗ[Acoef i] Acoef i × Acoef i :=
    (CoefMod.equiv (Acoef i) α (TorsS K S W ((2 ^ i : ℕ) : ℤ))).symm.trans
      (coefficientTensorEquiv (Acoef i) φ)
  exact ⟨eA.trans (pairVectorEquiv (Acoef i))⟩

end ReviewedStageCorollaries

end ZInQ.Contrib.RC53Assist.LocalDegreeTwo

namespace ZInQ.Contrib.RC53Assist.LocalDegreeTwo

open CategoryTheory Module
open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.InnerLimitArith

section InvariantExistence

open _root_.ValuativeRel
open ZInQ.Contrib.CloudB3RC53.TameQuotient

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ} [NeZero n]
  {R M : Type} [CommRing R] [Algebra (ZMod n) R]
  [AddCommGroup M] [Module R M] [Module (ZMod n) M] [IsScalarTower (ZMod n) R M]
  [DistribMulAction (Field.absoluteGaloisGroup F) M]
  [SMulCommClass (Field.absoluteGaloisGroup F) R M] [SMulCommClass R (ZMod n) M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup F) M]
  {ι : Type} [Fintype ι] (b : Basis ι (ZMod n) M)

include b in
/-- The normalized local degree-two coordinate exists for the actual local
Galois group and any finite free residue coefficient module. The tame symbol
and surjectivity are proved. The characteristic-zero stage corollary
discharges the Kummer--Brauer injection by Hilbert 90. -/
theorem exists_normalizedLocalCoordinate_with_brauer
    (hn : n.Coprime (ringChar 𝓀[F]))
    (htriv : ∀ (g : Field.absoluteGaloisGroup F) (m : M), g • m = m)
    (hμ : ∀ (g : Gal(AlgebraicClosure F/F)) (ζ : AlgebraicClosure F), ζ ^ n = 1 → g ζ = ζ) :
    ∃ (D : TameOrientation F n)
      (c₂ : (contCochains R (Field.absoluteGaloisGroup F) M).X 2 →ₗ[R] M),
      LocalDegreeTwoCoordinate c₂ ∧ LocalDegreeTwoNormalized c₂
        (fun g => algebraMap (ZMod n) R (D.unramified g))
        (fun g => algebraMap (ZMod n) R (D.kummer g)) ∧
      ∃ η : ZMod n ≃+ KummerCoeff F n,
        BrauerCoordinateFormula η (kummerCoefficients_fixed hμ) htriv c₂ ∧
          (((η 1).toMul : (SeparableClosure F)ˣ) : AlgebraicClosure F) =
            ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal D.root D.inertia := by
  have hnF : IsUnit (n : F) := isUnit_iff_ne_zero.mpr (natCast_ne_zero_of_coprime_ringChar hn)
  have hKB := ZInQ.Manuscript.RC.KummerMaps.compKummerToBr_injective F n hnF
  have : NeZero (n : SeparableClosure F) := ⟨hnF.natCast_ne_zero_of_algebra⟩
  obtain ⟨π, hπ⟩ := exists_isUniformizer F
  obtain ⟨β, hβ⟩ := exists_pow_eq_units_map hnF π
  let βbar : AlgebraicClosure F := (β : SeparableClosure F)
  have hβbar : βbar ^ n = algebraMap F (AlgebraicClosure F) (π : F) := algebraicRoot_pow π β hβ
  have hβ0 : βbar ≠ 0 := algebraicRoot_ne_zero β
  have hπv : (normalizedValuation F π).toAdd = 1 := by
    rw [(isUniformizer_def π).mp hπ, toAdd_ofAdd]
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (SeparableClosure F) n
  let ζu : (SeparableClosure F)ˣ := (hζ.isUnit (NeZero.ne n)).unit
  have hζu : IsPrimitiveRoot ζu n := hζ.isUnit_unit (NeZero.ne n)
  let η : ZMod n ≃+ KummerCoeff F n := hζu.zmodEquivRootsOfUnity
  have hη1 : ((η 1).toMul : (SeparableClosure F)ˣ) = ζu := by
    simpa using hζu.coe_zmodEquivRootsOfUnity_apply_natCast 1
  let ζbar : rootsOfUnity n (AlgebraicClosure F) :=
    restrictRootsOfUnity (algebraMap (SeparableClosure F) (AlgebraicClosure F)) n (η 1).toMul
  have hζbar : ((ζbar : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) =
      algebraMap (SeparableClosure F) (AlgebraicClosure F) (ζu : SeparableClosure F) := by
    change algebraMap (SeparableClosure F) (AlgebraicClosure F)
      (((η 1).toMul : (SeparableClosure F)ˣ) : SeparableClosure F) = _
    rw [hη1]
  obtain ⟨σ, hσ⟩ := tameChar_surjective hn hβbar hβ0 π.ne_zero hπv ζbar
  have hσval : kummerVal βbar σ.1 = ((ζbar : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) := by
    simpa only [coe_tameChar] using congrArg
      (fun x : rootsOfUnity n (AlgebraicClosure F) => ((x : (AlgebraicClosure F)ˣ) :
        AlgebraicClosure F)) hσ
  have hζuf : IsPrimitiveRoot (ζu : SeparableClosure F) n := by
    change IsPrimitiveRoot ((hζ.isUnit (NeZero.ne n)).unit : SeparableClosure F) n
    rw [IsUnit.unit_spec]
    exact hζ
  have hζσ : IsPrimitiveRoot (kummerVal βbar σ.1) n := by
    rw [hσval, hζbar]
    exact hζuf.map_of_injective (algebraMap (SeparableClosure F) (AlgebraicClosure F)).injective
  have hησ : (((η 1).toMul : (SeparableClosure F)ˣ) : AlgebraicClosure F) =
      kummerVal βbar σ.1 := by
    have hval : ((ζbar : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) =
        (((η 1).toMul : (SeparableClosure F)ˣ) : AlgebraicClosure F) := rfl
    exact hval.symm.trans hσval.symm
  obtain ⟨φ, hφ, hφβ⟩ := exists_frobeniusLift_fix hn hβbar hβ0 π.ne_zero hπv
  let D : TameOrientation F n :=
    { uniformizer := π
      uniformizer_is := hπ
      root := βbar
      root_pow := hβbar
      root_ne_zero := hβ0
      frobenius := φ
      frobenius_is := hφ
      frobenius_fix := hφβ
      inertia := σ.1
      inertia_mem := σ.2
      primitive := hζσ }
  let hμs := kummerCoefficients_fixed hμ
  obtain ⟨hc, hnorm⟩ := normalizedCoefficientCoordinate_spec (R := R) b η hμs htriv hKB π β hβ hπ
  refine ⟨D, normalizedCoefficientCoordinate (R := R) b η hμs, hc, ?_, η,
    normalizedCoefficientCoordinate_brauerFormula η hμs htriv b, hησ⟩
  intro m z hz
  apply hnorm m z
  intro g h
  have hl : tameKummerCharacter η π β hβ h = D.kummer h :=
    tameKummerCharacter_eq_log π β hβ η hζσ hησ h
  exact (hz g h).trans (congrArg (fun x : ZMod n =>
    (algebraMap (ZMod n) R (D.unramified g) * algebraMap (ZMod n) R x) • m) hl.symm)

end InvariantExistence

section StageInvariantExistence

open NumberField IsDedekindDomain _root_.ValuativeRel
open ZInQ.Manuscript.RC.HeegnerAlgebra ZInQ.Manuscript.RC.CoefModules

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α] (q : HeightOneSpectrum (𝓞 K))

/-- The normalized degree-two coordinate at an odd derivative stage prime,
for the actual localized stage coefficient module. The full-torsion,
derivative-action and fixed-root inputs have their exact arithmetic types. -/
theorem exists_stageCoordinate_with_brauer (h2 : (2 : 𝓞 K) ∉ q.asIdeal)
    (hW : FullTorsion K S W (2 ^ i))
    (htriv : ∀ (g : Gloc K q) (m : ResMod (locMap K S q) (Mcoef K S W i α)), g • m = m)
    (hμ : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K)/q.adicCompletion K))
      (ζ : AlgebraicClosure (q.adicCompletion K)), ζ ^ (2 ^ i) = 1 → g ζ = ζ) :
    ∃ (D : TameOrientation (q.adicCompletion K) (2 ^ i))
      (c₂ : (contCochains (Acoef i) (Gloc K q)
        (ResMod (locMap K S q) (Mcoef K S W i α))).X 2 →ₗ[Acoef i]
          ResMod (locMap K S q) (Mcoef K S W i α)),
      LocalDegreeTwoCoordinate c₂ ∧ LocalDegreeTwoNormalized c₂
        (fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (D.unramified g))
        (fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (D.kummer g)) ∧
      ∃ η : ZMod (2 ^ i) ≃+ KummerCoeff (q.adicCompletion K) (2 ^ i),
        StageBrauerCoordinateFormula W i α q η hμ htriv c₂ ∧
          (((η 1).toMul : (SeparableClosure (q.adicCompletion K))ˣ) :
              AlgebraicClosure (q.adicCompletion K)) =
            ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal D.root D.inertia := by
  have : NeZero (2 ^ i) := ⟨pow_ne_zero i two_ne_zero⟩
  let M := ResMod (locMap K S q) (Mcoef K S W i α)
  let : Module (ZMod (2 ^ i)) M := AddCommGroup.zmodModule (localizedMcoef_nsmul W i α q)
  let : SMulCommClass (Acoef i) (ZMod (2 ^ i)) M := residueScalarComm (Acoef i) M
  let : IsScalarTower (ZMod (2 ^ i)) (Acoef i) M := residueScalarTower (Acoef i) M
  let : DistribMulAction (Field.absoluteGaloisGroup (q.adicCompletion K)) M :=
    inferInstanceAs (DistribMulAction (Gloc K q) M)
  let : SMulCommClass (Field.absoluteGaloisGroup (q.adicCompletion K)) (Acoef i) M :=
    inferInstanceAs (SMulCommClass (Gloc K q) (Acoef i) M)
  let : ContinuousSMul (Field.absoluteGaloisGroup (q.adicCompletion K)) M :=
    inferInstanceAs (ContinuousSMul (Gloc K q) M)
  obtain ⟨b⟩ := localizedMcoef_basis W i α q hW
  have hp : (ringChar 𝓀[q.adicCompletion K]).Prime :=
    (CharP.char_is_prime_or_zero 𝓀[q.adicCompletion K] _).resolve_right
      (CharP.char_ne_zero_of_finite 𝓀[q.adicCompletion K] _)
  have hnd : ¬ ringChar 𝓀[q.adicCompletion K] ∣ 2 := by
    rw [HeightOneSpectrum.ringChar_residueField_adicCompletion_dvd_iff]
    exact_mod_cast h2
  have hn : (2 ^ i).Coprime (ringChar 𝓀[q.adicCompletion K]) :=
    Nat.Coprime.pow_left i ((hp.coprime_iff_not_dvd.mpr hnd).symm)
  obtain ⟨D, c₂, hc, hnorm, η, hInv, hη⟩ :=
    exists_normalizedLocalCoordinate_with_brauer (R := Acoef i) b hn htriv hμ
  exact ⟨D, c₂, hc, hnorm, η, hInv, hη⟩

end StageInvariantExistence

end ZInQ.Contrib.RC53Assist.LocalDegreeTwo

/-!
# Split local replacement of a paired Selmer diagram

A local deformation retract transports the cup product and its same-condition
isotropy homotopy. The cup target is replaced by a homotopy pullback so that
compatibility with localization holds exactly, rather than only on cohomology.
The compact trace is pulled back through an explicit chain map.

The construction keeps the global complex and the condition complex unchanged.
It does not identify a relaxed condition with its orthogonal complement, and
it does not infer same-condition isotropy from strict/relaxed orthogonality.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace

open CategoryTheory Module
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.Limits
open ZInQ.Manuscript.RC.FibreDuality (splitSelData)
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex)

section TensorHomotopy

variable {A : Type} [CommRing A] {L S T : GCx A}
  (R : GRetract L S) (P : GPair L L T)

/-- The projection followed by inclusion on the original local complex. -/
def localRetractEnd : GHom L L := ghomComp R.p R.i

/-- The tensor-contraction homotopy of the cup product. -/
def cupHomotopy (a b c : ℤ) (h : a + b = c + 1) :
    L.X a →ₗ[A] L.X b →ₗ[A] T.X c :=
  (P.P (a - 1) b c (by omega)).comp (R.h a (a - 1) (by omega)) +
    sgn a • ((P.P a (b - 1) c (by omega)).compl₁₂
      ((localRetractEnd R).f a a rfl) (R.h b (b - 1) (by omega)))

/-- The homotopy has the classical two-term tensor formula. -/
theorem cupHomotopy_apply (a b c : ℤ) (h : a + b = c + 1) (x : L.X a) (y : L.X b) :
    cupHomotopy R P a b c h x y =
      P.P (a - 1) b c (by omega) (R.h a (a - 1) (by omega) x) y +
        sgn a • P.P a (b - 1) c (by omega)
          (R.i.f a a rfl (R.p.f a a rfl x)) (R.h b (b - 1) (by omega) y) := rfl

/-- The tensor homotopy formula with explicitly chosen predecessor indices. -/
theorem cupHomotopy_apply_of (a b c a₀ b₀ : ℤ) (h : a + b = c + 1)
    (ha : a₀ + 1 = a) (hb : b₀ + 1 = b) (x : L.X a) (y : L.X b) :
    cupHomotopy R P a b c h x y =
      P.P a₀ b c (by omega) (R.h a a₀ ha x) y +
        sgn a • P.P a b₀ c (by omega)
          (R.i.f a a rfl (R.p.f a a rfl x)) (R.h b b₀ hb y) := by
  obtain rfl : a₀ = a - 1 := by omega
  obtain rfl : b₀ = b - 1 := by omega
  rfl

/-- The original cup and the projected cup differ by the explicit
bilinear coboundary of the tensor-contraction homotopy. -/
theorem cupHomotopy_identity (a b c : ℤ) (h : a + b = c + 1) (x : L.X a) (y : L.X b) :
    T.d c (c + 1) rfl (cupHomotopy R P a b c h x y) +
      cupHomotopy R P (a + 1) b (c + 1) (by omega) (L.d a (a + 1) rfl x) y +
      sgn a • cupHomotopy R P a (b + 1) (c + 1) (by omega) x (L.d b (b + 1) rfl y) =
    P.P a b (c + 1) (by omega) x y -
      P.P a b (c + 1) (by omega)
        (R.i.f a a rfl (R.p.f a a rfl x)) (R.i.f b b rfl (R.p.f b b rfl y)) := by
  have h1 := P.leib (a - 1) a b (b + 1) c (c + 1) (by omega) (by omega) rfl rfl
    (R.h a (a - 1) (by omega) x) y
  have h2 := P.leib a (a + 1) (b - 1) b c (c + 1) (by omega) rfl (by omega) rfl
    (R.i.f a a rfl (R.p.f a a rfl x)) (R.h b (b - 1) (by omega) y)
  have hx := R.homotopy a x
  have hy := R.homotopy b y
  rw [cupHomotopy_apply_of R P a b c (a - 1) (b - 1) h (by omega) (by omega),
    cupHomotopy_apply_of R P (a + 1) b (c + 1) a (b - 1) (by omega) rfl (by omega),
    cupHomotopy_apply_of R P a (b + 1) (c + 1) (a - 1) b (by omega) (by omega) rfl,
    map_add, map_zsmul, h1, h2, sgn_pred, sgn_succ, ← ghom_comm_d R.i, ← ghom_comm_d R.p]
  have hxx : L.d (a - 1) a (by omega) (R.h a (a - 1) (by omega) x) +
      R.h (a + 1) a rfl (L.d a (a + 1) rfl x) =
        x - R.i.f a a rfl (R.p.f a a rfl x) := hx.symm
  have hyy : L.d (b - 1) b (by omega) (R.h b (b - 1) (by omega) y) +
      R.h (b + 1) b rfl (L.d b (b + 1) rfl y) =
        y - R.i.f b b rfl (R.p.f b b rfl y) := hy.symm
  simp only [smul_add, smul_smul, sgn_mul_self, one_smul, neg_smul]
  calc
    _ = P.P a b (c + 1) (by omega)
          (L.d (a - 1) a (by omega) (R.h a (a - 1) (by omega) x) +
            R.h (a + 1) a rfl (L.d a (a + 1) rfl x)) y +
        P.P a b (c + 1) (by omega) (R.i.f a a rfl (R.p.f a a rfl x))
          (L.d (b - 1) b (by omega) (R.h b (b - 1) (by omega) y) +
            R.h (b + 1) b rfl (L.d b (b + 1) rfl y)) := by
      rw [LinearMap.map_add₂, map_add]
      abel
    _ = _ := by rw [hxx, hyy, LinearMap.map_sub₂, map_sub]; abel

/-- The tensor-homotopy identity with arbitrary neighboring indices. -/
theorem cupHomotopy_identity_of (a a₁ b b₁ c c₁ : ℤ)
    (h : a + b = c + 1) (ha : a + 1 = a₁) (hb : b + 1 = b₁) (hc : c + 1 = c₁)
    (x : L.X a) (y : L.X b) :
    T.d c c₁ hc (cupHomotopy R P a b c h x y) +
      cupHomotopy R P a₁ b c₁ (by omega) (L.d a a₁ ha x) y +
      sgn a • cupHomotopy R P a b₁ c₁ (by omega) x (L.d b b₁ hb y) =
    P.P a b c₁ (by omega) x y - P.P a b c₁ (by omega)
      (R.i.f a a rfl (R.p.f a a rfl x)) (R.i.f b b rfl (R.p.f b b rfl y)) := by
  subst ha hb hc
  exact cupHomotopy_identity R P a b c h x y

end TensorHomotopy

/-- The identity chain map transports a pairing value to an equal target index. -/
theorem pair_cast {A : Type} [CommRing A] {X Y T : GCx A} (P : GPair X Y T)
    (a b c k : ℤ) (h : a + b = c) (hk : c = k) (x : X.X a) (y : Y.X b) :
    (gHomId T).f c k hk (P.P a b c h x y) = P.P a b k (by omega) x y := by
  subst hk
  rfl

section Target

variable {A : Type} [CommRing A] {E T : GCx A} (r : GHom E T)

/-- A homotopy pullback target for exact cup compatibility. -/
def replacementTarget : GCx A :=
  selCx { G := E, U := T, L := T, res := r, ι := gHomId T }

/-- The local target projection of the homotopy pullback. -/
def replacementRes : GHom (replacementTarget r) T where
  f a b h := by subst h; exact (LinearMap.fst A _ _).comp (LinearMap.snd A _ _)
  comm a a₁ b b₁ hab ha hb ha'b' z := by subst hab ha'b'; rfl

/-- The local target projection respects equal index names. -/
theorem replacementRes_value (a b : ℤ) (h : a = b)
    (e : E.X a) (t : T.X a) (y : T.X (a - 1)) :
    (replacementRes r).f a b h (e, t, y) = (gHomId T).f a b h t := by
  subst h
  rfl

/-- The compact target maps to the original compact target by adding its
two local correction coordinates. -/
def replacementConeMap : GHom (coneCx (replacementRes r)) (coneCx r) where
  f a b h := by
    subst h
    exact (LinearMap.fst A (E.X a) (T.X a × T.X (a - 1)) ∘ₗ
      LinearMap.fst A ((replacementTarget r).X a) (T.X (a - 1))).prod
      (((LinearMap.snd A (T.X a) (T.X (a - 1)) ∘ₗ
          LinearMap.snd A (E.X a) (T.X a × T.X (a - 1))) ∘ₗ
          LinearMap.fst A ((replacementTarget r).X a) (T.X (a - 1))) +
        LinearMap.snd A ((replacementTarget r).X a) (T.X (a - 1)))
  comm a a₁ b b₁ hab ha hb ha'b' z := by
    subst hab ha'b'
    obtain ⟨⟨e, t, y⟩, w⟩ := z
    refine Prod.ext rfl ?_
    change (r.f a (a₁ - 1) (by omega) e - (gHomId T).f a (a₁ - 1) (by omega) t -
        T.d (a - 1) (a₁ - 1) (by omega) y) +
      ((replacementRes r).f a (a₁ - 1) (by omega) (e, t, y) -
        T.d (a - 1) (a₁ - 1) (by omega) w) =
      r.f a (a₁ - 1) (by omega) e - T.d (a - 1) (a₁ - 1) (by omega) (y + w)
    rw [replacementRes_value, map_add]
    abel

/-- Evaluation of the compact-target comparison. -/
theorem replacementConeMap_apply (n : ℤ) (e : E.X n) (t : T.X n)
    (y w : T.X (n - 1)) :
    (replacementConeMap r).f n n rfl ((e, t, y), w) = (e, y + w) := rfl

end Target

section CompactComparison

variable {A : Type} [CommRing A] {X L S : GCx A}
  (R : GRetract L S) (f : GHom X L)

/-- The elementary identity used to compare compact cones. -/
theorem localConeInclusion_aux (a a₁ k : ℤ) (ha : a + 1 = a₁) (hk : a = k) (x : X.X a) :
    R.i.f k k rfl (R.p.f k k rfl (f.f a k hk x)) +
      R.h a₁ k (by omega) (f.f a₁ a₁ rfl (X.d a a₁ ha x)) =
    f.f a k hk x - L.d (a - 1) k (by omega)
      (R.h a (a - 1) (by omega) (f.f a a rfl x)) := by
  subst hk
  have h := R.homotopy_of a (a - 1) a₁ (by omega) ha (f.f a a rfl x)
  rw [ghom_comm_d f]
  linear_combination (norm := abel) -h

/-- The comparison from the split compact cone to the actual compact
cone, with the required localization homotopy correction. -/
def compactInclusion : GHom (coneCx (ghomComp f R.p)) (coneCx f) where
  f a b hab := by
    subst hab
    exact (LinearMap.fst A (X.X a) (S.X (a - 1))).prod
      ((R.i.f (a - 1) (a - 1) rfl ∘ₗ LinearMap.snd A (X.X a) (S.X (a - 1))) +
        (R.h a (a - 1) (by omega) ∘ₗ f.f a a rfl ∘ₗ LinearMap.fst A (X.X a) (S.X (a - 1))))
  comm a a₁ b b₁ hab ha hb ha'b' z := by
    subst hab ha'b'
    obtain ⟨x, y⟩ := z
    refine Prod.ext rfl ?_
    change R.i.f (a₁ - 1) (a₁ - 1) rfl
        (R.p.f (a₁ - 1) (a₁ - 1) rfl (f.f a (a₁ - 1) (by omega) x) -
          S.d (a - 1) (a₁ - 1) (by omega) y) +
        R.h a₁ (a₁ - 1) (by omega) (f.f a₁ a₁ rfl (X.d a a₁ ha x)) =
      f.f a (a₁ - 1) (by omega) x - L.d (a - 1) (a₁ - 1) (by omega)
        (R.i.f (a - 1) (a - 1) rfl y + R.h a (a - 1) (by omega) (f.f a a rfl x))
    rw [map_sub, map_add, ghom_comm_d R.i]
    have h := localConeInclusion_aux R f a a₁ (a₁ - 1) ha (by omega) x
    linear_combination (norm := abel) h

/-- The comparison in the other direction projects the local coordinate. -/
def compactProjection : GHom (coneCx f) (coneCx (ghomComp f R.p)) where
  f a b hab := by
    subst hab
    exact LinearMap.prodMap (LinearMap.id : X.X a →ₗ[A] X.X a)
      (R.p.f (a - 1) (a - 1) rfl)
  comm a a₁ b b₁ hab ha hb ha'b' z := by
    subst hab ha'b'
    obtain ⟨x, y⟩ := z
    refine Prod.ext rfl ?_
    change R.p.f (a₁ - 1) (a₁ - 1) rfl
      (f.f a (a₁ - 1) (by omega) x - L.d (a - 1) (a₁ - 1) (by omega) y) = _
    rw [map_sub, ghom_comm_d R.p]
    rfl

/-- The comparison maps of compact cones preserve the split cone exactly. -/
theorem compactProjection_inclusion (n : ℤ) (z : (coneCx (ghomComp f R.p)).X n) :
    (compactProjection R f).f n n rfl ((compactInclusion R f).f n n rfl z) = z := by
  obtain ⟨x, y⟩ := z
  change (x, R.p.f (n - 1) (n - 1) rfl
    (R.i.f (n - 1) (n - 1) rfl y + R.h n (n - 1) (by omega) (f.f n n rfl x))) = (x, y)
  rw [map_add, R.p_i, R.p_h, add_zero]

/-- The compact-cone contraction. -/
def compactHomotopy (a b : ℤ) (hab : b + 1 = a) :
    (coneCx f).X a →ₗ[A] (coneCx f).X b :=
  (0 : (coneCx f).X a →ₗ[A] X.X b).prod
    (-(R.h (a - 1) (b - 1) (by omega) ∘ₗ LinearMap.snd A (X.X a) (L.X (a - 1))))

/-- Reindexing a local homotopy applied to a localization. -/
theorem localHomotopy_congr (a k b : ℤ) (hk : a = k) (hab : b + 1 = a) (x : X.X a) :
    R.h k b (by omega) (f.f a k hk x) = R.h a b hab (f.f a a rfl x) := by
  subst hk
  rfl

/-- Compact-cone contraction identity. -/
theorem compactHomotopy_identity (n : ℤ) (z : (coneCx f).X n) :
    z - (compactInclusion R f).f n n rfl ((compactProjection R f).f n n rfl z) =
      (coneCx f).d (n - 1) n (by omega) (compactHomotopy R f n (n - 1) (by omega) z) +
      compactHomotopy R f (n + 1) n rfl ((coneCx f).d n (n + 1) rfl z) := by
  obtain ⟨x, y⟩ := z
  refine Prod.ext ?_ ?_
  · change x - x = X.d (n - 1) n (by omega) 0 + 0
    rw [sub_self, map_zero, add_zero]
  · change y - (R.i.f (n - 1) (n - 1) rfl (R.p.f (n - 1) (n - 1) rfl y) +
        R.h n (n - 1) (by omega) (f.f n n rfl x)) =
      (f.f (n - 1) (n - 1) rfl 0 -
          L.d (n - 1 - 1) (n - 1) (by omega) (-R.h (n - 1) (n - 1 - 1) (by omega) y)) +
        -R.h (n + 1 - 1) (n - 1) (by omega)
          (f.f n (n + 1 - 1) (by omega) x - L.d (n - 1) (n + 1 - 1) (by omega) y)
    rw [map_zero, map_neg, zero_sub, neg_neg, map_sub,
      localHomotopy_congr R f n (n + 1 - 1) (n - 1) (by omega) (by omega)]
    have h := R.homotopy_of (n - 1) (n - 1 - 1) (n + 1 - 1) (by omega) (by omega) y
    linear_combination (norm := abel) h

/-- The local deformation retract gives an actual compact-cone
homotopy equivalence, not merely equal cohomology dimensions. -/
def compactRetraction : GRetract (coneCx f) (coneCx (ghomComp f R.p)) where
  i := compactInclusion R f
  p := compactProjection R f
  h := compactHomotopy R f
  p_i := compactProjection_inclusion R f
  homotopy := compactHomotopy_identity R f
  h_h a b c hab hbc z := by
    obtain ⟨x, y⟩ := z
    refine Prod.ext rfl ?_
    change -R.h (b - 1) (c - 1) (by omega) (-R.h (a - 1) (b - 1) (by omega) y) = 0
    rw [map_neg, neg_neg, R.h_h]
  h_i a b hab z := by
    obtain ⟨x, y⟩ := z
    refine Prod.ext rfl ?_
    change -R.h (a - 1) (b - 1) (by omega)
      (R.i.f (a - 1) (a - 1) rfl y + R.h a (a - 1) (by omega) (f.f a a rfl x)) = 0
    rw [map_add, R.h_i, R.h_h, add_zero, neg_zero]
  p_h a b hab z := by
    obtain ⟨x, y⟩ := z
    refine Prod.ext rfl ?_
    change R.p.f (b - 1) (b - 1) rfl (-R.h (a - 1) (b - 1) (by omega) y) = 0
    rw [map_neg, R.p_h, neg_zero]

end CompactComparison

section TraceIdentities

variable {A : Type} [CommRing A] {L S T : GCx A}
  (R : GRetract L S) (P : GPair L L T) (τ : T.X 2 →ₗ[A] A)
  (hτ : ∀ z, τ (T.d 1 2 rfl z) = 0)

include hτ in
/-- The local trace of the Leibniz rule in total degree one. -/
theorem traceCup_leib_of (a a₁ b b₁ : ℤ) (h : a + b = 1)
    (ha : a + 1 = a₁) (hb : b + 1 = b₁) (x : L.X a) (y : L.X b) :
    τ (P.P a₁ b 2 (by omega) (L.d a a₁ ha x) y) +
      sgn a • τ (P.P a b₁ 2 (by omega) x (L.d b b₁ hb y)) = 0 := by
  have h0 := hτ (P.P a b 1 h x y)
  rw [P.leib a a₁ b b₁ 1 2 h ha hb rfl x y, map_add, map_zsmul] at h0
  exact h0

include hτ in
/-- The tensor-contraction correction agrees with the compact-cone
homotopy correction after the local trace. -/
theorem traceCup_correction (a b : ℤ) (h : a + b = 3)
    (x : L.X a) (y : L.X b) (z : S.X (b - 1)) :
    τ (cupHomotopy R P a b 2 (by omega) x y) +
      sgn a • τ (P.P a (b - 1) 2 (by omega)
        (R.i.f a a rfl (R.p.f a a rfl x)) (R.i.f (b - 1) (b - 1) rfl z)) -
      sgn a • τ (P.P a (b - 1) 2 (by omega) x
        (R.i.f (b - 1) (b - 1) rfl z + R.h b (b - 1) (by omega) y)) =
    τ (P.P (a - 1) b 2 (by omega) (R.h a (a - 1) (by omega) x)
      (y - L.d (b - 1) b (by omega)
        (R.i.f (b - 1) (b - 1) rfl z + R.h b (b - 1) (by omega) y))) +
      sgn (a + 1) • τ (P.P a (b - 1) 2 (by omega)
        (R.h (a + 1) a rfl (L.d a (a + 1) rfl x))
        (R.i.f (b - 1) (b - 1) rfl z + R.h b (b - 1) (by omega) y)) := by
  let w : L.X (b - 1) := R.i.f (b - 1) (b - 1) rfl z + R.h b (b - 1) (by omega) y
  have hL := traceCup_leib_of P τ hτ (a - 1) a (b - 1) b (by omega)
    (by omega) (by omega) (R.h a (a - 1) (by omega) x) w
  rw [sgn_pred] at hL
  have hR := congrArg (fun u => τ (P.P a (b - 1) 2 (by omega) u w)) (R.homotopy a x)
  rw [LinearMap.map_sub₂, LinearMap.map_add₂, map_sub, map_add] at hR
  rw [cupHomotopy_apply_of R P a b 2 (a - 1) (b - 1) (by omega) (by omega) (by omega),
    map_add, map_zsmul, map_add, map_add, map_sub, map_sub, sgn_succ]
  change _ = τ (P.P (a - 1) b 2 (by omega) (R.h a (a - 1) (by omega) x) y) -
      τ (P.P (a - 1) b 2 (by omega) (R.h a (a - 1) (by omega) x)
        (L.d (b - 1) b (by omega) w)) +
      -(sgn a) • τ (P.P a (b - 1) 2 (by omega)
        (R.h (a + 1) a rfl (L.d a (a + 1) rfl x)) w)
  have hR' := congrArg (fun s : A => sgn a • s) hR
  have hL' := congrArg (fun s : A => sgn a • s) hL
  dsimp [w] at hR' hL' ⊢
  simp only [map_add, smul_add, smul_sub, smul_neg, neg_smul,
    smul_smul, sgn_mul_self, smul_zero, one_smul] at hR' hL' ⊢
  linear_combination (norm := abel) -hR' - hL'

end TraceIdentities

/-- A target-index cast commutes with a chain map. -/
theorem ghom_cast {A : Type} [CommRing A] {X Y : GCx A} (f : GHom X Y)
    (a k : ℤ) (hk : a = k) (x : X.X a) :
    (gHomId Y).f a k hk (f.f a a rfl x) = f.f a k hk x := by subst hk; rfl

/-- A target-index cast commutes with a differential. -/
theorem differential_cast {A : Type} [CommRing A] (Y : GCx A)
    (a b k : ℤ) (hab : a + 1 = b) (hk : b = k) (x : Y.X a) :
    (gHomId Y).f b k hk (Y.d a b hab x) = Y.d a k (by omega) x := by subst hk; rfl

/-- A target-index cast does not change a trace pairing value. -/
theorem tracePair_right_cast {A : Type} [CommRing A] {X Y T : GCx A}
    (P : GPair X Y T) (τ : T.X 2 →ₗ[A] A)
    (a b k : ℤ) (h : a + b = 2) (hk : b = k) (x : X.X a) (y : Y.X b) :
    τ (P.P a k 2 (by omega) x ((gHomId Y).f b k hk y)) = τ (P.P a b 2 h x y) := by
  subst hk
  rfl

section Replacement

variable {A : Type} [CommRing A] (D : SelData A)
  (R : GRetract D.L (splitLocalComplex A)) (Q : SelPairData D D)

/-- The same global and condition complexes, with the full local complex
replaced by its split model. -/
abbrev replacementData : SelData A :=
  splitSelData D.G (ghomComp D.res R.p) D.U (ghomComp D.ι R.p)

/-- The local cup product transported along the inclusion of the split model. -/
def replacementLocalCup :
    GPair (splitLocalComplex A) (splitLocalComplex A) Q.EL := R.restrictPair R Q.cupL

/-- The global cup product in the homotopy pullback target. -/
def replacementGlobalCup : GPair D.G D.G (replacementTarget Q.resE) where
  P a b c h :=
    LinearMap.mk₂ A
      (fun x y => (Q.cupG.P a b c h x y,
        (replacementLocalCup D R Q).P a b c h
          ((ghomComp D.res R.p).f a a rfl x) ((ghomComp D.res R.p).f b b rfl y),
        cupHomotopy R Q.cupL a b (c - 1) (by omega)
          (D.res.f a a rfl x) (D.res.f b b rfl y)))
      (fun x x' y => by
        simp only [map_add]
        rfl)
      (fun s x y => by
        simp only [map_smul]
        rfl)
      (fun x y y' => by simp only [map_add]; rfl)
      (fun s x y => by simp only [map_smul]; rfl)
  leib a a₁ b b₁ c c₁ h ha hb hc x y := by
    subst ha hb hc
    refine Prod.ext (Q.cupG.leib a (a + 1) b (b + 1) c (c + 1) h rfl rfl rfl x y)
      (Prod.ext ?_ ?_)
    · change Q.EL.d c (c + 1) rfl
          ((replacementLocalCup D R Q).P a b c h
            ((ghomComp D.res R.p).f a a rfl x) ((ghomComp D.res R.p).f b b rfl y)) =
        (replacementLocalCup D R Q).P (a + 1) b (c + 1) (by omega)
          ((ghomComp D.res R.p).f (a + 1) (a + 1) rfl (D.G.d a (a + 1) rfl x))
          ((ghomComp D.res R.p).f b b rfl y) +
        sgn a • (replacementLocalCup D R Q).P a (b + 1) (c + 1) (by omega)
          ((ghomComp D.res R.p).f a a rfl x)
          ((ghomComp D.res R.p).f (b + 1) (b + 1) rfl (D.G.d b (b + 1) rfl y))
      rw [ghom_comm_d, ghom_comm_d]
      exact (replacementLocalCup D R Q).leib a (a + 1) b (b + 1) c (c + 1) h
        rfl rfl rfl _ _
    · let k : ℤ := c + 1 - 1
      have hk : c = k := by dsimp [k]; omega
      have hH := cupHomotopy_identity_of R Q.cupL a (a + 1) b (b + 1) (c - 1) k
        (by omega) rfl rfl (by omega) (D.res.f a a rfl x) (D.res.f b b rfl y)
      have hcomp := Q.compat a b c a b k h (by omega) rfl rfl hk x y
      change Q.resE.f c k hk (Q.cupG.P a b c h x y) -
          (gHomId Q.EL).f c k hk
            ((replacementLocalCup D R Q).P a b c h
              ((ghomComp D.res R.p).f a a rfl x) ((ghomComp D.res R.p).f b b rfl y)) -
          Q.EL.d (c - 1) k (by omega)
            (cupHomotopy R Q.cupL a b (c - 1) (by omega)
              (D.res.f a a rfl x) (D.res.f b b rfl y)) =
        cupHomotopy R Q.cupL (a + 1) b k (by omega)
          (D.res.f (a + 1) (a + 1) rfl (D.G.d a (a + 1) rfl x)) (D.res.f b b rfl y) +
        sgn a • cupHomotopy R Q.cupL a (b + 1) k (by omega)
          (D.res.f a a rfl x) (D.res.f (b + 1) (b + 1) rfl (D.G.d b (b + 1) rfl y))
      rw [hcomp, pair_cast, ghom_comm_d D.res, ghom_comm_d D.res]
      change Q.cupL.P a b k (by omega) (D.res.f a a rfl x) (D.res.f b b rfl y) -
          Q.cupL.P a b k (by omega)
            (R.i.f a a rfl (R.p.f a a rfl (D.res.f a a rfl x)))
            (R.i.f b b rfl (R.p.f b b rfl (D.res.f b b rfl y))) -
          Q.EL.d (c - 1) k (by omega)
            (cupHomotopy R Q.cupL a b (c - 1) (by omega)
              (D.res.f a a rfl x) (D.res.f b b rfl y)) = _
      linear_combination (norm := abel) -hH

/-- The same-condition isotropy homotopy is corrected by the tensor
contraction; it is not replaced by an orthogonality assertion. -/
def replacementIsotropy (a b c : ℤ) (h : a + b = c + 1) :
    D.U.X a →ₗ[A] D.U.X b →ₗ[A] Q.EL.X c :=
  Q.hU a b c h - (cupHomotopy R Q.cupL a b c h).compl₁₂
    (D.ι.f a a rfl) (D.ι.f b b rfl)

/-- The transported same-condition cup data with exact localization
compatibility in every degree. -/
def replacementPair : SelPairData (replacementData D R) (replacementData D R) where
  E := replacementTarget Q.resE
  EL := Q.EL
  resE := replacementRes Q.resE
  cupG := replacementGlobalCup D R Q
  cupL := replacementLocalCup D R Q
  compat a b c a' b' c' h h' ha hb hc x y := by subst ha hb hc; rfl
  hU := replacementIsotropy D R Q
  isotropy a a₁ b b₁ c c₁ h ha hb hc u v := by
    subst ha hb hc
    have hI := Q.isotropy a (a + 1) b (b + 1) c (c + 1) h rfl rfl rfl u v
    have hH := cupHomotopy_identity R Q.cupL a b c h
      (D.ι.f a a rfl u) (D.ι.f b b rfl v)
    simp only [replacementIsotropy, LinearMap.sub_apply, LinearMap.compl₁₂_apply,
      map_sub, smul_sub]
    change Q.EL.d c (c + 1) rfl (Q.hU a b c h u v) -
        Q.EL.d c (c + 1) rfl (cupHomotopy R Q.cupL a b c h (D.ι.f a a rfl u) (D.ι.f b b rfl v)) +
        (Q.hU (a + 1) b (c + 1) (by omega) (D.U.d a (a + 1) rfl u) v -
          cupHomotopy R Q.cupL (a + 1) b (c + 1) (by omega)
            (D.ι.f (a + 1) (a + 1) rfl (D.U.d a (a + 1) rfl u)) (D.ι.f b b rfl v)) +
        (sgn a • Q.hU a (b + 1) (c + 1) (by omega) u (D.U.d b (b + 1) rfl v) -
          sgn a • cupHomotopy R Q.cupL a (b + 1) (c + 1) (by omega)
            (D.ι.f a a rfl u) (D.ι.f (b + 1) (b + 1) rfl (D.U.d b (b + 1) rfl v))) = _
    rw [ghom_comm_d D.ι, ghom_comm_d D.ι]
    dsimp [replacementLocalCup, GRetract.restrictPair, ghomComp]
    linear_combination (norm := abel) hI - hH

variable (tr : (coneCx Q.resE).X 3 →ₗ[A] A)
  (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)

/-- The transported global compact trace. -/
def replacementTrace : (coneCx (replacementPair D R Q).resE).X 3 →ₗ[A] A :=
  tr.comp ((replacementConeMap Q.resE).f 3 3 rfl)

include htr in
/-- The transported trace kills coboundaries by the proved chain-map
identity, without assuming the desired trace condition. -/
theorem replacementTrace_kills (z : (coneCx (replacementPair D R Q).resE).X 2) :
    replacementTrace D R Q tr ((coneCx (replacementPair D R Q).resE).d 2 3 rfl z) = 0 := by
  change tr ((replacementConeMap Q.resE).f 3 3 rfl
    ((coneCx (replacementRes Q.resE)).d 2 3 rfl z)) = 0
  rw [ghom_comm_d (replacementConeMap Q.resE)]
  exact htr _

/-- The compact trace evaluates by adding the local homotopy correction
to the local cup coordinate. -/
theorem replacementTrace_apply (e : Q.E.X 3) (t : Q.EL.X 3) (y w : Q.EL.X (3 - 1)) :
    replacementTrace D R Q tr ((e, t, y), w) = tr (e, y + w) := rfl

/-- The local component of the original compact trace. -/
def localTrace : Q.EL.X 2 →ₗ[A] A := tr.comp (LinearMap.inr A (Q.E.X 3) (Q.EL.X 2))

include htr in
/-- The local trace kills local degree-two coboundaries. -/
theorem localTrace_kills (y : Q.EL.X 1) : localTrace D Q tr (Q.EL.d 1 2 rfl y) = 0 := by
  have h := htr ((0, y) : (coneCx Q.resE).X 2)
  change tr (Q.E.d 2 3 rfl 0, Q.resE.f 2 2 rfl 0 - Q.EL.d 1 2 rfl y) = 0 at h
  rw [map_zero, map_zero, zero_sub] at h
  have he : ((0, -Q.EL.d 1 2 rfl y) : (coneCx Q.resE).X 3) = -(0, Q.EL.d 1 2 rfl y) := by
    exact Prod.ext (by simp) rfl
  rw [he, map_neg, neg_eq_zero] at h
  exact h

include htr in
/-- Same-condition isotropy forces the trace of the cup of two
condition cocycles to vanish, even when the isotropy homotopy is nonzero. -/
theorem sameConditionCup_trace_zero
    (u v : D.U.X 1) (hu : D.U.d 1 2 rfl u = 0) (hv : D.U.d 1 2 rfl v = 0) :
    tr (0, Q.cupL.P 1 1 2 rfl (D.ι.f 1 1 rfl u) (D.ι.f 1 1 rfl v)) = 0 := by
  have hI := Q.isotropy 1 2 1 2 1 2 rfl rfl rfl rfl u v
  rw [hu, hv, LinearMap.map_zero₂, map_zero, smul_zero, add_zero, add_zero] at hI
  change localTrace D Q tr (Q.cupL.P 1 1 2 rfl (D.ι.f 1 1 rfl u) (D.ι.f 1 1 rfl v)) = 0
  rw [← hI]
  exact localTrace_kills D Q tr htr _

include htr in
/-- A condition whose cycles surject onto the whole local degree-one
space cannot be self-isotropic for a nonzero retained mixed cup pairing. -/
theorem fullDegreeOne_selfPair_obstruction
    (hU : ∀ u : D.U.X 1, D.U.d 1 2 rfl u = 0)
    (hι : Function.Surjective (D.ι.f 1 1 rfl)) (x y : D.L.X 1)
    (hxy : tr (0, Q.cupL.P 1 1 2 rfl x y) ≠ 0) : False := by
  obtain ⟨u, rfl⟩ := hι x
  obtain ⟨v, rfl⟩ := hι y
  exact hxy (sameConditionCup_trace_zero D Q tr htr u v (hU u) (hU v))

/-- The original compact local coordinate of a split compact cochain. -/
def compactCoordinate (n : ℤ) : (compactCx (replacementData D R)).X n →ₗ[A] D.L.X (n - 1) :=
  (LinearMap.snd A (D.G.X n) (D.L.X (n - 1))).comp
    ((compactInclusion R D.res).f n n rfl)

/-- The original compact local coordinate on a tuple. -/
theorem compactCoordinate_apply (n : ℤ) (x : D.G.X n) (y : (splitLocalComplex A).X (n - 1)) :
    compactCoordinate D R n (x, y) =
      R.i.f (n - 1) (n - 1) rfl y + R.h n (n - 1) (by omega) (D.res.f n n rfl x) := rfl

/-- The compact local coordinate commutes with the compact differential,
including the necessary target-index transport. -/
theorem compactCoordinate_boundary (n n₁ : ℤ) (hn : n + 1 = n₁)
    (z : (compactCx (replacementData D R)).X n) :
    compactCoordinate D R n₁ ((compactCx (replacementData D R)).d n n₁ hn z) =
      (gHomId D.L).f n (n₁ - 1) (by omega)
        (D.res.f n n rfl z.1 - D.L.d (n - 1) n (by omega) (compactCoordinate D R n z)) := by
  have h := congrArg Prod.snd
    ((compactInclusion R D.res).comm n n₁ n n₁ rfl hn hn rfl z)
  change compactCoordinate D R n₁ ((compactCx (replacementData D R)).d n n₁ hn z) =
      D.res.f n (n₁ - 1) (by omega) z.1 -
        D.L.d (n - 1) (n₁ - 1) (by omega) (compactCoordinate D R n z) at h
  rw [map_sub, ghom_cast, differential_cast]
  exact h

/-- Evaluation of a global duality map before local replacement. -/
theorem originalGlobal_eval (a : ℤ) (x : D.G.X a) (z : (compactCx D).X (3 - a)) :
    asDual ((globalDualityMap Q tr htr).f a a rfl x) z =
      tr (Q.cupG.P a (3 - a) 3 (by omega) x z.1,
        sgn a • Q.cupL.P a (3 - a - 1) 2 (by omega) (D.res.f a a rfl x) z.2) := by
  change tr (selCupFun Q a (3 - a) 3 (by omega) (x, 0, 0) (z.1, 0, z.2)) = _
  simp only [selCupFun, map_zero, zero_add, add_zero]
  rfl

/-- The original global duality map pulled back along the proved compact
comparison. -/
def pulledGlobalDuality : GHom D.G (dualCx (compactCx (replacementData D R)) 3) :=
  ghomComp (globalDualityMap Q tr htr) (dualHom (compactInclusion R D.res) 3)

/-- Evaluation of the pulled global duality map. -/
theorem pulledGlobal_eval (a : ℤ) (x : D.G.X a)
    (z : (compactCx (replacementData D R)).X (3 - a)) :
    asDual ((pulledGlobalDuality D R Q tr htr).f a a rfl x) z =
      tr (Q.cupG.P a (3 - a) 3 (by omega) x z.1,
        sgn a • Q.cupL.P a (3 - a - 1) 2 (by omega) (D.res.f a a rfl x)
          (compactCoordinate D R (3 - a) z)) := by
  change asDual ((globalDualityMap Q tr htr).f a a rfl x)
    ((compactInclusion R D.res).f (3 - a) (3 - a) rfl z) = _
  rw [originalGlobal_eval]
  rfl

/-- The explicit global cochain homotopy for replacement of the local complex. -/
def globalHomotopy (a b : ℤ) (hab : b + 1 = a) :
    D.G.X a →ₗ[A] (dualCx (compactCx (replacementData D R)) 3).X b :=
  sgn a • (((Q.cupL.P (a - 1) (3 - b - 1) 2 (by omega)).compl₁₂
      (R.h a (a - 1) (by omega) ∘ₗ D.res.f a a rfl)
      (compactCoordinate D R (3 - b))).compr₂ (localTrace D Q tr))

/-- The global homotopy with an explicitly named local predecessor. -/
theorem globalHomotopy_apply_of (a b a₀ : ℤ) (hab : b + 1 = a) (ha : a₀ + 1 = a)
    (x : D.G.X a) (z : (compactCx (replacementData D R)).X (3 - b)) :
    asDual (globalHomotopy D R Q tr a b hab x) z =
      sgn a • localTrace D Q tr (Q.cupL.P a₀ (3 - b - 1) 2 (by omega)
        (R.h a a₀ ha (D.res.f a a rfl x)) (compactCoordinate D R (3 - b) z)) := by
  obtain rfl : a₀ = a - 1 := by omega
  rfl

include htr in
/-- The transported global duality map is homotopic to the pullback of
the original global duality map. -/
theorem globalHomotopy_identity (a : ℤ) (x : D.G.X a) :
    (globalDualityMap (replacementPair D R Q) (replacementTrace D R Q tr)
        (replacementTrace_kills D R Q tr htr)).f a a rfl x -
      (pulledGlobalDuality D R Q tr htr).f a a rfl x =
    (dualCx (compactCx (replacementData D R)) 3).d (a - 1) a (by omega)
        (globalHomotopy D R Q tr a (a - 1) (by omega) x) +
      globalHomotopy D R Q tr (a + 1) a rfl (D.G.d a (a + 1) rfl x) := by
  apply dualCx_ext
  intro z
  have hT := traceCup_correction R Q.cupL (localTrace D Q tr) (localTrace_kills D Q tr htr)
    a (3 - a) (by omega) (D.res.f a a rfl x) (D.res.f (3 - a) (3 - a) rfl z.1) z.2
  have hZ := compactCoordinate_boundary D R (3 - a) (3 - (a - 1)) (by omega) z
  have hK₁ := globalHomotopy_apply_of D R Q tr a (a - 1) (a - 1) (by omega) (by omega) x
    ((compactCx (replacementData D R)).d (3 - a) (3 - (a - 1)) (by omega) z)
  have hK₂ := globalHomotopy_apply_of D R Q tr (a + 1) a a rfl rfl (D.G.d a (a + 1) rfl x) z
  rw [hZ, tracePair_right_cast] at hK₁
  rw [ghom_comm_d D.res] at hK₂
  have hsign : -(sgn (a - 1)) = sgn a := by rw [sgn_pred, neg_neg]
  change asDual
        ((globalDualityMap (replacementPair D R Q) (replacementTrace D R Q tr)
          (replacementTrace_kills D R Q tr htr)).f a a rfl x) z -
      asDual ((pulledGlobalDuality D R Q tr htr).f a a rfl x) z =
    -(sgn (a - 1)) • asDual (globalHomotopy D R Q tr a (a - 1) (by omega) x)
        ((compactCx (replacementData D R)).d (3 - a) (3 - (a - 1)) (by omega) z) +
      asDual (globalHomotopy D R Q tr (a + 1) a rfl (D.G.d a (a + 1) rfl x)) z
  rw [hK₁, hK₂, hsign, smul_smul, sgn_mul_self, one_smul]
  have he := originalGlobal_eval (replacementData D R) (replacementPair D R Q)
    (replacementTrace D R Q tr) (replacementTrace_kills D R Q tr htr) a x z
  rw [he, pulledGlobal_eval]
  change tr (Q.cupG.P a (3 - a) 3 (by omega) x z.1,
      cupHomotopy R Q.cupL a (3 - a) 2 (by omega)
        (D.res.f a a rfl x) (D.res.f (3 - a) (3 - a) rfl z.1) +
      sgn a • Q.cupL.P a (3 - a - 1) 2 (by omega)
        (R.i.f a a rfl (R.p.f a a rfl (D.res.f a a rfl x)))
        (R.i.f (3 - a - 1) (3 - a - 1) rfl z.2)) -
      tr (Q.cupG.P a (3 - a) 3 (by omega) x z.1,
        sgn a • Q.cupL.P a (3 - a - 1) 2 (by omega)
          (D.res.f a a rfl x) (compactCoordinate D R (3 - a) z)) = _
  have htrsplit (e : Q.E.X 3) (v w : Q.EL.X 2) :
      tr (e, v) - tr (e, w) = localTrace D Q tr (v - w) := by
    rw [← map_sub]
    change tr (e - e, v - w) = tr (0, v - w)
    rw [sub_self]
  rw [htrsplit, map_sub, map_add, map_zsmul, map_zsmul]
  exact hT

include htr in
/-- The explicitly constructed global cochain homotopy. -/
def globalComparisonHomotopy :
    Homotopy
      (GHom.toCC (globalDualityMap (replacementPair D R Q) (replacementTrace D R Q tr)
        (replacementTrace_kills D R Q tr htr)))
      (GHom.toCC (pulledGlobalDuality D R Q tr htr)) :=
  homotopyOfIdentities _ _ (globalHomotopy D R Q tr) (by
    intro a
    rw [toCC_d_hom_eq _ a (a + 1) rfl, toCC_d_hom_eq _ (a - 1) a (by omega)]
    apply LinearMap.ext
    intro x
    have h := globalHomotopy_identity D R Q tr htr a x
    change (globalDualityMap (replacementPair D R Q) (replacementTrace D R Q tr)
        (replacementTrace_kills D R Q tr htr)).f a a rfl x =
      globalHomotopy D R Q tr (a + 1) a rfl (D.G.d a (a + 1) rfl x) +
      (dualCx (compactCx (replacementData D R)) 3).d (a - 1) a (by omega)
        (globalHomotopy D R Q tr a (a - 1) (by omega) x) +
      (pulledGlobalDuality D R Q tr htr).f a a rfl x
    linear_combination (norm := abel) h)

include htr in
/-- Global duality survives the local split replacement. The original
quasi-isomorphism may be supplied by the existing stage global duality theorem. -/
theorem replacementGlobal_quasiIso
    (hG : QuasiIso (GHom.toCC (globalDualityMap Q tr htr))) :
    QuasiIso (GHom.toCC (globalDualityMap (replacementPair D R Q) (replacementTrace D R Q tr)
      (replacementTrace_kills D R Q tr htr))) := by
  have hC := ((compactRetraction R D.res).dual 3).quasiIso_p
  have hP : QuasiIso (GHom.toCC (pulledGlobalDuality D R Q tr htr)) := by
    change QuasiIso (GHom.toCC
      (ghomComp (globalDualityMap Q tr htr) (dualHom (compactInclusion R D.res) 3)))
    rw [← GHom.toCC_comp]
    have : QuasiIso (GHom.toCC (globalDualityMap Q tr htr)) := hG
    have : QuasiIso (GHom.toCC (dualHom (compactInclusion R D.res) 3)) := hC
    infer_instance
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap,
    (globalComparisonHomotopy D R Q tr htr).homologyMap_eq n]
  have := hP
  infer_instance

include htr in
/-- The construction produces the exact pairing-and-trace shape of the
split-stage consumer. Its hypotheses refer to the original paired diagram
and an independent local deformation retract. -/
theorem exists_splitPair_trace :
    ∃ (Q' : SelPairData
        (splitSelData D.G (ghomComp D.res R.p) D.U (ghomComp D.ι R.p))
        (splitSelData D.G (ghomComp D.res R.p) D.U (ghomComp D.ι R.p)))
      (tr' : (coneCx Q'.resE).X 3 →ₗ[A] A),
      (∀ z, tr' ((coneCx Q'.resE).d 2 3 rfl z) = 0) ∧
      ∀ (a b : ℤ) (h : a + b = 2)
        (x : (splitLocalComplex A).X a) (y : (splitLocalComplex A).X b),
        tr' (0, Q'.cupL.P a b 2 h x y) =
          tr (0, Q.cupL.P a b 2 h (R.i.f a a rfl x) (R.i.f b b rfl y)) := by
  refine ⟨replacementPair D R Q, replacementTrace D R Q tr,
    replacementTrace_kills D R Q tr htr, ?_⟩
  intro a b h x y
  change tr (0, (0 : Q.EL.X 2) + Q.cupL.P a b 2 h
    (R.i.f a a rfl x) (R.i.f b b rfl y)) = _
  rw [zero_add]

end Replacement

section SecondTransport

variable {A : Type} [CommRing A] (D D' : SelData A)

/-- Cochain identifications of the second coefficient and condition
systems, compatible with actual localization and actual condition maps. -/
structure SecondComparison where
  global : GHom D.G D'.G
  loc : GHom D.L D'.L
  condition : GHom D.U D'.U
  res_comm : ∀ a (x : D.G.X a),
    D'.res.f a a rfl (global.f a a rfl x) = loc.f a a rfl (D.res.f a a rfl x)
  condition_comm : ∀ a (u : D.U.X a),
    D'.ι.f a a rfl (condition.f a a rfl u) = loc.f a a rfl (D.ι.f a a rfl u)

variable {D D'} (C : SecondComparison D D') (Q : SelPairData D D')

/-- Localization compatibility with different names for an equal target index. -/
theorem secondComparison_res_at (a k : ℤ) (hk : a = k) (x : D.G.X a) :
    C.loc.f k k rfl (D.res.f a k hk x) = D'.res.f a k hk (C.global.f a a rfl x) := by
  subst hk
  exact (C.res_comm a x).symm

/-- Pulling back the second coefficient system gives genuine
same-condition cup data, with the original isotropy homotopy retained. -/
def secondPullPair : SelPairData D D where
  E := Q.E
  EL := Q.EL
  resE := Q.resE
  cupG :=
    { P a b c h := (Q.cupG.P a b c h).compl₂ (C.global.f b b rfl)
      leib a a₁ b b₁ c c₁ h ha hb hc x y := by
        change Q.E.d c c₁ hc (Q.cupG.P a b c h x (C.global.f b b rfl y)) = _
        rw [Q.cupG.leib a a₁ b b₁ c c₁ h ha hb hc, ← ghom_comm_d C.global]
        rfl }
  cupL :=
    { P a b c h := (Q.cupL.P a b c h).compl₂ (C.loc.f b b rfl)
      leib a a₁ b b₁ c c₁ h ha hb hc x y := by
        change Q.EL.d c c₁ hc (Q.cupL.P a b c h x (C.loc.f b b rfl y)) = _
        rw [Q.cupL.leib a a₁ b b₁ c c₁ h ha hb hc, ← ghom_comm_d C.loc]
        rfl }
  compat a b c a' b' c' h h' ha hb hc x y := by
    subst ha hb hc
    change Q.resE.f c c rfl (Q.cupG.P a b c h x (C.global.f b b rfl y)) = _
    rw [Q.compat a b c a b c h h rfl rfl rfl, C.res_comm]
    rfl
  hU a b c h := (Q.hU a b c h).compl₂ (C.condition.f b b rfl)
  isotropy a a₁ b b₁ c c₁ h ha hb hc u v := by
    change Q.EL.d c c₁ hc (Q.hU a b c h u (C.condition.f b b rfl v)) +
      Q.hU a₁ b c₁ (by omega) (D.U.d a a₁ ha u) (C.condition.f b b rfl v) +
      sgn a • Q.hU a b₁ c₁ (by omega) u (C.condition.f b₁ b₁ rfl (D.U.d b b₁ hb v)) = _
    rw [ghom_comm_d C.condition]
    rw [Q.isotropy a a₁ b b₁ c c₁ h ha hb hc u (C.condition.f b b rfl v), C.condition_comm]
    rfl

/-- The compact comparison between second coefficient systems. -/
def secondCompactMap : GHom (compactCx D) (compactCx D') where
  f a b h := by subst h; exact LinearMap.prodMap (C.global.f a a rfl) (C.loc.f (a - 1) (a - 1) rfl)
  comm a a₁ b b₁ hab ha hb ha'b' z := by
    subst hab ha'b'
    obtain ⟨x, y⟩ := z
    refine Prod.ext (ghom_comm_d C.global a a₁ ha x) ?_
    change C.loc.f (a₁ - 1) (a₁ - 1) rfl
        (D.res.f a (a₁ - 1) (by omega) x - D.L.d (a - 1) (a₁ - 1) (by omega) y) =
      D'.res.f a (a₁ - 1) (by omega) (C.global.f a a rfl x) -
        D'.L.d (a - 1) (a₁ - 1) (by omega) (C.loc.f (a - 1) (a - 1) rfl y)
    rw [map_sub, ghom_comm_d C.loc, secondComparison_res_at C a (a₁ - 1) (by omega)]

variable (tr : (coneCx Q.resE).X 3 →ₗ[A] A)
  (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)

/-- The global duality map under second-system cochain transport. -/
theorem secondPull_globalMap :
    GHom.toCC (globalDualityMap (secondPullPair C Q) tr htr) =
      GHom.toCC (ghomComp (globalDualityMap Q tr htr) (dualHom (secondCompactMap C) 3)) := by
  apply GHom.toCC_ext
  intro a x
  apply dualCx_ext
  intro z
  change tr (selCupFun (secondPullPair C Q) a (3 - a) 3 (by omega) (x, 0, 0) (z.1, 0, z.2)) =
    tr (selCupFun Q a (3 - a) 3 (by omega) (x, 0, 0)
      (C.global.f (3 - a) (3 - a) rfl z.1, 0, C.loc.f (3 - a - 1) (3 - a - 1) rfl z.2))
  simp only [selCupFun, map_zero, zero_add, add_zero]
  rfl

/-- The compact cochain comparison is bijective in every degree when
its actual global and local cochain comparisons are bijective. -/
theorem secondCompactMap_bijective
    (hG : ∀ n, Function.Bijective (C.global.f n n rfl))
    (hL : ∀ n, Function.Bijective (C.loc.f n n rfl)) (n : ℤ) :
    Function.Bijective ((secondCompactMap C).f n n rfl) := by
  constructor
  · intro x y h
    apply Prod.ext
    · exact (hG n).1 (congrArg Prod.fst h)
    · exact (hL (n - 1)).1 (congrArg Prod.snd h)
  · intro z
    obtain ⟨x, hx⟩ := (hG n).2 z.1
    obtain ⟨y, hy⟩ := (hL (n - 1)).2 z.2
    exact ⟨(x, y), Prod.ext hx hy⟩

/-- A termwise cochain identification induces an actual compact-complex
isomorphism, so its quasi-isomorphy is not an assumed duality conclusion. -/
theorem secondCompactMap_quasiIso
    (hG : ∀ n, Function.Bijective (C.global.f n n rfl))
    (hL : ∀ n, Function.Bijective (C.loc.f n n rfl)) :
    QuasiIso (GHom.toCC (secondCompactMap C)) := by
  let e : (compactCx D).toCC ≅ (compactCx D').toCC :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n => (LinearEquiv.ofBijective ((secondCompactMap C).f n n rfl)
        (secondCompactMap_bijective C hG hL n)).toModuleIso)
      (by
        intro a b hab
        change (GHom.toCC (secondCompactMap C)).f a ≫ (compactCx D').toCC.d a b =
          (compactCx D).toCC.d a b ≫ (GHom.toCC (secondCompactMap C)).f b
        exact (GHom.toCC (secondCompactMap C)).comm a b)
  have he : e.hom = GHom.toCC (secondCompactMap C) := by ext n z; rfl
  rw [← he]
  infer_instance

/-- Global duality under the second-system identification follows from
the actual original global duality and the proved compact identification. -/
theorem secondPull_global_quasiIso [Module.Injective A A]
    (hG : ∀ n, Function.Bijective (C.global.f n n rfl))
    (hL : ∀ n, Function.Bijective (C.loc.f n n rfl))
    (hQ : QuasiIso (GHom.toCC (globalDualityMap Q tr htr))) :
    QuasiIso (GHom.toCC (globalDualityMap (secondPullPair C Q) tr htr)) := by
  rw [secondPull_globalMap, ← GHom.toCC_comp]
  have : QuasiIso (GHom.toCC (globalDualityMap Q tr htr)) := hQ
  have : QuasiIso (GHom.toCC (dualHom (secondCompactMap C) 3)) :=
    dualHom_quasiIso (secondCompactMap C) 3 (secondCompactMap_quasiIso C hG hL)
  infer_instance

/-- The full split-stage pairing, compact trace, and global-duality
conclusion, from the actual paired coefficient systems and cochain comparisons. -/
theorem exists_splitPair_trace_duality_of_second [Module.Injective A A]
    (R : GRetract D.L (splitLocalComplex A))
    (hG : ∀ n, Function.Bijective (C.global.f n n rfl))
    (hL : ∀ n, Function.Bijective (C.loc.f n n rfl))
    (hQ : QuasiIso (GHom.toCC (globalDualityMap Q tr htr))) :
    ∃ (Q' : SelPairData
        (splitSelData D.G (ghomComp D.res R.p) D.U (ghomComp D.ι R.p))
        (splitSelData D.G (ghomComp D.res R.p) D.U (ghomComp D.ι R.p)))
      (tr' : (coneCx Q'.resE).X 3 →ₗ[A] A)
      (htr' : ∀ z, tr' ((coneCx Q'.resE).d 2 3 rfl z) = 0),
      QuasiIso (GHom.toCC (globalDualityMap Q' tr' htr')) ∧
      ∀ (a b : ℤ) (h : a + b = 2)
        (x : (splitLocalComplex A).X a) (y : (splitLocalComplex A).X b),
        tr' (0, Q'.cupL.P a b 2 h x y) =
          tr (0, Q.cupL.P a b 2 h (R.i.f a a rfl x) (C.loc.f b b rfl (R.i.f b b rfl y))) := by
  let Qs := secondPullPair C Q
  let Q' := replacementPair D R Qs
  let tr' := replacementTrace D R Qs tr
  let htr' := replacementTrace_kills D R Qs tr htr
  refine ⟨Q', tr', htr', replacementGlobal_quasiIso D R Qs tr htr
    (secondPull_global_quasiIso C Q tr htr hG hL hQ), ?_⟩
  intro a b h x y
  change tr (0, (0 : Q.EL.X 2) + Q.cupL.P a b 2 h
    (R.i.f a a rfl x) (C.loc.f b b rfl (R.i.f b b rfl y))) = _
  rw [zero_add]

end SecondTransport

section RetractionCoordinates

variable {A : Type} [CommRing A] {X Y S : GCx A}

/-- The inverse of a degreewise bijective cochain comparison. -/
def inverseCochain (Θ : GHom Y S) (hΘ : ∀ n, Function.Bijective (Θ.f n n rfl)) : GHom S Y where
  f a b hab := by
    subst hab
    exact (LinearEquiv.ofBijective (Θ.f a a rfl) (hΘ a)).symm.toLinearMap
  comm a a₁ b b₁ hab ha hb ha'b' z := by
    subst hab ha'b'
    apply (hΘ a₁).1
    change Θ.f a₁ a₁ rfl
        ((LinearEquiv.ofBijective (Θ.f a₁ a₁ rfl) (hΘ a₁)).symm (S.d a a₁ ha z)) =
      Θ.f a₁ a₁ rfl (Y.d a a₁ ha
        ((LinearEquiv.ofBijective (Θ.f a a rfl) (hΘ a)).symm z))
    rw [ghom_comm_d Θ]
    exact (LinearEquiv.ofBijective (Θ.f a₁ a₁ rfl) (hΘ a₁)).apply_symm_apply _ |>.trans
      (congrArg (S.d a a₁ ha)
        ((LinearEquiv.ofBijective (Θ.f a a rfl) (hΘ a)).apply_symm_apply z)).symm

/-- The degreewise inverse is a left inverse. -/
theorem inverseCochain_left (Θ : GHom Y S) (hΘ : ∀ n, Function.Bijective (Θ.f n n rfl))
    (n : ℤ) (y : Y.X n) :
    (inverseCochain Θ hΘ).f n n rfl (Θ.f n n rfl y) = y :=
  (LinearEquiv.ofBijective (Θ.f n n rfl) (hΘ n)).symm_apply_apply y

/-- The degreewise inverse is a right inverse. -/
theorem inverseCochain_right (Θ : GHom Y S) (hΘ : ∀ n, Function.Bijective (Θ.f n n rfl))
    (n : ℤ) (y : S.X n) :
    Θ.f n n rfl ((inverseCochain Θ hΘ).f n n rfl y) = y :=
  (LinearEquiv.ofBijective (Θ.f n n rfl) (hΘ n)).apply_symm_apply y

/-- A cochain isomorphism relabels a normalized deformation retract. -/
def relabelRetraction (R : GRetract X Y) (Θ : GHom Y S)
    (hΘ : ∀ n, Function.Bijective (Θ.f n n rfl)) : GRetract X S where
  i := ghomComp (inverseCochain Θ hΘ) R.i
  p := ghomComp R.p Θ
  h := R.h
  p_i n y := by
    change Θ.f n n rfl (R.p.f n n rfl (R.i.f n n rfl ((inverseCochain Θ hΘ).f n n rfl y))) = y
    rw [R.p_i, inverseCochain_right]
  homotopy n x := by
    change x - R.i.f n n rfl ((inverseCochain Θ hΘ).f n n rfl (Θ.f n n rfl (R.p.f n n rfl x))) = _
    rw [inverseCochain_left]
    exact R.homotopy n x
  h_h := R.h_h
  h_i a b hab y := R.h_i a b hab ((inverseCochain Θ hΘ).f a a rfl y)
  p_h a b hab x := by
    change Θ.f b b rfl (R.p.f b b rfl (R.h a b hab x)) = 0
    rw [R.p_h, map_zero]

/-- Surjectivity on cocycles supplies surjectivity of the model coordinates
when the coordinate target has zero differential. -/
theorem modelCoordinate_surjective (R : GRetract X Y) (P : GHom X S)
    (hS : ∀ a b hab (z : S.X a), S.d a b hab z = 0)
    (hcyc : ∀ n (s : S.X n), ∃ x : X.X n, X.d n (n + 1) rfl x = 0 ∧ P.f n n rfl x = s)
    (n : ℤ) : Function.Surjective ((ghomComp R.i P).f n n rfl) := by
  intro s
  obtain ⟨x, hx, hs⟩ := hcyc n s
  have h := congrArg (P.f n n rfl) (R.homotopy n x)
  rw [map_sub, map_add, hx, map_zero, map_zero, add_zero, ghom_comm_d P, hS] at h
  exact ⟨R.p.f n n rfl x, (sub_eq_zero.mp h).symm.trans hs⟩

/-- On finite model terms of the prescribed sizes, the coordinate
comparison is a genuine cochain isomorphism. -/
theorem modelCoordinate_bijective (R : GRetract X Y) (P : GHom X S)
    [∀ n, Finite (Y.X n)]
    (hcard : ∀ n, Nat.card (Y.X n) = Nat.card (S.X n))
    (hS : ∀ a b hab (z : S.X a), S.d a b hab z = 0)
    (hcyc : ∀ n (s : S.X n), ∃ x : X.X n, X.d n (n + 1) rfl x = 0 ∧ P.f n n rfl x = s)
    (n : ℤ) : Function.Bijective ((ghomComp R.i P).f n n rfl) :=
  (Nat.bijective_iff_surjective_and_card _).mpr
    ⟨modelCoordinate_surjective R P hS hcyc n, hcard n⟩

/-- A change of projection to a zero-differential target changes only
the contraction homotopy, not the chosen inclusion. -/
def correctedContraction (R : GRetract X S) (P : GHom X S) (a b : ℤ) (hab : b + 1 = a) :
    X.X a →ₗ[A] X.X b :=
  R.h a b hab - (R.i.f b b rfl ∘ₗ P.f b b rfl ∘ₗ R.h a b hab)

/-- The corrected contraction has the required homotopy identity for the
new, specified coordinate projection. -/
theorem correctedContraction_identity (R : GRetract X S) (P : GHom X S)
    (hS : ∀ a b hab (z : S.X a), S.d a b hab z = 0)
    (hPi : ∀ n (s : S.X n), P.f n n rfl (R.i.f n n rfl s) = s)
    (n : ℤ) (x : X.X n) :
    x - R.i.f n n rfl (P.f n n rfl x) =
      X.d (n - 1) n (by omega) (correctedContraction R P n (n - 1) (by omega) x) +
        correctedContraction R P (n + 1) n rfl (X.d n (n + 1) rfl x) := by
  have h := R.homotopy n x
  have hP := congrArg (P.f n n rfl) h
  rw [map_sub, map_add, hPi, ghom_comm_d P, hS, zero_add] at hP
  have hI : X.d (n - 1) n (by omega)
      (R.i.f (n - 1) (n - 1) rfl (P.f (n - 1) (n - 1) rfl (R.h n (n - 1) (by omega) x))) = 0 := by
    rw [← ghom_comm_d R.i, hS, map_zero]
  change x - R.i.f n n rfl (P.f n n rfl x) =
    X.d (n - 1) n (by omega) (R.h n (n - 1) (by omega) x -
      R.i.f (n - 1) (n - 1) rfl (P.f (n - 1) (n - 1) rfl (R.h n (n - 1) (by omega) x))) +
      (R.h (n + 1) n rfl (X.d n (n + 1) rfl x) -
        R.i.f n n rfl (P.f n n rfl (R.h (n + 1) n rfl (X.d n (n + 1) rfl x))))
  rw [map_sub, hI, sub_zero]
  have hiP := congrArg (R.i.f n n rfl) hP
  rw [map_sub] at hiP
  linear_combination (norm := abel) h - hiP

/-- The normalization side identities are preserved by the corrected
contraction with its specified projection. -/
def rebaseRetraction (R : GRetract X S) (P : GHom X S)
    (hS : ∀ a b hab (z : S.X a), S.d a b hab z = 0)
    (hPi : ∀ n (s : S.X n), P.f n n rfl (R.i.f n n rfl s) = s) : GRetract X S where
  i := R.i
  p := P
  h := correctedContraction R P
  p_i := hPi
  homotopy := correctedContraction_identity R P hS hPi
  h_h a b c hab hbc x := by
    change R.h b c hbc (R.h a b hab x - R.i.f b b rfl (P.f b b rfl (R.h a b hab x))) -
      R.i.f c c rfl (P.f c c rfl
        (R.h b c hbc (R.h a b hab x - R.i.f b b rfl (P.f b b rfl (R.h a b hab x))))) = 0
    rw [map_sub, R.h_h, R.h_i, sub_self, map_zero, map_zero, sub_self]
  h_i a b hab s := by
    change R.h a b hab (R.i.f a a rfl s) -
      R.i.f b b rfl (P.f b b rfl (R.h a b hab (R.i.f a a rfl s))) = 0
    rw [R.h_i, map_zero, map_zero, sub_self]
  p_h a b hab x := by
    change P.f b b rfl (R.h a b hab x - R.i.f b b rfl (P.f b b rfl (R.h a b hab x))) = 0
    rw [map_sub, hPi, sub_self]

/-- A finite model of the prescribed term sizes, plus independently
realized coordinate cocycles, gives a normalized retract with the exact
coordinate projection, rather than an unspecified cohomology equivalence. -/
def specifiedCoordinateRetraction (R : GRetract X Y) (P : GHom X S)
    [∀ n, Finite (Y.X n)]
    (hcard : ∀ n, Nat.card (Y.X n) = Nat.card (S.X n))
    (hS : ∀ a b hab (z : S.X a), S.d a b hab z = 0)
    (hcyc : ∀ n (s : S.X n), ∃ x : X.X n, X.d n (n + 1) rfl x = 0 ∧ P.f n n rfl x = s) :
    GRetract X S :=
  rebaseRetraction
    (relabelRetraction R (ghomComp R.i P) (modelCoordinate_bijective R P hcard hS hcyc)) P hS (by
      intro n s
      change (ghomComp R.i P).f n n rfl
        ((inverseCochain (ghomComp R.i P) (modelCoordinate_bijective R P hcard hS hcyc)).f n n
          rfl s) = s
      exact inverseCochain_right _ _ n s)

end RetractionCoordinates

section LocalProjection

open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.RC53Assist.InnerLimit (Vec2 Coords splitLocalTerms)

variable {A G M : Type} [CommRing A] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulCommClass G A M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  (e : M ≃ₗ[A] Vec2 A) (φ σ : G)
  (c₂ : (contCochains A G M).X 2 →ₗ[A] M)

/-- The local cochain projection uses the actual normalized degree-two
coordinate, together with evaluation in degrees zero and one. -/
def localProjectionAt : ∀ n : ℤ,
    (natCx (contCochains A G M)).X n →ₗ[A] (splitLocalComplex A).X n
  | .ofNat 0 => e.toLinearMap.comp (evalZero A M)
  | .ofNat 1 => (e.prodCongr e).toLinearMap.comp ((evalOne A M φ).prod (evalOne A M σ))
  | .ofNat 2 => e.toLinearMap.comp c₂
  | .ofNat (_ + 3) => 0
  | .negSucc _ => 0

/-- The actual normalized coordinate makes the local projection a chain
map into the split model. No quasi-isomorphism is asserted from normalization alone. -/
def localProjection
    (htriv : ∀ (g : G) (m : M), g • m = m)
    (hc : LocalDegreeTwoCoordinate c₂) :
    GHom (natCx (contCochains A G M)) (splitLocalComplex A) where
  f a b hab := by subst hab; exact localProjectionAt e φ σ c₂ a
  comm a a₁ b b₁ hab ha hb ha'b' x := by
    subst hab ha'b' ha
    have hzero : (splitLocalComplex A).d a (a + 1) rfl
      (localProjectionAt e φ σ c₂ a x) = 0 := rfl
    rw [hzero]
    rcases a with n | n
    · rcases n with _ | _ | _ | n
      · change (e (evalOne A M φ (((contCochains A G M).d 0 1).hom x)),
          e (evalOne A M σ (((contCochains A G M).d 0 1).hom x))) = 0
        rw [evalOne_d_zero, evalOne_d_zero, htriv, htriv, sub_self, map_zero]
        rfl
      · change e (c₂ (((contCochains A G M).d 1 2).hom x)) = 0
        rw [hc.1, map_zero]
      · rfl
      · rfl
    · have : Subsingleton ((natCx (contCochains A G M)).X (.negSucc n)) := by
        change Subsingleton PUnit
        infer_instance
      have hx : x = 0 := Subsingleton.elim _ _
      rw [hx, map_zero, map_zero]

/-- The degree-two part of the local projection is the produced
normalized coordinate followed by the coefficient basis. -/
theorem localProjection_two
    (htriv : ∀ (g : G) (m : M), g • m = m) (hc : LocalDegreeTwoCoordinate c₂)
    (z : (contCochains A G M).X 2) :
    (localProjection e φ σ c₂ htriv hc).f 2 2 rfl z = e (c₂ z) := rfl

/-- The projection reads the oriented tame cup in degree two without an
undetermined scalar factor. -/
theorem localProjection_normalized
    (htriv : ∀ (g : G) (m : M), g • m = m) (hc : LocalDegreeTwoCoordinate c₂)
    (u κ : G → A) (hn : LocalDegreeTwoNormalized c₂ u κ)
    (m : M) (z : (contCochains A G M).X 2)
    (hz : ∀ g h, evalTwo A M g h z = (u g * κ h) • m) :
    (localProjection e φ σ c₂ htriv hc).f 2 2 rfl z = e m := by
  rw [localProjection_two, hn m z hz]

/-- The degree-two local comparison is already an isomorphism on
cohomology, with its exact cocycle evaluation rule. -/
theorem localProjection_degreeTwo_equiv (hc : LocalDegreeTwoCoordinate c₂) :
    ∃ f : subquot (LinearMap.range ((contCochains A G M).d 1 2).hom)
        (LinearMap.ker ((contCochains A G M).d 2 3).hom) ≃ₗ[A] Vec2 A,
      ∀ z : LinearMap.ker ((contCochains A G M).d 2 3).hom,
        f (Submodule.Quotient.mk z) = e (c₂ z) := by
  obtain ⟨f, hf⟩ := hc.exists_equiv
  exact ⟨f.trans e, fun z => congrArg e (hf z)⟩

/-- Trivial derivative action makes every degree-zero cochain a cocycle. -/
theorem localZero_d_zero (htriv : ∀ (g : G) (m : M), g • m = m)
    (x : (contCochains A G M).X 0) : ((contCochains A G M).d 0 1).hom x = 0 := by
  apply Subtype.ext
  funext g
  have hg : g = fun _ : Fin 1 => g 0 := by funext j; fin_cases j; rfl
  rw [hg]
  change evalOne A M (g 0) (((contCochains A G M).d 0 1).hom x) = 0
  rw [evalOne_d_zero, htriv, sub_self]

/-- Two continuous additive tame characters with the oriented Frobenius
and inertia values realize every coefficient coordinate pair by an actual
continuous one-cocycle. -/
theorem tameCoord_surjective_of_characters (n : ℕ) [NeZero n]
    [TopologicalSpace (ZMod n)] [DiscreteTopology (ZMod n)] [Module (ZMod n) M]
    (htriv : ∀ (g : G) (m : M), g • m = m)
    (u κ : G → ZMod n) (huc : Continuous u) (hκc : Continuous κ)
    (hu : ∀ g h, u (g * h) = u g + u h) (hκ : ∀ g h, κ (g * h) = κ g + κ h)
    (huφ : u φ = 1) (hκφ : κ φ = 0) (huσ : u σ = 0) (hκσ : κ σ = 1) :
    Function.Surjective (tameCoord (R := A) (M := M) φ σ) := by
  intro y
  let F : G → M := fun g => u g • y.1 + κ g • y.2
  have hc : Continuous F :=
    (((continuous_of_discreteTopology : Continuous (fun a : ZMod n => a • y.1)).comp huc).add
      ((continuous_of_discreteTopology : Continuous (fun a : ZMod n => a • y.2)).comp hκc))
  have hF (g h : G) : F (g * h) = F g + F h := by
    dsimp [F]
    rw [hu, hκ, add_smul, add_smul]
    abel
  let z : (contCochains A G M).X 1 := ⟨fun x => F (x 0), hc.comp (continuous_apply 0)⟩
  have hz : ((contCochains A G M).d 1 2).hom z = 0 := by
    apply Subtype.ext
    funext g
    have hg : g = ![g 0, g 1] := by funext j; fin_cases j <;> rfl
    rw [hg]
    change evalTwo A M (g 0) (g 1) (((contCochains A G M).d 1 2).hom z) = 0
    rw [evalTwo_d, htriv]
    change F (g 1) - F (g 0 * g 1) + F (g 0) = 0
    rw [hF]
    abel
  refine ⟨⟨z, hz⟩, ?_⟩
  change (F φ, F σ) = y
  dsimp [F]
  rw [huφ, hκφ, huσ, hκσ, one_smul, zero_smul, zero_smul, one_smul, add_zero, zero_add]

/-- The local projection is onto in every degree on cocycles. Degree one
uses independently realized tame-coordinate cocycles, and degree two uses
the already produced normalized coordinate. -/
theorem localProjection_cocycles_surjective
    (htriv : ∀ (g : G) (m : M), g • m = m) (hc : LocalDegreeTwoCoordinate c₂)
    (htame : Function.Surjective (tameCoord (R := A) (M := M) φ σ)) :
    ∀ n (s : (splitLocalComplex A).X n),
      ∃ x : (natCx (contCochains A G M)).X n,
        (natCx (contCochains A G M)).d n (n + 1) rfl x = 0 ∧
          (localProjection e φ σ c₂ htriv hc).f n n rfl x = s := by
  intro n s
  rcases n with n | n
  · rcases n with _ | _ | _ | n
    · let x : (contCochains A G M).X 0 := ⟨fun _ => e.symm s, continuous_const⟩
      refine ⟨x, localZero_d_zero htriv x, ?_⟩
      change e (e.symm s) = s
      exact e.apply_symm_apply s
    · obtain ⟨x, hx⟩ := htame ((e.prodCongr e).symm s)
      refine ⟨(x : (contCochains A G M).X 1), x.2, ?_⟩
      change (e.prodCongr e) (tameCoord φ σ x) = s
      rw [hx, LinearEquiv.apply_symm_apply]
    · obtain ⟨x, hx, hs⟩ := hc.2.2 (e.symm s)
      refine ⟨x, hx, ?_⟩
      change e (c₂ x) = s
      rw [hs, LinearEquiv.apply_symm_apply]
    · have : Subsingleton ((splitLocalComplex A).X (Int.ofNat (n + 3))) := by
        change Subsingleton PUnit
        infer_instance
      refine ⟨0, map_zero _, ?_⟩
      rw [map_zero]
      exact Subsingleton.elim _ _
  · have : Subsingleton ((splitLocalComplex A).X (Int.negSucc n)) := by
      change Subsingleton PUnit
      infer_instance
    refine ⟨0, map_zero _, ?_⟩
    rw [map_zero]
    exact Subsingleton.elim _ _

/-- The prescribed local residual ranks in degrees zero, one, and two. -/
def splitLocalRank : ℤ → ℕ
  | .ofNat 0 => 2
  | .ofNat 1 => 4
  | .ofNat 2 => 2
  | .ofNat (_ + 3) => 0
  | .negSucc _ => 0

/-- The finite split term has exactly the prescribed number of coefficient
coordinates in every degree. -/
theorem splitLocalTerms_card (n : ℤ) :
    Nat.card ((splitLocalComplex A).X n) = Nat.card A ^ splitLocalRank n := by
  rcases n with n | n
  · rcases n with _ | _ | _ | n
    · change Nat.card (Fin 2 → A) = Nat.card A ^ 2
      rw [Nat.card_fun, Nat.card_fin]
    · change Nat.card ((Fin 2 → A) × (Fin 2 → A)) = Nat.card A ^ 4
      simp only [Nat.card_prod, Nat.card_fun, Nat.card_fin]
      rw [← pow_add]
    · change Nat.card (Fin 2 → A) = Nat.card A ^ 2
      rw [Nat.card_fun, Nat.card_fin]
    · change Nat.card PUnit = Nat.card A ^ 0
      simp only [Nat.card_unique, pow_zero]
  · change Nat.card PUnit = Nat.card A ^ 0
    simp only [Nat.card_unique, pow_zero]

/-- The remaining local deformation-retract input is constrained to use
the actual degree-zero, tame degree-one, and normalized degree-two maps. -/
structure OrientedLocalRetraction where
  retract : GRetract (natCx (contCochains A G M)) (splitLocalComplex A)
  projection : ∀ n (z : (natCx (contCochains A G M)).X n),
    retract.p.f n n rfl z = localProjectionAt e φ σ c₂ n z

/-- The oriented local retract is constructed from flatness, finite
residual cohomology with the independently specified local ranks, and
realized tame degree-one cocycles. No retract or pairing conclusion is assumed. -/
theorem exists_orientedLocalRetraction [Finite A] [IsLocalRing A]
    (htriv : ∀ (g : G) (m : M), g • m = m) (hc : LocalDegreeTwoCoordinate c₂)
    (htame : Function.Surjective (tameCoord (R := A) (M := M) φ σ))
    (hnil : IsNilpotent (IsLocalRing.maximalIdeal A))
    (hflat : ∀ n, Module.Flat A ((natCx (contCochains A G M)).X n))
    (hfin : ∀ n, Module.Finite (IsLocalRing.ResidueField A)
      (residualCohomologyAt (natCx (contCochains A G M)) n))
    (hdim : ∀ n, Module.finrank (IsLocalRing.ResidueField A)
      (residualCohomologyAt (natCx (contCochains A G M)) n) = splitLocalRank n) :
    Nonempty (OrientedLocalRetraction e φ σ c₂) := by
  have : ∀ n, Module.Flat A ((natCx (contCochains A G M)).X n) := hflat
  obtain ⟨R, hR⟩ := exists_gradedModel hnil (natCx (contCochains A G M)) hfin
  have : ∀ n, Finite (R.modelCx.X n) := fun n => by
    change Finite (Fin (R.rank n) → A)
    infer_instance
  have hcard (n : ℤ) : Nat.card (R.modelCx.X n) = Nat.card ((splitLocalComplex A).X n) := by
    change Nat.card (Fin (R.rank n) → A) = _
    rw [Nat.card_fun, Nat.card_fin, hR n, hdim n]
    exact (splitLocalTerms_card (A := A) n).symm
  let r := specifiedCoordinateRetraction R.retract (localProjection e φ σ c₂ htriv hc)
    hcard (fun _ _ _ _ => rfl) (localProjection_cocycles_surjective e φ σ c₂ htriv hc htame)
  exact ⟨⟨r, fun _ _ => rfl⟩⟩

end LocalProjection

section RelativeSupport

open ZInQ.Manuscript.RC.SelmerComplex

variable {A : Type} [CommRing A] (D : SelData A) (Q : SelPairData D D)
  (Lq Tq Uq : GCx A) (rq : GHom D.G Lq) (sq : GHom Q.E Tq) (ιq : GHom Uq Lq)
  (Pq : GPair Lq Lq Tq)

/-- The local cup and condition input at one retained place. The old
Selmer diagram supplies the global cup; this input supplies only the
actual localization compatibility and the retained same-condition isotropy. -/
structure RetainedPlaceInput where
  compat : ∀ a b c (h : a + b = c) (x : D.G.X a) (y : D.G.X b),
    sq.f c c rfl (Q.cupG.P a b c h x y) = Pq.P a b c h (rq.f a a rfl x) (rq.f b b rfl y)
  hU : ∀ a b c : ℤ, a + b = c + 1 → Uq.X a →ₗ[A] Uq.X b →ₗ[A] Tq.X c
  isotropy : ∀ a a₁ b b₁ c c₁ (h : a + b = c + 1)
    (ha : a + 1 = a₁) (hb : b + 1 = b₁) (hc : c + 1 = c₁) (u : Uq.X a) (v : Uq.X b),
    Tq.d c c₁ hc (hU a b c h u v) +
      hU a₁ b c₁ (by omega) (Uq.d a a₁ ha u) v +
      sgn a • hU a b₁ c₁ (by omega) u (Uq.d b b₁ hb v) =
        Pq.P a b c₁ (by omega) (ιq.f a a rfl u) (ιq.f b b rfl v)

variable (V : RetainedPlaceInput D Q Lq Tq Uq rq sq ιq Pq)

/-- When the retained condition cup table vanishes on cochains, its
same-condition isotropy datum is constructed with zero primitive. This
hypothesis is about the actual condition image, not strict/relaxed annihilators. -/
def retainedInput_of_conditionCupZero
    (hcompat : ∀ a b c (h : a + b = c) (x : D.G.X a) (y : D.G.X b),
      sq.f c c rfl (Q.cupG.P a b c h x y) = Pq.P a b c h (rq.f a a rfl x) (rq.f b b rfl y))
    (hzero : ∀ a b c (h : a + b = c) (u : Uq.X a) (v : Uq.X b),
      Pq.P a b c h (ιq.f a a rfl u) (ιq.f b b rfl v) = 0) :
    RetainedPlaceInput D Q Lq Tq Uq rq sq ιq Pq where
  compat := hcompat
  hU _ _ _ _ := 0
  isotropy a a₁ b b₁ c c₁ h ha hb hc u v := by
    change Tq.d c c₁ hc 0 + (0 : Tq.X c₁) + sgn a • 0 = _
    rw [map_zero, zero_add, smul_zero, zero_add, hzero]

/-- Old places are absorbed into the global complex, leaving precisely
one retained local complex at the derivative prime. -/
def relativeData : SelData A :=
  ⟨selCx D, Uq, Lq, ghomComp (projG D) rq, ιq⟩

/-- The retained localization reads the global cochain component of an
old Selmer cochain, with the full degree-index transport. -/
theorem relativeRes_apply_of (a b : ℤ) (hab : a = b) (x : (selCx D).X a) :
    (relativeData D Lq Uq rq ιq).res.f a b hab x = rq.f a b hab x.1 := by subst hab; rfl

/-- The relative pairing uses the actual cup on the old Selmer complex
and the retained local cup. Its same-condition isotropy is the retained
place input, not strict/relaxed orthogonality. -/
def relativePair : SelPairData (relativeData D Lq Uq rq ιq) (relativeData D Lq Uq rq ιq) where
  E := coneCx Q.resE
  EL := Tq
  resE := ghomComp (coneProj Q.resE) sq
  cupG := selPair Q
  cupL := Pq
  compat a b c a' b' c' h h' ha hb hc x y := by
    subst ha hb hc
    change sq.f c c rfl (Q.cupG.P a b c h x.1 y.1) = _
    exact V.compat a b c h x.1 y.1
  hU := V.hU
  isotropy := V.isotropy

/-- The scalar target at all places, partitioned into old places and the
retained derivative place. -/
def allTargetRes : GHom Q.E (prodCx Q.EL Tq) := prodLift Q.resE sq

/-- Flattening the relative compact scalar cone restores the original
all-place scalar cone. -/
def relativeTargetFlatten : GHom
    (coneCx (ghomComp (coneProj Q.resE) sq)) (coneCx (allTargetRes D Q Tq sq)) where
  f a b hab := by
    subst hab
    exact
      { toFun := fun z => (z.1.1, z.1.2, z.2)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  comm a a₁ b b₁ hab ha hb ha'b' z := by
    subst hab ha'b'
    obtain ⟨⟨e, y⟩, w⟩ := z
    refine Prod.ext rfl (Prod.ext rfl ?_)
    change (ghomComp (coneProj Q.resE) sq).f a (a₁ - 1) (by omega) (e, y) -
        Tq.d (a - 1) (a₁ - 1) (by omega) w =
      sq.f a (a₁ - 1) (by omega) e - Tq.d (a - 1) (a₁ - 1) (by omega) w
    have hh : (ghomComp (coneProj Q.resE) sq).f a (a₁ - 1) (by omega) (e, y) =
        sq.f a (a₁ - 1) (by omega) e := by
      have hk : a = a₁ - 1 := by omega
      subst hk
      rfl
    rw [hh]

variable (trAll : (coneCx (allTargetRes D Q Tq sq)).X 3 →ₗ[A] A)
  (htrAll : ∀ z, trAll ((coneCx (allTargetRes D Q Tq sq)).d 2 3 rfl z) = 0)

/-- The relative trace is the original all-place trace, not a newly
postulated scalar functional. -/
def relativeTrace : (coneCx (relativePair D Q Lq Tq Uq rq sq ιq Pq V).resE).X 3 →ₗ[A] A :=
  trAll.comp ((relativeTargetFlatten D Q Tq sq).f 3 3 rfl)

include htrAll in
/-- The all-place trace boundary identity transports to the relative cone. -/
theorem relativeTrace_kills (z : (coneCx (relativePair D Q Lq Tq Uq rq sq ιq Pq V).resE).X 2) :
    relativeTrace D Q Lq Tq Uq rq sq ιq Pq V trAll
      ((coneCx (relativePair D Q Lq Tq Uq rq sq ιq Pq V).resE).d 2 3 rfl z) = 0 := by
  change trAll ((relativeTargetFlatten D Q Tq sq).f 3 3 rfl
    ((coneCx (ghomComp (coneProj Q.resE) sq)).d 2 3 rfl z)) = 0
  rw [(relativeTargetFlatten D Q Tq sq).comm 2 3 2 3 rfl rfl rfl rfl]
  exact htrAll _

/-- Product cups on partitioned local complexes. -/
def partitionPair {X Y X' Y' T T' : GCx A}
    (P : GPair X X' T) (P' : GPair Y Y' T') : GPair (prodCx X Y) (prodCx X' Y') (prodCx T T') where
  P a b c h := LinearMap.mk₂ A
    (fun x y => (P.P a b c h x.1 y.1, P'.P a b c h x.2 y.2))
    (by
      intro x y z
      refine Prod.ext ?_ ?_
      · change P.P a b c h (x.1 + y.1) z.1 = P.P a b c h x.1 z.1 + P.P a b c h y.1 z.1
        exact LinearMap.map_add₂ _ _ _ _
      · change P'.P a b c h (x.2 + y.2) z.2 = P'.P a b c h x.2 z.2 + P'.P a b c h y.2 z.2
        exact LinearMap.map_add₂ _ _ _ _)
    (by
      intro r x y
      refine Prod.ext ?_ ?_
      · change P.P a b c h (r • x.1) y.1 = r • P.P a b c h x.1 y.1
        exact LinearMap.map_smul₂ _ _ _ _
      · change P'.P a b c h (r • x.2) y.2 = r • P'.P a b c h x.2 y.2
        exact LinearMap.map_smul₂ _ _ _ _)
    (by
      intro x y z
      refine Prod.ext ?_ ?_
      · change P.P a b c h x.1 (y.1 + z.1) = P.P a b c h x.1 y.1 + P.P a b c h x.1 z.1
        exact map_add _ _ _
      · change P'.P a b c h x.2 (y.2 + z.2) = P'.P a b c h x.2 y.2 + P'.P a b c h x.2 z.2
        exact map_add _ _ _)
    (by
      intro r x y
      refine Prod.ext ?_ ?_
      · change P.P a b c h x.1 (r • y.1) = r • P.P a b c h x.1 y.1
        exact map_smul _ _ _
      · change P'.P a b c h x.2 (r • y.2) = r • P'.P a b c h x.2 y.2
        exact map_smul _ _ _)
  leib a a₁ b b₁ c c₁ h ha hb hc x y :=
    Prod.ext (P.leib a a₁ b b₁ c c₁ h ha hb hc x.1 y.1)
      (P'.leib a a₁ b b₁ c c₁ h ha hb hc x.2 y.2)

/-- The auxiliary all-place relaxed datum used only to establish the
relative global-duality obligation. -/
def allRelaxData : SelData A :=
  ⟨D.G, prodCx D.U Lq, prodCx D.L Lq, prodLift D.res rq, prodMapG D.ι (gHomId Lq)⟩

/-- The auxiliary all-place strict datum used only for the duality target. -/
def allStrictData : SelData A :=
  ⟨D.G, prodCx D.U (ZInQ.Manuscript.RC.SelmerComplex.zeroCx A), prodCx D.L Lq, prodLift D.res rq,
    prodMapG D.ι (zeroGHom (ZInQ.Manuscript.RC.SelmerComplex.zeroCx A) Lq)⟩

/-- The all-place pairing uses old-condition isotropy. The retained-place
factor is relaxed on the first side and strict on the second; this does not
supply or replace the distinct retained same-condition isotropy input. -/
def allPlacePair : SelPairData (allRelaxData D Lq rq) (allStrictData D Lq rq) where
  E := Q.E
  EL := prodCx Q.EL Tq
  resE := allTargetRes D Q Tq sq
  cupG := Q.cupG
  cupL := partitionPair Q.cupL Pq
  compat a b c a' b' c' h h' ha hb hc x y := by
    subst ha hb hc
    exact Prod.ext (Q.compat a b c a b c h h rfl rfl rfl x y) (V.compat a b c h x y)
  hU a b c h := LinearMap.mk₂ A (fun u v => (Q.hU a b c h u.1 v.1, (0 : Tq.X c)))
    (by
      intro x y z
      refine Prod.ext ?_ (zero_add 0).symm
      change Q.hU a b c h (x.1 + y.1) z.1 = Q.hU a b c h x.1 z.1 + Q.hU a b c h y.1 z.1
      exact LinearMap.map_add₂ _ _ _ _)
    (by
      intro r x y
      refine Prod.ext ?_ (smul_zero r).symm
      change Q.hU a b c h (r • x.1) y.1 = r • Q.hU a b c h x.1 y.1
      exact LinearMap.map_smul₂ _ _ _ _)
    (by
      intro x y z
      refine Prod.ext ?_ (zero_add 0).symm
      change Q.hU a b c h x.1 (y.1 + z.1) = Q.hU a b c h x.1 y.1 + Q.hU a b c h x.1 z.1
      exact map_add _ _ _)
    (by
      intro r x y
      refine Prod.ext ?_ (smul_zero r).symm
      change Q.hU a b c h x.1 (r • y.1) = r • Q.hU a b c h x.1 y.1
      exact map_smul _ _ _)
  isotropy a a₁ b b₁ c c₁ h ha hb hc u v := by
    refine Prod.ext (Q.isotropy a a₁ b b₁ c c₁ h ha hb hc u.1 v.1) ?_
    change Tq.d c c₁ hc 0 + (0 : Tq.X c₁) + sgn a • 0 = Pq.P a b c₁ (by omega) u.2 0
    rw [map_zero, map_zero, smul_zero, add_zero, add_zero]

/-- The old Selmer cochain is a section of the all-place relaxed
cochain, with the retained condition component equal to its actual localization. -/
def relaxedSection : GHom (selCx D) (selCx (allRelaxData D Lq rq)) where
  f a b hab := by
    subst hab
    exact
      { toFun := fun x => (x.1, (x.2.1, rq.f a a rfl x.1), (x.2.2, 0))
        map_add' x y := by
          change (x.1 + y.1, (x.2.1 + y.2.1, rq.f a a rfl (x.1 + y.1)), (x.2.2 + y.2.2, 0)) =
            (x.1 + y.1, (x.2.1 + y.2.1, rq.f a a rfl x.1 + rq.f a a rfl y.1), (x.2.2 + y.2.2, 0 +
              0))
          rw [map_add, zero_add]
        map_smul' r x := by
          change (r • x.1, (r • x.2.1, rq.f a a rfl (r • x.1)), (r • x.2.2, 0)) =
            (r • x.1, (r • x.2.1, r • rq.f a a rfl x.1), (r • x.2.2, r • 0))
          rw [map_smul, smul_zero] }
  comm a a₁ b b₁ hab ha hb ha'b' x := by
    subst hab ha'b'
    refine Prod.ext rfl (Prod.ext (Prod.ext rfl (ghom_comm_d rq a a₁ ha x.1)) (Prod.ext rfl ?_))
    change (0 : Lq.X (a₁ - 1)) = rq.f a (a₁ - 1) (by omega) x.1 -
      (gHomId Lq).f a (a₁ - 1) (by omega) (rq.f a a rfl x.1) -
        Lq.d (a - 1) (a₁ - 1) (by omega) 0
    rw [ghom_cast, map_zero, sub_self, sub_zero]

/-- Forgetting only the retained relaxed condition and local homotopy
component leaves the old Selmer cochain intact. -/
def relaxedProjection : GHom (selCx (allRelaxData D Lq rq)) (selCx D) where
  f a b hab := by
    subst hab
    exact
      { toFun := fun x => (x.1, x.2.1.1, x.2.2.1)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  comm a a₁ b b₁ hab ha hb ha'b' x := by
    subst hab ha'b'
    rfl

/-- Casting a chain-map value back to its original index changes no value. -/
theorem ghom_uncast {X Y : GCx A} (f : GHom X Y) (a b : ℤ) (hab : a = b) (x : X.X a) :
    (gHomId Y).f b a hab.symm (f.f a b hab x) = f.f a a rfl x := by subst hab; rfl

/-- Opposite index casts cancel. -/
theorem identity_uncast (X : GCx A) (a b : ℤ) (hab : a = b) (x : X.X a) :
    (gHomId X).f b a hab.symm ((gHomId X).f a b hab x) = x := by subst hab; rfl

/-- Casting the output of a differential back to its original index
changes no value. -/
theorem differential_uncast (X : GCx A) (a b c : ℤ) (hab : a + 1 = b) (hbc : b = c) (x : X.X a) :
    (gHomId X).f c b hbc.symm (X.d a c (by omega) x) = X.d a b hab x := by subst hbc; rfl

/-- The explicit contraction of the additional relaxed factor. -/
def relaxedContraction (a b : ℤ) (hab : b + 1 = a) :
    (selCx (allRelaxData D Lq rq)).X a →ₗ[A] (selCx (allRelaxData D Lq rq)).X b where
  toFun x := (0, (0, -(gHomId Lq).f (a - 1) b (by omega) x.2.2.2), (0, 0))
  map_add' x y := by
    change (0, (0, -(gHomId Lq).f (a - 1) b (by omega) (x.2.2.2 + y.2.2.2)), (0, 0)) =
      (0 + 0, (0 + 0, -(gHomId Lq).f (a - 1) b (by omega) x.2.2.2 +
        -(gHomId Lq).f (a - 1) b (by omega) y.2.2.2), (0 + 0, 0 + 0))
    rw [map_add, neg_add]
    simp only [zero_add]
  map_smul' r x := by
    change (0, (0, -(gHomId Lq).f (a - 1) b (by omega) (r • x.2.2.2)), (0, 0)) =
      (r • 0, (r • 0, r • -(gHomId Lq).f (a - 1) b (by omega) x.2.2.2), (r • 0, r • 0))
    simp only [map_smul, smul_zero, smul_neg]

/-- The additional relaxed factor is contractible, with the exact section
and projection on old Selmer cochains. -/
def relaxedRetraction : GRetract (selCx (allRelaxData D Lq rq)) (selCx D) where
  i := relaxedSection D Lq rq
  p := relaxedProjection D Lq rq
  h := relaxedContraction D Lq rq
  p_i _ _ := rfl
  homotopy n x := by
    refine Prod.ext ?_ (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_))
    · change (show D.G.X n from x.1) - (show D.G.X n from x.1) =
        D.G.d (n - 1) n (by omega) 0 + (0 : D.G.X n)
      rw [sub_self, map_zero, zero_add]
    · change x.2.1.1 - x.2.1.1 = D.U.d (n - 1) n (by omega) 0 + 0
      rw [sub_self, map_zero, zero_add]
    · change x.2.1.2 - rq.f n n rfl x.1 =
        Lq.d (n - 1) n (by omega) (-x.2.2.2) +
          -((gHomId Lq).f (n + 1 - 1) n (by omega)
            (rq.f n (n + 1 - 1) (by omega) x.1 -
              (gHomId Lq).f n (n + 1 - 1) (by omega) x.2.1.2 -
              Lq.d (n - 1) (n + 1 - 1) (by omega) x.2.2.2))
      rw [map_sub, map_sub, ghom_uncast rq n (n + 1 - 1) (by omega),
        identity_uncast Lq n (n + 1 - 1) (by omega),
        differential_uncast Lq (n - 1) n (n + 1 - 1) (by omega) (by omega), map_neg]
      abel
    · change x.2.2.1 - x.2.2.1 =
        (D.res.f (n - 1) (n - 1) rfl 0 - D.ι.f (n - 1) (n - 1) rfl 0 -
          D.L.d (n - 1 - 1) (n - 1) (by omega) 0) + 0
      rw [sub_self, map_zero, map_zero, map_zero, sub_self, sub_zero, zero_add]
    · change x.2.2.2 - 0 =
        (rq.f (n - 1) (n - 1) rfl 0 - (-x.2.2.2) -
          Lq.d (n - 1 - 1) (n - 1) (by omega) 0) + 0
      rw [sub_zero, map_zero, map_zero, sub_zero, add_zero, zero_sub, neg_neg]
  h_h a b c hab hbc x := by
    change (0, (0, -(gHomId Lq).f (b - 1) c (by omega) 0), (0, 0)) = 0
    rw [map_zero, neg_zero]
    rfl
  h_i a b hab x := by
    change (0, (0, -(gHomId Lq).f (a - 1) b (by omega) 0), (0, 0)) = 0
    rw [map_zero, neg_zero]
    rfl
  p_h _ _ _ _ := rfl

/-- The strictly retained all-place complex is the compact complex of
the relative one-place datum. -/
def strictFlatten : GHom (selCx (allStrictData D Lq rq))
    (compactCx (relativeData D Lq Uq rq ιq)) where
  f a b hab := by
    subst hab
    exact
      { toFun := fun x => ((x.1, x.2.1.1, x.2.2.1), x.2.2.2)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  comm a a₁ b b₁ hab ha hb ha'b' x := by
    subst hab ha'b'
    refine Prod.ext rfl ?_
    change rq.f a (a₁ - 1) (by omega) x.1 - (0 : Lq.X (a₁ - 1)) -
        Lq.d (a - 1) (a₁ - 1) (by omega) x.2.2.2 =
      (show Lq.X (a₁ - 1) from (relativeData D Lq Uq rq ιq).res.f a (a₁ - 1) (by omega)
        (x.1, x.2.1.1, x.2.2.1)) - Lq.d (a - 1) (a₁ - 1) (by omega) x.2.2.2
    rw [relativeRes_apply_of, sub_zero]

/-- The strict flattening is bijective in every degree. -/
theorem strictFlatten_bijective (n : ℤ) :
    Function.Bijective ((strictFlatten D Lq Uq rq ιq).f n n rfl) := by
  constructor
  · intro x y h
    obtain ⟨a, ⟨u, v⟩, ⟨z, w⟩⟩ := x
    obtain ⟨a', ⟨u', v'⟩, ⟨z', w'⟩⟩ := y
    change ((a, u, z), w) = ((a', u', z'), w') at h
    have ha := congrArg (fun p : (D.G.X n × D.U.X n × D.L.X (n - 1)) × Lq.X (n - 1) => p.1.1) h
    have hu := congrArg (fun p : (D.G.X n × D.U.X n × D.L.X (n - 1)) × Lq.X (n - 1) => p.1.2.1) h
    have hz := congrArg (fun p : (D.G.X n × D.U.X n × D.L.X (n - 1)) × Lq.X (n - 1) => p.1.2.2) h
    have hw := congrArg (fun p : (D.G.X n × D.U.X n × D.L.X (n - 1)) × Lq.X (n - 1) => p.2) h
    cases ha
    cases hu
    cases hz
    cases hw
    have : Subsingleton ((ZInQ.Manuscript.RC.SelmerComplex.zeroCx A).X n) := by
      change Subsingleton PUnit
      infer_instance
    exact Prod.ext rfl (Prod.ext (Prod.ext rfl (Subsingleton.elim _ _)) rfl)
  · intro x
    exact ⟨(x.1.1, (x.1.2.1, 0), (x.1.2.2, x.2)), rfl⟩

/-- The strict flattening is an actual normalized retract with zero
contraction, hence its inverse and both dual comparisons are proved equivalences. -/
def strictRetraction : GRetract (selCx (allStrictData D Lq rq))
    (compactCx (relativeData D Lq Uq rq ιq)) where
  i := inverseCochain (strictFlatten D Lq Uq rq ιq) (strictFlatten_bijective D Lq Uq rq ιq)
  p := strictFlatten D Lq Uq rq ιq
  h _ _ _ := 0
  p_i := inverseCochain_right _ _
  homotopy n x := by
    rw [inverseCochain_left]
    change x - x = (selCx (allStrictData D Lq rq)).d (n - 1) n (by omega) 0 + 0
    rw [sub_self, map_zero, zero_add]
  h_h _ _ _ _ _ _ := rfl
  h_i _ _ _ _ := rfl
  p_h a b hab x := map_zero _

/-- The strict inverse packs the old Selmer cochain and the retained
local cochain into the actual all-place strict tuple. -/
theorem strictInverse_apply (n : ℤ) (z : (compactCx (relativeData D Lq Uq rq ιq)).X n) :
    (strictRetraction D Lq Uq rq ιq).i.f n n rfl z =
      (z.1.1, (z.1.2.1, 0), (z.1.2.2, z.2)) := by
  apply (strictFlatten_bijective D Lq Uq rq ιq n).1
  change (strictFlatten D Lq Uq rq ιq).f n n rfl
    ((inverseCochain (strictFlatten D Lq Uq rq ιq) (strictFlatten_bijective D Lq Uq rq ιq)).f n n
      rfl z) = _
  rw [inverseCochain_right]
  rfl

/-- The relative global duality is the all-place Selmer duality under
proved relaxed and strict cochain comparisons. This identity does not use
the retained same-condition isotropy in place of old-place orthogonality. -/
theorem relativeGlobal_map_eq :
    GHom.toCC (globalDualityMap (relativePair D Q Lq Tq Uq rq sq ιq Pq V)
      (relativeTrace D Q Lq Tq Uq rq sq ιq Pq V trAll)
      (relativeTrace_kills D Q Lq Tq Uq rq sq ιq Pq V trAll htrAll)) =
    GHom.toCC (ghomComp
      (ghomComp (relaxedRetraction D Lq rq).i
        (selmerDualityMap (allPlacePair D Q Lq Tq Uq rq sq ιq Pq V) trAll htrAll))
      (dualHom (strictRetraction D Lq Uq rq ιq).i 3)) := by
  apply GHom.toCC_ext
  intro a x
  apply dualCx_ext
  intro z
  change asDual
      ((globalDualityMap (relativePair D Q Lq Tq Uq rq sq ιq Pq V)
        (relativeTrace D Q Lq Tq Uq rq sq ιq Pq V trAll)
        (relativeTrace_kills D Q Lq Tq Uq rq sq ιq Pq V trAll htrAll)).f a a rfl x) z =
    asDual ((selmerDualityMap (allPlacePair D Q Lq Tq Uq rq sq ιq Pq V) trAll htrAll).f a a rfl
      ((relaxedRetraction D Lq rq).i.f a a rfl x))
      ((strictRetraction D Lq Uq rq ιq).i.f (3 - a) (3 - a) rfl z)
  rw [strictInverse_apply, selmerDualityMap_apply, originalGlobal_eval]
  change trAll (Q.cupG.P a (3 - a) 3 (by omega) x.1 z.1.1,
      (selCupFun Q a (3 - a) 3 (by omega) x z.1).2,
      sgn a • Pq.P a (3 - a - 1) (3 - 1) (by omega) (rq.f a a rfl x.1) z.2) =
    trAll (Q.cupG.P a (3 - a) 3 (by omega) x.1 z.1.1,
      (selCupFun Q a (3 - a) 3 (by omega) x z.1).2,
      Pq.P (a - 1) (3 - a) (3 - 1) (by omega) 0 0 +
        sgn a • Pq.P a (3 - a - 1) (3 - 1) (by omega) (rq.f a a rfl x.1) z.2 + (0 : Tq.X (3 - 1)))
  rw [map_zero, zero_add, add_zero]

/-- The relative global-duality obligation follows from original
all-place global duality and independent old-condition local orthogonality.
Those are the global and local hypotheses of the proved Selmer-duality
construction, not a hypothesis asserting the relative conclusion. -/
theorem relativeGlobal_quasiIso
    (hG : QuasiIso (GHom.toCC (globalDualityMap
      (allPlacePair D Q Lq Tq Uq rq sq ιq Pq V) trAll htrAll)))
    (hL : QuasiIso (GHom.toCC (localDualityMap
      (allPlacePair D Q Lq Tq Uq rq sq ιq Pq V) trAll htrAll))) :
    QuasiIso (GHom.toCC (globalDualityMap (relativePair D Q Lq Tq Uq rq sq ιq Pq V)
      (relativeTrace D Q Lq Tq Uq rq sq ιq Pq V trAll)
      (relativeTrace_kills D Q Lq Tq Uq rq sq ιq Pq V trAll htrAll))) := by
  have hSel : QuasiIso (GHom.toCC
      (selmerDualityMap (allPlacePair D Q Lq Tq Uq rq sq ιq Pq V) trAll htrAll)) :=
    quasiIso_τ₂ (sesHom (allPlacePair D Q Lq Tq Uq rq sq ιq Pq V) trAll htrAll)
      (sesTop_shortExact (allRelaxData D Lq rq)) (sesBot_shortExact (allStrictData D Lq rq)) hL hG
  rw [relativeGlobal_map_eq D Q Lq Tq Uq rq sq ιq Pq V trAll htrAll,
    ← GHom.toCC_comp, ← GHom.toCC_comp]
  have : QuasiIso (GHom.toCC (relaxedRetraction D Lq rq).i) :=
    (relaxedRetraction D Lq rq).quasiIso_i
  have : QuasiIso (GHom.toCC
    (selmerDualityMap (allPlacePair D Q Lq Tq Uq rq sq ιq Pq V) trAll htrAll)) := hSel
  have : QuasiIso (GHom.toCC (dualHom (strictRetraction D Lq Uq rq ιq).i 3)) :=
    ((strictRetraction D Lq Uq rq ιq).dual 3).quasiIso_p
  infer_instance

/-- The exact one-place split pairing and trace consumed by the retained
stage theorem, after old places have been absorbed and the actual retained
local projection has been realized by a normalized retract. -/
theorem exists_relativeSplitPair_trace_duality (R : GRetract Lq (splitLocalComplex A))
    (hG : QuasiIso (GHom.toCC (globalDualityMap
      (allPlacePair D Q Lq Tq Uq rq sq ιq Pq V) trAll htrAll)))
    (hL : QuasiIso (GHom.toCC (localDualityMap
      (allPlacePair D Q Lq Tq Uq rq sq ιq Pq V) trAll htrAll))) :
    ∃ (Q' : SelPairData
        (splitSelData (selCx D) (ghomComp (ghomComp (projG D) rq) R.p) Uq (ghomComp ιq R.p))
        (splitSelData (selCx D) (ghomComp (ghomComp (projG D) rq) R.p) Uq (ghomComp ιq R.p)))
      (tr' : (coneCx Q'.resE).X 3 →ₗ[A] A)
      (htr' : ∀ z, tr' ((coneCx Q'.resE).d 2 3 rfl z) = 0),
      QuasiIso (GHom.toCC (globalDualityMap Q' tr' htr')) ∧
      ∀ (a b : ℤ) (h : a + b = 2) (u : (splitLocalComplex A).X a) (v : (splitLocalComplex A).X b),
        tr' (0, Q'.cupL.P a b 2 h u v) = trAll (0, 0, Pq.P a b 2 h (R.i.f a a rfl u) (R.i.f b b
          rfl v)) := by
  let Dr := relativeData D Lq Uq rq ιq
  let Qr := relativePair D Q Lq Tq Uq rq sq ιq Pq V
  let tr := relativeTrace D Q Lq Tq Uq rq sq ιq Pq V trAll
  let ht := relativeTrace_kills D Q Lq Tq Uq rq sq ιq Pq V trAll htrAll
  let Q' := replacementPair Dr R Qr
  let tr' := replacementTrace Dr R Qr tr
  let ht' := replacementTrace_kills Dr R Qr tr ht
  refine ⟨Q', tr', ht', replacementGlobal_quasiIso Dr R Qr tr ht
    (relativeGlobal_quasiIso D Q Lq Tq Uq rq sq ιq Pq V trAll htrAll hG hL), ?_⟩
  intro a b h u v
  change trAll (0, 0, (0 : Tq.X 2) + Pq.P a b 2 h (R.i.f a a rfl u) (R.i.f b b rfl v)) = _
  rw [zero_add]

end RelativeSupport

section ActualStageSource

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.RC53Assist.InnerLimitArith (exists_stageTrace stageGlobalDuality)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α] (hμ : HasRootsOfUnity K S (2 ^ i))
  (ΔA : GaloisLocalConditions K S (Acoef i) (Mcoef K S W i α))
  (ΔB : GaloisLocalConditions K S (Acoef i) (Mcoef K S W i (charInv α)))
  (I : GaloisTruncIsotropyData K S (Acoef i) (weilPairingData W i α hμ)
    (weilPairingM_smul W hμ (Acoef i) α) ΔA ΔB)

/-- The actual paired coefficient systems before local split replacement. -/
abbrev actualStagePair :=
  galoisPairDataT K S (Acoef i) (weilPairingData W i α hμ)
    (weilPairingM_smul W hμ (Acoef i) α) ΔA ΔB I

/-- The source trace and global duality for the actual stage data,
with the second coefficient system identified on cochains. Both conclusions
are obtained from the existing stage trace and stage global duality theorems. -/
theorem exists_actualStageSource_trace_duality
    (h541 : NekovarProp541T K) (h543 : NekovarProp543T K) (hK : IsTotallyComplex K)
    (hSfin : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hW : FullTorsion K S W (2 ^ i))
    (C : SecondComparison (galoisSelData K S (Acoef i) (Mcoef K S W i α) ΔA)
      (galoisSelData K S (Acoef i) (Mcoef K S W i (charInv α)) ΔB))
    (hG : ∀ n, Function.Bijective (C.global.f n n rfl))
    (hL : ∀ n, Function.Bijective (C.loc.f n n rfl)) :
    ∃ (tr : (coneCx (secondPullPair C (actualStagePair W i α hμ ΔA ΔB I)).resE).X 3 →ₗ[Acoef i]
      Acoef i)
      (htr : ∀ z, tr ((coneCx (secondPullPair C (actualStagePair W i α hμ ΔA ΔB I)).resE).d 2 3
        rfl z) = 0),
      QuasiIso (GHom.toCC
        (globalDualityMap (secondPullPair C (actualStagePair W i α hμ ΔA ΔB I)) tr htr)) := by
  obtain ⟨tr, htr, htr3⟩ := exists_stageTrace W i α hμ h541 hK hSfin h2 ΔA ΔB I
  have hdual := stageGlobalDuality W i α hμ h543 hK hSfin h2 hW ΔA ΔB I tr htr htr3
  have : Module.Injective (Acoef i) (Acoef i) :=
    ZInQ.Contrib.CloudB3RC53.SelmerDuality.acoef_selfInjective i
  exact ⟨tr, htr, secondPull_global_quasiIso C (actualStagePair W i α hμ ΔA ΔB I) tr htr hG hL
    hdual⟩

end ActualStageSource

end ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace

namespace ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace

open NumberField IsDedekindDomain Module
open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.HeegnerAlgebra ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.Limits
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.RC53Assist.InnerLimit (Vec2 splitLocalComplex)
open ZInQ.Contrib.RC53Assist.LocalDegreeTwo

section ActualOrientedLocalModel

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α]
  (q : HeightOneSpectrum (𝓞 K))

/-- The actual finite coefficient ring has nilpotent maximal ideal. -/
theorem stageMaximalIdeal_nilpotent :
    IsNilpotent (IsLocalRing.maximalIdeal (Acoef i)) :=
  ElliotRing.isNilpotent_maximalIdeal i

omit [W.IsElliptic] in
/-- The degree-one coordinate pair uses exactly the Frobenius and inertia
of the same orientation that normalized the degree-two coordinate. -/
theorem stageOrientation_tameCoord_surjective
    (D : TameOrientation (q.adicCompletion K) (2 ^ i))
    (htriv : ∀ (g : Gloc K q)
      (m : ResMod (locMap K S q) (Mcoef K S W i α)), g • m = m)
    (hμ : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K)/q.adicCompletion K))
      (ζ : AlgebraicClosure (q.adicCompletion K)), ζ ^ (2 ^ i) = 1 → g ζ = ζ) :
    Function.Surjective (tameCoord (G := Gloc K q) (R := Acoef i)
      (M := ResMod (locMap K S q) (Mcoef K S W i α)) D.frobenius D.inertia) := by
  have : NeZero (2 ^ i) := ⟨pow_ne_zero i two_ne_zero⟩
  have : Fact (1 < 2 ^ i) := ⟨Nat.one_lt_two_pow (NeZero.ne i)⟩
  let M := ResMod (locMap K S q) (Mcoef K S W i α)
  let : Module (ZMod (2 ^ i)) M :=
    AddCommGroup.zmodModule (localizedMcoef_nsmul W i α q)
  obtain ⟨huφ, huσ, hκφ, hκσ⟩ := D.character_values
  exact tameCoord_surjective_of_characters (A := Acoef i) (G := Gloc K q) (M := M)
    D.frobenius D.inertia (2 ^ i) htriv D.unramified D.kummer
    (continuous_urCharN (K := q.adicCompletion K) (n := 2 ^ i))
    (continuous_kummerLog D.root_pow D.root_ne_zero D.primitive hμ)
    (urCharN_mul (K := q.adicCompletion K) (n := 2 ^ i))
    (kummerLog_mul D.root_pow D.root_ne_zero D.primitive hμ)
    huφ hκφ huσ hκσ

omit [W.IsElliptic] [NeZero i] in
/-- Flatness of the actual local cochains follows from the rank-two full
coefficient basis and compactness of the actual local Galois group. -/
theorem actualLocal_cochains_flat
    (e : ResMod (locMap K S q) (Mcoef K S W i α) ≃ₗ[Acoef i] Vec2 (Acoef i))
    (n : ℤ) : Module.Flat (Acoef i)
      ((natCx (contCochains (Acoef i) (Gloc K q)
        (ResMod (locMap K S q) (Mcoef K S W i α)))).X n) := by
  let M := ResMod (locMap K S q) (Mcoef K S W i α)
  have : Module.Free (Acoef i) M :=
    Module.Free.of_basis ((Pi.basisFun (Acoef i) (Fin 2)).map e.symm)
  have : Module.Flat (Acoef i) M := inferInstance
  rcases n with n | n
  · exact flat_contCochains (R := Acoef i) (G := Gloc K q) (M := M) n
  · change Module.Flat (Acoef i) PUnit
    infer_instance

/-- The no-injectivity stage-coordinate corollary is used directly in
constructing the split cochain projection. Its degree-one components use
the same chosen tame orientation, not an independently imposed lift. -/
theorem exists_stageSplitProjection
    (h2 : (2 : 𝓞 K) ∉ q.asIdeal) (hW : FullTorsion K S W (2 ^ i))
    (htriv : ∀ (g : Gloc K q)
      (m : ResMod (locMap K S q) (Mcoef K S W i α)), g • m = m)
    (hμ : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K)/q.adicCompletion K))
      (ζ : AlgebraicClosure (q.adicCompletion K)), ζ ^ (2 ^ i) = 1 → g ζ = ζ) :
    ∃ (D : TameOrientation (q.adicCompletion K) (2 ^ i))
      (c₂ : (contCochains (Acoef i) (Gloc K q)
        (ResMod (locMap K S q) (Mcoef K S W i α))).X 2 →ₗ[Acoef i]
          ResMod (locMap K S q) (Mcoef K S W i α))
      (e : ResMod (locMap K S q) (Mcoef K S W i α) ≃ₗ[Acoef i] Vec2 (Acoef i))
      (hc : LocalDegreeTwoCoordinate c₂),
      LocalDegreeTwoNormalized c₂
        (fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (D.unramified g))
        (fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (D.kummer g)) ∧
      Function.Surjective (tameCoord (G := Gloc K q) (R := Acoef i)
        (M := ResMod (locMap K S q) (Mcoef K S W i α)) D.frobenius D.inertia) ∧
      ∀ z : (contCochains (Acoef i) (Gloc K q)
        (ResMod (locMap K S q) (Mcoef K S W i α))).X 2,
        (localProjection (G := Gloc K q) e D.frobenius D.inertia c₂ htriv hc).f 2 2 rfl z = e (c₂
          z) := by
  obtain ⟨D, c₂, hc, hn⟩ := exists_stageCoordinate_without_hKB W i α q h2 hW htriv hμ
  obtain ⟨e⟩ := exists_localizedMcoef_equiv W i α q hW
  exact ⟨D, c₂, e, hc, hn, stageOrientation_tameCoord_surjective W i α q D htriv hμ,
    fun z => localProjection_two (G := Gloc K q) e D.frobenius D.inertia c₂ htriv hc z⟩

/-- The actual local split model, with a common tame orientation and an
exported Brauer invariant formula. The independent residual cohomology
finiteness and rank inputs are the remaining local arithmetic data. -/
theorem exists_stageOrientedLocalRetraction
    (h2 : (2 : 𝓞 K) ∉ q.asIdeal) (hW : FullTorsion K S W (2 ^ i))
    (htriv : ∀ (g : Gloc K q)
      (m : ResMod (locMap K S q) (Mcoef K S W i α)), g • m = m)
    (hμ : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K)/q.adicCompletion K))
      (ζ : AlgebraicClosure (q.adicCompletion K)), ζ ^ (2 ^ i) = 1 → g ζ = ζ)
    (hfin : ∀ n, Module.Finite (IsLocalRing.ResidueField (Acoef i))
      (residualCohomologyAt (natCx (contCochains (Acoef i) (Gloc K q)
        (ResMod (locMap K S q) (Mcoef K S W i α)))) n))
    (hdim : ∀ n, Module.finrank (IsLocalRing.ResidueField (Acoef i))
      (residualCohomologyAt (natCx (contCochains (Acoef i) (Gloc K q)
        (ResMod (locMap K S q) (Mcoef K S W i α)))) n) = splitLocalRank n) :
    ∃ (D : TameOrientation (q.adicCompletion K) (2 ^ i))
      (c₂ : (contCochains (Acoef i) (Gloc K q)
        (ResMod (locMap K S q) (Mcoef K S W i α))).X 2 →ₗ[Acoef i]
          ResMod (locMap K S q) (Mcoef K S W i α))
      (η : ZMod (2 ^ i) ≃+ KummerCoeff (q.adicCompletion K) (2 ^ i))
      (e : ResMod (locMap K S q) (Mcoef K S W i α) ≃ₗ[Acoef i] Vec2 (Acoef i))
      (_R : OrientedLocalRetraction (G := Gloc K q) e D.frobenius D.inertia c₂),
      LocalDegreeTwoCoordinate c₂ ∧ LocalDegreeTwoNormalized c₂
        (fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (D.unramified g))
        (fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (D.kummer g)) ∧
      StageBrauerCoordinateFormula W i α q η hμ htriv c₂ ∧
      (((η 1).toMul : (SeparableClosure (q.adicCompletion K))ˣ) :
          AlgebraicClosure (q.adicCompletion K)) =
        ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal D.root D.inertia := by
  obtain ⟨D, c₂, hc, hn, η, hInv, hη⟩ :=
    exists_stageCoordinate_with_brauer W i α q h2 hW htriv hμ
  obtain ⟨e⟩ := exists_localizedMcoef_equiv W i α q hW
  have htame := stageOrientation_tameCoord_surjective W i α q D htriv hμ
  obtain ⟨R⟩ := exists_orientedLocalRetraction (G := Gloc K q) e D.frobenius D.inertia c₂ htriv
    hc htame
    (stageMaximalIdeal_nilpotent i) (actualLocal_cochains_flat W i α q e) hfin hdim
  exact ⟨D, c₂, η, e, R, hc, hn, hInv, hη⟩

end ActualOrientedLocalModel

end ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace

namespace ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace

open NumberField IsDedekindDomain Module
open TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.HeegnerAlgebra ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.Limits
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.RC53Assist.InnerLimit (Vec2 splitLocalComplex)
open ZInQ.Manuscript.RC.FibreDuality (splitSelData)
open ZInQ.Contrib.RC53Assist.LocalDegreeTwo

section NativeStagePairing

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α]
  (q : HeightOneSpectrum (𝓞 K))

/-- The actual retained local cochain complex at the coefficient stage. -/
abbrev actualStageLocalCx : GCx (Acoef i) :=
  natCx (contCochains (Acoef i) (Gloc K q)
    (ResMod (locMap K S q) (Mcoef K S W i α)))

variable (Dold : SelData (Acoef i)) (Qold : SelPairData Dold Dold)
  (Tq Uq : GCx (Acoef i))
  (rq : GHom Dold.G (actualStageLocalCx W i α q))
  (sq : GHom Qold.E Tq) (ιq : GHom Uq (actualStageLocalCx W i α q))
  (Pq : GPair (actualStageLocalCx W i α q) (actualStageLocalCx W i α q) Tq)
  (V : RetainedPlaceInput Dold Qold (actualStageLocalCx W i α q) Tq Uq rq sq ιq Pq)
  (trAll : (coneCx (allTargetRes Dold Qold Tq sq)).X 3 →ₗ[Acoef i] Acoef i)
  (htrAll : ∀ z, trAll ((coneCx (allTargetRes Dold Qold Tq sq)).d 2 3 rfl z) = 0)

/-- The actual-stage producer combines the no-injectivity arithmetic
coordinate, its common tame orientation, the proved local retract, the
retained same-condition cup data, and the original global and local duality
obligations. Neither a split pairing, a split trace, nor its global duality
is an input. -/
theorem exists_stagePairing_trace
    (h2 : (2 : 𝓞 K) ∉ q.asIdeal) (hW : FullTorsion K S W (2 ^ i))
    (htriv : ∀ (g : Gloc K q)
      (m : ResMod (locMap K S q) (Mcoef K S W i α)), g • m = m)
    (hμ : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K)/q.adicCompletion K))
      (ζ : AlgebraicClosure (q.adicCompletion K)), ζ ^ (2 ^ i) = 1 → g ζ = ζ)
    (hfin : ∀ n, Module.Finite (IsLocalRing.ResidueField (Acoef i))
      (residualCohomologyAt (actualStageLocalCx W i α q) n))
    (hdim : ∀ n, Module.finrank (IsLocalRing.ResidueField (Acoef i))
      (residualCohomologyAt (actualStageLocalCx W i α q) n) = splitLocalRank n)
    (hG : QuasiIso (GHom.toCC (globalDualityMap
      (allPlacePair Dold Qold (actualStageLocalCx W i α q) Tq Uq rq sq ιq Pq V)
      trAll htrAll)))
    (hL : QuasiIso (GHom.toCC (localDualityMap
      (allPlacePair Dold Qold (actualStageLocalCx W i α q) Tq Uq rq sq ιq Pq V)
      trAll htrAll))) :
    ∃ (p : GHom (actualStageLocalCx W i α q) (splitLocalComplex (Acoef i)))
      (Q : SelPairData
        (splitSelData (selCx Dold) (ghomComp (ghomComp (projG Dold) rq) p)
          Uq (ghomComp ιq p))
        (splitSelData (selCx Dold) (ghomComp (ghomComp (projG Dold) rq) p)
          Uq (ghomComp ιq p)))
      (tr : (coneCx Q.resE).X 3 →ₗ[Acoef i] Acoef i)
      (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0),
      QuasiIso (GHom.toCC (globalDualityMap Q tr htr)) := by
  have hmodel := exists_stageOrientedLocalRetraction (K := K) (S := S)
    W i α q h2 hW htriv hμ hfin hdim
  rcases hmodel with ⟨D, c₂, η, e, R, hmodel⟩
  obtain ⟨Q, tr, htr, hdual, htrace⟩ :=
    exists_relativeSplitPair_trace_duality Dold Qold (actualStageLocalCx W i α q)
      Tq Uq rq sq ιq Pq V trAll htrAll R.retract hG hL
  exact ⟨R.retract.p, Q, tr, htr, hdual⟩

end NativeStagePairing

end ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace
