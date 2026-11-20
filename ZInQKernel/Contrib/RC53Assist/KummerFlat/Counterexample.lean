import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.StageFlat
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Kummer
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Ring
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Characters
import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitRegularityBounds

/-!
# Flatness of the finite Kummer condition: the degree-one obstruction

The finite condition in manuscript lines 3413–3438 has terms
`C⁰`, `kummerZ' ⊔ B¹`, and zero elsewhere. The second term is an
actual submodule, not a free module on formal cochains. In particular,
a zero coefficient map leaves precisely the coboundary module.

The finite free model in manuscript lines 4391–4414 therefore requires
an additional argument in degree one. The results below separate that
argument from the flatness of the ambient continuous cochain modules.

The counterexample concerns arbitrary equivariant coefficient maps,
which are permitted to be zero. It does not assert nonflatness for the
canonical torsion inclusion of the derived Kummer condition. The
actual stage obstruction is also proved for split four-torsion twisted
by a nontrivial local quadratic character.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.KummerFlat

open CategoryTheory IsLocalRing
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.RC53Assist.InnerLimitArith

section ScalarObstruction

variable {R : Type} [CommRing R] [IsLocalRing R]
  {M : Type} [AddCommGroup M] [Module R M]

/-- Kind: theorem, proved. A nonzero module annihilated by a nonzero
scalar cannot be flat over a local ring with nilpotent maximal ideal.
This is the contrapositive of the freeness step at tex 4409–4412. -/
theorem not_flat_of_annihilator [Nontrivial M]
    (hnil : IsNilpotent (maximalIdeal R)) (r : R) (hr : r ≠ 0)
    (hkill : ∀ x : M, r • x = 0) : ¬ Module.Flat R M := by
  intro hflat
  have : Module.Flat R M := hflat
  have : Module.Free R M := ZInQ.Manuscript.RC.Limits.flat_module_free hnil
  have : FaithfulSMul R M := inferInstance
  apply hr
  exact eq_of_smul_eq_smul (fun x : M => (hkill x).trans (zero_smul R x).symm)

end ScalarObstruction

section StageScalar

/-- Kind: definition. Evaluation at `t = 0` on the positive coefficient
stage `A_i = (ℤ/2^i)[t]/(t^i)` of tex 2725. -/
def stageConstantTerm (i : ℕ) (hi : i ≠ 0) : Acoef i →+* ZMod (2 ^ i) :=
  Ideal.Quotient.lift _ (Polynomial.evalRingHom 0) (fun p hp => by
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    simp [hi])

/-- Kind: theorem, proved. The scalar two is nonzero in the second
coefficient stage of tex 2725, although its square is zero. -/
theorem stage_two_ne_zero : (2 : Acoef 2) ≠ 0 := by
  intro h
  have h' := congrArg (stageConstantTerm 2 (by decide)) h
  rw [map_ofNat, map_zero] at h'
  exact (by decide : (2 : ZMod 4) ≠ 0) h'

/-- Kind: theorem, proved. A nonzero module killed by two is not flat
over the second coefficient stage; tex 2725 and 4409–4412. -/
theorem stage_not_flat_of_two_annihilator
    {M : Type} [AddCommGroup M] [Module (Acoef 2) M] [Nontrivial M]
    (hkill : ∀ x : M, (2 : Acoef 2) • x = 0) :
    ¬ Module.Flat (Acoef 2) M :=
  not_flat_of_annihilator
    (ZInQ.Manuscript.RC.Limits.ElliotRing.isNilpotent_maximalIdeal 2)
    2 stage_two_ne_zero hkill

end StageScalar

section Coboundaries

variable {R : Type} [CommRing R] [IsLocalRing R]
  {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {M : Type} [AddCommGroup M] [Module R M]
  [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]
  [ContinuousSMul G M]

/-- Kind: theorem, proved. If a nonzero scalar kills every difference
`g • x - x` and some such difference is nonzero, the actual continuous
coboundaries are not flat. The differential is the one at tex 3413–3418;
the flat-to-free criterion is tex 4409–4412. -/
theorem contB1_not_flat_of_annihilator
    (hnil : IsNilpotent (maximalIdeal R)) (r : R) (hr : r ≠ 0)
    (hkill : ∀ (g : G) (x : M), r • (g • x - x) = 0)
    (hmove : ∃ (g : G) (x : M), g • x ≠ x) :
    ¬ Module.Flat R (contB1 R G M) := by
  obtain ⟨g, x, hx⟩ := hmove
  let b : contB1 R G M :=
    ⟨contD R G M 0 (constCochain x), ⟨constCochain x, rfl⟩⟩
  have hb : b ≠ 0 := by
    intro h
    have h' := congrArg (fun y : contB1 R G M => cfun y.1 (fun _ => g)) h
    change cfun (contD R G M 0 (constCochain x)) (fun _ => g) = 0 at h'
    rw [cfun_contD_constCochain] at h'
    exact hx (sub_eq_zero.mp h')
  have : Nontrivial (contB1 R G M) := ⟨⟨b, 0, hb⟩⟩
  apply not_flat_of_annihilator (M := ↥(contB1 R G M)) hnil r hr
  rintro ⟨y, hy⟩
  obtain ⟨c, rfl⟩ := (mem_contB1_iff y).mp hy
  apply Subtype.ext
  apply Subtype.ext
  funext gs
  change r • cfun (contD R G M 0 c) gs = 0
  rw [contD_zero_apply]
  exact hkill (gs 0) (cfun c default)

end Coboundaries

section OtherDegrees

variable {R : Type} [CommRing R]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module R M]
  [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  [CompactSpace G] [Module.Flat R M]

/-- Kind: theorem, proved. All terms of a cocycle condition except
possibly degree one are flat whenever the coefficient module is flat.
The zero and one terms are those of tex 3415–3417; continuous cochain
flatness is the finite-partition argument of tex 4412–4414. -/
theorem flat_cocycleCondition_of_ne_one
    (Z : Submodule R (contCochain R G M 1))
    (hZ : ∀ z ∈ Z, contD R G M 1 z = 0)
    (n : ℤ) (hn : n ≠ 1) :
    Module.Flat R ((cocycleCondition Z hZ).X n) := by
  cases n with
  | negSucc j =>
    change Module.Flat R PUnit
    infer_instance
  | ofNat j =>
    cases j with
    | zero =>
      change Module.Flat R ↥(⊤ : Submodule R (contCochain R G M 0))
      have : Module.Flat R (contCochain R G M 0) :=
        flat_contCochains (R := R) (G := G) (M := M) 0
      exact Module.Flat.of_linearEquiv (LinearEquiv.ofTop _ rfl)
    | succ j =>
      cases j with
      | zero => exact False.elim (hn rfl)
      | succ j =>
        change Module.Flat R ↥(⊥ : Submodule R (contCochain R G M (j + 2)))
        infer_instance

end OtherDegrees

section ZeroKummerMap

variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
  (B : WeierstrassCurve F) [B.IsElliptic] (m : ℕ) [NeZero m]
  {R : Type} [CommRing R]
  {M : Type} [AddCommGroup M] [Module R M]
  [DistribMulAction (Field.absoluteGaloisGroup F) M]
  [SMulCommClass (Field.absoluteGaloisGroup F) R M]
  [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (Field.absoluteGaloisGroup F) M]

omit [ContinuousSMul (Field.absoluteGaloisGroup F) M] in
/-- Kind: theorem, proved. A zero torsion coefficient map has zero
extended Kummer span, with precisely the definition in tex 3430–3438. -/
theorem kummerZ'_zero :
    kummerZ' R (0 : TorsAlg F B m →+ M) = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    change kummerCocycleIn (0 : TorsAlg F B m →+ M) p.1 p.2 = 0
    apply Subtype.ext
    funext gs
    change p.1 • (0 : M) = 0
    exact smul_zero p.1
  · exact bot_le

/-- Kind: theorem, proved. The degree-one term of the actual Kummer
condition for a zero coefficient map is the coboundary module, not a
free module on chosen cochains; tex 3415–3418 and 3430–3438. -/
theorem kummerConditionIn_zero_X_one
    (hι : ∀ (g : Field.absoluteGaloisGroup F) (t : TorsAlg F B m),
      (0 : TorsAlg F B m →+ M) (g • t) = g • (0 : TorsAlg F B m →+ M) t) :
    (kummerConditionIn R (0 : TorsAlg F B m →+ M) hι).X 1 =
      ModuleCat.of R (contB1 R (Field.absoluteGaloisGroup F) M) := by
  change ModuleCat.of R ↥(kummerZ' R (0 : TorsAlg F B m →+ M) ⊔
    contB1 R (Field.absoluteGaloisGroup F) M) = _
  rw [kummerZ'_zero B m, bot_sup_eq]

/-- Kind: theorem, proved. The permitted zero coefficient map gives a
nonflat degree-one Kummer term when the action has a nonzero difference
annihilated by a nonzero scalar. This concerns the actual complex of
tex 3430–3438 and the model hypothesis of tex 4391–4414. -/
theorem kummerConditionIn_zero_not_flat [IsLocalRing R]
    (hnil : IsNilpotent (maximalIdeal R)) (r : R) (hr : r ≠ 0)
    (hkill : ∀ (g : Field.absoluteGaloisGroup F) (x : M), r • (g • x - x) = 0)
    (hmove : ∃ (g : Field.absoluteGaloisGroup F) (x : M), g • x ≠ x)
    (hι : ∀ (g : Field.absoluteGaloisGroup F) (t : TorsAlg F B m),
      (0 : TorsAlg F B m →+ M) (g • t) = g • (0 : TorsAlg F B m →+ M) t) :
    ¬ Module.Flat R ((kummerConditionIn R (0 : TorsAlg F B m →+ M) hι).X 1) := by
  rw [kummerConditionIn_zero_X_one B m hι]
  exact contB1_not_flat_of_annihilator hnil r hr hkill hmove

end ZeroKummerMap

section SignCoefficients

variable {G : Type} [Group G] (χ : G →* ℤˣ)

/-- Kind: definition. The free rank-two stage module with quadratic
scalar action, as allowed by the characters in tex 2725–2726 and 2791. -/
def SignModule (_χ : G →* ℤˣ) : Type := Acoef 2 × Acoef 2

/-- Kind: instance, defined. The additive group of the sign coefficient
module; tex 2725–2726. -/
instance signModuleAddCommGroup : AddCommGroup (SignModule χ) :=
  inferInstanceAs (AddCommGroup (Acoef 2 × Acoef 2))

/-- Kind: instance, defined. The stage-ring scalar structure of the sign
coefficient module; tex 2725–2726. -/
instance signModuleModule : Module (Acoef 2) (SignModule χ) :=
  inferInstanceAs (Module (Acoef 2) (Acoef 2 × Acoef 2))

/-- Kind: instance, proved. The sign coefficient module is free of rank
two over the second stage ring; tex 2725. -/
instance signModuleFree : Module.Free (Acoef 2) (SignModule χ) :=
  inferInstanceAs (Module.Free (Acoef 2) (Acoef 2 × Acoef 2))

/-- Kind: instance, proved. The sign coefficient module is nonzero;
tex 2725 and the nonzero scalar two. -/
instance signModuleNontrivial : Nontrivial (SignModule χ) :=
  inferInstanceAs (Nontrivial (Acoef 2 × Acoef 2))

/-- Kind: instance, defined. The Galois action is multiplication by the
quadratic character, with unchanged stage scalars; tex 2726 and 2791. -/
instance signModuleAction : DistribMulAction G (SignModule χ) where
  smul g x := (χ g) • (x : Acoef 2 × Acoef 2)
  one_smul x := by change (χ 1) • (x : Acoef 2 × Acoef 2) = x; rw [map_one, one_smul]
  mul_smul g h x := by
    change (χ (g * h)) • (x : Acoef 2 × Acoef 2) = (χ g) • ((χ h) • x)
    rw [map_mul, mul_smul]
  smul_zero g := smul_zero (χ g)
  smul_add g x y := smul_add (χ g) x y

/-- Kind: instance, proved. The quadratic action commutes with the
coefficient-ring scalars; tex 2725–2726 and 2791. -/
instance signModuleSMulCommClass : SMulCommClass G (Acoef 2) (SignModule χ) where
  smul_comm g r x := smul_comm (χ g) r (x : Acoef 2 × Acoef 2)

/-- Kind: instance, defined. Finite coefficients carry the discrete
topology used by the continuous cochains in tex 3455–3463. -/
instance signModuleTopology : TopologicalSpace (SignModule χ) := ⊥

/-- Kind: instance, proved. The sign coefficient topology is discrete;
tex 3455–3463. -/
instance signModuleDiscrete : DiscreteTopology (SignModule χ) := ⟨rfl⟩

variable [TopologicalSpace G] [IsTopologicalGroup G] [IsOpenKer χ]

/-- Kind: instance, proved. A quadratic character with open kernel gives
a continuous action on the discrete stage module; tex 2781–2796. -/
instance signModuleContinuousSMul : ContinuousSMul G (SignModule χ) := by
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro x
  exact Subgroup.isOpen_mono (H₁ := χ.ker) (fun g hg => by
    rw [MonoidHom.mem_ker] at hg
    change (χ g) • (x : Acoef 2 × Acoef 2) = x
    rw [hg, one_smul]) (IsOpenKer.isOpen_ker (α := χ))

omit [IsOpenKer χ] [IsTopologicalGroup G] [TopologicalSpace G] in
/-- Kind: theorem, proved. Every sign-action coboundary at the second
stage is killed by two; tex 2725–2726 and 3413–3418. -/
theorem signModule_two_smul_difference (g : G) (x : SignModule χ) :
    (2 : Acoef 2) • (g • x - x) = 0 := by
  change (2 : Acoef 2) • (((χ g : ℤˣ) : ℤ) • (x : Acoef 2 × Acoef 2) - x) = 0
  rcases Int.units_eq_one_or (χ g) with hg | hg
  · simp only [hg, Units.val_one, one_zsmul, sub_self, smul_zero]
  · rw [hg, Units.val_neg, Units.val_one]
    change (2 : Acoef 2) • ((-1 : ℤ) • (x : Acoef 2 × Acoef 2) - x) = 0
    rw [← Int.cast_smul_eq_zsmul (Acoef 2), Int.cast_neg, Int.cast_one]
    change (2 : Acoef 2) • ((-1 : Acoef 2) • (x : Acoef 2 × Acoef 2) - x) = 0
    rw [smul_sub, smul_smul, ← sub_smul]
    have hcoef : (2 : Acoef 2) * (-1) - 2 = 0 := by
      calc
        (2 : Acoef 2) * (-1) - 2 = -(2 : Acoef 2) ^ 2 := by ring
        _ = 0 := by rw [ZInQ.Manuscript.RC.HeegnerAlgebra.two_pow_A 2, neg_zero]
    rw [hcoef]
    exact zero_smul (Acoef 2) (x : Acoef 2 × Acoef 2)

omit [IsOpenKer χ] [IsTopologicalGroup G] [TopologicalSpace G] in
/-- Kind: theorem, proved. A character taking the value minus one acts
nontrivially on the free rank-two stage module; tex 2725–2726 and 2791. -/
theorem signModule_action_nontrivial (hχ : ∃ g : G, χ g = -1) :
    ∃ (g : G) (x : SignModule χ), g • x ≠ x := by
  obtain ⟨g, hg⟩ := hχ
  refine ⟨g, (1, 0), ?_⟩
  intro h
  have h' := congrArg (fun x : SignModule χ => (x : Acoef 2 × Acoef 2).1) h
  change (((χ g : ℤˣ) : ℤ) • (1 : Acoef 2)) = 1 at h'
  rw [hg, Units.val_neg, Units.val_one, neg_one_zsmul] at h'
  change -(1 : Acoef 2) = 1 at h'
  apply stage_two_ne_zero
  linear_combination -h'

end SignCoefficients

section QuadraticCharacter

variable {F : Type} [Field F] [CharZero F]
  (s : AlgebraicClosure F) {a : F} (hs : s ^ 2 = algebraMap F (AlgebraicClosure F) a)
  (hs0 : s ≠ 0)

include hs in
omit [CharZero F] in
/-- Kind: theorem, proved. An automorphism sends a nonzero square root
to itself or its negative; tex 2726 and 2791. -/
theorem sqrt_image_sign (g : Field.absoluteGaloisGroup F) :
    g.toAlgHom s = s ∨ g.toAlgHom s = -s := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [← map_pow, hs, AlgHom.commutes]

include hs0 in
/-- Kind: theorem, proved. The two signs of a nonzero square root are
distinct in characteristic zero; tex 2726 and 2791. -/
theorem sqrt_neg_ne_self : -s ≠ s := by
  intro h
  have h2 : (2 : AlgebraicClosure F) * s = 0 := by linear_combination -h
  exact hs0 ((mul_eq_zero.mp h2).resolve_left two_ne_zero)

open Classical in
/-- Kind: definition. The genuine absolute Galois character attached to
a nonzero square root; tex 2726 and 2791. -/
def sqrtCharacter (s : AlgebraicClosure F) {a : F}
    (hs : s ^ 2 = algebraMap F (AlgebraicClosure F) a) (hs0 : s ≠ 0) :
    Field.absoluteGaloisGroup F →* ℤˣ where
  toFun g := if g.toAlgHom s = s then 1 else -1
  map_one' := by
    change (if s = s then (1 : ℤˣ) else -1) = 1
    simp
  map_mul' g h := by
    have hne := sqrt_neg_ne_self s hs0
    have hcomp : (g * h).toAlgHom s = g.toAlgHom (h.toAlgHom s) := rfl
    rcases sqrt_image_sign s hs g with hg | hg <;>
      rcases sqrt_image_sign s hs h with hh | hh
    · simp [hcomp, hg, hh]
    · have hgh : (g * h).toAlgHom s = -s := by rw [hcomp, hh, map_neg, hg]
      simp [hgh, hg, hh, hne]
    · have hgh : (g * h).toAlgHom s = -s := by rw [hcomp, hh, hg]
      simp [hgh, hg, hh, hne]
    · have hgh : (g * h).toAlgHom s = s := by rw [hcomp, hh, map_neg, hg, neg_neg]
      simp [hgh, hg, hh, hne]

/-- Kind: instance, proved. The quadratic character has open kernel:
its kernel is the open stabilizer of its defining square root;
tex 2781–2796. -/
instance sqrtCharacterOpenKer : IsOpenKer (sqrtCharacter s hs hs0) := by
  classical
  constructor
  have heq : ((sqrtCharacter s hs hs0).ker : Set (Field.absoluteGaloisGroup F)) =
      {g | g.toAlgHom s = s} := by
    ext g
    by_cases hg : g.toAlgHom s = s <;> simp [MonoidHom.mem_ker, sqrtCharacter, hg]
  rw [heq]
  exact isOpen_fix s

/-- Kind: theorem, proved. A nonsquare defines a nontrivial quadratic
character. The fixed-field characterization is the Galois descent used
in tex 3413–3417, with the character of tex 2726 and 2791. -/
theorem sqrtCharacter_has_negative (ha : ¬ ∃ x : F, x ^ 2 = a) :
    ∃ g : Field.absoluteGaloisGroup F, sqrtCharacter s hs hs0 g = -1 := by
  classical
  have hnot : ¬ ∀ g : Field.absoluteGaloisGroup F, g.toAlgHom s = s := by
    intro hfix
    obtain ⟨x, hx⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed s).mpr (fun g => hfix g)
    apply ha
    refine ⟨x, (algebraMap F (AlgebraicClosure F)).injective ?_⟩
    rw [map_pow, hx]
    exact hs
  push Not at hnot
  obtain ⟨g, hg⟩ := hnot
  exact ⟨g, by simp [sqrtCharacter, hg]⟩

end QuadraticCharacter

section DyadicExample

/-- Kind: theorem, proved. Two is not a square in the dyadic local
field: its valuation is odd. This supplies a concrete quadratic
character for the local conditions of tex 3413–3438. -/
theorem padic_two_not_square : ¬ ∃ x : Padic 2, x ^ 2 = 2 := by
  rintro ⟨x, hx⟩
  have hv := congrArg (Padic.valuation (p := 2)) hx
  rw [Padic.valuation_pow] at hv
  norm_num [Padic.valuation_ofNat, padicValNat_self] at hv
  omega

/-- Kind: definition. A square root of two in the algebraic closure of
the dyadic local field; tex 2726 and 3413–3438. -/
def dyadicSqrtTwo : AlgebraicClosure (Padic 2) :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (2 : AlgebraicClosure (Padic 2))
    (by decide : 0 < 2))

/-- Kind: theorem, proved. The defining square-root equation of the
quadratic character; tex 2726 and 2791. -/
theorem dyadicSqrtTwo_sq :
    dyadicSqrtTwo ^ 2 = algebraMap (Padic 2) (AlgebraicClosure (Padic 2)) 2 := by
  rw [map_ofNat]
  exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
    (2 : AlgebraicClosure (Padic 2)) (by decide : 0 < 2))

/-- Kind: theorem, proved. The chosen square root is nonzero;
tex 2726 and 2791. -/
theorem dyadicSqrtTwo_ne_zero : dyadicSqrtTwo ≠ 0 := by
  intro h
  have hs := dyadicSqrtTwo_sq
  rw [h, zero_pow (by decide), map_ofNat] at hs
  norm_num at hs

/-- Kind: definition. The continuous quadratic character of the actual
extension obtained by adjoining the square root of two to the dyadic
field; tex 2726 and 2791. -/
def dyadicSignCharacter : Field.absoluteGaloisGroup (Padic 2) →* ℤˣ :=
  sqrtCharacter dyadicSqrtTwo dyadicSqrtTwo_sq dyadicSqrtTwo_ne_zero

/-- Kind: instance, proved. The concrete quadratic character has open
kernel, as required of stage characters in tex 2781–2796. -/
instance dyadicSignCharacterOpenKer : IsOpenKer dyadicSignCharacter :=
  sqrtCharacterOpenKer dyadicSqrtTwo dyadicSqrtTwo_sq dyadicSqrtTwo_ne_zero

/-- Kind: theorem, proved. The concrete dyadic character takes the value
minus one; tex 2726 and 2791. -/
theorem dyadicSignCharacter_has_negative :
    ∃ g : Field.absoluteGaloisGroup (Padic 2), dyadicSignCharacter g = -1 :=
  sqrtCharacter_has_negative dyadicSqrtTwo dyadicSqrtTwo_sq dyadicSqrtTwo_ne_zero
    padic_two_not_square

open Classical in
/-- Kind: definition. The literal finite Kummer condition over `A₂`
for the elliptic curve `y² = x³ - x` over the dyadic field and the zero
equivariant map from its four-torsion into the free sign module. This
map is permitted by the coefficient-map interface of tex 3430–3438. -/
def dyadicZeroKummerCondition : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx (Acoef 2) :=
  kummerConditionIn (Acoef 2)
    (0 : TorsAlg (Padic 2) (curveY2X3mX.baseChange (Padic 2)) 4 →+
      SignModule dyadicSignCharacter)
    (fun _ _ => by simp)

/-- Kind: theorem, proved. Every ambient continuous cochain module in
the concrete dyadic example is free over the second stage ring. Thus
the degree-one obstruction is not a failure of ambient cochain
flatness. This is the finite-partition method of tex 4409–4414. -/
theorem dyadicAmbientCochains_free (n : ℕ) :
    Module.Free (Acoef 2)
      ((contCochains (Acoef 2) (Field.absoluteGaloisGroup (Padic 2))
        (SignModule dyadicSignCharacter)).X n) :=
  free_contCochains (R := Acoef 2) (G := Field.absoluteGaloisGroup (Padic 2))
    (M := SignModule dyadicSignCharacter)
    (ZInQ.Manuscript.RC.Limits.ElliotRing.isNilpotent_maximalIdeal 2) n

/-- Kind: theorem, proved. A concrete degree-one Kummer term over the
actual second stage ring is not flat, although its coefficient module
is free of rank two. No flatness or nonflatness premise is used;
tex 2725, 3430–3438, and 4391–4414. -/
theorem dyadicZeroKummerCondition_not_flat :
    ¬ Module.Flat (Acoef 2) (dyadicZeroKummerCondition.X 1) := by
  classical
  exact kummerConditionIn_zero_not_flat (curveY2X3mX.baseChange (Padic 2)) 4
    (ZInQ.Manuscript.RC.Limits.ElliotRing.isNilpotent_maximalIdeal 2)
    2 stage_two_ne_zero (signModule_two_smul_difference dyadicSignCharacter)
    (signModule_action_nontrivial dyadicSignCharacter dyadicSignCharacter_has_negative)
    (fun _ _ => by simp)

/-- Kind: theorem, proved. The same concrete condition has flat terms
in every degree other than one; tex 3415–3417 and 4412–4414. -/
theorem dyadicZeroKummerCondition_flat_off_one (n : ℤ) (hn : n ≠ 1) :
    Module.Flat (Acoef 2) (dyadicZeroKummerCondition.X n) := by
  classical
  exact flat_cocycleCondition_of_ne_one (R := Acoef 2)
    (G := Field.absoluteGaloisGroup (Padic 2)) (M := SignModule dyadicSignCharacter) _ _ n hn

end DyadicExample

section StageTerms

open NumberField IsDedekindDomain
open ZInQ.Contrib.RC53Assist.ResidualBounds (standardOldAt)
open ZInQ.Manuscript.RC.Wiring (stdOldConditions)

variable {K : Type} [Field K] [NumberField K]
  {S₀ S : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic]

/-- Kind: theorem, proved. Under the actual stage torsion hypothesis,
every standard old-condition term outside degree one is flat. This
uses the actual `MinS` coefficient module, not an abstract replacement;
tex 2725, 3415–3417, and 4391–4414. -/
theorem standardOldAt_flat_off_one (i : ℕ) [NeZero i]
    (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]
    (hTor : FullTorsion K S₀ W (2 ^ i)) (v : Places K S)
    [DecidableEq (v.1.adicCompletion K)] (label : ℕ)
    (E : WeierstrassCurve (v.1.adicCompletion K)) [E.IsElliptic] (m : ℕ) [NeZero m]
    (ι : TorsAlg (v.1.adicCompletion K) E m →+
      ResMod (locMap K S v.1) (MinS hS W i α))
    (hι : ∀ (g : Gloc K v.1) t, ι (g • t) = g • ι t) (n : ℤ) (hn : n ≠ 1) :
    Module.Flat (Acoef i)
      ((standardOldAt K S (Acoef i) (MinS hS W i α) v label E m ι hι).U.X n) := by
  by_cases h01 : label = 0 ∨ label = 1
  · exact ZInQ.Manuscript.RC.Wiring.standardOldAt_flat_of_label hS W i α hTor
      v label h01 E m ι hι n
  · have h0 : label ≠ 0 := fun h => h01 (Or.inl h)
    have h1 : label ≠ 1 := fun h => h01 (Or.inr h)
    have : Module.Free (Acoef i) (Mcoef K S₀ W i α) :=
      ZInQ.Manuscript.RC.Wiring.mcoef_free W i α hTor
    have : Module.Flat (Acoef i) (ResMod (locMap K S v.1) (MinS hS W i α)) :=
      inferInstanceAs (Module.Flat (Acoef i) (Mcoef K S₀ W i α))
    have : CompactSpace (Gloc K v.1) := ZInQ.Manuscript.RC.FibreDuality.compactSpace_Gloc v.1
    unfold standardOldAt
    rw [ite_eq_right h0, ite_eq_right h1]
    exact flat_cocycleCondition_of_ne_one (R := Acoef i) (G := Gloc K v.1)
      (M := ResMod (locMap K S v.1) (MinS hS W i α)) _ _ n hn

omit [W.IsElliptic] in
/-- Kind: theorem, proved. The literal standard Kummer condition at the
actual second stage is nonflat for a zero coefficient map and a
nontrivial local sign action. These are conditions on the actual action
and map, not a flatness or nonflatness premise; tex 2725–2726,
3430–3438, and 4391–4414. -/
theorem standardOldAt_not_flat_of_zero
    (α : GKS K S₀ →* (Acoef 2)ˣ) [IsOpenKer α] (v : Places K S)
    [DecidableEq (v.1.adicCompletion K)] (label : ℕ) (h0 : label ≠ 0) (h1 : label ≠ 1)
    (E : WeierstrassCurve (v.1.adicCompletion K)) [E.IsElliptic] (m : ℕ) [NeZero m]
    (ι : TorsAlg (v.1.adicCompletion K) E m →+
      ResMod (locMap K S v.1) (MinS hS W 2 α))
    (hι : ∀ (g : Gloc K v.1) t, ι (g • t) = g • ι t) (hzero : ι = 0)
    (hsign : ∀ (g : Gloc K v.1) (x : ResMod (locMap K S v.1) (MinS hS W 2 α)),
      g • x = x ∨ g • x = -x)
    (hmove : ∃ (g : Gloc K v.1) (x : ResMod (locMap K S v.1) (MinS hS W 2 α)),
      g • x ≠ x) :
    ¬ Module.Flat (Acoef 2)
      ((standardOldAt K S (Acoef 2) (MinS hS W 2 α) v label E m ι hι).U.X 1) := by
  subst ι
  unfold standardOldAt
  rw [ite_eq_right h0, ite_eq_right h1]
  exact kummerConditionIn_zero_not_flat E m
    (ZInQ.Manuscript.RC.Limits.ElliotRing.isNilpotent_maximalIdeal 2)
    2 stage_two_ne_zero (by
      intro g x
      rcases hsign g x with hx | hx
      · rw [hx, sub_self, smul_zero]
      · rw [hx]
        have hneg : -x - x = ((-1 : Acoef 2) - 1) • x := by
          rw [sub_smul, neg_one_smul, one_smul]
        rw [hneg, smul_smul]
        have hcoef : (2 : Acoef 2) * (-1 - 1) = 0 := by
          calc
            (2 : Acoef 2) * (-1 - 1) = -(2 : Acoef 2) ^ 2 := by ring
            _ = 0 := by rw [ZInQ.Manuscript.RC.HeegnerAlgebra.two_pow_A 2, neg_zero]
        rw [hcoef]
        exact zero_smul (Acoef 2) x) hmove hι

variable (α : ∀ i, GKS K S₀ →* (Acoef i)ˣ) [hα : ∀ i, IsOpenKer (α i)]
  (Bv : ∀ v : Places K S, WeierstrassCurve (v.1.adicCompletion K))
  [hBv : ∀ v, (Bv v).IsElliptic] (label : ℕ → Places K S → ℕ) (m : ℕ → ℕ)
  [hm : ∀ i, NeZero (m i)]
  (ιK : ∀ i (v : Places K S), TorsAlg (v.1.adicCompletion K) (Bv v) (m i) →+
    ResMod (locMap K S v.1) (MinS hS W i (α i)))
  (hιK : ∀ i (v : Places K S) (g : Gloc K v.1) t,
    ιK i v (g • t) = g • ιK i v t)

open Classical in
/-- Kind: theorem, proved. All quantified stage terms of the exact
standard old-condition family are flat off degree one, from the
existing full-torsion input alone; tex 2725, 3415–3417, and 4391–4414. -/
theorem stdOldConditions_flat_off_one
    (hTor : ∀ i, FullTorsion K S₀ W (2 ^ i)) (i : ℕ) [NeZero i]
    (v : Places K S) (hv : v.1 ∈ S₀) (n : ℤ) (hn : n ≠ 1) :
    Module.Flat (Acoef i)
      (((stdOldConditions hS W α Bv label m ιK hιK) i v hv).U.X n) := by
  have := hα i
  have := hBv v
  have := hm i
  exact standardOldAt_flat_off_one hS W i (α i) (hTor i) v (label i v)
    (Bv v) (m i) (ιK i v) (hιK i v) n hn

open Classical in
omit [W.IsElliptic] in
/-- Kind: theorem, proved. The exact quantified Kummer-flatness field
cannot hold if one second-stage old place has a zero coefficient map
and a nontrivial local sign action. The conclusion is the negation of
that field's complete quantifier order; tex 2725–2726, 3430–3438, and
4391–4414. -/
theorem hcflatK_refuted_at_two (v : Places K S) (hv : v.1 ∈ S₀)
    (h0 : label 2 v ≠ 0) (h1 : label 2 v ≠ 1) (hzero : ιK 2 v = 0)
    (hsign : ∀ (g : Gloc K v.1)
      (x : ResMod (locMap K S v.1) (MinS hS W 2 (α 2))), g • x = x ∨ g • x = -x)
    (hmove : ∃ (g : Gloc K v.1)
      (x : ResMod (locMap K S v.1) (MinS hS W 2 (α 2))), g • x ≠ x) :
    ¬ (∀ i [NeZero i] (w : Places K S) (hw : w.1 ∈ S₀) (n : ℤ),
      label i w ≠ 0 → label i w ≠ 1 → Module.Flat (Acoef i)
        (((stdOldConditions hS W α Bv label m ιK hιK) i w hw).U.X n)) := by
  have := hα 2
  have := hBv v
  have := hm 2
  intro hflat
  exact (standardOldAt_not_flat_of_zero hS W (α 2) v (label 2 v) h0 h1
    (Bv v) (m 2) (ιK 2 v) (hιK 2 v) hzero hsign hmove) (hflat 2 v hv 1 h0 h1)

end StageTerms

section SplitTorsion

open scoped TensorProduct
open NumberField IsDedekindDomain
open ZInQ.Contrib.RC53Assist.ResidualBounds (standardOldAt)

/-- Kind: theorem, proved. If the torsion representation is fixed, its
scalar extension is acted on solely through the twisting character.
This is the actual tensor construction of tex 2725–2726 and 2790–2796. -/
theorem coefMod_smul_of_fixed {G : Type} [Group G] {A : Type} [CommRing A]
    (α : G →* Aˣ) {T : Type} [AddCommGroup T] [DistribMulAction G T]
    (hfixed : ∀ (g : G) (t : T), g • t = t) (g : G) (x : CoefMod A α T) :
    g • x = ((α g : Aˣ) : A) • x := by
  obtain ⟨y, rfl⟩ := (CoefMod.equiv A α T).surjective x
  induction y using TensorProduct.inductionOn with
  | tmul a t =>
    rw [CoefMod.smul_tmul, hfixed]
    change (((α g : Aˣ) : A) * a) ⊗ₜ[ℤ] t = ((α g : Aˣ) : A) • (a ⊗ₜ[ℤ] t)
    rw [TensorProduct.smul_tmul', smul_eq_mul]
  | add y z hy hz =>
    simpa only [map_add, smul_add] using congrArg₂ (· + ·) hy hz

/-- Kind: definition. The scalar stage character obtained from an
integer-valued quadratic character; tex 2726 and 2791. -/
def quadraticStageCharacter {G : Type} [Group G] (χ : G →* ℤˣ) (i : ℕ) :
    G →* (Acoef i)ˣ := (intUnitsTo (Acoef i)).comp χ

/-- Kind: instance, proved. A quadratic character with open kernel
retains an open kernel at every coefficient stage; tex 2781–2796. -/
instance quadraticStageCharacterOpenKer {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (χ : G →* ℤˣ) [IsOpenKer χ] (i : ℕ) :
    IsOpenKer (quadraticStageCharacter χ i) := isOpenKer_map χ (intUnitsTo (Acoef i))

variable {K : Type} [Field K] [NumberField K]
  {S₀ S : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic]
  (χ : GKS K S₀ →* ℤˣ) [IsOpenKer χ]

omit [W.IsElliptic] [IsOpenKer χ] in
/-- Kind: theorem, proved. For split torsion, the actual inflated
coefficient module has the local quadratic action prescribed by its
character, including both restriction maps; tex 2725–2726, 2791,
and 3479–3498. -/
theorem minS_quadratic_action (i : ℕ)
    (hfixed : ∀ (g : GKS K S₀) (t : TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)), g • t = t)
    (v : Places K S) (g : Gloc K v.1)
    (x : ResMod (locMap K S v.1) (MinS hS W i (quadraticStageCharacter χ i))) :
    g • x = ((χ (inflMap K hS (locMap K S v.1 g)) : ℤˣ) : ℤ) • x := by
  let σ : GKS K S₀ := inflMap K hS (locMap K S v.1 g)
  let y : Mcoef K S₀ W i (quadraticStageCharacter χ i) := x
  change σ • y = ((χ σ : ℤˣ) : ℤ) • y
  rw [coefMod_smul_of_fixed (quadraticStageCharacter χ i) hfixed]
  change ((((χ σ : ℤˣ) : ℤ) : Acoef i)) • y = _
  exact Int.cast_smul_eq_zsmul (Acoef i) ((χ σ : ℤˣ) : ℤ) y

/-- Kind: theorem, proved. For the actual `MinS` module, split
four-torsion and a nontrivial local quadratic character yield a
nonflat zero-map Kummer term at stage two. The full-torsion premise is
the existing stage input; neither a module flatness conclusion nor a
local action identity is assumed. Tex 2725–2726, 3430–3438,
3479–3498, and 4391–4414. -/
theorem standardOldAt_split_quadratic_not_flat
    (hTor : FullTorsion K S₀ W (2 ^ 2))
    (hfixed : ∀ (g : GKS K S₀) (t : TorsS K S₀ W ((2 ^ 2 : ℕ) : ℤ)), g • t = t)
    (v : Places K S) [DecidableEq (v.1.adicCompletion K)]
    (hχ : ∃ g : Gloc K v.1, χ (inflMap K hS (locMap K S v.1 g)) = -1)
    (label : ℕ) (h0 : label ≠ 0) (h1 : label ≠ 1)
    (E : WeierstrassCurve (v.1.adicCompletion K)) [E.IsElliptic] (m : ℕ) [NeZero m]
    (ι : TorsAlg (v.1.adicCompletion K) E m →+
      ResMod (locMap K S v.1) (MinS hS W 2 (quadraticStageCharacter χ 2)))
    (hι : ∀ (g : Gloc K v.1) t, ι (g • t) = g • ι t) (hzero : ι = 0) :
    ¬ Module.Flat (Acoef 2)
      ((standardOldAt K S (Acoef 2) (MinS hS W 2 (quadraticStageCharacter χ 2))
        v label E m ι hι).U.X 1) := by
  let M := ResMod (locMap K S v.1) (MinS hS W 2 (quadraticStageCharacter χ 2))
  have hsign : ∀ (g : Gloc K v.1) (x : M), g • x = x ∨ g • x = -x := by
    intro g x
    have hact := minS_quadratic_action hS W χ 2 hfixed v g x
    rcases Int.units_eq_one_or (χ (inflMap K hS (locMap K S v.1 g))) with hg | hg
    · exact Or.inl (by rw [hact, hg, Units.val_one, one_zsmul])
    · exact Or.inr (by rw [hact, hg, Units.val_neg, Units.val_one, neg_one_zsmul])
  have hfree : Module.Free (Acoef 2) (Mcoef K S₀ W 2 (quadraticStageCharacter χ 2)) :=
    ZInQ.Manuscript.RC.Wiring.mcoef_free W 2 (quadraticStageCharacter χ 2) hTor
  have : Module.Free (Acoef 2) M := inferInstanceAs
    (Module.Free (Acoef 2) (Mcoef K S₀ W 2 (quadraticStageCharacter χ 2)))
  have hnt : Nontrivial (Mcoef K S₀ W 2 (quadraticStageCharacter χ 2)) :=
    (ZInQ.Manuscript.RC.Wiring.mcoefEquiv W 2 (quadraticStageCharacter χ 2) hTor).toEquiv.symm.nontrivial
  have : Nontrivial M := inferInstanceAs
    (Nontrivial (Mcoef K S₀ W 2 (quadraticStageCharacter χ 2)))
  have : FaithfulSMul (Acoef 2) M := inferInstance
  have hnot : ¬ ∀ x : M, (2 : Acoef 2) • x = 0 := by
    intro hx
    apply stage_two_ne_zero
    exact eq_of_smul_eq_smul (fun x : M => (hx x).trans (zero_smul (Acoef 2) x).symm)
  push Not at hnot
  obtain ⟨x, hx⟩ := hnot
  obtain ⟨g, hg⟩ := hχ
  have hmove : ∃ (g : Gloc K v.1) (x : M), g • x ≠ x := by
    refine ⟨g, x, ?_⟩
    intro heq
    have hact := minS_quadratic_action hS W χ 2 hfixed v g x
    rw [hg, Units.val_neg, Units.val_one, neg_one_zsmul] at hact
    have hxx : -x = x := hact.symm.trans heq
    apply hx
    rw [two_smul]
    calc
      x + x = -x + x := by rw [hxx]
      _ = 0 := neg_add_cancel x
  exact standardOldAt_not_flat_of_zero hS W (quadraticStageCharacter χ 2)
    v label h0 h1 E m ι hι hzero hsign hmove

end SplitTorsion

section ModelRequirement

open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex)
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.Limits (GradedModel)

/-- Kind: theorem, proved. The stage matrix-diagram consumer needs a
bounded graded finite free model and the actual duality data, not
termwise flatness of the chosen cochain presentation. The model's
localization, global trace pairing, and local trace pairing are retained
exactly. This exposes the weaker sufficient interface at tex 4391–4451;
it does not construct the required model for arbitrary Kummer maps. -/
theorem exists_stage_diagram_of_gradedModel
    {A : Type} [CommRing A] (G : GCx A) {U : GCx A}
    {res : GHom G (splitLocalComplex A)} {ι : GHom U (splitLocalComplex A)}
    (Q : SelPairData (splitSelData G res U ι) (splitSelData G res U ι))
    (tr : (coneCx Q.resE).X 3 →ₗ[A] A)
    (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (hdual : QuasiIso (GHom.toCC (globalDualityMap Q tr htr)))
    (R : GradedModel G) (lo hi : ℤ)
    (hr : ∀ n, n < lo ∨ hi < n → R.rank n = 0) :
    ∃ S : StageMatrixDiagram A R.rank,
      S.dC = R.dC ∧ S.res = modelRes R (stagePairingInputOfSel Q tr htr) ∧
        S.glob = modelGlob R (stagePairingInputOfSel Q tr htr) ∧ S.loc = stageLocMat Q tr := by
  exact exists_stageMatrixDiagram R (stagePairingInputOfSel Q tr htr)
    (quasiIso_stageDualityMap_of_global Q tr htr hdual) lo hi hr

end ModelRequirement

end ZInQ.Contrib.RC53Assist.KummerFlat
