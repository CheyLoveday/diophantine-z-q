import ZInQKernel.Contrib.RC53Assist.LocalDegreeTwo.NormalizedPairing
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.CupOne
import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitRegularity

/-!
# Tame cup products at derivative primes

The unramified character is placed before the uniformizer character in the
normalized local invariant. Reversing these characters changes the sign by
an explicit coboundary. A character lifted to twice the coefficient exponent
has a coboundary square, without division by two in the coefficient ring.
These identities are used at the retained precision of the derivative
conditions (tex 3090–3096, 4859–4863, 5035–5042).
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.ResidueIdentity

open CategoryTheory Module
open scoped Matrix TensorProduct
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.InnerLimitArith

/-- Kind: proved theorem. The integral quadratic refinement is additive up
 to its cross term (tex 3090–3096, 4859–4863). -/
theorem chooseTwo_add (a b : ℕ) :
    (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hrec (k : ℕ) : (k + 1).choose 2 = k.choose 1 + k.choose 2 :=
      Nat.choose_succ_succ k 1
    rw [Nat.add_succ, hrec (a + b), hrec b, ih]
    simp only [Nat.choose_one_right, Nat.mul_succ]
    omega

/-- Kind: proved theorem. Twice the exponent is a period of the quadratic
 refinement modulo the exponent (tex 3090–3096, 4859–4863). -/
theorem chooseTwo_double (n : ℕ) : (2 * n).choose 2 = n * (2 * n - 1) := by
  rw [Nat.choose_two_right]
  rw [show 2 * n * (2 * n - 1) = n * (2 * n - 1) * 2 by ring]
  simp

/-- Kind: proved theorem. The quadratic refinement descends modulo twice
 the exponent (tex 3090–3096, 4859–4863). -/
theorem chooseTwo_period (n a : ℕ) :
    (((a + 2 * n).choose 2 : ℕ) : ZMod n) = (a.choose 2 : ZMod n) := by
  rw [chooseTwo_add, chooseTwo_double]
  simp [Nat.cast_mul]

/-- Kind: definition. The integral quadratic refinement on a character
 with twice the coefficient exponent (tex 3090–3096, 4859–4863). -/
def quadraticResidue (n : ℕ) (x : ZMod (2 * n)) : ZMod n :=
  (x.val.choose 2 : ZMod n)

/-- Kind: proved theorem. The cross term of the quadratic refinement is
 the product of the reduced character values (tex 3090–3096, 4859–4863). -/
theorem quadraticResidue_add (n : ℕ) [NeZero n] (x y : ZMod (2 * n)) :
    quadraticResidue n (x + y) = quadraticResidue n x + quadraticResidue n y +
      (x.val : ZMod n) * (y.val : ZMod n) := by
  have : NeZero (2 * n) := ⟨mul_ne_zero two_ne_zero (NeZero.ne n)⟩
  have he : quadraticResidue n (x + y) = ((x.val + y.val).choose 2 : ZMod n) := by
    by_cases h : x.val + y.val < 2 * n
    · rw [quadraticResidue, ZMod.val_add_of_lt h]
    · have hv : x.val + y.val = (x + y).val + 2 * n :=
        ZMod.val_add_val_of_le (le_of_not_gt h)
      rw [hv, chooseTwo_period]
      rfl
  rw [he, chooseTwo_add]
  simp only [quadraticResidue, Nat.cast_add, Nat.cast_mul]

section CharacterCochains

variable {R G M : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- Kind: definition. The coefficient-valued tame two-cochain
 `(g,h) ↦ u(g)κ(h)m` (tex 4859–4863, 5035–5042). -/
def characterProduct (u κ : G → R) (hu : Continuous u) (hκ : Continuous κ)
    (m : M) : (contCochains R G M).X 2 :=
  mkCochain2 (fun p => (u p.1 * κ p.2) • m)
    ((continuous_of_discreteTopology : Continuous (fun p : R × R =>
      (p.1 * p.2) • m)).comp
        ((hu.comp continuous_fst).prodMk (hκ.comp continuous_snd)))

/-- Kind: proved theorem. Evaluation of the tame two-cochain
 (tex 4859–4863, 5035–5042). -/
theorem characterProduct_eval (u κ : G → R) (hu : Continuous u) (hκ : Continuous κ)
    (m : M) (g h : G) :
    evalTwo R M g h (characterProduct u κ hu hκ m) = (u g * κ h) • m := rfl

/-- Kind: proved theorem. The tame product of additive characters is a
 two-cocycle for trivial derivative action (tex 4859–4863, 5035–5042). -/
theorem characterProduct_cycle (u κ : G → R) (hu : Continuous u) (hκ : Continuous κ)
    (htriv : ∀ (g : G) (m : M), g • m = m)
    (hua : ∀ g h, u (g * h) = u g + u h)
    (hκa : ∀ g h, κ (g * h) = κ g + κ h) (m : M) :
    ((contCochains R G M).d 2 3).hom (characterProduct u κ hu hκ m) = 0 := by
  apply contCochains_ext
  intro v
  have hv : v = ![v 0, v 1, v 2] := by funext j; fin_cases j <;> rfl
  rw [hv, contFun_d23, htriv]
  change (u (v 1) * κ (v 2)) • m - (u (v 0 * v 1) * κ (v 2)) • m +
    (u (v 0) * κ (v 1 * v 2)) • m - (u (v 0) * κ (v 1)) • m = 0
  rw [hua, hκa]
  module

/-- Kind: definition. The pointwise character product, whose coboundary
 compares the two orders of the mixed cup (tex 4859–4863, 5035–5042). -/
def mixedPrimitive (u κ : G → R) (hu : Continuous u) (hκ : Continuous κ)
    (m : M) : (contCochains R G M).X 1 :=
  mkCochain1 (fun g => (u g * κ g) • m)
    ((continuous_of_discreteTopology : Continuous (fun p : R × R =>
      (p.1 * p.2) • m)).comp (hu.prodMk hκ))

/-- Kind: proved theorem. Reversing the mixed cup introduces exactly a
 coboundary, at integral two-power precision (tex 4859–4863, 5035–5042). -/
theorem mixedPrimitive_d (u κ : G → R) (hu : Continuous u) (hκ : Continuous κ)
    (htriv : ∀ (g : G) (m : M), g • m = m)
    (hua : ∀ g h, u (g * h) = u g + u h)
    (hκa : ∀ g h, κ (g * h) = κ g + κ h) (m : M) :
    ((contCochains R G M).d 1 2).hom (mixedPrimitive u κ hu hκ m) =
      -(characterProduct u κ hu hκ m + characterProduct κ u hκ hu m) := by
  apply contCochains_ext
  intro v
  have hv : v = ![v 0, v 1] := by funext j; fin_cases j <;> rfl
  rw [hv, contFun_d12, htriv]
  change (u (v 1) * κ (v 1)) • m - (u (v 0 * v 1) * κ (v 0 * v 1)) • m +
    (u (v 0) * κ (v 0)) • m =
      -((u (v 0) * κ (v 1)) • m + (κ (v 0) * u (v 1)) • m)
  rw [hua, hκa]
  module

/-- Kind: proved theorem. A normalized local coordinate reads the reversed
 mixed cup with negative orientation (tex 4859–4863, 5035–5042). -/
theorem reversedProduct_coordinate
    (c₂ : (contCochains R G M).X 2 →ₗ[R] M)
    (hkill : ∀ a, c₂ (((contCochains R G M).d 1 2).hom a) = 0)
    (u κ : G → R) (hu : Continuous u) (hκ : Continuous κ)
    (htriv : ∀ (g : G) (m : M), g • m = m)
    (hua : ∀ g h, u (g * h) = u g + u h)
    (hκa : ∀ g h, κ (g * h) = κ g + κ h)
    (hn : LocalDegreeTwoNormalized c₂ u κ) (m : M) :
    c₂ (characterProduct κ u hκ hu m) = -m := by
  have hm : c₂ (characterProduct u κ hu hκ m) = m :=
    hn m _ (characterProduct_eval u κ hu hκ m)
  have hz := hkill (mixedPrimitive u κ hu hκ m)
  rw [mixedPrimitive_d u κ hu hκ htriv hua hκa, map_neg, map_add, hm,
    neg_eq_zero] at hz
  calc
    _ = (m + c₂ (characterProduct κ u hκ hu m)) - m := by abel
    _ = -m := by rw [hz, zero_sub]

variable (n : ℕ) [NeZero n] [Algebra (ZMod n) R]

/-- Kind: definition. An integral square primitive obtained from a
 character of twice the coefficient exponent (tex 3090–3096, 4859–4863). -/
def liftedSquarePrimitive (χ : G → ZMod (2 * n)) (hχ : Continuous χ) (m : M) :
    (contCochains R G M).X 1 :=
  mkCochain1 (fun g => algebraMap (ZMod n) R (quadraticResidue n (χ g)) • m)
    ((continuous_of_discreteTopology : Continuous (fun a : ZMod (2 * n) =>
      algebraMap (ZMod n) R (quadraticResidue n a) • m)).comp hχ)

/-- Kind: proved theorem. An additive lift to twice the coefficient
 exponent makes the square cup a coboundary (tex 3090–3096, 4859–4863). -/
theorem liftedSquarePrimitive_d
    (u : G → R) (hu : Continuous u)
    (χ : G → ZMod (2 * n)) (hχ : Continuous χ)
    (hχa : ∀ g h, χ (g * h) = χ g + χ h)
    (hlift : ∀ g, u g = algebraMap (ZMod n) R ((χ g).val : ZMod n))
    (htriv : ∀ (g : G) (m : M), g • m = m) (m : M) :
    ((contCochains R G M).d 1 2).hom (liftedSquarePrimitive n χ hχ m) =
      -characterProduct u u hu hu m := by
  apply contCochains_ext
  intro v
  have hv : v = ![v 0, v 1] := by funext j; fin_cases j <;> rfl
  rw [hv, contFun_d12, htriv]
  change algebraMap (ZMod n) R (quadraticResidue n (χ (v 1))) • m -
    algebraMap (ZMod n) R (quadraticResidue n (χ (v 0 * v 1))) • m +
    algebraMap (ZMod n) R (quadraticResidue n (χ (v 0))) • m =
      -((u (v 0) * u (v 1)) • m)
  rw [hχa, quadraticResidue_add, map_add, map_add, map_mul,
    ← hlift (v 0), ← hlift (v 1)]
  module

/-- Kind: proved theorem. A local trace killing coboundaries vanishes on
 the square of a character with an additive double-exponent lift. The
 hypothesis is a character-lifting fact, not a cup-table identity
 (tex 3090–3096, 4859–4863, 5035–5042). -/
theorem liftedProduct_coordinate_zero
    (c₂ : (contCochains R G M).X 2 →ₗ[R] M)
    (hkill : ∀ a, c₂ (((contCochains R G M).d 1 2).hom a) = 0)
    (u : G → R) (hu : Continuous u)
    (χ : G → ZMod (2 * n)) (hχ : Continuous χ)
    (hχa : ∀ g h, χ (g * h) = χ g + χ h)
    (hlift : ∀ g, u g = algebraMap (ZMod n) R ((χ g).val : ZMod n))
    (htriv : ∀ (g : G) (m : M), g • m = m) (m : M) :
    c₂ (characterProduct u u hu hu m) = 0 := by
  have hz := hkill (liftedSquarePrimitive n χ hχ m)
  rw [liftedSquarePrimitive_d n u hu χ hχ hχa hlift htriv, map_neg, neg_eq_zero] at hz
  exact hz

end CharacterCochains

section CoefficientNaturality

variable {R G M N : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  [AddCommGroup N] [Module R N] [DistribMulAction G N] [SMulCommClass G R N]
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul G N]

/-- Kind: proved theorem. The fundamental tame cochain is linear in its
 coefficient (tex 4859–4863, 5035–5042). -/
theorem characterProduct_smul (u κ : G → R) (hu : Continuous u) (hκ : Continuous κ)
    (r : R) (m : M) :
    characterProduct u κ hu hκ (r • m) = r • characterProduct u κ hu hκ m := by
  apply contCochains_ext
  intro v
  change (u (v 0) * κ (v 1)) • (r • m) = r • ((u (v 0) * κ (v 1)) • m)
  exact smul_comm _ _ _

/-- Kind: definition. Applying a coefficient homomorphism to actual
 continuous cochains (tex 2762–2767, 4859–4863). -/
def coefficientMap (f : M →ₗ[R] N) (n : ℕ) :
    (contCochains R G M).X n →ₗ[R] (contCochains R G N).X n where
  toFun z := (contSubCx R G N).ofSub
    ⟨fun v => f (contFun z v),
      (continuous_of_discreteTopology : Continuous f).comp ((contSubCx R G M).el z).2⟩
  map_add' _ _ := contCochains_ext fun _ => map_add f _ _
  map_smul' r _ := contCochains_ext fun _ => map_smul f r _

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Kind: proved theorem. Evaluation commutes with the coefficient map
 (tex 2762–2767, 4859–4863). -/
theorem coefficientMap_eval (f : M →ₗ[R] N) (n : ℕ)
    (z : (contCochains R G M).X n) (v : Fin n → G) :
    contFun (coefficientMap f n z) v = f (contFun z v) := rfl

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Kind: proved theorem. Coefficient maps preserve coboundaries for the
 trivial local actions at derivative primes (tex 2762–2767, 4859–4863). -/
theorem coefficientMap_d12 (f : M →ₗ[R] N)
    (hM : ∀ (g : G) (m : M), g • m = m)
    (hN : ∀ (g : G) (m : N), g • m = m)
    (a : (contCochains R G M).X 1) :
    coefficientMap f 2 (((contCochains R G M).d 1 2).hom a) =
      ((contCochains R G N).d 1 2).hom (coefficientMap f 1 a) := by
  apply contCochains_ext
  intro v
  have hv : v = ![v 0, v 1] := by funext j; fin_cases j <;> rfl
  rw [hv]
  change f (contFun (((contCochains R G M).d 1 2).hom a) ![v 0, v 1]) = _
  rw [contFun_d12, contFun_d12, hM, hN]
  change f (contFun a (fun _ => v 1) - contFun a (fun _ => v 0 * v 1) +
    contFun a (fun _ => v 0)) =
      f (contFun a (fun _ => v 1)) - f (contFun a (fun _ => v 0 * v 1)) +
        f (contFun a (fun _ => v 0))
  rw [map_add, map_sub]

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Kind: proved theorem. Coefficient maps preserve two-cocycles for the
 trivial local actions at derivative primes (tex 2762–2767, 4859–4863). -/
theorem coefficientMap_d23 (f : M →ₗ[R] N)
    (hM : ∀ (g : G) (m : M), g • m = m)
    (hN : ∀ (g : G) (m : N), g • m = m)
    (z : (contCochains R G M).X 2) :
    coefficientMap f 3 (((contCochains R G M).d 2 3).hom z) =
      ((contCochains R G N).d 2 3).hom (coefficientMap f 2 z) := by
  apply contCochains_ext
  intro v
  have hv : v = ![v 0, v 1, v 2] := by funext j; fin_cases j <;> rfl
  rw [hv]
  change f (contFun (((contCochains R G M).d 2 3).hom z) ![v 0, v 1, v 2]) = _
  rw [contFun_d23, contFun_d23, hM, hN]
  change f (contFun z ![v 1, v 2] - contFun z ![v 0 * v 1, v 2] +
    contFun z ![v 0, v 1 * v 2] - contFun z ![v 0, v 1]) =
      f (contFun z ![v 1, v 2]) - f (contFun z ![v 0 * v 1, v 2]) +
        f (contFun z ![v 0, v 1 * v 2]) - f (contFun z ![v 0, v 1])
  rw [map_sub, map_add, map_sub]

/-- Kind: proved theorem. Coefficient maps carry the oriented fundamental
 cup to the fundamental cup with the mapped coefficient
 (tex 2762–2767, 4859–4863). -/
theorem coefficientMap_characterProduct (f : M →ₗ[R] N)
    (u κ : G → R) (hu : Continuous u) (hκ : Continuous κ) (m : M) :
    coefficientMap f 2 (characterProduct u κ hu hκ m) =
      characterProduct u κ hu hκ (f m) := by
  apply contCochains_ext
  intro v
  exact map_smul f _ _

/-- Kind: proved theorem. Normalized degree-two coordinates are natural
 on every actual two-cocycle, not merely on the fundamental cup
 (tex 2762–2767, 4859–4863). -/
theorem coefficientMap_coordinate
    (cM : (contCochains R G M).X 2 →ₗ[R] M)
    (cN : (contCochains R G N).X 2 →ₗ[R] N)
    (hcM : LocalDegreeTwoCoordinate cM)
    (hkillN : ∀ a, cN (((contCochains R G N).d 1 2).hom a) = 0)
    (u κ : G → R) (hu : Continuous u) (hκ : Continuous κ)
    (hua : ∀ g h, u (g * h) = u g + u h)
    (hκa : ∀ g h, κ (g * h) = κ g + κ h)
    (hM : ∀ (g : G) (m : M), g • m = m)
    (hN : ∀ (g : G) (m : N), g • m = m)
    (hnM : LocalDegreeTwoNormalized cM u κ)
    (hnN : LocalDegreeTwoNormalized cN u κ)
    (f : M →ₗ[R] N) (z : (contCochains R G M).X 2)
    (hz : ((contCochains R G M).d 2 3).hom z = 0) :
    cN (coefficientMap f 2 z) = f (cM z) := by
  let z₀ := characterProduct u κ hu hκ (cM z)
  have hz₀ : ((contCochains R G M).d 2 3).hom z₀ = 0 :=
    characterProduct_cycle u κ hu hκ hM hua hκa _
  have hm₀ : cM z₀ = cM z := hnM _ _ (characterProduct_eval u κ hu hκ _)
  have hcycle : ((contCochains R G M).d 2 3).hom (z - z₀) = 0 := by
    rw [map_sub, hz, hz₀, sub_self]
  have hzero : cM (z - z₀) = 0 := by rw [map_sub, hm₀, sub_self]
  obtain ⟨a, ha⟩ := hcM.2.1 (z - z₀) hcycle hzero
  have hvalue : cN (coefficientMap f 2 (z - z₀)) = 0 := by
    rw [← ha, coefficientMap_d12 f hM hN]
    exact hkillN _
  rw [map_sub, map_sub] at hvalue
  have hfund : cN (coefficientMap f 2 z₀) = f (cM z) := by
    rw [coefficientMap_characterProduct]
    exact hnN _ _ (characterProduct_eval u κ hu hκ _)
  rw [hfund] at hvalue
  exact sub_eq_zero.mp hvalue

end CoefficientNaturality

section ActualCup

variable {R G M N : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  [AddCommGroup N] [Module R N] [DistribMulAction G N] [SMulCommClass G R N]
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul G N]
  (β : M →ₗ[R] M →ₗ[R] N)

/-- Kind: proved theorem. The actual inhomogeneous Weil cup in tame
 coordinates expands into the four scalar character products
 (tex 2762–2767, 4859–4863, 5035–5042). -/
theorem contCup_character_expansion
    (u κ : G → R) (hu : Continuous u) (hκ : Continuous κ)
    (hM : ∀ (g : G) (m : M), g • m = m)
    (a b : (contCochains R G M).X 1) (x₀ x₁ y₀ y₁ : M)
    (ha : ∀ g, evalOne R M g a = u g • x₀ + κ g • x₁)
    (hb : ∀ g, evalOne R M g b = u g • y₀ + κ g • y₁) :
    contCup β continuous_of_discreteTopology 1 1 2 rfl a b =
      characterProduct u u hu hu (β x₀ y₀) +
        characterProduct u κ hu hκ (β x₀ y₁) +
        characterProduct κ u hκ hu (β x₁ y₀) +
        characterProduct κ κ hκ hκ (β x₁ y₁) := by
  apply contCochains_ext
  intro v
  change cupFun β 1 1 2 rfl (contFun a) (contFun b) v = _
  rw [cupFun_one_one_apply, hM]
  change β (evalOne R M (v 0) a) (evalOne R M (v 1) b) = _
  rw [ha, hb]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  change (u (v 1)) • ((u (v 0)) • β x₀ y₀ + (κ (v 0)) • β x₁ y₀) +
    (κ (v 1)) • ((u (v 0)) • β x₀ y₁ + (κ (v 0)) • β x₁ y₁) =
      (u (v 0) * u (v 1)) • β x₀ y₀ +
        (u (v 0) * κ (v 1)) • β x₀ y₁ +
        (κ (v 0) * u (v 1)) • β x₁ y₀ +
        (κ (v 0) * κ (v 1)) • β x₁ y₁
  module

/-- Kind: proved theorem. The actual local cup, read in the normalized
 coordinate, has zero self-axis terms and the correctly signed mixed terms.
 Its independent inputs are additive double-exponent character lifts, not
 the residue pairing identity (tex 3090–3096, 4859–4863, 5035–5042). -/
theorem contCup_normalized_formula (n : ℕ) [NeZero n] [Algebra (ZMod n) R]
    (cN : (contCochains R G N).X 2 →ₗ[R] N)
    (hkill : ∀ z, cN (((contCochains R G N).d 1 2).hom z) = 0)
    (u κ : G → R) (hu : Continuous u) (hκ : Continuous κ)
    (hua : ∀ g h, u (g * h) = u g + u h)
    (hκa : ∀ g h, κ (g * h) = κ g + κ h)
    (χu χκ : G → ZMod (2 * n)) (hχu : Continuous χu) (hχκ : Continuous χκ)
    (hχua : ∀ g h, χu (g * h) = χu g + χu h)
    (hχκa : ∀ g h, χκ (g * h) = χκ g + χκ h)
    (hlu : ∀ g, u g = algebraMap (ZMod n) R ((χu g).val : ZMod n))
    (hlκ : ∀ g, κ g = algebraMap (ZMod n) R ((χκ g).val : ZMod n))
    (hM : ∀ (g : G) (m : M), g • m = m)
    (hN : ∀ (g : G) (m : N), g • m = m)
    (hn : LocalDegreeTwoNormalized cN u κ)
    (a b : (contCochains R G M).X 1) (x₀ x₁ y₀ y₁ : M)
    (ha : ∀ g, evalOne R M g a = u g • x₀ + κ g • x₁)
    (hb : ∀ g, evalOne R M g b = u g • y₀ + κ g • y₁) :
    cN (contCup β continuous_of_discreteTopology 1 1 2 rfl a b) =
      β x₀ y₁ - β x₁ y₀ := by
  have hzeroU (m : N) : cN (characterProduct u u hu hu m) = 0 :=
    liftedProduct_coordinate_zero n cN hkill u hu χu hχu hχua hlu hN m
  have hzeroK (m : N) : cN (characterProduct κ κ hκ hκ m) = 0 :=
    liftedProduct_coordinate_zero n cN hkill κ hκ χκ hχκ hχκa hlκ hN m
  have hmix : cN (characterProduct u κ hu hκ (β x₀ y₁)) = β x₀ y₁ :=
    hn _ _ (characterProduct_eval u κ hu hκ _)
  rw [contCup_character_expansion β u κ hu hκ hM a b x₀ x₁ y₀ y₁ ha hb,
    map_add, map_add, map_add, hzeroU, hzeroK, hmix,
    reversedProduct_coordinate cN hkill u κ hu hκ hN hua hκa hn]
  simp only [zero_add, add_zero, sub_eq_add_neg]

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Kind: proved theorem. The actual cup of two one-cocycles is a
 two-cocycle, with the original Weil coefficient pairing
 (tex 2762–2767, 4859–4863). -/
theorem contCup_cycle
    (hβ : ∀ (g : G) (x y : M), β (g • x) (g • y) = g • β x y)
    (a b : (contCochains R G M).X 1)
    (ha : ((contCochains R G M).d 1 2).hom a = 0)
    (hb : ((contCochains R G M).d 1 2).hom b = 0) :
    ((contCochains R G N).d 2 3).hom
      (contCup β continuous_of_discreteTopology 1 1 2 rfl a b) = 0 := by
  have h := (contNatPair β hβ continuous_of_discreteTopology).leib 1 1 2 rfl a b
  rw [ha, hb, LinearMap.map_zero₂, map_zero, smul_zero, zero_add] at h
  exact h

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Kind: proved theorem. The degree-two/degree-zero cup is the actual
 coefficient homomorphism on the degree-two cochain
 (tex 2762–2767, 4860–4863). -/
theorem contCup_twenty_eq
    (hM : ∀ (g : G) (m : M), g • m = m)
    (z : (contCochains R G M).X 2) (w : (contCochains R G M).X 0) :
    contCup β continuous_of_discreteTopology 2 0 2 rfl z w =
      coefficientMap (β.flip (evalZero R M w)) 2 z := by
  apply contCochains_ext
  intro v
  change cupFun β 2 0 2 rfl (contFun z) (contFun w) v = _
  rw [cupFun_apply, hM]
  change β (contFun z (fun i => v (Fin.castLE (by omega) i)))
      (contFun w (fun j => v ⟨2 + j, by omega⟩)) =
    β (contFun z v) (evalZero R M w)
  have hf : (fun i : Fin 2 => v (Fin.castLE (by omega) i)) = v := by
    funext j
    rfl
  have hs : (fun j : Fin 0 => v ⟨2 + j, by omega⟩) = Fin.elim0 :=
    Subsingleton.elim _ _
  rw [hf, hs]
  rfl

/-- Kind: proved theorem. The normalized local coordinates supply the
 degree-two/degree-zero adjoint for every actual two-cocycle
 (tex 2762–2767, 4860–4863). -/
theorem contCup_twenty_coordinate
    (cM : (contCochains R G M).X 2 →ₗ[R] M)
    (cN : (contCochains R G N).X 2 →ₗ[R] N)
    (hcM : LocalDegreeTwoCoordinate cM)
    (hkillN : ∀ z, cN (((contCochains R G N).d 1 2).hom z) = 0)
    (u κ : G → R) (hu : Continuous u) (hκ : Continuous κ)
    (hua : ∀ g h, u (g * h) = u g + u h)
    (hκa : ∀ g h, κ (g * h) = κ g + κ h)
    (hM : ∀ (g : G) (m : M), g • m = m)
    (hN : ∀ (g : G) (m : N), g • m = m)
    (hnM : LocalDegreeTwoNormalized cM u κ)
    (hnN : LocalDegreeTwoNormalized cN u κ)
    (z : (contCochains R G M).X 2) (w : (contCochains R G M).X 0)
    (hz : ((contCochains R G M).d 2 3).hom z = 0) :
    cN (contCup β continuous_of_discreteTopology 2 0 2 rfl z w) =
      β (cM z) (evalZero R M w) := by
  rw [contCup_twenty_eq β hM]
  exact coefficientMap_coordinate cM cN hcM hkillN u κ hu hκ hua hκa hM hN hnM hnN
    (β.flip (evalZero R M w)) z hz

end ActualCup

section TraceNormalization

variable {R G N : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup N] [Module R N] [DistribMulAction G N] [SMulCommClass G R N]
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul G N]

/-- Kind: definition. The scaling of the original local trace against
 the positively oriented uniformizer cup in a scalar coefficient frame
 (tex 2762–2767, 4860–4863, 5035–5038). -/
def traceScale (τ : (contCochains R G N).X 2 →ₗ[R] R) (e : N ≃ₗ[R] R)
    (u κ : G → R) (hu : Continuous u) (hκ : Continuous κ) : R :=
  τ (characterProduct u κ hu hκ (e.symm 1))

/-- Kind: proved theorem. A single fundamental cup fixes the entire
 normalization of the scalar local trace (tex 2762–2767, 4860–4863). -/
theorem trace_characterProduct
    (τ : (contCochains R G N).X 2 →ₗ[R] R) (e : N ≃ₗ[R] R)
    (u κ : G → R) (hu : Continuous u) (hκ : Continuous κ) (m : N) :
    τ (characterProduct u κ hu hκ m) = traceScale τ e u κ hu hκ * e m := by
  have hm : m = e m • e.symm 1 := by
    apply e.injective
    rw [map_smul, e.apply_symm_apply, smul_eq_mul, mul_one]
  calc
    _ = τ (characterProduct u κ hu hκ (e m • e.symm 1)) :=
      congrArg (fun v => τ (characterProduct u κ hu hκ v)) hm
    _ = e m * τ (characterProduct u κ hu hκ (e.symm 1)) := by
      rw [characterProduct_smul, map_smul, smul_eq_mul]
    _ = traceScale τ e u κ hu hκ * e m := by rw [traceScale, mul_comm]

/-- Kind: proved theorem. Every boundary-killing local trace factors on
 actual two-cocycles through the normalized Brauer coordinate. No cup table
 is assumed (tex 2762–2767, 4860–4863, 5035–5038). -/
theorem trace_cycle_formula
    (τ : (contCochains R G N).X 2 →ₗ[R] R)
    (hτ : ∀ a, τ (((contCochains R G N).d 1 2).hom a) = 0)
    (cN : (contCochains R G N).X 2 →ₗ[R] N) (hcN : LocalDegreeTwoCoordinate cN)
    (e : N ≃ₗ[R] R) (u κ : G → R) (hu : Continuous u) (hκ : Continuous κ)
    (hua : ∀ g h, u (g * h) = u g + u h)
    (hκa : ∀ g h, κ (g * h) = κ g + κ h)
    (hN : ∀ (g : G) (m : N), g • m = m)
    (hnN : LocalDegreeTwoNormalized cN u κ)
    (z : (contCochains R G N).X 2)
    (hz : ((contCochains R G N).d 2 3).hom z = 0) :
    τ z = traceScale τ e u κ hu hκ * e (cN z) := by
  let z₀ := characterProduct u κ hu hκ (cN z)
  have hz₀ : ((contCochains R G N).d 2 3).hom z₀ = 0 :=
    characterProduct_cycle u κ hu hκ hN hua hκa _
  have hc₀ : cN z₀ = cN z := hnN _ _ (characterProduct_eval u κ hu hκ _)
  have hcycle : ((contCochains R G N).d 2 3).hom (z - z₀) = 0 := by
    rw [map_sub, hz, hz₀, sub_self]
  have hzero : cN (z - z₀) = 0 := by rw [map_sub, hc₀, sub_self]
  obtain ⟨a, ha⟩ := hcN.2.1 (z - z₀) hcycle hzero
  have hvalue := hτ a
  rw [ha, map_sub, trace_characterProduct] at hvalue
  exact sub_eq_zero.mp hvalue

/-- Kind: proved theorem. Surjectivity of the original local trace on
 two-cocycles makes its normalization a unit. This is an independent local
 invariant fact, not perfectness of the desired split pairing
 (tex 2762–2767, 4860–4863, 5035–5038). -/
theorem traceScale_isUnit
    (τ : (contCochains R G N).X 2 →ₗ[R] R)
    (hτ : ∀ a, τ (((contCochains R G N).d 1 2).hom a) = 0)
    (cN : (contCochains R G N).X 2 →ₗ[R] N) (hcN : LocalDegreeTwoCoordinate cN)
    (e : N ≃ₗ[R] R) (u κ : G → R) (hu : Continuous u) (hκ : Continuous κ)
    (hua : ∀ g h, u (g * h) = u g + u h)
    (hκa : ∀ g h, κ (g * h) = κ g + κ h)
    (hN : ∀ (g : G) (m : N), g • m = m)
    (hnN : LocalDegreeTwoNormalized cN u κ)
    (honto : ∀ r : R, ∃ z, ((contCochains R G N).d 2 3).hom z = 0 ∧ τ z = r) :
    IsUnit (traceScale τ e u κ hu hκ) := by
  obtain ⟨z, hz, ht⟩ := honto 1
  have h := trace_cycle_formula τ hτ cN hcN e u κ hu hκ hua hκa hN hnN z hz
  rw [ht] at h
  refine ⟨⟨traceScale τ e u κ hu hκ, e (cN z), h.symm, ?_⟩, rfl⟩
  rw [mul_comm]
  exact h.symm

end TraceNormalization

section CoefficientWeil

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

/-- Kind: definition. The determinant pairing over the finite coefficient
 ring, before taking the characteristic-zero fibre
 (tex 2762–2767, 2798–2805, 5035–5038). -/
def determinantForm : (Fin 2 → R) →ₗ[R] (Fin 2 → R) →ₗ[R] R :=
  LinearMap.mk₂ R (fun x y => x 0 * y 1 - x 1 * y 0)
    (fun _ _ _ => by simp only [Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

/-- Kind: proved theorem. Evaluation of the coefficient determinant
 pairing (tex 2762–2767, 2798–2805, 5035–5038). -/
theorem determinantForm_apply (x y : Fin 2 → R) :
    determinantForm x y = x 0 * y 1 - x 1 * y 0 := rfl

/-- Kind: definition. The coefficient Weil normalization in the prescribed
 rank-two frame (tex 2762–2767, 2798–2805, 5035–5038). -/
def weilScale (β : M →ₗ[R] M →ₗ[R] R) (e : M ≃ₗ[R] (Fin 2 → R)) : R :=
  β (e.symm (Pi.single 0 1)) (e.symm (Pi.single 1 1))

/-- Kind: proved theorem. Alternation and bilinearity of the actual
 coefficient Weil pairing determine its entire rank-two table from a
 single coefficient value (tex 2762–2767, 2798–2805, 5035–5038). -/
theorem coefficientWeil_coordinates (β : M →ₗ[R] M →ₗ[R] R)
    (e : M ≃ₗ[R] (Fin 2 → R)) (hAlt : ∀ m, β m m = 0) (x y : M) :
    β x y = weilScale β e * determinantForm (e x) (e y) := by
  let v₀ := e.symm (Pi.single 0 1)
  let v₁ := e.symm (Pi.single 1 1)
  have hswap : β v₁ v₀ = -β v₀ v₁ := by
    have h := hAlt (v₀ + v₁)
    simp only [map_add, LinearMap.add_apply, hAlt, zero_add, add_zero] at h
    calc
      _ = (β v₁ v₀ + β v₀ v₁) - β v₀ v₁ := by abel
      _ = -β v₀ v₁ := by rw [h, zero_sub]
  have hexp (m : M) : m = (e m) 0 • v₀ + (e m) 1 • v₁ := by
    apply e.injective
    dsimp only [v₀, v₁]
    simp only [map_add, map_smul, LinearEquiv.apply_symm_apply]
    funext j
    fin_cases j <;> simp
  conv_lhs => rw [hexp x, hexp y]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    hAlt, hswap, smul_eq_mul, mul_zero, zero_add, add_zero]
  change _ = β v₀ v₁ * ((e x) 0 * (e y) 1 - (e x) 1 * (e y) 0)
  ring

/-- Kind: proved theorem. Perfectness of the original coefficient Weil
 pairing makes its basis normalization a unit, over the finite ring itself
 (tex 2762–2767, 2798–2805, 5035–5038). -/
theorem weilScale_isUnit (β : M →ₗ[R] M →ₗ[R] R)
    (e : M ≃ₗ[R] (Fin 2 → R)) (hAlt : ∀ m, β m m = 0)
    (honto : Function.Surjective β) : IsUnit (weilScale β e) := by
  let f : M →ₗ[R] R := (LinearMap.proj 1).comp e.toLinearMap
  obtain ⟨x, hx⟩ := honto f
  have h : β x (e.symm (Pi.single 1 1)) = 1 := by
    have hv := LinearMap.congr_fun hx (e.symm (Pi.single 1 1))
    simpa [f, Pi.single_apply] using hv
  rw [coefficientWeil_coordinates β e hAlt, e.apply_symm_apply,
    determinantForm_apply] at h
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
    mul_one, mul_zero, sub_zero] at h
  refine ⟨⟨weilScale β e, (e x) 0, h, ?_⟩, rfl⟩
  rw [mul_comm]
  exact h

end CoefficientWeil

/-- Kind: definition of arithmetic and cochain data. The local coefficient
 modules, their normalized degree-two coordinates, the original Weil
 pairing and original scalar trace, and the local conjugation on characters
 are retained separately. No residue pairing identity is a field of this
 record (tex 2762–2767, 2798–2805, 3090–3096, 4859–4863, 5027–5042). -/
structure LocalArithmeticData (R : Type) [CommRing R] [TopologicalSpace R]
    [DiscreteTopology R] (n : ℕ) [NeZero n] [Algebra (ZMod n) R] where
  /-- Kind: group data, the actual local Galois group (tex 4859–4863). -/
  G : Type
  /-- Kind: group structure data (tex 4859–4863). -/
  [groupG : Group G]
  /-- Kind: topology data (tex 4859–4863). -/
  [topologyG : TopologicalSpace G]
  /-- Kind: topological group data (tex 4859–4863). -/
  [topologicalGroupG : IsTopologicalGroup G]
  /-- Kind: coefficient module data (tex 2762–2767, 4859–4863). -/
  M : Type
  /-- Kind: additive coefficient structure data (tex 2762–2767). -/
  [addM : AddCommGroup M]
  /-- Kind: coefficient module structure data (tex 2762–2767). -/
  [moduleM : Module R M]
  /-- Kind: Galois action data (tex 2762–2767, 4859–4863). -/
  [actionM : DistribMulAction G M]
  /-- Kind: scalar compatibility data (tex 2762–2767). -/
  [commM : SMulCommClass G R M]
  /-- Kind: coefficient topology data (tex 2762–2767). -/
  [topologyM : TopologicalSpace M]
  /-- Kind: discrete coefficient topology data (tex 2762–2767). -/
  [discreteM : DiscreteTopology M]
  /-- Kind: continuous Galois action data (tex 2762–2767). -/
  [continuousM : ContinuousSMul G M]
  /-- Kind: scalar twist coefficient data (tex 2762–2767). -/
  N : Type
  /-- Kind: additive scalar twist structure data (tex 2762–2767). -/
  [addN : AddCommGroup N]
  /-- Kind: scalar twist module structure data (tex 2762–2767). -/
  [moduleN : Module R N]
  /-- Kind: scalar twist Galois action data (tex 2762–2767). -/
  [actionN : DistribMulAction G N]
  /-- Kind: scalar twist compatibility data (tex 2762–2767). -/
  [commN : SMulCommClass G R N]
  /-- Kind: scalar twist topology data (tex 2762–2767). -/
  [topologyN : TopologicalSpace N]
  /-- Kind: discrete scalar twist topology data (tex 2762–2767). -/
  [discreteN : DiscreteTopology N]
  /-- Kind: continuous scalar twist action data (tex 2762–2767). -/
  [continuousN : ContinuousSMul G N]
  /-- Kind: prescribed coefficient basis data (tex 2762–2767, 5035–5038). -/
  eM : M ≃ₗ[R] (Fin 2 → R)
  /-- Kind: scalar twist coefficient frame data (tex 2762–2767). -/
  eN : N ≃ₗ[R] R
  /-- Kind: original coefficient Weil pairing data (tex 2798–2805). -/
  β : M →ₗ[R] M →ₗ[R] N
  /-- Kind: arithmetic input, alternation of the original Weil pairing
   (tex 2798–2805). -/
  alternating : ∀ m, β m m = 0
  /-- Kind: arithmetic input, perfectness of the original coefficient Weil
   pairing, before local cohomology (tex 2798–2805). -/
  perfect : Function.Bijective (β.compr₂ eN.toLinearMap)
  /-- Kind: arithmetic input, trivial derivative coefficient action
   (tex 3090–3096, 4859–4863). -/
  trivialM : ∀ (g : G) (m : M), g • m = m
  /-- Kind: arithmetic input, fixed roots in the scalar twist
   (tex 3090–3096, 4859–4863). -/
  trivialN : ∀ (g : G) (m : N), g • m = m
  /-- Kind: arithmetic Frobenius data (tex 5027–5032). -/
  frobenius : G
  /-- Kind: tame inertia data (tex 5027–5032). -/
  inertia : G
  /-- Kind: arithmetic unramified character data (tex 5027–5032). -/
  u : G → R
  /-- Kind: tame uniformizer character data (tex 5027–5032). -/
  κ : G → R
  /-- Kind: continuous character input (tex 5027–5032). -/
  continuousU : Continuous u
  /-- Kind: continuous character input (tex 5027–5032). -/
  continuousK : Continuous κ
  /-- Kind: additive character input (tex 5027–5032). -/
  additiveU : ∀ g h, u (g * h) = u g + u h
  /-- Kind: additive character input (tex 5027–5032). -/
  additiveK : ∀ g h, κ (g * h) = κ g + κ h
  /-- Kind: Frobenius normalization input (tex 5027–5032). -/
  u_frobenius : u frobenius = 1
  /-- Kind: inertia normalization input (tex 5027–5032). -/
  u_inertia : u inertia = 0
  /-- Kind: Frobenius normalization input (tex 5027–5032). -/
  κ_frobenius : κ frobenius = 0
  /-- Kind: inertia normalization input (tex 5027–5032). -/
  κ_inertia : κ inertia = 1
  /-- Kind: double-exponent unramified character data (tex 3090–3096). -/
  χu : G → ZMod (2 * n)
  /-- Kind: double-exponent uniformizer character data (tex 3090–3096). -/
  χκ : G → ZMod (2 * n)
  /-- Kind: continuous lift input (tex 3090–3096). -/
  continuousχu : Continuous χu
  /-- Kind: continuous lift input (tex 3090–3096). -/
  continuousχκ : Continuous χκ
  /-- Kind: additive lift input (tex 3090–3096). -/
  additiveχu : ∀ g h, χu (g * h) = χu g + χu h
  /-- Kind: additive lift input (tex 3090–3096). -/
  additiveχκ : ∀ g h, χκ (g * h) = χκ g + χκ h
  /-- Kind: exact character reduction input (tex 3090–3096). -/
  liftU : ∀ g, u g = algebraMap (ZMod n) R ((χu g).val : ZMod n)
  /-- Kind: exact character reduction input (tex 3090–3096). -/
  liftK : ∀ g, κ g = algebraMap (ZMod n) R ((χκ g).val : ZMod n)
  /-- Kind: normalized coefficient coordinate data (tex 4860–4863). -/
  cM : (contCochains R G M).X 2 →ₗ[R] M
  /-- Kind: normalized scalar twist coordinate data (tex 4860–4863). -/
  cN : (contCochains R G N).X 2 →ₗ[R] N
  /-- Kind: proved coordinate specification input (tex 4860–4863). -/
  coordinateM : LocalDegreeTwoCoordinate cM
  /-- Kind: proved coordinate specification input (tex 4860–4863). -/
  coordinateN : LocalDegreeTwoCoordinate cN
  /-- Kind: positive tame-symbol orientation input (tex 4860–4863, 5035–5038). -/
  normalizedM : LocalDegreeTwoNormalized cM u κ
  /-- Kind: positive tame-symbol orientation input (tex 4860–4863, 5035–5038). -/
  normalizedN : LocalDegreeTwoNormalized cN u κ
  /-- Kind: normalized cochain retraction data from the local model producer
   (tex 4385–4451, 4860–4863). -/
  model : ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace.OrientedLocalRetraction
    eM frobenius inertia cM
  /-- Kind: actual local representative pullback data (tex 5027–5032). -/
  θ : G →ₜ* G
  /-- Kind: coefficient conjugation data (tex 2798–2805, 5027–5032). -/
  j : M →ₗ[R] M
  /-- Kind: coefficient conjugation matrix data (tex 2798–2805, 5027–5032). -/
  J : Matrix (Fin 2) (Fin 2) R
  /-- Kind: coefficient basis identification input (tex 2798–2805, 5035–5038). -/
  conjugationCoordinates : ∀ m, eM (j m) = J *ᵥ eM m
  /-- Kind: inverse residue-size data for tame pullback (tex 5027–5032). -/
  tameScale : R
  /-- Kind: arithmetic input, Frobenius-coordinate pullback
   (tex 5027–5032). -/
  pullU : ∀ g, u (θ g) = u g
  /-- Kind: arithmetic input, tame-coordinate pullback
   (tex 5027–5032). -/
  pullK : ∀ g, κ (θ g) = tameScale * κ g
  /-- Kind: original scalar local trace data (tex 2762–2767, 4385–4388). -/
  τ : (contCochains R G N).X 2 →ₗ[R] R
  /-- Kind: original local trace boundary input (tex 2762–2767, 4385–4388). -/
  trace_kills : ∀ a, τ (((contCochains R G N).d 1 2).hom a) = 0
  /-- Kind: arithmetic input, surjectivity of the original local invariant
   on two-cocycles (tex 2762–2767, 4860–4863). -/
  trace_onto : ∀ r : R, ∃ z, ((contCochains R G N).d 2 3).hom z = 0 ∧ τ z = r

attribute [instance] LocalArithmeticData.groupG LocalArithmeticData.topologyG
  LocalArithmeticData.topologicalGroupG LocalArithmeticData.addM LocalArithmeticData.moduleM
  LocalArithmeticData.actionM LocalArithmeticData.commM LocalArithmeticData.topologyM
  LocalArithmeticData.discreteM LocalArithmeticData.continuousM LocalArithmeticData.addN
  LocalArithmeticData.moduleN LocalArithmeticData.actionN LocalArithmeticData.commN
  LocalArithmeticData.topologyN LocalArithmeticData.discreteN LocalArithmeticData.continuousN

section LocalArithmetic

variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {n : ℕ} [NeZero n] [Algebra (ZMod n) R] (X : LocalArithmeticData R n)

/-- Kind: definition. The original Weil pairing read in its scalar frame
 (tex 2798–2805, 5035–5038). -/
def LocalArithmeticData.scalarWeil : X.M →ₗ[R] X.M →ₗ[R] R :=
  X.β.compr₂ X.eN.toLinearMap

/-- Kind: definition. The retained scalar multiplying the determinant
 pairing, including the original local trace scaling
 (tex 2798–2805, 5035–5038). -/
def LocalArithmeticData.ε : R :=
  traceScale X.τ X.eN X.u X.κ X.continuousU X.continuousK *
    weilScale X.scalarWeil X.eM

/-- Kind: proved theorem. Both factors in the actual coefficient and trace
 normalization are units at the finite stage (tex 2798–2805, 5035–5038). -/
theorem LocalArithmeticData.ε_isUnit : IsUnit X.ε := by
  have hAlt : ∀ m, X.scalarWeil m m = 0 := by
    intro m
    change X.eN (X.β m m) = 0
    rw [X.alternating, map_zero]
  exact (traceScale_isUnit X.τ X.trace_kills X.cN X.coordinateN X.eN X.u X.κ
    X.continuousU X.continuousK X.additiveU X.additiveK X.trivialN X.normalizedN
    X.trace_onto).mul (weilScale_isUnit X.scalarWeil X.eM hAlt X.perfect.2)

/-- Kind: definition. The actual conjugation pullback on continuous
 cochains, with its coefficient action (tex 2798–2805, 5027–5032). -/
def LocalArithmeticData.transportMap : contCochains R X.G X.M ⟶ contCochains R X.G X.M :=
  contCochainsMap X.θ X.j continuous_of_discreteTopology
    (fun g m => by rw [X.trivialM, X.trivialM])

/-- Kind: definition. A component of the actual conjugation cochain map
 (tex 2798–2805, 5027–5032). -/
def LocalArithmeticData.transport (p : ℕ) :
    (contCochains R X.G X.M).X p →ₗ[R] (contCochains R X.G X.M).X p :=
  (X.transportMap.f p).hom

/-- Kind: proved theorem. The actual conjugation cochain map has the
 prescribed pullback formula on one-cochains (tex 2798–2805, 5027–5032). -/
theorem LocalArithmeticData.transport_one (a : (contCochains R X.G X.M).X 1) (g : X.G) :
    evalOne R X.M g (X.transport 1 a) = X.j (evalOne R X.M (X.θ g) a) := rfl

/-- Kind: proved theorem. The actual conjugation cochain map acts on
 zero-cochains only through the coefficient conjugation
 (tex 2798–2805, 4860–4863). -/
theorem LocalArithmeticData.transport_zero (a : (contCochains R X.G X.M).X 0) :
    evalZero R X.M (X.transport 0 a) = X.j (evalZero R X.M a) := by
  change X.j (contFun a (X.θ ∘ Fin.elim0)) = X.j (contFun a Fin.elim0)
  rw [Subsingleton.elim (X.θ ∘ Fin.elim0) Fin.elim0]

/-- Kind: proved theorem. Conjugation preserves actual one-cocycles
 (tex 2798–2805, 5027–5032). -/
theorem LocalArithmeticData.transport_cycle_one
    (a : (contCochains R X.G X.M).X 1)
    (ha : ((contCochains R X.G X.M).d 1 2).hom a = 0) :
    ((contCochains R X.G X.M).d 1 2).hom (X.transport 1 a) = 0 := by
  have h := congrArg (fun f => ModuleCat.Hom.hom f a) (X.transportMap.comm 1 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ha, map_zero] at h
  exact h

/-- Kind: definition. The actual degree-zero representative of a split
 coordinate (tex 4860–4863). -/
def LocalArithmeticData.localZero (x : Fin 2 → R) : (contCochains R X.G X.M).X 0 :=
  X.model.retract.i.f 0 0 rfl x

/-- Kind: definition. The actual degree-one representative of a split
 finite/singular coordinate (tex 4860–4863). -/
def LocalArithmeticData.localOne (x : (Fin 2 → R) × (Fin 2 → R)) :
    (contCochains R X.G X.M).X 1 :=
  X.model.retract.i.f 1 1 rfl x

/-- Kind: definition. The actual degree-two representative of a split
 normalized coordinate (tex 4860–4863). -/
def LocalArithmeticData.localTwo (x : Fin 2 → R) : (contCochains R X.G X.M).X 2 :=
  X.model.retract.i.f 2 2 rfl x

/-- Kind: proved theorem. The model inclusion gives actual one-cocycles
 (tex 4385–4451, 4860–4863). -/
theorem LocalArithmeticData.localOne_cycle (x : (Fin 2 → R) × (Fin 2 → R)) :
    ((contCochains R X.G X.M).d 1 2).hom (X.localOne x) = 0 := by
  have h := X.model.retract.i.comm 1 2 1 2 rfl rfl rfl rfl x
  change X.model.retract.i.f 2 2 rfl 0 =
    ((contCochains R X.G X.M).d 1 2).hom (X.localOne x) at h
  rw [map_zero] at h
  exact h.symm

/-- Kind: proved theorem. The model inclusion gives actual two-cocycles
 (tex 4385–4451, 4860–4863). -/
theorem LocalArithmeticData.localTwo_cycle (x : Fin 2 → R) :
    ((contCochains R X.G X.M).d 2 3).hom (X.localTwo x) = 0 := by
  have h := X.model.retract.i.comm 2 3 2 3 rfl rfl rfl rfl x
  change X.model.retract.i.f 3 3 rfl 0 =
    ((contCochains R X.G X.M).d 2 3).hom (X.localTwo x) at h
  rw [map_zero] at h
  exact h.symm

/-- Kind: proved theorem. The degree-zero representative has exactly the
 prescribed coefficient value (tex 4860–4863). -/
theorem LocalArithmeticData.localZero_value (x : Fin 2 → R) :
    evalZero R X.M (X.localZero x) = X.eM.symm x := by
  have h := X.model.retract.p_i 0 x
  rw [X.model.projection] at h
  change X.eM (evalZero R X.M (X.localZero x)) = x at h
  apply X.eM.injective
  rw [h, X.eM.apply_symm_apply]

/-- Kind: proved theorem. The degree-two representative has exactly the
 prescribed normalized coordinate (tex 4860–4863). -/
theorem LocalArithmeticData.localTwo_value (x : Fin 2 → R) :
    X.cM (X.localTwo x) = X.eM.symm x := by
  have h := X.model.retract.p_i 2 x
  rw [X.model.projection] at h
  change X.eM (X.cM (X.localTwo x)) = x at h
  apply X.eM.injective
  rw [h, X.eM.apply_symm_apply]

/-- Kind: proved theorem. The normalized retraction makes every degree-one
 representative the actual additive tame-character cocycle. This is a
 cochain formula, not a pairing-table hypothesis
 (tex 4860–4863, 5027–5032). -/
theorem LocalArithmeticData.localOne_value (x : (Fin 2 → R) × (Fin 2 → R)) (g : X.G) :
    evalOne R X.M g (X.localOne x) =
      X.u g • X.eM.symm x.1 + X.κ g • X.eM.symm x.2 := by
  let w : (contCochains R X.G X.M).X 1 :=
    mkCochain1 (fun h => X.u h • X.eM.symm x.1 + X.κ h • X.eM.symm x.2)
      ((continuous_of_discreteTopology : Continuous (fun p : R × R =>
        p.1 • X.eM.symm x.1 + p.2 • X.eM.symm x.2)).comp
          (X.continuousU.prodMk X.continuousK))
  have hw : ((contCochains R X.G X.M).d 1 2).hom w = 0 := by
    apply contCochains_ext
    intro v
    have hv : v = ![v 0, v 1] := by funext j; fin_cases j <;> rfl
    rw [hv, contFun_d12, X.trivialM]
    change (X.u (v 1) • X.eM.symm x.1 + X.κ (v 1) • X.eM.symm x.2) -
      (X.u (v 0 * v 1) • X.eM.symm x.1 + X.κ (v 0 * v 1) • X.eM.symm x.2) +
      (X.u (v 0) • X.eM.symm x.1 + X.κ (v 0) • X.eM.symm x.2) = 0
    rw [X.additiveU, X.additiveK]
    module
  let p₁ : (contCochains R X.G X.M).X 1 →ₗ[R]
      (Fin 2 → R) × (Fin 2 → R) := X.model.retract.p.f 1 1 rfl
  let i₁ : ((Fin 2 → R) × (Fin 2 → R)) →ₗ[R]
      (contCochains R X.G X.M).X 1 := X.model.retract.i.f 1 1 rfl
  let h₁ : (contCochains R X.G X.M).X 1 →ₗ[R]
      (contCochains R X.G X.M).X 0 := X.model.retract.h 1 0 (by omega)
  let h₂ : (contCochains R X.G X.M).X 2 →ₗ[R]
      (contCochains R X.G X.M).X 1 := X.model.retract.h 2 1 rfl
  have hpi : p₁ (i₁ x) = x := X.model.retract.p_i 1 x
  have hpw : p₁ w = x := by
    change X.model.retract.p.f 1 1 rfl w = x
    rw [X.model.projection]
    change (X.eM (X.u X.frobenius • X.eM.symm x.1 +
      X.κ X.frobenius • X.eM.symm x.2),
      X.eM (X.u X.inertia • X.eM.symm x.1 + X.κ X.inertia • X.eM.symm x.2)) = x
    rw [X.u_frobenius, X.κ_frobenius, X.u_inertia, X.κ_inertia,
      one_smul, zero_smul, zero_smul, one_smul, add_zero, zero_add,
      X.eM.apply_symm_apply, X.eM.apply_symm_apply]
  have hp : p₁ (i₁ x - w) = 0 := by rw [map_sub, hpi, hpw, sub_self]
  have hi : ((contCochains R X.G X.M).d 1 2).hom (i₁ x) = 0 := X.localOne_cycle x
  have hc : ((contCochains R X.G X.M).d 1 2).hom (i₁ x - w) = 0 := by
    rw [map_sub, hi, hw, sub_self]
  have h := X.model.retract.homotopy 1 (i₁ x - w)
  change i₁ x - w - i₁ (p₁ (i₁ x - w)) =
    ((contCochains R X.G X.M).d 0 1).hom (h₁ (i₁ x - w)) +
      h₂ (((contCochains R X.G X.M).d 1 2).hom (i₁ x - w)) at h
  rw [hp, map_zero, sub_zero, hc, map_zero, add_zero] at h
  have hd : ((contCochains R X.G X.M).d 0 1).hom (h₁ (i₁ x - w)) = 0 :=
    ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace.localZero_d_zero X.trivialM _
  rw [hd] at h
  have he : X.localOne x = w := sub_eq_zero.mp h
  rw [he]
  rfl

/-- Kind: proved theorem. The conjugated degree-one representative has
 its finite coefficient acted on by the Tate conjugation and its singular
 coefficient multiplied by the actual tame pullback scale
 (tex 2798–2805, 5027–5032). -/
theorem LocalArithmeticData.transportedOne_value
    (y : (Fin 2 → R) × (Fin 2 → R)) (g : X.G) :
    evalOne R X.M g (X.transport 1 (X.localOne y)) =
      X.u g • X.j (X.eM.symm y.1) +
        X.κ g • (X.tameScale • X.j (X.eM.symm y.2)) := by
  rw [X.transport_one, X.localOne_value, X.pullU, X.pullK,
    map_add, map_smul, map_smul]
  module

/-- Kind: proved theorem. The actual conjugated coefficient Weil pairing
 is the determinant cross pairing in the prescribed Tate frame
 (tex 2798–2805, 5035–5038). -/
theorem LocalArithmeticData.scalarWeil_conj (x y : X.M) :
    X.eN (X.β x (X.j y)) =
      weilScale X.scalarWeil X.eM * determinantForm (X.eM x) (X.J *ᵥ X.eM y) := by
  have hAlt : ∀ m, X.scalarWeil m m = 0 := by
    intro m
    change X.eN (X.β m m) = 0
    rw [X.alternating, map_zero]
  change X.scalarWeil x (X.j y) = _
  rw [coefficientWeil_coordinates X.scalarWeil X.eM hAlt, X.conjugationCoordinates]

/-- Kind: definition. The trace of the actual transported local cup of
 the two degree-one representatives (tex 2798–2805, 4860–4863, 5035–5042). -/
def LocalArithmeticData.cup11 (x y : (Fin 2 → R) × (Fin 2 → R)) : R :=
  X.τ (contCup X.β continuous_of_discreteTopology 1 1 2 rfl
    (X.localOne x) (X.transport 1 (X.localOne y)))

/-- Kind: definition. The trace of the actual transported local
 degree-two/degree-zero cup (tex 2798–2805, 4860–4863). -/
def LocalArithmeticData.cup20 (x y : Fin 2 → R) : R :=
  X.τ (contCup X.β continuous_of_discreteTopology 2 0 2 rfl
    (X.localTwo x) (X.transport 0 (X.localZero y)))

/-- Kind: proved theorem. The actual local cup and its original scalar
 trace have the retained tame-coordinate table. The square terms vanish
 by double-exponent lifts and the reversed mixed term has negative
 orientation (tex 3090–3096, 4860–4863, 5035–5042). -/
theorem LocalArithmeticData.cup11_formula (x y : (Fin 2 → R) × (Fin 2 → R)) :
    X.cup11 x y = X.ε *
      (X.tameScale * determinantForm x.1 (X.J *ᵥ y.2) -
        determinantForm x.2 (X.J *ᵥ y.1)) := by
  have hβ : ∀ (g : X.G) (a b : X.M),
      X.β (g • a) (g • b) = g • X.β a b := by
    intro g a b
    rw [X.trivialM, X.trivialM, X.trivialN]
  have hcycle := contCup_cycle X.β hβ (X.localOne x) (X.transport 1 (X.localOne y))
    (X.localOne_cycle x) (X.transport_cycle_one (X.localOne y) (X.localOne_cycle y))
  unfold LocalArithmeticData.cup11
  rw [trace_cycle_formula X.τ X.trace_kills X.cN X.coordinateN X.eN X.u X.κ
    X.continuousU X.continuousK X.additiveU X.additiveK X.trivialN X.normalizedN _ hcycle]
  rw [contCup_normalized_formula X.β n X.cN X.coordinateN.1 X.u X.κ
    X.continuousU X.continuousK X.additiveU X.additiveK X.χu X.χκ
    X.continuousχu X.continuousχκ X.additiveχu X.additiveχκ X.liftU X.liftK
    X.trivialM X.trivialN X.normalizedN (X.localOne x) (X.transport 1 (X.localOne y))
    (X.eM.symm x.1) (X.eM.symm x.2) (X.j (X.eM.symm y.1))
    (X.tameScale • X.j (X.eM.symm y.2)) (X.localOne_value x) (X.transportedOne_value y)]
  rw [map_sub, map_smul, map_smul, X.scalarWeil_conj, X.scalarWeil_conj,
    X.eM.apply_symm_apply, X.eM.apply_symm_apply,
    X.eM.apply_symm_apply, X.eM.apply_symm_apply]
  simp only [smul_eq_mul]
  unfold LocalArithmeticData.ε
  ring

/-- Kind: proved theorem. The actual degree-two/degree-zero local cup is
 the conjugated coefficient Weil pairing read through the normalized
 coordinate and the original trace (tex 2798–2805, 4860–4863). -/
theorem LocalArithmeticData.cup20_formula (x y : Fin 2 → R) :
    X.cup20 x y = X.ε * determinantForm x (X.J *ᵥ y) := by
  let z := X.localTwo x
  let w := X.transport 0 (X.localZero y)
  have hcycle : ((contCochains R X.G X.N).d 2 3).hom
      (contCup X.β continuous_of_discreteTopology 2 0 2 rfl z w) = 0 := by
    rw [contCup_twenty_eq X.β X.trivialM,
      ← coefficientMap_d23 _ X.trivialM X.trivialN, X.localTwo_cycle, map_zero]
  unfold LocalArithmeticData.cup20
  rw [trace_cycle_formula X.τ X.trace_kills X.cN X.coordinateN X.eN X.u X.κ
    X.continuousU X.continuousK X.additiveU X.additiveK X.trivialN X.normalizedN _ hcycle]
  rw [contCup_twenty_coordinate X.β X.cM X.cN X.coordinateM X.coordinateN.1 X.u X.κ
    X.continuousU X.continuousK X.additiveU X.additiveK X.trivialM X.trivialN
    X.normalizedM X.normalizedN _ _ (X.localTwo_cycle x),
    X.localTwo_value, X.transport_zero, X.localZero_value, X.scalarWeil_conj,
    X.eM.apply_symm_apply, X.eM.apply_symm_apply]
  unfold LocalArithmeticData.ε
  ring

end LocalArithmetic

section MatrixForms

open ZInQ.Manuscript.RC.FibreDuality

variable {R S : Type} [CommRing R] [CommRing S]

/-- Kind: definition. The transported coefficient cross form over the
 finite ring (tex 2798–2805, 5035–5038). -/
def crossForm (ε : R) (J : Matrix (Fin 2) (Fin 2) R) :
    (Fin 2 → R) →ₗ[R] (Fin 2 → R) →ₗ[R] R :=
  ε • determinantForm.compl₂ J.mulVecLin

/-- Kind: proved theorem. The cross form has the actual determinant
 expression (tex 2798–2805, 5035–5038). -/
theorem crossForm_apply (ε : R) (J : Matrix (Fin 2) (Fin 2) R) (x y : Fin 2 → R) :
    crossForm ε J x y = ε * determinantForm x (J *ᵥ y) := by
  simp [crossForm]

/-- Kind: definition. The degree-one tame cup form, with the original
 inverse residue-size scale retained (tex 5027–5042). -/
def cupForm11 (ε s : R) (J : Matrix (Fin 2) (Fin 2) R) :
    ((Fin 2 → R) × (Fin 2 → R)) →ₗ[R] ((Fin 2 → R) × (Fin 2 → R)) →ₗ[R] R :=
  s • (crossForm ε J).compl₁₂ (LinearMap.fst R _ _) (LinearMap.snd R _ _) -
    (crossForm ε J).compl₁₂ (LinearMap.snd R _ _) (LinearMap.fst R _ _)

/-- Kind: proved theorem. Evaluation of the retained degree-one tame cup
 form (tex 5027–5042). -/
theorem cupForm11_apply (ε s : R) (J : Matrix (Fin 2) (Fin 2) R)
    (x y : (Fin 2 → R) × (Fin 2 → R)) :
    cupForm11 ε s J x y = ε *
      (s * determinantForm x.1 (J *ᵥ y.2) - determinantForm x.2 (J *ᵥ y.1)) := by
  simp only [cupForm11, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.compl₁₂_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    crossForm_apply, smul_eq_mul]
  ring

/-- Kind: definition. The standard basis of the finite and singular
 coordinate planes (tex 4860–4863). -/
def splitBasisOne (R : Type) [CommRing R] :
    (Fin 2 ⊕ Fin 2) → (Fin 2 → R) × (Fin 2 → R)
  | Sum.inl i => (Pi.single i 1, 0)
  | Sum.inr i => (0, Pi.single i 1)

/-- Kind: proved theorem. The split-plane basis is exactly the basis of
 the existing local coordinate equivalence (tex 4860–4863). -/
theorem lCoordR_one_single (a : Fin 2 ⊕ Fin 2) :
    (lCoordR R 1).symm (Pi.single a 1) = splitBasisOne R a := by
  cases a with
  | inl i =>
    apply Prod.ext
    · funext j
      by_cases h : j = i
      · subst j
        simp [lCoordR, LinearEquiv.sumArrowLequivProdArrow, splitBasisOne]
      · have hs : (Sum.inl j : Fin 2 ⊕ Fin 2) ≠ Sum.inl i :=
          fun he => h (Sum.inl.inj he)
        simp [lCoordR, LinearEquiv.sumArrowLequivProdArrow, splitBasisOne, h, hs]
    · funext j
      simp [lCoordR, LinearEquiv.sumArrowLequivProdArrow, splitBasisOne]
  | inr i =>
    apply Prod.ext
    · funext j
      simp [lCoordR, LinearEquiv.sumArrowLequivProdArrow, splitBasisOne]
    · funext j
      by_cases h : j = i
      · subst j
        simp [lCoordR, LinearEquiv.sumArrowLequivProdArrow, splitBasisOne]
      · have hs : (Sum.inr j : Fin 2 ⊕ Fin 2) ≠ Sum.inr i :=
          fun he => h (Sum.inr.inj he)
        simp [lCoordR, LinearEquiv.sumArrowLequivProdArrow, splitBasisOne, h, hs]

/-- Kind: definition. The actual degree-one tame cup matrix at finite
 precision (tex 4385–4451, 4860–4863, 5035–5042). -/
def cupMatrix11 (ε s : R) (J : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  Matrix.of fun a b => match a, b with
    | Sum.inl _, Sum.inl _ => 0
    | Sum.inl i, Sum.inr j => s * crossForm ε J (Pi.single i 1) (Pi.single j 1)
    | Sum.inr i, Sum.inl j => -crossForm ε J (Pi.single i 1) (Pi.single j 1)
    | Sum.inr _, Sum.inr _ => 0

/-- Kind: definition. The actual degree-two/degree-zero cup matrix at
 finite precision (tex 4385–4451, 4860–4863). -/
def cupMatrix20 (ε : R) (J : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 2) (Fin 2) R :=
  Matrix.of fun a b => crossForm ε J (Pi.single a 1) (Pi.single b 1)

/-- Kind: proved theorem. The degree-one matrix is the matrix of the
 proved arithmetic tame cup form (tex 4860–4863, 5035–5042). -/
theorem cupMatrix11_basis (ε s : R) (J : Matrix (Fin 2) (Fin 2) R)
    (a b : Fin 2 ⊕ Fin 2) :
    cupMatrix11 ε s J a b = cupForm11 ε s J
      ((lCoordR R 1).symm (Pi.single a 1))
      ((lCoordR R 1).symm (Pi.single b 1)) := by
  rw [lCoordR_one_single, lCoordR_one_single]
  cases a <;> cases b <;> simp [cupMatrix11, cupForm11, splitBasisOne]

/-- Kind: proved theorem. A coefficient homomorphism fixes the standard
 coordinate basis (tex 4385–4451, 4860–4863). -/
theorem map_single_one (f : R →+* S) (i : Fin 2) :
    (fun j : Fin 2 => f ((Pi.single i (1 : R) : Fin 2 → R) j)) =
      (Pi.single i (1 : S) : Fin 2 → S) := by
  funext j
  by_cases h : j = i <;> simp [h]

/-- Kind: proved theorem. Coefficient change preserves the original
 determinant cross form (tex 4385–4451, 5035–5042). -/
theorem map_crossForm (f : R →+* S) (ε : R) (J : Matrix (Fin 2) (Fin 2) R)
    (x y : Fin 2 → R) :
    f (crossForm ε J x y) = crossForm (f ε) (J.map f)
      (fun j => f (x j)) (fun j => f (y j)) := by
  simp [crossForm_apply, determinantForm_apply, map_add, map_sub, map_mul]

/-- Kind: proved theorem. The degree-one cup matrix respects coefficient
 change, as a finite polynomial identity (tex 4385–4451, 5035–5042). -/
theorem map_cupMatrix11 (f : R →+* S) (ε s : R) (J : Matrix (Fin 2) (Fin 2) R) :
    (cupMatrix11 ε s J).map f = cupMatrix11 (f ε) (f s) (J.map f) := by
  ext a b
  cases a <;> cases b <;>
    simp [cupMatrix11, map_crossForm, map_single_one, map_mul, map_neg]

/-- Kind: proved theorem. The degree-two/degree-zero cup matrix respects
 coefficient change (tex 4385–4451, 4860–4863). -/
theorem map_cupMatrix20 (f : R →+* S) (ε : R) (J : Matrix (Fin 2) (Fin 2) R) :
    (cupMatrix20 ε J).map f = cupMatrix20 (f ε) (J.map f) := by
  ext a b
  simp [cupMatrix20, map_crossForm, map_single_one]

end MatrixForms

section LimitForms

open ZInQ.Manuscript.RC.Limits

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R]

/-- Kind: proved theorem. The actual degree-one cup matrix survives the
 retained inner limit entry by entry (tex 4385–4451, 5035–5042). -/
theorem ulim_cupMatrix11 (U : Ultrafilter ℕ) (ε s : ℕ → R)
    (J : Matrix (Fin 2) (Fin 2) R) :
    ulimMat U (fun i => cupMatrix11 (ε i) (s i) J) =
      cupMatrix11 (ulim U ε) (ulim U s) J := by
  ext a b
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      change ulim U (fun _ => (0 : R)) = 0
      exact ulim_zero U
    | inr b =>
      change ulim U (fun i => s i * (ε i *
          determinantForm (Pi.single a 1) (J *ᵥ Pi.single b 1))) =
        ulim U s * (ulim U ε * determinantForm (Pi.single a 1) (J *ᵥ Pi.single b 1))
      rw [ulim_mul, ulim_mul, ulim_const]
  | inr a =>
    cases b with
    | inl b =>
      change ulim U (fun i => -(ε i *
          determinantForm (Pi.single a 1) (J *ᵥ Pi.single b 1))) =
        -(ulim U ε * determinantForm (Pi.single a 1) (J *ᵥ Pi.single b 1))
      rw [ulim_neg, ulim_mul, ulim_const]
    | inr b =>
      change ulim U (fun _ => (0 : R)) = 0
      exact ulim_zero U

/-- Kind: proved theorem. The actual degree-two/degree-zero cup matrix
 survives the retained inner limit (tex 4385–4451, 4860–4863). -/
theorem ulim_cupMatrix20 (U : Ultrafilter ℕ) (ε : ℕ → R)
    (J : Matrix (Fin 2) (Fin 2) R) :
    ulimMat U (fun i => cupMatrix20 (ε i) J) = cupMatrix20 (ulim U ε) J := by
  ext a b
  change ulim U (fun i => ε i * determinantForm (Pi.single a 1) (J *ᵥ Pi.single b 1)) =
    ulim U ε * determinantForm (Pi.single a 1) (J *ᵥ Pi.single b 1)
  rw [ulim_mul, ulim_const]

/-- Kind: proved theorem. The retained scalar normalization has a unit
 inner limit, using the retained inverses rather than an unsupported
 inference from nonzero finite values (tex 4385–4451, 5035–5038). -/
theorem ulim_units_isUnit (U : Ultrafilter ℕ) (ε : ℕ → Rˣ) :
    IsUnit (ulim U (fun i => (ε i : R))) := by
  let a := ulim U (fun i => (ε i : R))
  let b := ulim U (fun i => (ε i).inv)
  have hab : a * b = 1 := by
    change ulim U (fun i => (ε i : R)) * ulim U (fun i => (ε i).inv) = 1
    rw [← ulim_mul]
    have he : (fun i => (ε i : R) * (ε i).inv) = fun _ => (1 : R) := by
      funext i
      exact (ε i).val_inv
    rw [he, ulim_one]
  refine ⟨⟨a, b, hab, ?_⟩, rfl⟩
  rw [mul_comm]
  exact hab

end LimitForms

section FibreForms

open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.Uniform

variable {k : Type} [Field k]

/-- Kind: proved theorem. The local pairing of the retained degree-one
 cup matrix is the proved arithmetic form (tex 4860–4863, 5035–5042). -/
theorem localPairing_b11_of_cupMatrix
    (M : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) k) (ε s : k)
    (J : Matrix (Fin 2) (Fin 2) k) (hM : M 1 1 = cupMatrix11 ε s J)
    (x y : (Fin 2 → k) × (Fin 2 → k)) :
    (localPairingOfMat M).b11 x y = cupForm11 ε s J x y := by
  change lCoord k 1 x ⬝ᵥ (M 1 1 *ᵥ lCoord k 1 y) = _
  rw [hM]
  have h := bilin_eq_dot_coords (cupForm11 ε s J) (lCoord k 1) (lCoord k 1) x y
  have he : Matrix.of (fun a b => cupForm11 ε s J
      ((lCoord k 1).symm (Pi.single a 1)) ((lCoord k 1).symm (Pi.single b 1))) =
      cupMatrix11 ε s J := by
    ext a b
    exact (cupMatrix11_basis ε s J a b).symm
  have ht := congrArg (fun A : Matrix (lIdx 1) (lIdx 1) k =>
    lCoord k 1 x ⬝ᵥ (A *ᵥ lCoord k 1 y)) he
  exact ht.symm.trans h.symm

/-- Kind: proved theorem. The local degree-two/degree-zero pairing of the
 retained cup matrix is the actual coefficient cross form
 (tex 4860–4863, 5035–5038). -/
theorem localPairing_b20_of_cupMatrix
    (M : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) k) (ε : k)
    (J : Matrix (Fin 2) (Fin 2) k) (hM : M 2 0 = cupMatrix20 ε J)
    (x y : Fin 2 → k) :
    (localPairingOfMat M).b20 x y = crossForm ε J x y := by
  change x ⬝ᵥ (M 2 0 *ᵥ y) = _
  rw [hM]
  exact (bilin_eq_dot_coords (crossForm ε J) (LinearEquiv.refl k (Fin 2 → k))
    (LinearEquiv.refl k (Fin 2 → k)) x y).symm

/-- Kind: proved theorem. Actual conjugation makes the determinant cross
 pairing symmetric, with no residual alternatingness inference
 (tex 2798–2805, 5035–5043). -/
theorem determinantForm_conj_symm (J : Matrix (Fin 2) (Fin 2) k)
    (hJ : J * J = 1) (hdet : J.det = -1) (x y : Fin 2 → k) :
    determinantForm x (J *ᵥ y) = determinantForm y (J *ᵥ x) := by
  change weil x (J *ᵥ y) = weil y (J *ᵥ x)
  rw [weil_swap (J *ᵥ y) x, weil_J_left hJ hdet]
  ring

/-- Kind: proved theorem. The arithmetic tame cup form is exactly the
 negative transposed switch form, with the sign supplied by the actual
 tame pullback scale (tex 5027–5043). -/
theorem cupForm11_eq_switch (ε s : k) (J : Matrix (Fin 2) (Fin 2) k)
    (hJ : J * J = 1) (hdet : J.det = -1)
    (x y : (Fin 2 → k) × (Fin 2 → k)) :
    cupForm11 ε s J x y = -(switchPairing ε (-s) J y x) := by
  rw [cupForm11_apply, planePairing_apply, crossPairing_apply, crossPairing_apply]
  change ε * (s * determinantForm x.1 (J *ᵥ y.2) -
      determinantForm x.2 (J *ᵥ y.1)) =
    -(ε * determinantForm y.1 (J *ᵥ x.2) + (-s) *
      (ε * determinantForm x.1 (J *ᵥ y.2)))
  rw [determinantForm_conj_symm J hJ hdet x.2 y.1]
  ring

/-- Kind: proved theorem. The retained degree-two/degree-zero cup is
 perfect from the original trace unit and the actual Tate involution.
 No perfectness of the desired local pairing is assumed
 (tex 2798–2805, 4860–4863). -/
theorem localPairing_b20_bijective_of_cupMatrix
    (M : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) k) (ε : k)
    (J : Matrix (Fin 2) (Fin 2) k) (hM : M 2 0 = cupMatrix20 ε J)
    (hε : ε ≠ 0) (hJ : J * J = 1) :
    Function.Bijective (localPairingOfMat M).b20 := by
  have he : (localPairingOfMat M).b20 = crossPairing ε J := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    rw [localPairing_b20_of_cupMatrix M ε J hM]
    rfl
  rw [he]
  exact (crossPairing_isPerfPair hε hJ).bijective_left

end FibreForms

section RetainedArithmetic

open Filter NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.Limits hiding Lambda
open ZInQ.Manuscript.RC.Uniform (Lambda switchPairing)
open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Contrib.RC53Assist.InnerLimit
open ZInQ.Manuscript.RC.CoefModules (ActualConj)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open scoped PowerSeries.WithPiTopology

/-- Kind: local instance. The arithmetic coefficient exponent is nonzero
 at every stage (tex 2723–2727, 4860–4863). -/
local instance stageExponent_neZero (i : ℕ) : NeZero (2 ^ i) :=
  ⟨pow_ne_zero i two_ne_zero⟩

/-- Kind: local instance. The finite coefficient stage has its discrete
 topology (tex 2723–2727, 4385–4451). -/
local instance stageScalar_topology (i : ℕ) : TopologicalSpace (StageA i) := ⊥

/-- Kind: local instance. The coefficient topology is discrete
 (tex 2723–2727, 4385–4451). -/
local instance stageScalar_discrete (i : ℕ) : DiscreteTopology (StageA i) := ⟨rfl⟩

/-- Kind: definition. The positive coefficient-stage arithmetic data use
 the actual exponent and exactly the ring of the retained-stage consumer
 (tex 2723–2727, 4385–4451, 4860–4863). -/
def StageArithmeticData (i : ℕ) [NeZero i] : Type 1 :=
  LocalArithmeticData (StageA i) (2 ^ i)

/-- Kind: definition of retained arithmetic realization data. The lifted
 scalars come from the original trace and coefficient Weil basis. The
 local matrices lift the actual transported cochain cups, not a prescribed
 bilinear table. The two realization fields are the existing local matrix
 lift and cochain trace transport specialized to bidegrees one/one and
 two/zero (tex 4385–4451, 4860–4863, 5027–5042). -/
structure RetainedLocalArithmetic (U : Ultrafilter ℕ)
    (C : ComplexStages (R := Lambda) stageIdeal U) (D : RetainedLimitPairingStages U C) where
  /-- Kind: arithmetic and cochain data at positive stages
   (tex 4385–4451, 4860–4863). -/
  stage : ∀ i, ∀ [NeZero i], StageArithmeticData i
  /-- Kind: unit lift data for the original trace/Weil normalization
   (tex 4385–4451, 5035–5038). -/
  ε : ℕ → Lambdaˣ
  /-- Kind: lift data for the actual tame pullback scale
   (tex 5027–5032). -/
  s : ℕ → Lambda
  /-- Kind: actual integral Tate conjugation matrix data
   (tex 2798–2805, 3090–3096). -/
  J : Matrix (Fin 2) (Fin 2) Lambda
  /-- Kind: arithmetic Tate involution input (tex 2798–2805, 3090–3096). -/
  J_square : J * J = 1
  /-- Kind: arithmetic cyclotomic determinant input
   (tex 2798–2805, 3090–3096). -/
  J_det : J.det = -1
  /-- Kind: scalar lift identification with the original trace and
   coefficient Weil normalization (tex 4385–4451, 5035–5038). -/
  ε_lift : ∀ i, ∀ [NeZero i], stageMap i (ε i : Lambda) = (stage i).ε
  /-- Kind: actual tame scale lift identification (tex 5027–5032). -/
  s_lift : ∀ i, ∀ [NeZero i], stageMap i (s i) = (stage i).tameScale
  /-- Kind: actual coefficient Tate-basis identification
   (tex 2798–2805, 3090–3096). -/
  J_lift : ∀ i, ∀ [NeZero i], (stage i).J = J.map (stageMap i)
  /-- Kind: retained derivative congruence for inverse residue size
   (tex 3090–3096, 5027–5032). -/
  s_congr : ∀ᶠ i in (U : Filter ℕ), s i + 1 ∈ stageIdeal i
  /-- Kind: cochain realization identification. The retained degree-one
   matrix is the original transported local cup read through its original
   trace, on the existing split-model coordinate basis
   (tex 4385–4451, 4860–4863). -/
  realization11 : ∀ i, ∀ [NeZero i], ∀ a b : Fin 2 ⊕ Fin 2,
    stageMap i (D.loc 1 1 i a b) =
      (stage i).cup11 (splitBasisOne (StageA i) a) (splitBasisOne (StageA i) b)
  /-- Kind: cochain realization identification. The retained degree-two/
   degree-zero matrix is the original transported local cup read through
   its original trace (tex 4385–4451, 4860–4863). -/
  realization20 : ∀ i, ∀ [NeZero i], ∀ a b : Fin 2,
    stageMap i (D.loc 2 0 i a b) = (stage i).cup20 (Pi.single a 1) (Pi.single b 1)

variable {U : Ultrafilter ℕ} {C : ComplexStages (R := Lambda) stageIdeal U}
  {D : RetainedLimitPairingStages U C} (X : RetainedLocalArithmetic U C D)

/-- Kind: proved theorem. The original transported stage cups supply the
 exact reduced degree-one matrix; no residue table is an input
 (tex 4385–4451, 4860–4863, 5035–5042). -/
theorem RetainedLocalArithmetic.stage_matrix11 (i : ℕ) [NeZero i] :
    (D.loc 1 1 i).map (stageMap i) =
      cupMatrix11 (stageMap i (X.ε i : Lambda)) (stageMap i (X.s i)) (X.J.map (stageMap i)) := by
  ext a b
  rw [Matrix.map_apply, X.realization11, (X.stage i).cup11_formula,
    cupMatrix11_basis, cupForm11_apply, lCoordR_one_single, lCoordR_one_single,
    ← X.ε_lift i, ← X.s_lift i, X.J_lift i]

/-- Kind: proved theorem. The original transported stage adjoints supply
 the exact reduced degree-two/degree-zero matrix
 (tex 4385–4451, 4860–4863). -/
theorem RetainedLocalArithmetic.stage_matrix20 (i : ℕ) [NeZero i] :
    (D.loc 2 0 i).map (stageMap i) =
      cupMatrix20 (stageMap i (X.ε i : Lambda)) (X.J.map (stageMap i)) := by
  ext a b
  rw [Matrix.map_apply, X.realization20, (X.stage i).cup20_formula]
  change _ = crossForm (stageMap i (X.ε i : Lambda)) (X.J.map (stageMap i))
    (Pi.single a 1) (Pi.single b 1)
  rw [crossForm_apply, ← X.ε_lift i, X.J_lift i]

/-- Kind: proved theorem. The retained derivative congruences give inverse
 residue size minus one in the inner limit (tex 3090–3096, 5027–5032). -/
theorem RetainedLocalArithmetic.scale_limit (hU : (U : Filter ℕ) ≤ cofinite) :
    ulim U X.s = -1 := by
  have h := ulim_eq_zero_of_mem stageIdeal_tendsToZero hU X.s_congr
  rw [ulim_add, ulim_const] at h
  exact eq_neg_iff_add_eq_zero.mpr h

/-- Kind: proved theorem. The retained local degree-one matrix is the
 inner limit of the proved original arithmetic cup matrices
 (tex 4385–4451, 5035–5042). -/
theorem RetainedLocalArithmetic.matrix11_limit (hU : (U : Filter ℕ) ≤ cofinite) :
    ulimMat U (D.loc 1 1) = cupMatrix11 (ulim U (fun i => (X.ε i : Lambda))) (-1) X.J := by
  have hn : ∀ᶠ i in (U : Filter ℕ), i ≠ 0 := Eventually.filter_mono hU (by simp)
  have h : ∀ᶠ i in (U : Filter ℕ), ∀ a b,
      D.loc 1 1 i a b - cupMatrix11 (X.ε i : Lambda) (X.s i) X.J a b ∈ stageIdeal i := by
    filter_upwards [hn] with i hi
    have : NeZero i := ⟨hi⟩
    intro a b
    rw [← ker_stageMap, RingHom.mem_ker, map_sub]
    have he := (X.stage_matrix11 i).trans (map_cupMatrix11 (stageMap i)
      (X.ε i : Lambda) (X.s i) X.J).symm
    have hv := congrFun (congrFun he a) b
    simp only [Matrix.map_apply] at hv
    rw [hv, sub_self]
  have he := ulimMat_eq_of_sub_mem stageIdeal_tendsToZero hU h
  rw [ulim_cupMatrix11, X.scale_limit hU] at he
  exact he

/-- Kind: proved theorem. The retained degree-two/degree-zero local
 matrix is the inner limit of the proved original arithmetic adjoints
 (tex 4385–4451, 4860–4863). -/
theorem RetainedLocalArithmetic.matrix20_limit (hU : (U : Filter ℕ) ≤ cofinite) :
    ulimMat U (D.loc 2 0) = cupMatrix20 (ulim U (fun i => (X.ε i : Lambda))) X.J := by
  have hn : ∀ᶠ i in (U : Filter ℕ), i ≠ 0 := Eventually.filter_mono hU (by simp)
  have h : ∀ᶠ i in (U : Filter ℕ), ∀ a b,
      D.loc 2 0 i a b - cupMatrix20 (X.ε i : Lambda) X.J a b ∈ stageIdeal i := by
    filter_upwards [hn] with i hi
    have : NeZero i := ⟨hi⟩
    intro a b
    rw [← ker_stageMap, RingHom.mem_ker, map_sub]
    have he := (X.stage_matrix20 i).trans (map_cupMatrix20 (stageMap i)
      (X.ε i : Lambda) X.J).symm
    have hv := congrFun (congrFun he a) b
    simp only [Matrix.map_apply] at hv
    rw [hv, sub_self]
  have he := ulimMat_eq_of_sub_mem stageIdeal_tendsToZero hU h
  rw [ulim_cupMatrix20] at he
  exact he

/-- Kind: definition. The original arithmetic trace/Weil normalization
 at the coefficient fibre (tex 4385–4451, 5035–5038). -/
def RetainedLocalArithmetic.εAt (P : Ideal Lambda) [P.IsPrime] : ResAt P :=
  algebraMap Lambda (ResAt P) (ulim U (fun i => (X.ε i : Lambda)))

/-- Kind: definition. The actual retained Tate conjugation at the
 coefficient fibre (tex 2798–2805, 3090–3096, 5035–5038). -/
def RetainedLocalArithmetic.JAt (P : Ideal Lambda) [P.IsPrime] :
    Matrix (Fin 2) (Fin 2) (ResAt P) :=
  X.J.map (algebraMap Lambda (ResAt P))

/-- Kind: proved theorem. The arithmetic normalization is nonzero at the
 fibre because its retained inner limit is a unit
 (tex 4385–4451, 5035–5038). -/
theorem RetainedLocalArithmetic.εAt_ne_zero (P : Ideal Lambda) [P.IsPrime] : X.εAt P ≠ 0 := by
  exact ((ulim_units_isUnit U X.ε).map (algebraMap Lambda (ResAt P))).ne_zero

/-- Kind: proved theorem. The actual Tate involution survives coefficient
 specialization (tex 2798–2805, 3090–3096). -/
theorem RetainedLocalArithmetic.JAt_square (P : Ideal Lambda) [P.IsPrime] :
    X.JAt P * X.JAt P = 1 := by
  unfold RetainedLocalArithmetic.JAt
  rw [← Matrix.map_mul, X.J_square, Matrix.map_one _ (map_zero _) (map_one _)]

/-- Kind: proved theorem. The actual cyclotomic determinant survives
 coefficient specialization (tex 2798–2805, 3090–3096). -/
theorem RetainedLocalArithmetic.JAt_det (P : Ideal Lambda) [P.IsPrime] :
    (X.JAt P).det = -1 := by
  unfold RetainedLocalArithmetic.JAt
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, X.J_det, map_neg, map_one]

/-- Kind: proved theorem. The actual original local cup supplies `hb11`
 and its degree-two adjoint supplies `h20` for the general retained
 certificate. No residue identity and no desired local perfectness are
 assumed (tex 4385–4451, 4860–4863, 5027–5043). -/
theorem RetainedLocalArithmetic.residue_inputs (hU : (U : Filter ℕ) ≤ cofinite)
    (P : Ideal Lambda) [P.IsPrime] :
    (∀ x y, (localPairingOfMat (D.locK P)).b11 x y =
      -(switchPairing (X.εAt P) 1 (X.JAt P) y x)) ∧
      Function.Bijective (localPairingOfMat (D.locK P)).b20 := by
  have h11 : D.locK P 1 1 = cupMatrix11 (X.εAt P) (-1) (X.JAt P) := by
    change (ulimMat U (D.loc 1 1)).map (algebraMap Lambda (ResAt P)) = _
    rw [X.matrix11_limit hU, map_cupMatrix11, map_neg, map_one]
    rfl
  have h20 : D.locK P 2 0 = cupMatrix20 (X.εAt P) (X.JAt P) := by
    change (ulimMat U (D.loc 2 0)).map (algebraMap Lambda (ResAt P)) = _
    rw [X.matrix20_limit hU, map_cupMatrix20]
    rfl
  refine ⟨?_, localPairing_b20_bijective_of_cupMatrix (D.locK P) (X.εAt P) (X.JAt P)
    h20 (X.εAt_ne_zero P) (X.JAt_square P)⟩
  intro x y
  rw [localPairing_b11_of_cupMatrix (D.locK P) (X.εAt P) (-1) (X.JAt P) h11,
    cupForm11_eq_switch _ _ _ (X.JAt_square P) (X.JAt_det P)]
  simp only [neg_neg]

/-- Kind: proved theorem. The general inner-limit pairing certificate is
 supplied by the original local arithmetic cups and the retained global
 duality. The residue identity is proved, not passed to the consumer
 (tex 4385–4451, 4860–4863, 5027–5070). -/
theorem RetainedLocalArithmetic.certificate (hU : (U : Filter ℕ) ≤ cofinite)
    (E : RetainedGlobalDualityStages D) (P : Ideal Lambda) [P.IsPrime] :
    FibreInnerLimitPairingCertificate U hU P C (D.resLimit hU P) (X.εAt P) 1 (X.JAt P) := by
  obtain ⟨hb11, h20⟩ := X.residue_inputs hU P
  exact fibreInnerLimitPairingCertificate_of_retained' hU E P (X.εAt P) 1 (X.JAt P)
    (X.εAt_ne_zero P) one_ne_zero (X.JAt_square P) hb11 h20

/-- Kind: proved theorem. Identifying the actual retained Tate matrix with
 `conjMatrix` puts the certificate in the precise conjugation convention
 of the height-one consumer. This remaining identification is about the
 coefficient action alone, not the pairing (tex 2798–2805, 5027–5070). -/
theorem RetainedLocalArithmetic.certificate_at_conj (hU : (U : Filter ℕ) ≤ cofinite)
    (E : RetainedGlobalDualityStages D) (P : Ideal Lambda) [P.IsPrime]
    {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
    (Cn : ActualConj K S) (W : WeierstrassCurve K)
    (hW : W.map (Cn.κ : K →+* K) = W) [W.IsElliptic] [HasFullTwoTorsion K S W]
    (hJ : X.JAt P = conjMatrix Cn W hW P) :
    FibreInnerLimitPairingCertificate U hU P C (D.resLimit hU P) (X.εAt P) 1
      (conjMatrix Cn W hW P) := by
  rw [← hJ]
  exact X.certificate hU E P

open scoped WeierstrassCurve

/-- Kind: proved theorem. For a curve over the rationals, the existing
 realized conjugation dictionary supplies the exact coefficient matrix
 required by the height-one consumer (tex 2798–2805, 5027–5070). -/
theorem RetainedLocalArithmetic.certificate_at_rational_curve
    (hU : (U : Filter ℕ) ≤ cofinite) (Eglob : RetainedGlobalDualityStages D)
    (P : Ideal Lambda) [P.IsPrime]
    {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
    (B : WeierstrassCurve ℚ) [B.IsElliptic] [HasFullTwoTorsion K S (B⁄K)]
    (Cn : ActualConj K S) (hW : (B⁄K).map (Cn.κ : K →+* K) = B⁄K)
    (hJ : X.J = (conjMatrixK B Cn).map (algebraMap ℤ_[2] Lambda)) :
    FibreInnerLimitPairingCertificate U hU P C (D.resLimit hU P) (X.εAt P) 1
      (conjMatrix Cn (B⁄K) hW P) := by
  apply X.certificate_at_conj hU Eglob P Cn (B⁄K) hW
  unfold RetainedLocalArithmetic.JAt
  rw [hJ, Matrix.map_map, conjMatrix_eq_conjMatrixK B Cn hW P]
  congr 1

open ZInQ.Manuscript.RC.Wiring (resAt)
open ZInQ.Contrib.CloudB3RC53.UniformSwitch (TwoTermStage)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (InnerLimitStepData fiberH1)
open ZInQ.Manuscript.RC.Uniform (finPlane)

/-- Kind: definition with proved residue fields. The general inner-limit
 stage-step data are supplied without `ILStageStep.hloc`: their `hb11` and
 `h20` are the proved arithmetic residue inputs. Detection and the two
 side identifications are unchanged independent inputs
 (tex 4385–4451, 5027–5086). -/
def RetainedLocalArithmetic.toStepData (hU : (U : Filter ℕ) ≤ cofinite)
    (Eglob : RetainedGlobalDualityStages D) (P : Ideal Lambda) [P.IsPrime]
    {F : Type} [Field F] {ι : Localization.AtPrime P →+* F} (S₀ S₁ : TwoTermStage ι)
    (hdet : finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) ≤
      (limitRelaxed (fibreLimitGlobal U hU P C) (D.resLimit hU P)).U)
    (φ : (selCx (finiteLimitSide (fibreLimitGlobal U hU P C)
      (D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) S₀)
    (φ' : (selCx (singularLimitSide (fibreLimitGlobal U hU P C)
      (D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) S₁) :
    InnerLimitStepData P S₀ S₁ where
  U := U
  hU := hU
  C := C
  D := D
  E := Eglob
  ε := X.εAt P
  σ := 1
  J := X.JAt P
  hε := X.εAt_ne_zero P
  hσ := one_ne_zero
  hJ := X.JAt_square P
  hb11 := (X.residue_inputs hU P).1
  h20 := (X.residue_inputs hU P).2
  hdet := hdet
  φ := φ
  φ' := φ'

section SplitStageRealization

open ZInQ.Contrib.CloudB3RC53.SelmerDuality

/-- Kind: definition with proved realization fields. The existing stage
 matrix lift and the original cochain trace comparison supply the two
 realization fields of the retained arithmetic record. The trace comparisons
 have actual transported cups as their targets, not determinant tables
 (tex 4385–4451, 4860–4863, 5027–5042). -/
def RetainedLocalArithmetic.of_splitStages
    (Y : ∀ i, ∀ [NeZero i], StageArithmeticData i)
    (ε : ℕ → Lambdaˣ) (s : ℕ → Lambda) (J : Matrix (Fin 2) (Fin 2) Lambda)
    (hJ : J * J = 1) (hJdet : J.det = -1)
    (hε : ∀ i, ∀ [NeZero i], stageMap i (ε i : Lambda) = (Y i).ε)
    (hs : ∀ i, ∀ [NeZero i], stageMap i (s i) = (Y i).tameScale)
    (hmat : ∀ i, ∀ [NeZero i], (Y i).J = J.map (stageMap i))
    (hcongr : ∀ᶠ i in (U : Filter ℕ), s i + 1 ∈ stageIdeal i)
    (G Uc : ∀ i, GCx (StageA i))
    (res : ∀ i, GHom (G i) (splitLocalComplex (StageA i)))
    (ιc : ∀ i, GHom (Uc i) (splitLocalComplex (StageA i)))
    (Q : ∀ i, SelPairData (splitSelData (G i) (res i) (Uc i) (ιc i))
      (splitSelData (G i) (res i) (Uc i) (ιc i)))
    (tr : ∀ i, (coneCx (Q i).resE).X 3 →ₗ[StageA i] StageA i)
    (hlift : ∀ i, i ≠ 0 → ∀ a b, (D.loc a b i).map (stageMap i) = stageLocMat (Q i) (tr i) a b)
    (htrace11 : ∀ i, ∀ [NeZero i], ∀ x y : (Fin 2 → StageA i) × (Fin 2 → StageA i),
      tr i (0, (Q i).cupL.P 1 1 2 rfl x y) = (Y i).cup11 x y)
    (htrace20 : ∀ i, ∀ [NeZero i], ∀ x y : Fin 2 → StageA i,
      tr i (0, (Q i).cupL.P 2 0 2 rfl x y) = (Y i).cup20 x y) :
    RetainedLocalArithmetic U C D where
  stage := Y
  ε := ε
  s := s
  J := J
  J_square := hJ
  J_det := hJdet
  ε_lift := hε
  s_lift := hs
  J_lift := hmat
  s_congr := hcongr
  realization11 := by
    intro i _ a b
    have he := congrFun (congrFun (hlift i (NeZero.ne i) 1 1) a) b
    simp only [Matrix.map_apply] at he
    have hQ : stageLocMat (Q i) (tr i) 1 1 a b =
        tr i (0, (Q i).cupL.P 1 1 2 rfl
          ((lCoordR (StageA i) 1).symm (Pi.single a 1))
          ((lCoordR (StageA i) 1).symm (Pi.single b 1))) := rfl
    have ht := htrace11 i ((lCoordR (StageA i) 1).symm (Pi.single a 1))
      ((lCoordR (StageA i) 1).symm (Pi.single b 1))
    rw [lCoordR_one_single, lCoordR_one_single] at ht
    rw [lCoordR_one_single, lCoordR_one_single] at hQ
    exact (he.trans hQ).trans ht
  realization20 := by
    intro i _ a b
    have he := congrFun (congrFun (hlift i (NeZero.ne i) 2 0) a) b
    simp only [Matrix.map_apply] at he
    have hQ : stageLocMat (Q i) (tr i) 2 0 a b =
        tr i (0, (Q i).cupL.P 2 0 2 rfl (Pi.single a 1) (Pi.single b 1)) := rfl
    exact (he.trans hQ).trans (htrace20 i (Pi.single a 1) (Pi.single b 1))

end SplitStageRealization

open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.CoefModules (Mcoef Tate1 HasRootsOfUnity FullTorsion TorsS CoefMod
  CharMod cycA weilA weilA_perfect weilPairingData conjBC charInv IsOpenKer)
open ZInQ.Contrib.RC53Assist.LocalDegreeTwo (TameOrientation)

section ActualCoefficients

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α] (q : HeightOneSpectrum (𝓞 K))
  (hμ : HasRootsOfUnity K S (2 ^ i))

/-- Kind: definition. The actual localized rank-two coefficient module
 used by the retained arithmetic data (tex 2723–2727, 4860–4863). -/
abbrev actualM : Type := ResMod (locMap K S q) (Mcoef K S W i α)

/-- Kind: definition. The actual localized scalar twist coefficient
 module (tex 2762–2767, 4860–4863). -/
abbrev actualN : Type := ResMod (locMap K S q) (Tate1 (Acoef i) hμ)

/-- Kind: definition. The actual scalar twist coefficient frame; this is
 not a choice of a bilinear table (tex 2762–2767, 4860–4863). -/
def actualScalarFrame : actualN i q hμ ≃ₗ[Acoef i] Acoef i :=
  CharMod.equiv (Acoef i) (cycA (Acoef i) hμ)

/-- Kind: definition. The actual coefficient Weil pairing, before
 conjugating its second argument (tex 2798–2805). -/
def actualWeil : actualM W i α q →ₗ[Acoef i] actualM W i α q →ₗ[Acoef i] actualN i q hμ :=
  weilA W hμ (Acoef i)

omit [NeZero i] [IsOpenKer α] in
/-- Kind: proved theorem. Alternation of the actual coefficient Weil
 pairing supplies the corresponding arithmetic input (tex 2798–2805). -/
theorem actualWeil_alternating (m : actualM W i α q) : actualWeil W i α q hμ m m = 0 := by
  let T := TorsS K S W ((2 ^ i : ℕ) : ℤ)
  have hs (P : T) : ZInQ.Manuscript.RC.CoefModules.weilS W hμ P P = 0 := by
    have h := TauCeti.Isogeny.weilPairing_self (W.baseChange (AlgebraicClosure K)) (2 ^ i)
      (ZInQ.Manuscript.RC.CoefModules.natCast_ne_zero_bar (2 ^ i))
      (ZInQ.Manuscript.RC.CoefModules.inclTors W (2 ^ i) P)
    change ZInQ.Manuscript.RC.CoefModules.weilBar W (2 ^ i)
      (ZInQ.Manuscript.RC.CoefModules.inclTors W (2 ^ i) P)
      (ZInQ.Manuscript.RC.CoefModules.inclTors W (2 ^ i) P) = 0 at h
    rw [ZInQ.Manuscript.RC.CoefModules.weilS_apply, h, map_zero]
  have hsSwap (P Q : T) : ZInQ.Manuscript.RC.CoefModules.weilS W hμ Q P =
      -ZInQ.Manuscript.RC.CoefModules.weilS W hμ P Q := by
    rw [ZInQ.Manuscript.RC.CoefModules.weilS_apply,
      ZInQ.Manuscript.RC.CoefModules.weilS_apply,
      ZInQ.Manuscript.RC.CoefModules.weilBar_skew, map_neg]
  have hSwap (x y : Acoef i ⊗[ℤ] T) : weilA W hμ (Acoef i) y x =
      -weilA W hμ (Acoef i) x y := by
    induction x using TensorProduct.inductionOn with
    | tmul a P =>
      induction y using TensorProduct.inductionOn with
      | tmul b Q =>
        rw [ZInQ.Manuscript.RC.CoefModules.weilA_tmul,
          ZInQ.Manuscript.RC.CoefModules.weilA_tmul, hsSwap, map_neg]
        ring
      | add y z hy hz =>
        simp only [map_add, LinearMap.add_apply]
        rw [hy, hz, neg_add]
    | add x z hx hz =>
      simp only [map_add, LinearMap.add_apply]
      rw [hx, hz, neg_add]
  have hSelf (x : Acoef i ⊗[ℤ] T) : weilA W hμ (Acoef i) x x = 0 := by
    induction x using TensorProduct.inductionOn with
    | tmul a P =>
      rw [ZInQ.Manuscript.RC.CoefModules.weilA_tmul, hs, map_zero, mul_zero]
    | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply]
      rw [hx, hy, hSwap]
      ring
  exact hSelf (show Acoef i ⊗[ℤ] T from m)

omit [NeZero i] [IsOpenKer α] in
/-- Kind: proved theorem. Full elliptic torsion supplies perfectness of
 the actual coefficient Weil pairing, independently of the local cup
 residue identity (tex 2798–2805). -/
theorem actualWeil_perfect (hFull : FullTorsion K S W (2 ^ i)) :
    Function.Bijective ((actualWeil W i α q hμ).compr₂ (actualScalarFrame i q hμ).toLinearMap) := by
  change Function.Bijective (weilA W hμ (Acoef i))
  exact (weilA_perfect W hμ (Acoef i) hFull).1

/-- Kind: definition. Forgetting the inverse character on the underlying
 actual coefficient module is a coefficient map, not a duality assertion
 (tex 2762–2767, 2798–2805). -/
def actualInverseMap : actualM W i α q →ₗ[Acoef i]
    ResMod (locMap K S q) (Mcoef K S W i (charInv α)) :=
  ((CoefMod.equiv (Acoef i) α (TorsS K S W ((2 ^ i : ℕ) : ℤ))).symm.trans
    (CoefMod.equiv (Acoef i) (charInv α) (TorsS K S W ((2 ^ i : ℕ) : ℤ)))).toLinearMap

omit [NeZero i] in
/-- Kind: proved theorem. The actual same-module cup used in the
 arithmetic calculation is the native Weil cup against the inverse
 coefficient system after the coefficient map. The independent hypotheses
 are trivial derivative actions on the two actual modules, not a pairing
 table (tex 2762–2767, 2798–2805, 4860–4863). -/
theorem actualCup_eq_native
    (hM : ∀ (g : Gloc K q) (m : actualM W i α q), g • m = m)
    (hInv : ∀ (g : Gloc K q)
      (m : ResMod (locMap K S q) (Mcoef K S W i (charInv α))), g • m = m)
    (p r t : ℕ) (h : p + r = t)
    (x : (contCochains (Acoef i) (Gloc K q) (actualM W i α q)).X p)
    (y : (contCochains (Acoef i) (Gloc K q) (actualM W i α q)).X r) :
    contCup (actualWeil W i α q hμ) continuous_of_discreteTopology p r t h x y =
      contCup (resPairing (Acoef i) (GKS K S) (weilPairingData W i α hμ) (locMap K S q))
        continuous_of_discreteTopology p r t h x (coefficientMap (actualInverseMap W i α q) r y) := by
  apply contCochains_ext
  intro v
  change cupFun (actualWeil W i α q hμ) p r t h (contFun x) (contFun y) v = _
  rw [cupFun_apply]
  change _ = cupFun (resPairing (Acoef i) (GKS K S) (weilPairingData W i α hμ)
    (locMap K S q)) p r t h (contFun x)
    (contFun (coefficientMap (actualInverseMap W i α q) r y)) v
  rw [cupFun_apply, hM, hInv]
  rfl

variable (Cn : ActualConj K S) (hW : W.map (Cn.κ : K →+* K) = W)

/-- Kind: definition. The coefficient conjugation is the actual
 `id ⊗ ρ_T(τ)`, on the actual localized coefficient module
 (tex 2798–2805, 5027–5032). -/
def actualConjugation : actualM W i α q →ₗ[Acoef i] actualM W i α q :=
  conjBC Cn W hW (Acoef i)

/-- Kind: definition. The matrix of the actual coefficient conjugation
 in the prescribed finite coefficient frame (tex 2798–2805, 5027–5032). -/
def actualConjugationMatrix (e : actualM W i α q ≃ₗ[Acoef i] (Fin 2 → Acoef i)) :
    Matrix (Fin 2) (Fin 2) (Acoef i) :=
  LinearMap.toMatrix' (e.toLinearMap.comp
    ((actualConjugation W i α q Cn hW).comp e.symm.toLinearMap))

omit [NeZero i] [IsOpenKer α] [W.IsElliptic] in
/-- Kind: proved theorem. The actual coefficient conjugation has the
 displayed matrix in every prescribed coefficient frame
 (tex 2798–2805, 5027–5032). -/
theorem actualConjugationMatrix_coordinates
    (e : actualM W i α q ≃ₗ[Acoef i] (Fin 2 → Acoef i)) (m : actualM W i α q) :
    e (actualConjugation W i α q Cn hW m) =
      actualConjugationMatrix W i α q Cn hW e *ᵥ e m := by
  rw [actualConjugationMatrix, LinearMap.toMatrix'_mulVec]
  change e (actualConjugation W i α q Cn hW m) =
    e (actualConjugation W i α q Cn hW (e.symm (e m)))
  rw [e.symm_apply_apply]

/-- Kind: definition with proved coefficient inputs. The arithmetic data
 are instantiated on the actual local Galois group, the actual localized
 `M_i` and `A_i(1)`, and the actual Weil pairing and actual Tate conjugation.
 Coordinate/retraction inputs come from the normalized local producer;
 the remaining inputs concern roots, character pullback, and the original
 local invariant. None is the desired residue pairing identity
 (tex 2723–2727, 2762–2767, 2798–2805, 3090–3096, 4860–4863, 5027–5042). -/
def actualLocalArithmetic
    (hFull : FullTorsion K S W (2 ^ i))
    (Dt : TameOrientation (q.adicCompletion K) (2 ^ i))
    (hμloc : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K)/q.adicCompletion K))
      (ζ : AlgebraicClosure (q.adicCompletion K)), ζ ^ (2 ^ i) = 1 → g ζ = ζ)
    (e : actualM W i α q ≃ₗ[Acoef i] (Fin 2 → Acoef i))
    (cM : (contCochains (Acoef i) (Gloc K q) (actualM W i α q)).X 2 →ₗ[Acoef i]
      actualM W i α q)
    (cN : (contCochains (Acoef i) (Gloc K q) (actualN i q hμ)).X 2 →ₗ[Acoef i] actualN i q hμ)
    (hcM : LocalDegreeTwoCoordinate cM) (hcN : LocalDegreeTwoCoordinate cN)
    (hnM : LocalDegreeTwoNormalized cM
      (fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (Dt.unramified g))
      (fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (Dt.kummer g)))
    (hnN : LocalDegreeTwoNormalized cN
      (fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (Dt.unramified g))
      (fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (Dt.kummer g)))
    (model : ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace.OrientedLocalRetraction
      (G := Gloc K q) e Dt.frobenius Dt.inertia cM)
    (hM : ∀ (g : Gloc K q) (m : actualM W i α q), g • m = m)
    (hN : ∀ (g : Gloc K q) (m : actualN i q hμ), g • m = m)
    (χu χκ : Gloc K q → ZMod (2 * (2 ^ i)))
    (hχu : Continuous χu) (hχκ : Continuous χκ)
    (hχua : ∀ g h, χu (g * h) = χu g + χu h)
    (hχκa : ∀ g h, χκ (g * h) = χκ g + χκ h)
    (hlu : ∀ g, Dt.unramified g = ((χu g).val : ZMod (2 ^ i)))
    (hlκ : ∀ g, Dt.kummer g = ((χκ g).val : ZMod (2 ^ i)))
    (θ : Gloc K q →ₜ* Gloc K q) (s : Acoef i)
    (hθu : ∀ g, Dt.unramified (θ g) = Dt.unramified g)
    (hθκ : ∀ g, algebraMap (ZMod (2 ^ i)) (Acoef i) (Dt.kummer (θ g)) =
      s * algebraMap (ZMod (2 ^ i)) (Acoef i) (Dt.kummer g))
    (τ : (contCochains (Acoef i) (Gloc K q) (actualN i q hμ)).X 2 →ₗ[Acoef i] Acoef i)
    (hτ : ∀ a, τ (((contCochains (Acoef i) (Gloc K q) (actualN i q hμ)).d 1 2).hom a) = 0)
    (honto : ∀ r : Acoef i, ∃ z,
      ((contCochains (Acoef i) (Gloc K q) (actualN i q hμ)).d 2 3).hom z = 0 ∧ τ z = r) :
    StageArithmeticData i := by
  have : Fact (1 < 2 ^ i) := ⟨Nat.one_lt_two_pow (NeZero.ne i)⟩
  obtain ⟨huφ, huσ, hκφ, hκσ⟩ := Dt.character_values
  exact
    { G := Gloc K q
      groupG := inferInstance
      topologyG := inferInstance
      topologicalGroupG := inferInstance
      M := actualM W i α q
      addM := inferInstance
      moduleM := inferInstance
      actionM := inferInstance
      commM := inferInstance
      topologyM := inferInstance
      discreteM := inferInstance
      continuousM := inferInstance
      N := actualN i q hμ
      addN := inferInstance
      moduleN := inferInstance
      actionN := inferInstance
      commN := inferInstance
      topologyN := inferInstance
      discreteN := inferInstance
      continuousN := inferInstance
      eM := e
      eN := actualScalarFrame i q hμ
      β := actualWeil W i α q hμ
      alternating := actualWeil_alternating W i α q hμ
      perfect := actualWeil_perfect W i α q hμ hFull
      trivialM := hM
      trivialN := hN
      frobenius := Dt.frobenius
      inertia := Dt.inertia
      u := fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (Dt.unramified g)
      κ := fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (Dt.kummer g)
      continuousU := (continuous_of_discreteTopology : Continuous
        (algebraMap (ZMod (2 ^ i)) (Acoef i))).comp
          (continuous_urCharN (K := q.adicCompletion K) (n := 2 ^ i))
      continuousK := (continuous_of_discreteTopology : Continuous
        (algebraMap (ZMod (2 ^ i)) (Acoef i))).comp
          (continuous_kummerLog Dt.root_pow Dt.root_ne_zero Dt.primitive hμloc)
      additiveU := fun g h => by
        change algebraMap (ZMod (2 ^ i)) (Acoef i)
          (urCharN (q.adicCompletion K) (2 ^ i) (g * h)) =
            algebraMap (ZMod (2 ^ i)) (Acoef i) (urCharN (q.adicCompletion K) (2 ^ i) g) +
            algebraMap (ZMod (2 ^ i)) (Acoef i) (urCharN (q.adicCompletion K) (2 ^ i) h)
        rw [urCharN_mul, map_add]
      additiveK := fun g h => by
        change algebraMap (ZMod (2 ^ i)) (Acoef i)
          (kummerLog Dt.root_pow Dt.root_ne_zero Dt.primitive (g * h)) =
            algebraMap (ZMod (2 ^ i)) (Acoef i)
              (kummerLog Dt.root_pow Dt.root_ne_zero Dt.primitive g) +
            algebraMap (ZMod (2 ^ i)) (Acoef i)
              (kummerLog Dt.root_pow Dt.root_ne_zero Dt.primitive h)
        rw [kummerLog_mul Dt.root_pow Dt.root_ne_zero Dt.primitive hμloc, map_add]
      u_frobenius := by rw [huφ, map_one]
      u_inertia := by rw [huσ, map_zero]
      κ_frobenius := by rw [hκφ, map_zero]
      κ_inertia := by rw [hκσ, map_one]
      χu := χu
      χκ := χκ
      continuousχu := hχu
      continuousχκ := hχκ
      additiveχu := hχua
      additiveχκ := hχκa
      liftU := fun g => by rw [hlu]
      liftK := fun g => by rw [hlκ]
      cM := cM
      cN := cN
      coordinateM := hcM
      coordinateN := hcN
      normalizedM := hnM
      normalizedN := hnN
      model := model
      θ := θ
      j := actualConjugation W i α q Cn hW
      J := actualConjugationMatrix W i α q Cn hW e
      conjugationCoordinates := actualConjugationMatrix_coordinates W i α q Cn hW e
      tameScale := s
      pullU := fun g => by rw [hθu]
      pullK := hθκ
      τ := τ
      trace_kills := hτ
      trace_onto := honto }

end ActualCoefficients

end RetainedArithmetic

end ZInQ.Contrib.RC53Assist.ResidueIdentity
