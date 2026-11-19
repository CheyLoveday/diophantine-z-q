import ZInQKernel.Contrib.RC53Assist.TateCurve.LocalReadings.ValuationExtension
import ZInQKernel.Contrib.RC53Assist.TateCurve.LocalReadings.ResidueFrobenius

/-!
# The residue action of the local Galois group

The residue field is algebraic over the prime field. Every local automorphism
preserves the valuation ring, and reduction defines a homomorphism whose kernel
is precisely inertia. Arithmetic Frobenius reduces to the `p`-power automorphism.

Kinds: definitions and proved statements only.
Locators: Serre, *Local Fields*, I, §8 and III, §5. These section references concern
the book, not Serre's chapter in Cassels--Fröhlich.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open ZInQ.Contrib.RC53Assist.DecompositionGlue
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
open ZInQ.Contrib.RC53Assist.GlobalTrace
open scoped WithZero Pointwise

/-- **DEFINITION**: the rational local field used in the readings. -/
abbrev LocalBaseQ (p : ℕ) (hp : p.Prime) := (primeIdealQ p hp).adicCompletion ℚ

/-- **DEFINITION**: its chosen algebraic closure. -/
abbrev LocalClosureQ (p : ℕ) (hp : p.Prime) := AlgebraicClosure (LocalBaseQ p hp)

/-- **DEFINITION**: the base valuation ring. -/
abbrev LocalBaseIntegersQ (p : ℕ) (hp : p.Prime) :=
  (Valued.v : Valuation (LocalBaseQ p hp) ℤᵐ⁰).valuationSubring

/-- **DEFINITION**: the residue field at the extending valuation. -/
abbrev LocalResidueQ {p : ℕ} {hp : p.Prime} {Γ : Type}
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation (LocalClosureQ p hp) Γ) :=
  IsLocalRing.ResidueField w.valuationSubring

section Reduction

variable (p : ℕ) (hp : p.Prime) (Γ : Type) [LinearOrderedCommGroupWithZero Γ]
variable (w : Valuation (LocalClosureQ p hp) Γ)
variable (hw : (w.comap (algebraMap (LocalBaseQ p hp) (LocalClosureQ p hp))).IsEquiv
  (Valued.v : Valuation (LocalBaseQ p hp) ℤᵐ⁰))

include hw

/-- **PROVED**: the extending valuation ring is the integral closure of the
base ring of integers. Locator: spectral unit ball and valuation uniqueness. -/
theorem local_integral_iff_le_one (x : LocalClosureQ p hp) :
    IsIntegral (LocalBaseIntegersQ p hp) x ↔ w x ≤ 1 := by
  constructor
  · exact integral_valuation_le_one w fun a => hw.le_one_iff_le_one.mpr a.2
  · intro hx
    letI := padicNontriviallyNormedField p hp
    apply isIntegral_of_spectralNorm_le_one Valued.v
      (fun _ => Valued.toNormedField.norm_le_one_iff)
    exact (spectralValuation_le_one_iff _).mp
      ((local_valuation_isEquiv_spectral p hp Γ w hw).le_one_iff_le_one.mp hx)

/-- **PROVED**: the preceding elementwise assertion in the standard integral
closure characteristic predicate. Locator: the integral-closure definition. -/
theorem local_integer_isIntegralClosure :
    IsIntegralClosure w.valuationSubring (LocalBaseIntegersQ p hp) (LocalClosureQ p hp) where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff := by
    intro x
    rw [local_integral_iff_le_one p hp Γ w hw x]
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.2

/-- **PROVED**: the entire local Galois group is the decomposition group.
Locator: uniqueness of the valuation extending a complete DVR valuation. -/
theorem local_mem_decomposition (σ : LocalGaloisQ p hp) :
    σ ∈ w.valuationSubring.decompositionSubgroup (LocalBaseQ p hp) := by
  refine MulAction.mem_stabilizer_iff.mpr (SetLike.ext fun x => ?_)
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff,
    local_valuation_galois p hp Γ w hw]

/-- **DEFINITION**: the inclusion of the whole Galois group in the decomposition
subgroup, with the preceding preservation proof. -/
def localDecompositionHom : LocalGaloisQ p hp →*
    w.valuationSubring.decompositionSubgroup (LocalBaseQ p hp) where
  toFun σ := ⟨σ, local_mem_decomposition p hp Γ w hw σ⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

/-- **DEFINITION**: reduction of local automorphisms to automorphisms of the
actual residue field. Locator: the decomposition-group residue action. -/
def localResidueRingHom : LocalGaloisQ p hp →* (LocalResidueQ w ≃+* LocalResidueQ w) :=
  (MulSemiringAction.toRingAut
    (w.valuationSubring.decompositionSubgroup (LocalBaseQ p hp)) (LocalResidueQ w)).comp
      (localDecompositionHom p hp Γ w hw)

/-- **PROVED**: reducing the image of an integral element agrees with acting on
its residue class. Locator: equivariance of the residue quotient. -/
theorem localResidueRingHom_apply (σ : LocalGaloisQ p hp) (x : w.valuationSubring) :
    localResidueRingHom p hp Γ w hw σ (IsLocalRing.residue w.valuationSubring x) =
      IsLocalRing.residue w.valuationSubring (localDecompositionHom p hp Γ w hw σ • x) :=
  (IsLocalRing.ResidueField.residue_smul
    (w.valuationSubring.decompositionSubgroup (LocalBaseQ p hp))
    (localDecompositionHom p hp Γ w hw σ) x).symm

/-- **PROVED**: the kernel of the full local residue action is exactly the
inertia subgroup in the target statement. Locator: inertia is the residue kernel. -/
theorem mem_localInertia_iff_residueRingHom_eq_one (σ : LocalGaloisQ p hp) :
    σ ∈ localInertia w ↔ localResidueRingHom p hp Γ w hw σ = 1 := by
  rw [localInertia, Subgroup.mem_map]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    change (MulSemiringAction.toRingAut
      (w.valuationSubring.decompositionSubgroup (LocalBaseQ p hp)) (LocalResidueQ w))
        (localDecompositionHom p hp Γ w hw τ.val) = 1
    have he : localDecompositionHom p hp Γ w hw τ.val = τ := Subtype.ext rfl
    rw [he]
    exact hτ
  · intro hσ
    exact ⟨localDecompositionHom p hp Γ w hw σ, hσ, rfl⟩

/-- **PROVED**: an arithmetic Frobenius on the closure acts on the residue field
by the `p`-power map. Locator: the arithmetic Frobenius convention, Serre I, §8. -/
theorem localResidueRingHom_frobenius (σ : LocalGaloisQ p hp)
    (hσ : IsArithmeticFrobeniusOnClosureQ (primeIdealQ p hp) Γ w σ)
    (y : LocalResidueQ w) : localResidueRingHom p hp Γ w hw σ y = y ^ p := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  rw [localResidueRingHom_apply, ← map_pow, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  change w (σ (x : LocalClosureQ p hp) - (x : LocalClosureQ p hp) ^ p) < 1
  have h := hσ x x.2
  rwa [primeIdealQ_absNorm] at h

/-- **DEFINITION**: the embedding of the prime field in the residue field, via
reduction of the base valuation ring. -/
def localResidueBaseMap : ZMod p →+* LocalResidueQ w := by
  let v : Valuation (LocalBaseQ p hp) ℤᵐ⁰ := Valued.v
  letI : v.HasExtension w := ⟨hw.symm⟩
  letI : Algebra v.valuationSubring w.valuationSubring :=
    Valuation.HasExtension.instAlgebra_valuationSubring v w
  letI : IsLocalHom (algebraMap v.valuationSubring w.valuationSubring) := inferInstance
  exact (algebraMap (IsLocalRing.ResidueField v.valuationSubring) (LocalResidueQ w)).comp
    (residueFieldEquivZModQ p hp).symm.toRingHom

/-- **DEFINITION**: the resulting prime-field algebra structure. -/
def localResidueAlgebra : Algebra (ZMod p) (LocalResidueQ w) :=
  (localResidueBaseMap p hp Γ w hw).toAlgebra

/-- **PROVED**: the residue field has characteristic `p`.
Locator: the base residue identification with the prime field. -/
theorem local_residue_charP : CharP (LocalResidueQ w) p := by
  letI : Fact p.Prime := ⟨hp⟩
  exact charP_of_injective_ringHom (localResidueBaseMap p hp Γ w hw).injective p

/-- **PROVED**: the residue field of the algebraic closure is algebraic over the
prime field. Locator: integral ring extensions induce algebraic residue extensions. -/
theorem local_residue_isAlgebraic :
    letI := localResidueAlgebra p hp Γ w hw
    Algebra.IsAlgebraic (ZMod p) (LocalResidueQ w) := by
  letI : Fact p.Prime := ⟨hp⟩
  let v : Valuation (LocalBaseQ p hp) ℤᵐ⁰ := Valued.v
  letI : v.HasExtension w := ⟨hw.symm⟩
  letI : Algebra v.valuationSubring w.valuationSubring :=
    Valuation.HasExtension.instAlgebra_valuationSubring v w
  haveI : IsScalarTower v.valuationSubring w.valuationSubring (LocalClosureQ p hp) :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring' v w
  letI : IsLocalHom (algebraMap v.valuationSubring w.valuationSubring) := inferInstance
  haveI : IsIntegralClosure w.valuationSubring v.valuationSubring (LocalClosureQ p hp) :=
    local_integer_isIntegralClosure p hp Γ w hw
  haveI : Algebra.IsIntegral v.valuationSubring w.valuationSubring :=
    IsIntegralClosure.isIntegral_algebra v.valuationSubring (LocalClosureQ p hp)
  haveI : Algebra.IsIntegral v.valuationSubring (LocalResidueQ w) :=
    Algebra.IsIntegral.trans w.valuationSubring
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField v.valuationSubring) (LocalResidueQ w) :=
    Algebra.IsIntegral.tower_top v.valuationSubring
  letI := localResidueAlgebra p hp Γ w hw
  constructor
  intro x
  have hi : IsIntegral (IsLocalRing.ResidueField v.valuationSubring) x :=
    Algebra.IsIntegral.isIntegral x
  let e : ZMod p ≃+* IsLocalRing.ResidueField v.valuationSubring :=
    (residueFieldEquivZModQ p hp).symm
  exact ((e.isIntegral_iff rfl x).mpr hi).isAlgebraic

end Reduction

/-- **DEFINITION**: every ring automorphism of a prime-field algebra fixes that
prime field. Locator: every residue class is an integer cast. -/
def primeFieldRingAutHom (p : ℕ) (L : Type*) [Field L] [Algebra (ZMod p) L] :
    (L ≃+* L) →* (L ≃ₐ[ZMod p] L) where
  toFun φ :=
    { φ with
      commutes' := by
        intro a
        obtain ⟨n, rfl⟩ := ZMod.intCast_surjective a
        change φ (algebraMap (ZMod p) L (n : ZMod p)) =
          algebraMap (ZMod p) L (n : ZMod p)
        simp only [map_intCast] }
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

/-- **PROVED**: passing from ring to prime-field algebra automorphisms loses no
information. Locator: extensionality. -/
theorem primeFieldRingAutHom_injective (p : ℕ) (L : Type*) [Field L]
    [Algebra (ZMod p) L] : Function.Injective (primeFieldRingAutHom p L) := by
  intro φ ψ h
  ext x
  exact congrArg (fun f : L ≃ₐ[ZMod p] L => f x) h

section AlgebraReduction

variable (p : ℕ) (hp : p.Prime) (Γ : Type) [LinearOrderedCommGroupWithZero Γ]
variable (w : Valuation (LocalClosureQ p hp) Γ)
variable (hw : (w.comap (algebraMap (LocalBaseQ p hp) (LocalClosureQ p hp))).IsEquiv
  (Valued.v : Valuation (LocalBaseQ p hp) ℤᵐ⁰))

include hw

/-- **DEFINITION**: the local residue homomorphism as a prime-field Galois action. -/
def localResidueHom :
    letI := localResidueAlgebra p hp Γ w hw
    LocalGaloisQ p hp →* (LocalResidueQ w ≃ₐ[ZMod p] LocalResidueQ w) := by
  letI := localResidueAlgebra p hp Γ w hw
  exact (primeFieldRingAutHom p (LocalResidueQ w)).comp
    (localResidueRingHom p hp Γ w hw)

/-- **PROVED**: the kernel statement is unchanged for prime-field automorphisms.
Locator: the ring-action kernel and injectivity above. -/
theorem localResidueHom_ker :
    letI := localResidueAlgebra p hp Γ w hw
    (localResidueHom p hp Γ w hw).ker = localInertia w := by
  letI := localResidueAlgebra p hp Γ w hw
  ext σ
  rw [MonoidHom.mem_ker, mem_localInertia_iff_residueRingHom_eq_one p hp Γ w hw]
  exact (primeFieldRingAutHom_injective p (LocalResidueQ w)).eq_iff

/-- **PROVED**: the reduced arithmetic Frobenius is the `p`-power automorphism.
Locator: the preceding residue calculation. -/
theorem localResidueHom_frobenius (σ : LocalGaloisQ p hp)
    (hσ : IsArithmeticFrobeniusOnClosureQ (primeIdealQ p hp) Γ w σ) :
    letI := localResidueAlgebra p hp Γ w hw
    ∀ y : LocalResidueQ w, localResidueHom p hp Γ w hw σ y = y ^ p :=
  localResidueRingHom_frobenius p hp Γ w hw σ hσ

end AlgebraReduction

end ZInQ.Contrib.RC53Assist.TateCurve
