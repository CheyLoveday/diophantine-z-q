import ZInQKernel.Contrib.OneProof.RC.HCMV21.CompletionComparison
import ZInQKernel.Contrib.OneProof.RC.HCMV21.OrderStabilizer

/-! Relate the order of the one labelled reference to its adelic
representative. Tex 8464–8468 and 9150–9169. -/

namespace ZInQ.Manuscript.RC.HCMV21

open Eichler Adelic NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open scoped NumberField nonZeroDivisors

variable {a b : ℚ}

/-- The class of the actual fractional lattice of the analytic reference,
with the inverse-ideal action already installed on its class set. -/
def referenceAnalyticClass {F : Type*} [Field F] [NumberField F]
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : IdealLatticeClass (𝓞 F) F :=
  QuotientGroup.mk I

/-- The coordinates of the enhanced reference order as the left order
of the reference right lattice. This tests the one reference only. -/
def ReferenceOrderCoordinates (R S : Order a b) (z : Adelic.FiniteUnits R) : Prop :=
  ∀ (p : Prime) (x : Bp p.val a b),
    (↑(z.val p)⁻¹ : Bp p.val a b) * x * (z.val p : Bp p.val a b) ∈ R.completion p.val ↔
      x ∈ S.completion p.val

/-- Compatible local changes of frame give one restricted adelic
representative. Equal local orders use the identity coordinate. -/
theorem exists_referenceCoordinates (R S : Order a b)
    (h : ∀ p : Prime, ∃ u : (Bp p.val a b)ˣ, ∀ x : Bp p.val a b,
      (↑u⁻¹ : Bp p.val a b) * x * (u : Bp p.val a b) ∈ R.completion p.val ↔
        x ∈ S.completion p.val) :
    ∃ z : Adelic.FiniteUnits R, ReferenceOrderCoordinates R S z := by
  classical
  choose u hu using h
  let w (p : Prime) : (Bp p.val a b)ˣ :=
    if R.completion p.val = S.completion p.val then 1 else u p
  let z : Adelic.FiniteUnits R := ⟨w, by
    apply (finite_localLattice_ne R.full S.full).subset
    intro p hp
    by_contra! he
    change ¬ (localLattice p.val R.lattice ≠ localLattice p.val S.lattice) at he
    have he' : R.completion p.val = S.completion p.val := by
      apply Subalgebra.toSubmodule_injective
      rw [R.completion_toSubmodule, S.completion_toSubmodule]
      exact not_not.mp he
    exact hp (by simp [w, he', Adelic.localUnits])⟩
  refine ⟨z, fun p x => ?_⟩
  change (↑(w p)⁻¹ : Bp p.val a b) * x * (w p : Bp p.val a b) ∈ R.completion p.val ↔ _
  by_cases hp : R.completion p.val = S.completion p.val
  · simp [w, hp]
  · simpa [w, hp] using hu p x

/-- The rational left order of the reference class is its enhanced endomorphism
order once the local reference coordinates have been fixed. -/
theorem reference_leftRing_eq {R S : Order a b} {z : Adelic.FiniteUnits R}
    (h : ReferenceOrderCoordinates R S z) : (fromAdelic z).val.leftRing = S.ring := by
  ext x
  rw [mem_leftRing_iff]
  change (∀ p : Prime, _) ↔ x ∈ S.lattice
  rw [mem_iff_all_local S.full]
  apply forall_congr'
  intro p
  rw [← S.completion_toSubmodule]
  exact h p (toLocal p.val x)

/-- A local Hom factor measured at the reference is converted to the
detector's fixed right-ideal coordinates by multiplying on the right
by the reference's coordinate. -/
theorem mem_localRight_mul_reference {R S : Order a b} {z : Adelic.FiniteUnits R}
    (hz : ReferenceOrderCoordinates R S z) (p : Prime) (u : (Bp p.val a b)ˣ)
    (x : Bp p.val a b) :
    x * (z.val p : Bp p.val a b) ∈ localRight R p (u * z.val p) ↔ x ∈ localRight S p u := by
  rw [mem_localRight, mem_localRight, mul_inv_rev, Units.val_mul]
  rw [show ((↑(z.val p)⁻¹ : Bp p.val a b) * (↑u⁻¹ : Bp p.val a b)) *
      (x * (z.val p : Bp p.val a b)) =
      (↑(z.val p)⁻¹ : Bp p.val a b) * ((↑u⁻¹ : Bp p.val a b) * x) *
        (z.val p : Bp p.val a b) by simp only [mul_assoc]]
  exact hz p _

/-- Choose representatives of actual Hom ideals in the geometric frame.
At the labelling origin the relative right lattice is the enhanced order. -/
noncomputable def relativeReferenceRead (S : Order a b) {D : Type*}
    (x₀ : D) [DecidableEq D] (I : D → LPIdeal S) (x : D) : Adelic.FiniteUnits S :=
  if x = x₀ then 1 else Classical.choose (exists_adelic_representative (I x))

@[simp] theorem relativeReferenceRead_base (S : Order a b) {D : Type*}
    (x₀ : D) [DecidableEq D] (I : D → LPIdeal S) :
    relativeReferenceRead S x₀ I x₀ = 1 := by
  simp [relativeReferenceRead]

theorem relativeReferenceRead_spec (S : Order a b) {D : Type*}
    (x₀ : D) [DecidableEq D] (I : D → LPIdeal S)
    (h₀ : I x₀ = fromAdelic (1 : Adelic.FiniteUnits S)) (x : D) :
    fromAdelic (relativeReferenceRead S x₀ I x) = I x := by
  by_cases hx : x = x₀
  · subst x
    simpa using h₀.symm
  · simpa [relativeReferenceRead, hx] using Classical.choose_spec (exists_adelic_representative (I x))

/-- A change of reference is a restricted product since the two
rational orders agree at all but finitely many primes. -/
noncomputable def multiplyReference {R S : Order a b} (w : Adelic.FiniteUnits S)
    (z : Adelic.FiniteUnits R) : Adelic.FiniteUnits R :=
  ⟨fun p => w.val p * z.val p, by
    apply (w.property.union (z.property.union (finite_localLattice_ne S.full R.full))).subset
    intro p hp
    by_contra! hm
    change ¬ (w.val p ∉ Adelic.localUnits S p ∨
      z.val p ∉ Adelic.localUnits R p ∨ localLattice p.val S.lattice ≠ localLattice p.val R.lattice)
      at hm
    have hw : w.val p ∈ Adelic.localUnits S p := not_not.mp (not_or.mp hm).1
    have hz : z.val p ∈ Adelic.localUnits R p := not_not.mp (not_or.mp (not_or.mp hm).2).1
    have he' : localLattice p.val S.lattice = localLattice p.val R.lattice :=
      not_not.mp (not_or.mp (not_or.mp hm).2).2
    have he : S.completion p.val = R.completion p.val := by
      apply Subalgebra.toSubmodule_injective
      rw [S.completion_toSubmodule, R.completion_toSubmodule]
      exact he'
    have hw' : w.val p ∈ Adelic.localUnits R p := by
      change (w.val p : Bp p.val a b) ∈ S.completion p.val ∧
        (↑(w.val p)⁻¹ : Bp p.val a b) ∈ S.completion p.val at hw
      change (w.val p : Bp p.val a b) ∈ R.completion p.val ∧
        (↑(w.val p)⁻¹ : Bp p.val a b) ∈ R.completion p.val
      rwa [he] at hw
    exact hp ((Adelic.localUnits R p).mul_mem hw' hz)⟩

@[simp] theorem multiplyReference_one {R S : Order a b} (z : Adelic.FiniteUnits R) :
    multiplyReference (1 : Adelic.FiniteUnits S) z = z := by
  apply Subtype.ext
  funext p
  exact one_mul _

/-- Equality of relative local lattices in the geometric frame amounts
to equality of the two detector right lattices at that prime. -/
theorem localRight_mul_reference_eq_iff {R S : Order a b} {z : Adelic.FiniteUnits R}
    (hz : ReferenceOrderCoordinates R S z) (p : Prime)
    (u v : (Bp p.val a b)ˣ) :
    localRight R p (u * z.val p) = localRight R p (v * z.val p) ↔
      localRight S p u = localRight S p v := by
  constructor
  · intro h
    ext x
    rw [← mem_localRight_mul_reference hz p u, ← mem_localRight_mul_reference hz p v, h]
  · intro h
    ext y
    have hy : y * (↑(z.val p)⁻¹ : Bp p.val a b) * (z.val p : Bp p.val a b) = y := by
      rw [mul_assoc, Units.inv_mul, mul_one]
    conv_lhs => rw [← hy]
    conv_rhs => rw [← hy]
    rw [mem_localRight_mul_reference hz p u, mem_localRight_mul_reference hz p v, h]

/-- Read the family of geometric Hom lattices in the detector coordinates
of the same reference. The identity quotient is read as the reference. -/
noncomputable def geometricReferenceRead {R S : Order a b} (z : Adelic.FiniteUnits R)
    {D : Type*} (x₀ : D) [DecidableEq D] (I : D → LPIdeal S) : D → Adelic.FiniteUnits R :=
  fun x => multiplyReference (relativeReferenceRead S x₀ I x) z

@[simp] theorem geometricReferenceRead_base {R S : Order a b} (z : Adelic.FiniteUnits R)
    {D : Type*} (x₀ : D) [DecidableEq D] (I : D → LPIdeal S) :
    geometricReferenceRead z x₀ I x₀ = z := by
  simp [geometricReferenceRead]

/-- Test an adelic quotient factor against the completed geometric Hom
ideal. This gives the local equality in the assembly theorem when the
prime-to-level quotient has been placed in the common model. -/
theorem geometricReferenceRead_local {R S : Order a b} {z : Adelic.FiniteUnits R}
    (hz : ReferenceOrderCoordinates R S z) {D : Type*} (x₀ : D) [DecidableEq D]
    (I : D → LPIdeal S) (h₀ : I x₀ = fromAdelic (1 : Adelic.FiniteUnits S))
    (x : D) (p : Prime) (u : (Bp p.val a b)ˣ) :
    localRight R p (u * z.val p) = localRight R p ((geometricReferenceRead z x₀ I x).val p) ↔
      localRight S p u = localLattice p.val (I x).val.lattice := by
  change _ = localRight R p ((relativeReferenceRead S x₀ I x).val p * z.val p) ↔ _
  rw [localRight_mul_reference_eq_iff hz,
    ← fromAdelic_completion, relativeReferenceRead_spec S x₀ I h₀ x]

/-- The unit test at a framed reference. In any semilocal coordinates
the single hypothesis on the integral CM action says its integral
closure lies in the completed geometric order. Finiteness gives the
reverse containment, including at split primes. -/
theorem reference_hunit {F : Type*} [Field F] [NumberField F]
    {R S : Order a b} {z : Adelic.FiniteUnits R} (hz : ReferenceOrderCoordinates R S z)
    (j : 𝔸ᶠ[𝓞 F, F]ˣ →* Adelic.FiniteUnits R)
    (L : Prime → Type) [∀ p, CommRing (L p)] [∀ p : Prime, Algebra ℤ_[p.val] (L p)]
    (ι : ∀ p : Prime, L p →ₐ[ℤ_[p.val]] Bp p.val a b)
    (inj : ∀ p : Prime, Function.Injective (ι p))
    (hO : ∀ p : Prime, integralClosure ℤ_[p.val] (L p) ≤ (S.completion p.val).comap (ι p))
    (components : ∀ p : Prime, 𝔸ᶠ[𝓞 F, F]ˣ →* (L p)ˣ)
    (hcomponents : ∀ s : 𝔸ᶠ[𝓞 F, F]ˣ, s ∈ FiniteAdeleRing.integralUnits (𝓞 F) F ↔
      ∀ p : Prime, IsIntegral ℤ_[p.val] (components p s : L p) ∧
        IsIntegral ℤ_[p.val] (↑(components p s)⁻¹ : L p))
    (hj : ∀ (s : 𝔸ᶠ[𝓞 F, F]ˣ) (p : Prime),
      (j s).val p = Units.map (ι p).toMonoidHom (components p s)) :
    ∀ s : 𝔸ᶠ[𝓞 F, F]ˣ, z⁻¹ * j s * z ∈ Adelic.integralUnits R ↔
      s ∈ FiniteAdeleRing.integralUnits (𝓞 F) F := by
  intro s
  rw [hcomponents]
  change (∀ p : Prime, (z.val p)⁻¹ * (j s).val p * z.val p ∈ Adelic.localUnits R p) ↔ _
  apply forall_congr'
  intro p
  have hS := localLattice_full p S.full
  rw [← S.completion_toSubmodule] at hS
  let : Module.Finite ℤ_[p.val] (S.completion p.val) := Module.Finite.of_fg hS.fg
  change ((↑((z.val p)⁻¹ * (j s).val p * z.val p) : Bp p.val a b) ∈ R.completion p.val ∧
    (↑((z.val p)⁻¹ * (j s).val p * z.val p)⁻¹ : Bp p.val a b) ∈ R.completion p.val) ↔ _
  rw [mul_inv_rev, mul_inv_rev, inv_inv]
  simp only [Units.val_mul]
  rw [← mul_assoc (↑(z.val p)⁻¹ : Bp p.val a b) (↑((j s).val p)⁻¹ : Bp p.val a b)]
  rw [hz p ((j s).val p : Bp p.val a b), hz p (↑((j s).val p)⁻¹ : Bp p.val a b)]
  rw [hj s p, ← map_inv]
  exact isOrderUnit_iff_isIntegral_and_inv (ι p) (inj p) _ (hO p) (components p s)

end ZInQ.Manuscript.RC.HCMV21
