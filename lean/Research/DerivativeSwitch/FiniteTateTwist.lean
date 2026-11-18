import Research.DerivativeSwitch.ArithmeticSelmer
import Research.DerivativeSwitch.ConjugateWeilPairing
import Research.DerivativeSwitch.ContinuousCup
import Research.DerivativeSwitch.FiniteSelmerCoefficients
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The finite cyclotomic coefficient line

The character records the action on a primitive root of unity in the
chosen closure. A supported cyclotomic extension allows it to descend to
the same global quotient used by the Selmer cone. The coefficient line
extends the resulting character to the retained scalar or group ring.
-/

namespace Research.DerivativeSwitch.FiniteTateTwist

open ArithmeticSelmer ConjugateWeilPairing FiniteSelmerCoefficients
open ContinuousCup

noncomputable section

variable {F : Type} [Field F] {i : ℕ} {ζ : AlgebraicClosure F}

local instance : NeZero (2 ^ (i + 1)) := ⟨by positivity⟩

theorem exists_primitiveRoot [CharZero F] (i : ℕ) :
    ∃ ζ : AlgebraicClosure F, IsPrimitiveRoot ζ (2 ^ (i + 1)) := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure F)
    (n := 2 ^ i) (by positivity)
  have hpow : x ^ (2 ^ (i + 1)) = 1 := by
    rw [pow_succ, pow_mul, hx]
    norm_num
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
  have hlast : j = i + 1 := by
    by_contra h
    have hle : j ≤ i := by omega
    have hdiv : orderOf x ∣ 2 ^ i := hj' ▸ pow_dvd_pow 2 hle
    have he := orderOf_dvd_iff_pow_eq_one.mp hdiv
    rw [hx] at he
    norm_num at he
  exact ⟨x, IsPrimitiveRoot.iff_orderOf.mpr (hlast ▸ hj')⟩

def absoluteCharacter (hζ : IsPrimitiveRoot ζ (2 ^ (i + 1))) :
    Field.absoluteGaloisGroup F →* (Base (i + 1))ˣ := hζ.autToPow F

theorem absoluteCharacter_spec (hζ : IsPrimitiveRoot ζ (2 ^ (i + 1)))
    (g : Field.absoluteGaloisGroup F) :
    ζ ^ (absoluteCharacter hζ g : Base (i + 1)).val =
      (show AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F from g) ζ :=
  hζ.autToPow_spec F g

private theorem absoluteCharacter_eq_one_iff (hζ : IsPrimitiveRoot ζ (2 ^ (i + 1)))
    (g : Field.absoluteGaloisGroup F) : absoluteCharacter hζ g = 1 ↔
      (show AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F from g) ζ = ζ := by
  let inst : Fact (1 < 2 ^ (i + 1)) := ⟨one_lt_pow₀ (by decide) (by omega)⟩
  have h := absoluteCharacter_spec hζ g
  constructor
  · intro he
    rw [he, Units.val_one, ZMod.val_one, pow_one] at h
    exact h.symm
  · intro hg
    apply Units.ext
    apply ZMod.val_injective
    rw [Units.val_one, ZMod.val_one]
    exact hζ.pow_inj (ZMod.val_lt _) inst.out (h.trans (hg.trans (pow_one ζ).symm))

theorem absoluteCharacter_continuous (hζ : IsPrimitiveRoot ζ (2 ^ (i + 1)))
    [TopologicalSpace (Base (i + 1))ˣ] [DiscreteTopology (Base (i + 1))ˣ] :
    Continuous (absoluteCharacter hζ) := by
  apply continuous_of_continuousAt_one (absoluteCharacter hζ)
  rw [ContinuousAt, map_one, nhds_discrete ((Base (i + 1))ˣ), Filter.tendsto_pure]
  have he := (stabilizer_isOpen_of_isIntegral (K := F) ζ).mem_nhds
    (show (1 : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ∈ _ from Subgroup.one_mem _)
  apply Filter.Eventually.mono he
  intro g hg
  exact (absoluteCharacter_eq_one_iff hζ g).mpr hg

variable [NumberField F] (S : Finset (FinitePrime F))

omit [NumberField F] in
private theorem supportKernel_le_character (hζ : IsPrimitiveRoot ζ (2 ^ (i + 1)))
    (E : SupportedExtension F S) (hz : ζ ∈ E.carrier) :
    supportKernel F S ≤ (absoluteCharacter hζ).ker := by
  intro g hg
  have hfix : g ∈ E.carrier.fixingSubgroup :=
    (iInf_le (fun E : SupportedExtension F S => E.carrier.fixingSubgroup) E) hg
  exact MonoidHom.mem_ker.mpr ((absoluteCharacter_eq_one_iff hζ g).mpr
    ((IntermediateField.mem_fixingSubgroup_iff E.carrier g).mp hfix ζ hz))

def supportedCharacter (hζ : IsPrimitiveRoot ζ (2 ^ (i + 1)))
    (E : SupportedExtension F S) (hz : ζ ∈ E.carrier) : globalGroup F S →* (Base (i + 1))ˣ :=
  QuotientGroup.lift _ (absoluteCharacter hζ) (supportKernel_le_character S hζ E hz)

@[simp] theorem supportedCharacter_pullback (hζ : IsPrimitiveRoot ζ (2 ^ (i + 1)))
    (E : SupportedExtension F S) (hz : ζ ∈ E.carrier) (g : Field.absoluteGaloisGroup F) :
    supportedCharacter S hζ E hz (supportProjection F S g) = absoluteCharacter hζ g :=
  QuotientGroup.lift_mk _ _ _

theorem supportedCharacter_continuous (hζ : IsPrimitiveRoot ζ (2 ^ (i + 1)))
    (E : SupportedExtension F S) (hz : ζ ∈ E.carrier)
    [TopologicalSpace (Base (i + 1))ˣ] [DiscreteTopology (Base (i + 1))ˣ] :
    Continuous (supportedCharacter S hζ E hz) := by
  apply (QuotientGroup.isQuotientMap_mk (supportKernel F S)).continuous_iff.mpr
  change Continuous fun g => supportedCharacter S hζ E hz (supportProjection F S g)
  simpa only [supportedCharacter_pullback] using absoluteCharacter_continuous hζ

/-- The descended character restricts to the action on the transported
primitive root at the actual completion. -/
theorem supportedCharacter_at_place (hζ : IsPrimitiveRoot ζ (2 ^ (i + 1)))
    (E : SupportedExtension F S) (hz : ζ ∈ E.carrier) (v : FinitePrime F)
    (emb : PlaceEmbedding F v) (g : localGroup F v) :
    supportedCharacter S hζ E hz (placeLocalization F S v emb g) =
      absoluteCharacter (hζ.map_of_injective emb.injective) g := by
  change supportedCharacter S hζ E hz (supportProjection F S (absoluteLocalization F v emb g)) = _
  rw [supportedCharacter_pullback]
  apply Units.ext
  apply ZMod.val_injective
  have hlocal := hζ.map_of_injective emb.injective
  apply hlocal.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [← map_pow, absoluteCharacter_spec hζ, absoluteCharacter_spec hlocal]
  let alg : Algebra (AlgebraicClosure F) (AlgebraicClosure (completion F v)) := emb.toRingHom.toAlgebra
  let tower : IsScalarTower F (AlgebraicClosure F) (AlgebraicClosure (completion F v)) :=
    IsScalarTower.of_algebraMap_eq fun a => (emb.commutes a).symm
  let a : AlgebraicClosure (completion F v) ≃ₐ[completion F v] AlgebraicClosure (completion F v) := g
  exact (a.restrictScalars F).restrictNormal_commutes (AlgebraicClosure F) ζ

variable {R G : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Group G]

/-- The cyclotomic line over the selected finite coefficient ring. -/
def coefficientLine (base : Base (i + 1) →+* R) (chi : G →* (Base (i + 1))ˣ) : TopRep R G :=
  scalarTwist (TopRep.of (ContRepresentation.trivial R G R)) ((Units.map base.toMonoidHom).comp chi)

/-- The degree-one cochain cup for the twisted and conjugate carriers,
valued in the cyclotomic coefficient line on the supported group. -/
def conjugateCup11 (hζ : IsPrimitiveRoot ζ (2 ^ (i + 1)))
    (E : SupportedExtension F S) (hz : ζ ∈ E.carrier) (base : Base (i + 1) →+* R)
    (T : TopRep R (globalGroup F S)) (alpha : globalGroup F S →* Rˣ)
    (tau : globalGroup F S →* globalGroup F S) (e : T →ₗ[R] T →ₗ[R] R) (J : T ≃ₗ[R] T)
    (cont : Continuous fun xy : T × T => e xy.1 (J xy.2))
    (hAlpha : ∀ g, (alpha g : R) * (alpha (tau g) : R) = 1)
    (hJ : ∀ g y, J (T.ρ (tau g) y) = T.ρ g (J y))
    (hWeil : ∀ g x y, e (T.ρ g x) (T.ρ g y) =
      base (supportedCharacter S hζ E hz g) • e x y) :
    Cochain (scalarTwist T alpha) 1 →ₗ[R] Cochain (TopRep.res tau (scalarTwist T alpha)) 1 →ₗ[R]
      Cochain (coefficientLine base (supportedCharacter S hζ E hz)) 2 := by
  letI : CompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (CompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))
  let chi := (Units.map base.toMonoidHom).comp (supportedCharacter S hζ E hz)
  exact cup11 (paired T e J) cont
    (paired_equivariant T alpha e J tau chi hAlpha hJ hWeil)

end

end Research.DerivativeSwitch.FiniteTateTwist
