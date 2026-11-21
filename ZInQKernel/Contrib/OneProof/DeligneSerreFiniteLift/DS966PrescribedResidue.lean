import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import Mathlib.NumberTheory.NumberField.Basic

/-!
# The prescribed reduction at a finite place

For a map from the integers of a number field to a field of positive
characteristic, the kernel is the place. The canonical residue equivalence for
completion extends the original map uniquely; it does not leave a choice of an
automorphism of the residue field. This is the local comparison needed in the
same-quotient Deligne–Serre lift.
-/

noncomputable section

namespace DS966Small

open NumberField IsDedekindDomain
open scoped NumberField

variable {K k : Type*} [Field K] [NumberField K] [Field k]

/-- The kernel of a reduction to positive characteristic is nonzero.
Kind: PROVED. -/
theorem ker_reduction_ne_bot (f : 𝓞 K →+* k) {ℓ : ℕ} [CharP k ℓ] (hℓ : ℓ ≠ 0) :
    RingHom.ker f ≠ ⊥ := by
  intro he
  have hmem : (ℓ : 𝓞 K) ∈ RingHom.ker f := RingHom.mem_ker.mpr (by
    rw [map_natCast, CharP.cast_eq_zero k ℓ])
  exact (Nat.cast_ne_zero.mpr hℓ : (ℓ : 𝓞 K) ≠ 0) (by simpa [he] using hmem)

/-- The finite place determined by a reduction, with no choice of a prime
above its characteristic. Kind: definition. -/
def placeOfReduction (f : 𝓞 K →+* k) {ℓ : ℕ} [CharP k ℓ] (hℓ : ℓ ≠ 0) :
    HeightOneSpectrum (𝓞 K) :=
  ⟨RingHom.ker f, RingHom.ker_isPrime f, ker_reduction_ne_bot f hℓ⟩

/-- The map on the actual residue field of the completion's integer ring;
it is obtained via the existing quotient isomorphism. Kind: definition. -/
def completedResidueMap (f : 𝓞 K →+* k) (v : HeightOneSpectrum (𝓞 K))
    (hv : v.asIdeal = RingHom.ker f) :
    (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) →+* k :=
  (Ideal.Quotient.lift v.asIdeal f (fun _ ha => RingHom.mem_ker.mp (hv ▸ ha))).comp
    (v.residueFieldEquivAdicCompletionIntegers (K := K)).symm.toRingHom

/-- The completed residue map agrees exactly with the given reduction on global
integers. Kind: PROVED. -/
theorem completedResidueMap_apply_global (f : 𝓞 K →+* k) (v : HeightOneSpectrum (𝓞 K))
    (hv : v.asIdeal = RingHom.ker f) (a : 𝓞 K) :
    completedResidueMap f v hv
      (IsLocalRing.residue _ (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a)) = f a := by
  have he := v.residueFieldEquivAdicCompletionIntegers_apply_mk (K := K) a
  rw [← show v.residueFieldEquivAdicCompletionIntegers (K := K)
      (Ideal.Quotient.mk v.asIdeal a) =
      IsLocalRing.residue (v.adicCompletionIntegers K)
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) from he]
  unfold completedResidueMap
  rw [RingHom.comp_apply]
  have hsym := (v.residueFieldEquivAdicCompletionIntegers (K := K)).symm_apply_apply
    (Ideal.Quotient.mk v.asIdeal a)
  -- Avoid unfolding the completion's residue-field instances while rewriting.
  exact (congrArg (Ideal.Quotient.lift v.asIdeal f
      (fun _ ha => RingHom.mem_ker.mp (hv ▸ ha))) hsym).trans
    (Ideal.Quotient.lift_mk _ _ _)

/-- The extension to the residue field is unique. In particular it cannot be
replaced by an arbitrary Frobenius twist. Kind: PROVED. -/
theorem completedResidueMap_unique (f : 𝓞 K →+* k) (v : HeightOneSpectrum (𝓞 K))
    (hv : v.asIdeal = RingHom.ker f)
    (g : IsLocalRing.ResidueField (v.adicCompletionIntegers K) →+* k)
    (hg : ∀ a : 𝓞 K, g (IsLocalRing.residue _ (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a)) = f a) :
    g = completedResidueMap f v hv := by
  ext x
  obtain ⟨y, rfl⟩ := (v.residueFieldEquivAdicCompletionIntegers (K := K)).surjective x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [v.residueFieldEquivAdicCompletionIntegers_apply_mk]
  exact (hg a).trans (completedResidueMap_apply_global f v hv a).symm

/-- For the very place defined by the prescribed positive-characteristic
reduction, there is exactly one compatible residue embedding.
Kind: PROVED. -/
theorem existsUnique_completedResidueMap (f : 𝓞 K →+* k) {ℓ : ℕ} [CharP k ℓ] (hℓ : ℓ ≠ 0) :
    let v := placeOfReduction f hℓ
    ∃! g : IsLocalRing.ResidueField (v.adicCompletionIntegers K) →+* k,
      ∀ a : 𝓞 K, g (IsLocalRing.residue _ (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a)) = f a := by
  let v := placeOfReduction f hℓ
  exact ⟨completedResidueMap f v rfl, completedResidueMap_apply_global f v rfl,
    fun g hg => completedResidueMap_unique f v rfl g hg⟩

end DS966Small
