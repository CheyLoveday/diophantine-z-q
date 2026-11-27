import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.SignAxes
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.NonVacuity

/-!
# Detecting primes, part 3: the GLUE in its provable shape

Item (c) of the detecting-prime work. The switch GLUE `DetectingPrime T loc c₊ c₋`
(`SignSplitting.lean`) fixes the localization `loc` at a prime already chosen, and is false for a
zero class. Its provable form, `DetectingPrimeExists T loc c₊ c₋`, takes the localizations
`loc q` at all candidate new inert derivative primes `q ∈ P` and asserts, for nonzero `c₊ ∈ V₊`,
`c₋ ∈ V₋`, that some `q` detects both; likewise `DetectingPrimePlusExists` for one sign. All
`PROVED` except the two GLUE definitions themselves:

* `exists_detectingPrime`, `exists_detectingPrimePlus`: bridges to the fixed-prime GLUE at the
  chosen `q`, for every consumer that fixes the prime;
* `detectingPrimeExists_of_fixed`: the old form at one prime gives the new one;
* `detectionFields_of_exists`, `quadSignFields_of_exists`: SignSplitting's `hdetp`/`hdetm` and
  all quadratic sign fields from the existence form, when the local hypotheses hold at every new
  prime. The mixed-sign constructor `quadMixedDimsOfInputs` (`SignAxes.lean`) takes the
  fixed-prime GLUE at the prime given by `exists_detectingPrime`;
* `detectingPrimeExists_example`: non-vacuity.

What remains to prove `DetectingPrimeExists` (detecting-prime sizing):
* item 1, the bridge from the switch fibres (SelmerDuality models) to the genuine continuous
  Galois cohomology;
* item 5, RC16's exactness (5.4).

Two pieces are proved, in `Detecting/Localization.lean` and `Detecting/Frobenius.lean`:
localization at an unramified prime as evaluation at the Frobenius, and the Frobenius half of the
Chebotarev realization.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open Module ZInQ.Manuscript.RC.Uniform.QuadraticCase

section Exists

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] {P : Type}

/-- **The detecting prime in its provable shape** (tex L5086–5115, Lemma
`ex:limits-kernel-detection`): for NONZERO classes `c₊ ∈ V₊`, `c₋ ∈ V₋` there EXISTS a new inert
derivative prime `q ∈ P` whose localization `loc q` detects both. Classification: GLUE (input).
What remains to prove it (detecting-prime sizing, notes): item 1, the bridge from the switch
fibres (SelmerDuality models) to the genuine continuous Galois cohomology; and item 5, RC16's
exactness (5.4) of `ExactChebotarevRealization`. Localization at an unramified prime as evaluation
at the Frobenius (`Detecting.localization_eq_frobValue`) and the Frobenius half of the Chebotarev
realization (`Detecting.exactChebotarevRealization_of_exactness`) are proved. -/
def DetectingPrimeExists (T : V →ₗ[k] V) (loc : P → V →ₗ[k] (Fin 2 → k) × (Fin 2 → k))
    (cp cm : V) : Prop :=
  cp ≠ 0 → cm ≠ 0 → T cp = cp → T cm = -cm → ∃ q : P, loc q cp ≠ 0 ∧ loc q cm ≠ 0

/-- **The detecting prime for one sign, provable shape.** -/
def DetectingPrimePlusExists (T : V →ₗ[k] V) (loc : P → V →ₗ[k] (Fin 2 → k) × (Fin 2 → k))
    (cp : V) : Prop :=
  cp ≠ 0 → T cp = cp → ∃ q : P, loc q cp ≠ 0

/-- **Bridge to the fixed-prime GLUE** (`PROVED`): for nonzero classes of the two signs, the
existence form gives a prime `q` at which the old `DetectingPrime` holds. -/
theorem exists_detectingPrime {T : V →ₗ[k] V} {loc : P → V →ₗ[k] (Fin 2 → k) × (Fin 2 → k)}
    {cp cm : V} (h : DetectingPrimeExists T loc cp cm) (hp0 : cp ≠ 0) (hm0 : cm ≠ 0)
    (hcp : T cp = cp) (hcm : T cm = -cm) : ∃ q : P, DetectingPrime T (loc q) cp cm := by
  obtain ⟨q, h1, h2⟩ := h hp0 hm0 hcp hcm
  exact ⟨q, fun _ _ => ⟨h1, h2⟩⟩

/-- **Bridge for one sign** (`PROVED`). -/
theorem exists_detectingPrimePlus {T : V →ₗ[k] V} {loc : P → V →ₗ[k] (Fin 2 → k) × (Fin 2 → k)}
    {cp : V} (h : DetectingPrimePlusExists T loc cp) (hp0 : cp ≠ 0) (hcp : T cp = cp) :
    ∃ q : P, DetectingPrimePlus T (loc q) cp := by
  obtain ⟨q, h1⟩ := h hp0 hcp
  exact ⟨q, fun _ => h1⟩

/-- The old fixed-prime GLUE gives the existence form at any one prime (`PROVED`). -/
theorem detectingPrimeExists_of_fixed {T : V →ₗ[k] V} {loc : P → V →ₗ[k] (Fin 2 → k) × (Fin 2 → k)}
    {cp cm : V} (q : P) (h : DetectingPrime T (loc q) cp cm) : DetectingPrimeExists T loc cp cm :=
  fun _ _ hcp hcm => ⟨q, h hcp hcm⟩

end Exists

/-- **The detection fields from the existence form** (`PROVED`, by `exists_detectingPrime` and
`detectionFields_proof`): if the equivariance, the membership in `U_q` and the finiteness of the
localizations hold at every new prime `q` (as they do for every new inert derivative prime), then
some new prime `q` has `U_q ⊓ H_±` containing a nonzero vector of its finite axis (the fields
`hdetp`, `hdetm`). -/
theorem detectionFields_of_exists {k : Type} [Field k] (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (ep em : Fin 2 → k) (h2 : (2 : k) ≠ 0) (hp : J ep = ep) (hm : J em = -em) (he : e₂ ep em ≠ 0)
    {V : Type} [AddCommGroup V] [Module k V] (T : V →ₗ[k] V) {P : Type}
    (loc : P → V →ₗ[k] (Fin 2 → k) × (Fin 2 → k)) (U : P → Submodule k ((Fin 2 → k) × (Fin 2 → k)))
    (cp cm : V) (hloc : ∀ q v, loc q (T v) = localInv J (loc q v)) (hcp : T cp = cp)
    (hcm : T cm = -cm) (hp0 : cp ≠ 0) (hm0 : cm ≠ 0)
    (hUp : ∀ q, loc q cp ∈ U q) (hUm : ∀ q, loc q cm ∈ U q) (hFp : ∀ q, (loc q cp).2 = 0)
    (hFm : ∀ q, (loc q cm).2 = 0) (hex : DetectingPrimeExists T loc cp cm) :
    ∃ q : P, (∃ x ∈ U q ⊓ signPlane ep em, x ∈ finAxis ep ∧ x ≠ 0) ∧
      (∃ x ∈ U q ⊓ signPlane em ep, x ∈ finAxis em ∧ x ≠ 0) := by
  obtain ⟨q, hq⟩ := exists_detectingPrime hex hp0 hm0 hcp hcm
  exact ⟨q, detectionFields_proof k J ep em h2 hp hm he V T (loc q) (U q) cp cm (hloc q) hcp hcm
    (hUp q) (hUm q) (hFp q) (hFm q) hq⟩

/-- **All quadratic sign fields from the existence form** (`PROVED`, by `exists_detectingPrime`
and `quadSignFields_proof`): the data of `QuadSignFields` at some new prime `q`, when the local
hypotheses (stability and self-annihilation of `U_q`, equivariance, membership and finiteness of
the localizations) hold at every new prime. -/
theorem quadSignFields_of_exists {k : Type} [Field k] (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (ε : k)
    (h2 : (2 : k) ≠ 0) (hε : ε ≠ 0) (hJ2 : J ∘ₗ J = LinearMap.id) (hdet : LinearMap.det J = -1)
    {P : Type} (U : P → Submodule k ((Fin 2 → k) × (Fin 2 → k)))
    (hσ : ∀ q, ∀ u ∈ U q, localInv J u ∈ U q)
    (hU : ∀ q u, u ∈ U q ↔ ∀ w ∈ U q, localPair ε J u w = 0)
    {V : Type} [AddCommGroup V] [Module k V] (T : V →ₗ[k] V)
    (loc : P → V →ₗ[k] (Fin 2 → k) × (Fin 2 → k)) (cp cm : V)
    (hloc : ∀ q v, loc q (T v) = localInv J (loc q v)) (hcp : T cp = cp) (hcm : T cm = -cm)
    (hp0 : cp ≠ 0) (hm0 : cm ≠ 0) (hUp : ∀ q, loc q cp ∈ U q) (hUm : ∀ q, loc q cm ∈ U q)
    (hFp : ∀ q, (loc q cp).2 = 0) (hFm : ∀ q, (loc q cm).2 = 0)
    (hex : DetectingPrimeExists T loc cp cm) :
    ∃ q : P, ∃ (ep em : Fin 2 → k) (Up Um : Submodule k ((Fin 2 → k) × (Fin 2 → k))),
      J ep = ep ∧ J em = -em ∧ e₂ ep em ≠ 0 ∧
      IsSelfAnnihilatingIn ε J (signPlane ep em) Up ∧
      IsSelfAnnihilatingIn ε J (signPlane em ep) Um ∧
      (∃ x ∈ Up, x ∈ finAxis ep ∧ x ≠ 0) ∧ (∃ x ∈ Um, x ∈ finAxis em ∧ x ≠ 0) ∧
      U q = Up ⊔ Um := by
  obtain ⟨q, hq⟩ := exists_detectingPrime hex hp0 hm0 hcp hcm
  exact ⟨q, quadSignFields_proof k J ε h2 hε hJ2 hdet (U q) (hσ q) (hU q) V T (loc q) cp cm
    (hloc q) hcp hcm (hUp q) (hUm q) (hFp q) (hFm q) hq⟩

/-- **Non-vacuity of the existence forms** (`PROVED`): the model of `SwitchInputs.NonVacuity`
(`J₀ = diag(1, −1)` on `ℚ²`, localization `inl`, classes `e₊`, `e₋`), with one candidate prime. -/
theorem detectingPrimeExists_example :
    DetectingPrimeExists J₀L (fun _ : Unit => exLoc) eP eM ∧
      DetectingPrimePlusExists J₀L (fun _ : Unit => exLoc) eP :=
  ⟨detectingPrimeExists_of_fixed () exDetectingPrime,
    fun hp0 hcp => ⟨(), exDetectingPrimePlus hcp⟩⟩


end ZInQ.Contrib.CloudB3RC53.SwitchInputs
