import ZInQKernel.Contrib.CloudB3E2Norm.LocalComponents
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Kummer.SqrtMem
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RingClass.Field

/-!
# Ring class fields inside `K_S`, and the open stabilizers of the norm identity

Manuscript `diophantine_zq.tex`, tex 2779–2796 (the ring class fields `H_{r_i}` of the family) and
tex 4157–4170 (the norm identity over `G_{K,S}`). The Galois group of the genuine Selmer complexes
is `G_{K,S} = Gal(K_S/K)` with `K_S = unramifiedOutside K S ⊆ K̄` (the compositum of the finite
Galois subextensions unramified outside `S`). Tau Ceti's ring class field
`TauCeti.ClassFieldTheory.ringClassField O` of an order `O` lives in the separable closure
`Kˢ = separableClosure K K̄` and is unramified at every prime not dividing the conductor of `O`
(`isUnramifiedAt_ringClassField`).

* `toAlgClosure L` (definition): an intermediate field of `Kˢ/K` read in `K̄`;
  `isUnramifiedOutside_toAlgClosure` (PROVED): Mathlib's unramifiedness of the primes of `𝓞 L`
  over every `v ∉ S` gives the `K_S` notion `IsUnramifiedOutside K S` (transport of ramification
  indices along `𝓞 (L.map) ≃ₐ[𝓞 K] 𝓞 L`, the RC53 group's `isUnramifiedOutside_iff` and
  `forall_ramificationIdx_eq_one_of_equiv`).
* **`ringClassField_le_KS`** (PROVED): if `S` contains every prime dividing the conductor of `O`,
  the ring class field of `O` lies in `K_S`.
* **`ringClassFieldS O hS`** (definition): the ring class field as an intermediate field of
  `K_S/K`; `finiteDimensional_ringClassFieldS`, `isOpen_fixS_ringClassFieldS` (PROVED): its fixing
  subgroup `G_{H,S}` is open in `G_{K,S}`.
* **`exists_gval_of_fixS`** (PROVED): the open-stabilizer witness for `exists_gval_eq_transfer`:
  if the weighted sum `P̃` is fixed by the twisted action of every element of `fixS F` for a finite
  subextension `F` of `K_S/K` (e.g. `F = ringClassFieldS O hS` composed with a field of definition
  of the points), a genuine continuous cochain carrying `act(g₀) P̃ − P̃` exists.
* Non-vacuity: `nonVacuity_ringClassField` (the maximal order, whose conductor is the unit ideal,
  so `S = ∅` works).

**What remains**: (1) the compatibility of `ringClassFieldS` with the tree's `HeegnerPointData.H`
(fields `H_d ⊆ ℚ̄` over `ℚ`): an embedding `K_S → ℚ̄` over `K ⊆ ℚ̄` carrying the ring class field of
the order of conductor `d` to `H_d`; (2) the fields of definition of the points `y_T` (finite
extensions of the ring class fields inside `K_S`, by good reduction outside `S`) and the triviality
of the twisted action on `P̃` over them (the character is trivial on `G_{H_T}`, `GlobalChar.lean`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.RankCounts (IsUnramifiedOutside unramifiedOutside)
open ZInQ.Contrib.CloudB3RC53.RankCounts.KummerS (isUnramifiedOutside_iff
  forall_ramificationIdx_eq_one_of_equiv)
open ZInQ.Manuscript.RC.CoefModules (KS fixS isOpen_fixS)
open ZInQ.Manuscript.RC.SelmerComplex (GKS)

variable {K : Type} [Field K] [NumberField K]

/-- **An intermediate field of `Kˢ/K` read in `K̄`**: its image under the inclusion
`Kˢ = separableClosure K K̄ → K̄`. Kind: definition. -/
def toAlgClosure (L : IntermediateField K (SeparableClosure K)) :
    IntermediateField K (AlgebraicClosure K) :=
  L.map (separableClosure K (AlgebraicClosure K)).val

instance finiteDimensional_toAlgClosure (L : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K L] : FiniteDimensional K (toAlgClosure L) :=
  LinearEquiv.finiteDimensional (IntermediateField.equivMap L _).toLinearEquiv

/-- A finite subextension of `Kˢ/K` is a number field. -/
instance numberField_of_finiteDimensional_sep (L : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K L] : NumberField L :=
  @NumberField.mk _ _ inferInstance (Module.Finite.trans K L)

/-- **Unramified outside `S`, transported to `K̄`** (PROVED): if every prime of `𝓞 L` above every
`v ∉ S` is unramified over `𝓞 K`, then the image of `L` in `K̄` is unramified outside `S` in the
sense of `K_S`. -/
theorem isUnramifiedOutside_toAlgClosure (S : Set (HeightOneSpectrum (𝓞 K)))
    (L : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L]
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime]
      [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q) :
    IsUnramifiedOutside K S (toAlgClosure L) := by
  rw [isUnramifiedOutside_iff]
  intro v hv
  rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  refine forall_ramificationIdx_eq_one_of_equiv
    (RingOfIntegers.mapAlgEquiv (IntermediateField.equivMap L
      (separableClosure K (AlgebraicClosure K)).val).symm) v.asIdeal ?_
  intro P hP hPv
  have := h v hv P
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

section RingClass

open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder

variable (O : NumberFieldOrder K)

/-- **The ring class field lies in `K_S`** (PROVED) when `S` contains every prime dividing the
conductor of `O`: it is finite, normal (abelian) and unramified outside `S`. -/
theorem ringClassField_le_KS (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ O.conductor → v ∈ S) :
    toAlgClosure (ringClassField O) ≤ unramifiedOutside K S := by
  have hU : IsUnramifiedOutside K S (toAlgClosure (ringClassField O)) :=
    isUnramifiedOutside_toAlgClosure S (ringClassField O) fun v hv Q _ _ =>
      isUnramifiedAt_ringClassField O (fun hd => hv (hS v hd)) Q
  have hN : Normal K (toAlgClosure (ringClassField O)) :=
    Normal.of_algEquiv (IntermediateField.equivMap (ringClassField O)
      (separableClosure K (AlgebraicClosure K)).val)
  exact le_iSup₂_of_le (f := fun (L : IntermediateField K (AlgebraicClosure K))
    (_ : FiniteDimensional K L ∧ Normal K L ∧ IsUnramifiedOutside K S L) => L)
    (toAlgClosure (ringClassField O)) ⟨inferInstance, hN, hU⟩ le_rfl

/-- **The ring class field as an intermediate field of `K_S/K`** (for `S` containing the primes
of the conductor). Kind: definition. -/
def ringClassFieldS (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ O.conductor → v ∈ S) :
    IntermediateField K (KS K S) :=
  IntermediateField.restrict (ringClassField_le_KS O S hS)

instance finiteDimensional_ringClassFieldS (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ O.conductor → v ∈ S) :
    FiniteDimensional K (ringClassFieldS O S hS) :=
  LinearEquiv.finiteDimensional
    (IntermediateField.restrictAlgEquiv (ringClassField_le_KS O S hS)).toLinearEquiv

/-- **`G_{H,S}` is open in `G_{K,S}`**: the fixing subgroup of the ring class field.
Kind: PROVED. -/
theorem isOpen_fixS_ringClassFieldS (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ O.conductor → v ∈ S) :
    IsOpen (fixS K S (ringClassFieldS O S hS) : Set (GKS K S)) :=
  isOpen_fixS K S _

end RingClass

/-! ### The open-stabilizer witness -/

section Witness

set_option linter.unusedSectionVars false

variable (S : Set (HeightOneSpectrum (𝓞 K)))
  {k : Type} [Field k] [TopologicalSpace k]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M] {D : Type} [AddCommGroup D] [Module k D]

/-- **The open-stabilizer witness of `exists_gval_eq_transfer`** (PROVED): for a finite
subextension `F` of `K_S/K` whose fixing subgroup fixes the weighted sum `P̃` under the action,
a genuine continuous `1`-cochain `z` with `ι(z g) = act(g₀) P̃ − P̃` exists, provided the values lie
in `ι(M)`. -/
theorem exists_gval_of_fixS (F : IntermediateField K (KS K S)) [FiniteDimensional K F]
    (ι : M →ₗ[k] D) (hι : Function.Injective ι) (act : GKS K S → D → D)
    (hact : ∀ g h : GKS K S, act (g * h) = act g ∘ act h) (P : D)
    (hFP : ∀ v ∈ fixS K S F, act v P = P)
    (himg : ∀ g : GKS K S, ∃ m : M, ι m = act g P - P) :
    ∃ z : (ZInQ.Manuscript.RC.SelmerComplex.globalCx k (GKS K S) M).X 1,
      ∀ g : Fin 1 → GKS K S, ι (gval z g) = act (g 0) P - P :=
  exists_gval_eq_transfer ι hι act hact P (fixS K S F) (isOpen_fixS K S F) hFP himg

end Witness

/-! ### Non-vacuity -/

/-- **Non-vacuity of the hypothesis of `ringClassField_le_KS`**: for the maximal order (whose
conductor is the unit ideal, so no prime divides it) the empty set of places works; so its ring
class field lies in `K_∅`. Kind: PROVED. -/
theorem nonVacuity_ringClassField :
    ∀ v : HeightOneSpectrum (𝓞 K),
      v.asIdeal ∣ (TauCeti.GlobalNumberFields.maximalNumberFieldOrder K).conductor →
        v ∈ (∅ : Set (HeightOneSpectrum (𝓞 K))) := by
  intro v hv
  rw [TauCeti.GlobalNumberFields.NumberFieldOrder.conductor_maximal, Ideal.dvd_iff_le,
    top_le_iff] at hv
  exact absurd hv v.isPrime.ne_top

end ZInQ.Contrib.CloudB3E2.NormCochain
