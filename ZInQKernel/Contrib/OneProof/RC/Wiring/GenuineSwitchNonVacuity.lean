import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchLeaf

/-!
**Theorem 5.3, Lane RC0 round 4: a genuine configuration family without switching data**

Non-vacuity and non-collapse checks for `IsGenuineFamilyAt` and `RegularityInputsG`
(`GenuineSwitchLeaf.lean`), at every prime `𝔭` of `Λ`:

* `exZeroFamily P`: the configuration family with one configuration whose fiber is lane RC26's
  genuine Selmer data `galoisSelData ℚ ∅ k 0 Δ` (`K = ℚ`, empty support, zero coefficient module,
  strict conditions), actual class and functional zero, moving variable `t = X`.
* `exZeroFamily_isGenuine` (PROVED): it is genuine at `𝔭`; the genuineness predicate is satisfiable.
* `exZeroFamily_h1` (PROVED): its fiber has `H¹ = 0` (all its terms are zero).
* `exZeroFamily_no_data` (PROVED): it carries no `GenuineSwitchData` at all, for every coordinate
  `u` (in particular for `u = 1 ∈ ι(Λ_𝔭)`). Over a fixed genuine family, the existence of switching
  data is a condition on the genuine fiber and not on the coordinate: no one-stage datum can be
  invented for this family.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC.Uniform Module NumberField
  IsDedekindDomain CategoryTheory

open ZInQ.Contrib.CloudB3RC53.PairedFunctional (SelData selCx selT)
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (SwitchFamily GenuineSwitchData)
open ZInQ.Manuscript.RC.SelmerComplex (GKS galoisSelData GaloisLocalConditions strictConditions)

section ZeroFamily

variable (P : Ideal Lambda) [P.IsPrime]

/-- The empty support for `K = ℚ`. -/
abbrev emptySupport : Set (HeightOneSpectrum (𝓞 ℚ)) := ∅

/-- The action of `G_{ℚ,∅}` on the zero module is continuous (every map to a point is). -/
instance continuousSMul_GKS_punit : ContinuousSMul (GKS ℚ emptySupport) PUnit := ⟨continuous_const⟩

/-- Strict local conditions (no places) for the zero coefficient module. -/
def zeroConditions : GaloisLocalConditions ℚ emptySupport (ResAt P) PUnit :=
  strictConditions _ _ _ _ PUnit

/-- **The zero genuine fiber**: lane RC26's `galoisSelData ℚ ∅ k 0 Δ`. -/
def zeroFibre : SelData (ResAt P) :=
  galoisSelData ℚ emptySupport (ResAt P) PUnit (zeroConditions P)

/-- The zero fiber is genuine Galois Selmer data (finite support; the condition on the local maps is
vacuous: there are no places). Kind: PROVED. -/
theorem zeroFibre_isGalois : IsGaloisSelData (zeroFibre P) :=
  ⟨ℚ, inferInstance, inferInstance, emptySupport, PUnit, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    zeroConditions P, Set.finite_empty,
    fun v => ((Set.mem_empty_iff_false _).mp v.2).elim, rfl⟩

/-- **The zero configuration family**: one configuration, no derivative primes, fiber `zeroFibre`,
actual class and functional zero, moving variable `t = X`. Kind: definition. -/
def exZeroFamily : SwitchFamily (ResAt P) (Localization.AtPrime P) where
  Config := Unit
  Prime := Empty
  actual := ()
  next c _ := c
  fibre _ := zeroFibre P
  t := algebraMap Lambda (Localization.AtPrime P) PowerSeries.X
  zAct := 0
  hzAct := map_zero _
  lamAct := 0
  hlamAct _ := rfl

/-- **The zero family is genuine at `𝔭`.** Kind: PROVED. -/
theorem exZeroFamily_isGenuine : IsGenuineFamilyAt P (exZeroFamily P) :=
  ⟨fun _ => zeroFibre_isGalois P, rfl⟩

/-- A complex whose degree-`n` term is subsingleton has subsingleton degree-`n` homology. -/
theorem homology_subsingleton_of_X {R : Type} [Ring R] (C : CochainComplex (ModuleCat.{0} R) ℤ)
    (n : ℤ) (h : Subsingleton (C.X n)) : Subsingleton (C.homology n) := by
  have hi := (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
  have hs := (ModuleCat.epi_iff_surjective (C.homologyπ n)).mp inferInstance
  have hc : Subsingleton (C.cycles n) := ⟨fun a b => hi (Subsingleton.elim _ _)⟩
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hs a
  obtain ⟨b', rfl⟩ := hs b
  rw [Subsingleton.elim a' b']

/-- The degree-one term of the zero fiber's Selmer complex is zero (zero coefficients, no places).
Kind: PROVED. -/
theorem zeroFibre_X1_subsingleton : Subsingleton ((selCx (zeroFibre P)).toCC.X 1) := by
  constructor
  intro a b
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  have h1 : a1 = b1 := by
    obtain ⟨f, hf⟩ := a1
    obtain ⟨g, hg⟩ := b1
    have hfg : f = g := by
      change ((Fin 1 → GKS ℚ emptySupport) → PUnit) at f g
      exact funext fun x => rfl
    subst hfg
    rfl
  have he : IsEmpty (ZInQ.Manuscript.RC.SelmerComplex.Places ℚ emptySupport) :=
    ⟨fun v => (Set.mem_empty_iff_false _).mp v.2⟩
  have h2 : a2 = b2 := by
    change (∀ v : ZInQ.Manuscript.RC.SelmerComplex.Places ℚ emptySupport, _) at a2 b2
    exact funext fun v => (he.false v).elim
  have h3 : a3 = b3 := by
    change (∀ v : ZInQ.Manuscript.RC.SelmerComplex.Places ℚ emptySupport, _) at a3 b3
    exact funext fun v => (he.false v).elim
  rw [h1, h2, h3]

/-- **The zero family's genuine fiber has `H¹ = 0`.** Kind: PROVED. -/
theorem exZeroFamily_h1 :
    finrank (ResAt P) (((selCx ((exZeroFamily P).fibre (exZeroFamily P).actual)).toCC.homology
      1)) = 0 := by
  change finrank (ResAt P) ((selCx (zeroFibre P)).toCC.homology 1) = 0
  have := homology_subsingleton_of_X _ 1 (zeroFibre_X1_subsingleton P)
  exact Module.finrank_zero_of_subsingleton

/-- **The zero family carries no genuine switching datum, for any coordinate `u`** (in particular
for `u = 1 ∈ ι(Λ_𝔭)`): over this genuine family no one-stage datum can be invented
(`isEmpty_genuineSwitchData_of_h1_eq_zero`). Kind: PROVED. -/
theorem exZeroFamily_no_data (u : FractionRing Lambda) :
    IsEmpty (GenuineSwitchData (exZeroFamily P) (UniformSwitch.toFracAt P) (resAt P) u) :=
  isEmpty_genuineSwitchData_of_h1_eq_zero u (exZeroFamily_h1 P)

/-- The one-stage datum of the round-3 leaf exists at every coordinate of `Λ_𝔭`
(`oneStageSwitchData`), while over the genuine zero family no datum exists: the new inputs at a fixed
genuine family are strictly stronger than the old ones. Kind: PROVED. -/
theorem exZeroFamily_contrast (r : Localization.AtPrime P) :
    Nonempty (HeightOneSwitchDataAt P) ∧
      IsEmpty (GenuineSwitchData (exZeroFamily P) (UniformSwitch.toFracAt P) (resAt P)
        (UniformSwitch.toFracAt P r)) :=
  ⟨⟨oneStageSwitchData P r⟩, exZeroFamily_no_data P _⟩

end ZeroFamily

end ZInQ.Manuscript.RC.Wiring
