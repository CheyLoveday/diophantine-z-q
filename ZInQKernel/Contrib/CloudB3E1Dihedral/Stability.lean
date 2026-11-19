import ZInQKernel.Contrib.CloudB3E1Dihedral.Dihedral
import ZInQKernel.Contrib.TYZGenus.RingClassGalois

/-!
# The ring class field is stable under complex conjugation

Manuscript `diophantine_zq.tex`, tex 2778–2795.

This file proves `RingClassFieldConjStable` (`Dihedral.lean`) for every quadratic `K`: a ring
automorphism `τ` of `K̄` lying over `κ ≠ 1` maps the ring class field `H_f ⊆ K_S` onto itself.
With `ringClassDihedral_of_stable`, lane E2's `RingClassDihedral` is then PROVED
(**`ringClassDihedral`**).

The proof is TYZGenus's Bauer argument (`RingClassGalois.lean`, there for `ℚ(√−d)`), here for
general `K`:
* `tauSep` (definition): `τ` restricted to `Kˢ ⊆ K̄`. A `κ`-twisted conjugate of a separable
  element is separable (`isSeparable_map`).
* `picClass_conjPrimeTo` (PROVED): `[κ𝔭] = [𝔭]⁻¹` in `Pic(ℤ + f𝒪_K)`, from `𝔭 · κ𝔭 = (N𝔭)`.
* **`conjField_ringClassField_le`** (PROVED): `τ(R) ⊆ R` for Tau Ceti's ring class field `R`, by
  Bauer's theorem (`le_of_splitSet_diff_subset`, from Tau Ceti's Chebotarev density theorem). A
  prime `𝔭` prime to the conductor that splits completely in `R` has `[𝔭] = 1`, so `[κ⁻¹𝔭] = 1`;
  hence `κ⁻¹𝔭` splits completely in `R`, and so `𝔭` splits completely in `τ(R)`.
* **`ringClassFieldConjStable`** (PROVED), and **`ringClassDihedral`** (PROVED).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1Dihedral

open NumberField IsDedekindDomain Ideal Polynomial
open ZInQ.Contrib.CloudB3E1RingClass
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.CoefModules (tauS KS)
open ZInQ.Contrib.TYZGenus.RingClass (splitSet le_of_splitSet_diff_subset conjField mem_conjField
  ncard_primesOver_conjField finrank_conjField mem_splitSet_iff)
open TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory
open scoped Pointwise

variable {K : Type} [Field K] [NumberField K]

/-! ### `τ` on the separable closure -/

section Sep

variable (κ : K ≃+* K) (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
  (hτ : ∀ x : K,
    τ (algebraMap K (AlgebraicClosure K) x) = algebraMap K (AlgebraicClosure K) (κ x))

omit [NumberField K] in
include hτ in
/-- `τ` carries a root of `p` to a root of `κ(p)`. Kind: PROVED. -/
theorem aeval_map_κ (p : K[X]) (y : AlgebraicClosure K) :
    aeval (τ y) (p.map (κ : K →+* K)) = τ (aeval y p) := by
  rw [aeval_def, aeval_def, eval₂_map]
  have h := Polynomial.hom_eval₂ p (algebraMap K (AlgebraicClosure K))
    (τ : AlgebraicClosure K →+* AlgebraicClosure K) y
  rw [RingHom.coe_coe] at h
  rw [h]
  congr 1
  ext x
  simp [hτ]

omit [NumberField K] in
include hτ in
/-- **A `κ`-twisted conjugate of a separable element is separable.** Kind: PROVED. -/
theorem isSeparable_map {y : AlgebraicClosure K} (hy : IsSeparable K y) : IsSeparable K (τ y) := by
  have hint : IsIntegral K y := hy.isIntegral
  have h0 : aeval (τ y) ((minpoly K y).map (κ : K →+* K)) = 0 := by
    rw [aeval_map_κ κ τ hτ, minpoly.aeval, map_zero]
  have hsep : ((minpoly K y).map (κ : K →+* K)).Separable := Polynomial.Separable.map hy
  have hne : (minpoly K y).map (κ : K →+* K) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hint)
  exact hsep.of_dvd (minpoly.dvd K (τ y) h0)

/-- `τ` restricted to `Kˢ`, as a `ℚ`-automorphism. Kind: definition. -/
def tauSep : SeparableClosure K ≃ₐ[ℚ] SeparableClosure K :=
  RingEquiv.toRatAlgEquiv
    { toFun := fun y => ⟨τ y.1, (mem_separableClosure_iff).mpr
        (isSeparable_map κ τ hτ ((mem_separableClosure_iff).mp y.2))⟩
      invFun := fun y => ⟨τ.symm y.1, (mem_separableClosure_iff).mpr
        (isSeparable_map κ.symm τ.symm (ZInQ.Manuscript.RC.CoefModules.symm_algebraMap κ τ hτ)
          ((mem_separableClosure_iff).mp y.2))⟩
      left_inv := fun y => Subtype.ext (τ.symm_apply_apply y.1)
      right_inv := fun y => Subtype.ext (τ.apply_symm_apply y.1)
      map_mul' := fun x y => Subtype.ext (map_mul τ x.1 y.1)
      map_add' := fun x y => Subtype.ext (map_add τ x.1 y.1) }

theorem tauSep_apply (y : SeparableClosure K) :
    ((tauSep κ τ hτ y : SeparableClosure K) : AlgebraicClosure K) = τ y.1 := rfl

theorem tauSep_algebraMap (x : K) :
    tauSep κ τ hτ (algebraMap K (SeparableClosure K) x) =
      algebraMap K (SeparableClosure K) (ringEquivAlg κ x) :=
  Subtype.ext (hτ x)

end Sep

/-! ### `[κ𝔭] = [𝔭]⁻¹` in `Pic(ℤ + f𝒪_K)` -/

section Pic

variable (f : ℕ) (hf : f ≠ 0)

/-- **`[κ𝔭] = [𝔭]⁻¹`** in `Pic(ℤ + f𝒪_K)` for a prime `𝔭` prime to the conductor, `κ ≠ 1`.
Kind: PROVED. -/
theorem picClass_conjPrimeTo (hK : Module.finrank ℚ K = 2) (κ : K ≃+* K) (hκ : ringEquivAlg κ ≠ 1)
    (J : integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus)
    [(J : Ideal (𝓞 K)).IsPrime] :
    (ringClassOrder (K := K) f hf).picClass (conjPrimeTo κ f hf J) =
      ((ringClassOrder (K := K) f hf).picClass J)⁻¹ := by
  obtain ⟨σ, -, hσ⟩ := exists_conj hK
  have hJ0 : (J : Ideal (𝓞 K)) ≠ ⊥ :=
    ((mem_integralIdealsPrimeTo_conductorModulus_iff _).mp J.2).1
  apply eq_inv_of_mul_eq_one_right
  rw [← map_mul]
  refine ((ringClassOrder (K := K) f hf).picClass_eq_one_iff _).mpr
    ⟨(((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℤ) : 𝓞 K), Subalgebra.intCast_mem _ _, ?_⟩
  change (J : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)).map (κO κ : 𝓞 K →+* 𝓞 K) = _
  rw [map_mapRingEquiv_eq_smul, hσ _ hκ, mul_smul_eq_span_absNorm hK hσ _ hJ0]
  simp

theorem ringEquivAlg_symm_ne_one (κ : K ≃+* K) (hκ : ringEquivAlg κ ≠ 1) :
    ringEquivAlg κ.symm ≠ 1 := by
  intro h
  apply hκ
  ext x
  have := congrArg (fun g : K ≃ₐ[ℚ] K => g (κ x)) h
  simpa [ringEquivAlg_apply] using this.symm

end Pic

/-! ### Bauer's theorem: `τ(R) ⊆ R` -/

section Bauer

variable (f : ℕ) (hf : f ≠ 0)

/-- The image of a `K`-normal subfield under `τ` is `K`-normal. Kind: PROVED. -/
theorem normal_conjField' (τ : SeparableClosure K ≃ₐ[ℚ] SeparableClosure K) (c : K ≃ₐ[ℚ] K)
    (hτ : ∀ x, τ (algebraMap K (SeparableClosure K) x) = algebraMap K (SeparableClosure K) (c x))
    (E : IntermediateField K (SeparableClosure K)) [Normal K E] :
    Normal K (conjField (τ : SeparableClosure K →ₐ[ℚ] SeparableClosure K) c hτ E) := by
  rw [IntermediateField.normal_iff_forall_map_le']
  intro g
  rintro _ ⟨y, ⟨x, hx, rfl⟩, rfl⟩
  have hτs : ∀ k, τ.symm (algebraMap K (SeparableClosure K) (c k)) =
      algebraMap K (SeparableClosure K) k := by
    intro k; rw [← hτ, AlgEquiv.symm_apply_apply]
  let g' : Gal(SeparableClosure K/K) :=
    AlgEquiv.ofRingEquiv (f := τ.toRingEquiv.trans (g.toRingEquiv.trans τ.symm.toRingEquiv))
      (fun k => by
        simp only [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv]
        rw [hτ, AlgEquiv.commutes, hτs])
  have hg' : g' x ∈ E :=
    (IntermediateField.normal_iff_forall_map_le'.1 inferInstance g') ⟨x, hx, rfl⟩
  refine ⟨g' x, hg', ?_⟩
  simp [g']

/-- The ring class field as the fixed field of the trivial subgroup. Kind: PROVED. -/
theorem lift_fixedField_bot :
    IntermediateField.lift (IntermediateField.fixedField ((⊥ : Subgroup
      (Pic (ringClassOrder (K := K) f hf))).map
        (ringClassArtinEquiv (ringClassOrder (K := K) f hf)).toMonoidHom)) =
      ringClassField (ringClassOrder (K := K) f hf) := by
  rw [Subgroup.map_bot, IntermediateField.fixedField_bot, IntermediateField.lift_top]

theorem finite_conductor_primes' :
    {𝔭 : HeightOneSpectrum (𝓞 K) |
      (ringClassOrder (K := K) f hf).conductor ≤ 𝔭.asIdeal}.Finite := by
  have h := Ideal.finite_factors (R := 𝓞 K) (I := (ringClassOrder (K := K) f hf).conductor)
    (by simpa using (ringClassOrder (K := K) f hf).conductor_ne_bot)
  refine h.subset fun 𝔭 h𝔭 => ?_
  exact Ideal.dvd_iff_le.2 h𝔭

theorem mem_primeTo_of_not_le' (𝔭 : HeightOneSpectrum (𝓞 K))
    (h : ¬ (ringClassOrder (K := K) f hf).conductor ≤ 𝔭.asIdeal) :
    𝔭.asIdeal ∈ integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus := by
  rw [mem_integralIdealsPrimeTo_conductorModulus_iff]
  refine ⟨𝔭.ne_bot, ?_⟩
  by_contra hne
  exact h ((𝔭.isMaximal.eq_of_le hne le_sup_left).symm ▸ le_sup_right)

variable (κ : K ≃+* K) (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
  (hτ : ∀ x : K,
    τ (algebraMap K (AlgebraicClosure K) x) = algebraMap K (AlgebraicClosure K) (κ x))

/-- **`τ(R) ⊆ R`** for Tau Ceti's ring class field `R` of `ℤ + f𝒪_K` (Bauer's theorem; tex
2778–2795). Kind: PROVED. -/
theorem conjField_ringClassField_le (hK : Module.finrank ℚ K = 2) (hκ : ringEquivAlg κ ≠ 1) :
    conjField (tauSep κ τ hτ : SeparableClosure K →ₐ[ℚ] SeparableClosure K) (ringEquivAlg κ)
      (tauSep_algebraMap κ τ hτ) (ringClassField (ringClassOrder (K := K) f hf)) ≤
      ringClassField (ringClassOrder (K := K) f hf) := by
  set O := ringClassOrder (K := K) f hf with hO
  set R := ringClassField O with hR
  set E' := conjField (tauSep κ τ hτ : SeparableClosure K →ₐ[ℚ] SeparableClosure K)
    (ringEquivAlg κ) (tauSep_algebraMap κ τ hτ) R with hE'
  have hfr : Module.finrank K E' = Module.finrank K R := finrank_conjField _ _ _ _
  have : FiniteDimensional K E' :=
    Module.finite_of_finrank_pos (by rw [hfr]; exact Module.finrank_pos)
  have : Normal K E' := normal_conjField' (tauSep κ τ hτ) (ringEquivAlg κ) (tauSep_algebraMap κ τ hτ) R
  have : IsGalois K E' := IsGalois.mk
  refine le_of_splitSet_diff_subset _ (finite_conductor_primes' f hf) ?_
  rintro 𝔭 ⟨h𝔭, hT𝔭⟩
  have hJ := mem_primeTo_of_not_le' f hf 𝔭 hT𝔭
  let J : integralIdealsPrimeTo O.conductorModulus := ⟨𝔭.asIdeal, hJ⟩
  have : (J : Ideal (𝓞 K)).IsMaximal := 𝔭.isMaximal
  have : (J : Ideal (𝓞 K)).IsPrime := 𝔭.isPrime
  have h𝔭' : 𝔭 ∈ splitSet K (IntermediateField.lift (IntermediateField.fixedField
      ((⊥ : Subgroup (Pic O)).map (ringClassArtinEquiv O).toMonoidHom))) := by
    rw [lift_fixedField_bot]; exact h𝔭
  have hS : O.picClass J ∈ (⊥ : Subgroup (Pic O)) :=
    (mem_splitSet_iff O ⊥ J 𝔭 rfl).1 h𝔭'
  set J' := conjPrimeTo κ.symm f hf J with hJ'
  have hJ'p : (J' : Ideal (𝓞 K)).IsPrime := Ideal.map_isPrime_of_equiv _
  have hJ'0 : (J' : Ideal (𝓞 K)) ≠ ⊥ :=
    ((mem_integralIdealsPrimeTo_conductorModulus_iff _).mp J'.2).1
  have : (J' : Ideal (𝓞 K)).IsMaximal := hJ'p.isMaximal hJ'0
  have hpS : O.picClass J' ∈ (⊥ : Subgroup (Pic O)) := by
    rw [hJ', picClass_conjPrimeTo f hf hK κ.symm (ringEquivAlg_symm_ne_one κ hκ) J]
    exact inv_mem hS
  let 𝔮 : HeightOneSpectrum (𝓞 K) := ⟨_, hJ'p, hJ'0⟩
  have h𝔮 : 𝔮 ∈ splitSet K (IntermediateField.lift (IntermediateField.fixedField
      ((⊥ : Subgroup (Pic O)).map (ringClassArtinEquiv O).toMonoidHom))) :=
    (mem_splitSet_iff O ⊥ J' 𝔮 rfl).2 hpS
  rw [lift_fixedField_bot] at h𝔮
  have htr := ncard_primesOver_conjField (tauSep κ τ hτ : SeparableClosure K →ₐ[ℚ] _)
    (ringEquivAlg κ) (tauSep_algebraMap κ τ hτ) R (J' : Ideal (𝓞 K))
  have hpp : (J' : Ideal (𝓞 K)).comap
      ((RingOfIntegers.mapRingEquiv (ringEquivAlg κ).toRingEquiv).symm : 𝓞 K →+* 𝓞 K) =
      𝔭.asIdeal := by
    ext x
    rw [Ideal.mem_comap]
    change _ ∈ (𝔭.asIdeal).map (κO κ.symm : 𝓞 K →+* 𝓞 K) ↔ _
    rw [Ideal.map_comap_of_equiv, Ideal.mem_comap]
    have e : (κO κ.symm).symm ((RingOfIntegers.mapRingEquiv (ringEquivAlg κ).toRingEquiv).symm x) =
        x := by
      apply RingOfIntegers.ext
      simp only [RingOfIntegers.mapRingEquiv_symm_apply]
      exact κ.apply_symm_apply _
    rw [RingEquiv.coe_toRingHom, e]
  rw [hpp] at htr
  change (𝔭.asIdeal.primesOver (𝓞 E')).ncard = Module.finrank K E'
  rw [hfr, ← htr]
  exact h𝔮

end Bauer

/-! ### `RingClassFieldConjStable` and `RingClassDihedral` -/

section Final

open ZInQ.Contrib.CloudB3E2.NormCochain (toAlgClosure)

variable (f : ℕ) (hf : f ≠ 0) (S : Set (HeightOneSpectrum (𝓞 K)))
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S) (κ : K ≃+* K)
  (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
  (hτ : ∀ x : K,
    τ (algebraMap K (AlgebraicClosure K) x) = algebraMap K (AlgebraicClosure K) (κ x))
  (hSst : ∀ v w : HeightOneSpectrum (𝓞 K),
    w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K) → (v ∈ S ↔ w ∈ S))

theorem mem_ringClassFieldOf_iff (x : KS K S) :
    x ∈ ringClassFieldOf f hf S hS ↔
      ∃ s ∈ ringClassField (ringClassOrder (K := K) f hf), (s : AlgebraicClosure K) = x := by
  unfold ringClassFieldOf ZInQ.Contrib.CloudB3E2.NormCochain.ringClassFieldS
  rw [IntermediateField.mem_restrict]
  exact Iff.rfl

include hτ in
/-- An element of `K̄` in `R` is carried by `τ` into `R`. Kind: PROVED. -/
theorem tau_mem_ringClassField (hK : Module.finrank ℚ K = 2) (hκ : ringEquivAlg κ ≠ 1)
    {s : SeparableClosure K} (hs : s ∈ ringClassField (ringClassOrder (K := K) f hf)) :
    tauSep κ τ hτ s ∈ ringClassField (ringClassOrder (K := K) f hf) :=
  conjField_ringClassField_le f hf κ τ hτ hK hκ ⟨s, hs, rfl⟩

/-- **The ring class field is `τ`-stable** (tex 2778–2795): the named input of
`ringClassDihedral_of_stable`, PROVED. Kind: PROVED. -/
theorem ringClassFieldConjStable (hK : Module.finrank ℚ K = 2) (hκ : ringEquivAlg κ ≠ 1) :
    RingClassFieldConjStable f hf S hS κ τ hτ hSst := by
  intro x
  rw [mem_ringClassFieldOf_iff, mem_ringClassFieldOf_iff]
  constructor
  · rintro ⟨s, hs, hsx⟩
    refine ⟨tauSep κ τ hτ s, tau_mem_ringClassField f hf κ τ hτ hK hκ hs, ?_⟩
    rw [tauSep_apply, hsx]
    rfl
  · rintro ⟨s, hs, hsx⟩
    have hτ' := ZInQ.Manuscript.RC.CoefModules.symm_algebraMap κ τ hτ
    refine ⟨tauSep κ.symm τ.symm hτ' s,
      tau_mem_ringClassField f hf κ.symm τ.symm hτ' hK (ringEquivAlg_symm_ne_one κ hκ) hs, ?_⟩
    rw [tauSep_apply, hsx]
    exact τ.symm_apply_apply (x : AlgebraicClosure K)

/-- **`RingClassDihedral`, proved** (tex 2778–2795; Cox, Lemma 9.3): for `K` quadratic and a ring
automorphism `τ` of `K̄` over `κ ≠ 1`, conjugation by `τ` inverts `Gal(H_f/K)`. Kind: PROVED. -/
theorem ringClassDihedral (hK : Module.finrank ℚ K = 2) (hκ : ringEquivAlg κ ≠ 1) :
    ZInQ.Contrib.CloudB3E2.XiConj.RingClassDihedral f hf S hS κ τ hτ hSst :=
  ringClassDihedral_of_stable hK hκ (ringClassFieldConjStable f hf S hS κ τ hτ hSst hK hκ)

end Final

end ZInQ.Contrib.CloudB3E1Dihedral
