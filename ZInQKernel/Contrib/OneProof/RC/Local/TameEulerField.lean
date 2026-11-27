import ZInQKernel.Contrib.OneProof.RC.Local.TameQuasiIsoHigh

/-!
# Lane RC31, round 6: the local Euler characteristic for every coefficient field

Manuscript `diophantine_zq.tex`, tex 3470–3480 (Elliot's tame local free model (4.4)), with the
tame coordinates of tex 3298–3306 and 5026–5037.

The tree PRINT `MilneADT_I_2_8` (Milne, ADT I.2.8) is stated for `𝔽₂`-coefficients. The
continuous cohomology of a discrete module depends only on the underlying abelian group with its
`G`-action, so the statement transfers to every coefficient ring.

* `nonempty_contHomology_equiv` (PROVED): for two coefficient rings `k` and `R` acting on the
  same discrete `G`-module `M`, `Hⁿ(contCochains k G M) ≃ Hⁿ(contCochains R G M)` (both are
  `Hⁿ` of `M` as a discrete `ℤ`-module, through `contCohomologyLinearEquiv` and
  `ofDiscreteModuleRestrictScalarsIntEquiv`); `card_contZ0_scalars`, `card_contH1_scalars`,
  `card_contH2_scalars` (PROVED) for the explicit groups.
* `two_nsmul_eq_zero_of_field`, `smulCommClass_zmod_two` (PROVED): a vector space killed by a
  power of `2` is killed by `2`, hence an `𝔽₂[G]`-module.
* `euler_field`, `subsingleton_homology_field` (PROVED from `MilneADT_I_2_8`): for a finite
  extension `F` of `ℚ_p`, `p ≠ 2`, any coefficient field `k` and a finite discrete
  `k[G_F]`-module `M` of `2`-power exponent, `|H⁰| · |H²| = |H¹|` and `Hⁿ = 0` for `n > 2`.
* `quasiIso_tameCochainMap_field` (PROVED from `MilneADT_I_2_8` and `TameH2Surjective`): the
  tame comparison at `g = 1` is a quasi-isomorphism for every coefficient field.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Local

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.RC53Assist.TameBijective
open ZInQ.Contrib.CloudB3RC53.ContBridge (continuousSMul_of_discrete contCohomologyLinearEquiv)

/-! ### Independence of the coefficient ring -/

section Scalars

variable {k : Type} {R : Type} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] {M : Type} [AddCommGroup M] [DistribMulAction G M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

attribute [local instance] TopRep.distribMulAction in
/-- **The continuous cohomology does not depend on the coefficient ring** (tex 3470–3480): for
two coefficient rings `k`, `R` acting on the same discrete `G`-module `M` (commuting with `G`),
`Hⁿ(contCochains k G M) ≃ Hⁿ(contCochains R G M)`; both are the continuous cohomology of `M` as
a discrete `ℤ`-module. Kind: PROVED. -/
theorem nonempty_contHomology_equiv [CommRing k] [CommRing R] [Module k M] [Module R M]
    [SMulCommClass G k M] [SMulCommClass G R M] (n : ℕ) :
    Nonempty ((contCochains k G M).homology n ≃ (contCochains R G M).homology n) := by
  let _ : TopologicalSpace k := ⊥
  have : DiscreteTopology k := ⟨rfl⟩
  let _ : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  have : ContinuousSMul k M := continuousSMul_of_discrete k M
  have : ContinuousSMul R M := continuousSMul_of_discrete R M
  have ek := (contCohomologyLinearEquiv k G M n).toEquiv
  have eR := (contCohomologyLinearEquiv R G M n).toEquiv
  have zk := (TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv
    (TauCeti.ofDiscreteModule k G M) n).toEquiv
  have zR := (TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv
    (TauCeti.ofDiscreteModule R G M) n).toEquiv
  have hobj : TauCeti.ofDiscreteModule ℤ G (TauCeti.ofDiscreteModule k G M).V =
      TauCeti.ofDiscreteModule ℤ G (TauCeti.ofDiscreteModule R G M).V := rfl
  exact ⟨((ek.symm.trans zk.symm).trans (Equiv.cast (by rw [hobj]))).trans (zR.trans eR)⟩

/-- The orders of the explicit zero-cocycles agree for two coefficient fields (tex 3470–3480).
Kind: PROVED. -/
theorem card_contZ0_scalars [Field k] [Field R] [Module k M] [Module R M] [SMulCommClass G k M]
    [SMulCommClass G R M] : Nat.card (contZ0 k G M) = Nat.card (contZ0 R G M) := by
  rw [← card_contZ0_homology, ← card_contZ0_homology]
  exact Nat.card_congr (nonempty_contHomology_equiv 0).some

/-- The orders of the explicit first cohomology groups agree for two coefficient fields
(tex 3470–3480). Kind: PROVED. -/
theorem card_contH1_scalars [Field k] [Field R] [Module k M] [Module R M] [SMulCommClass G k M]
    [SMulCommClass G R M] : Nat.card (H1WrelK k G M) = Nat.card (H1WrelK R G M) := by
  rw [← card_contH1_homology, ← card_contH1_homology]
  exact Nat.card_congr (nonempty_contHomology_equiv 1).some

/-- The orders of the explicit second cohomology groups agree for two coefficient fields
(tex 3470–3480). Kind: PROVED. -/
theorem card_contH2_scalars [Field k] [Field R] [Module k M] [Module R M] [SMulCommClass G k M]
    [SMulCommClass G R M] : Nat.card (ContH2 k G M) = Nat.card (ContH2 R G M) := by
  rw [← card_contH2_homology, ← card_contH2_homology]
  exact Nat.card_congr (nonempty_contHomology_equiv 2).some

end Scalars

/-- A vector space killed by a power of `2` is killed by `2`: either `2 = 0` in `k`, or `2` is
invertible and the space is zero (tex 3470–3480). Kind: PROVED. -/
theorem two_nsmul_eq_zero_of_field {k : Type} [Field k] {M : Type} [AddCommGroup M]
    [Module k M] (hexp : ∃ e : ℕ, ∀ m : M, 2 ^ e • m = 0) (m : M) : 2 • m = 0 := by
  obtain ⟨e, he⟩ := hexp
  by_cases h2 : (2 : k) = 0
  · rw [← Nat.cast_smul_eq_nsmul k, Nat.cast_ofNat, h2, zero_smul]
  · have h := he m
    rw [← Nat.cast_smul_eq_nsmul k, Nat.cast_pow, Nat.cast_ofNat] at h
    have hm : m = 0 := (smul_eq_zero.mp h).resolve_left (pow_ne_zero _ h2)
    rw [hm, smul_zero]

/-- The `𝔽₂`-structure of a module killed by `2` commutes with any distributive group action
(tex 3470–3480). Kind: PROVED. -/
theorem smulCommClass_zmod_two {G : Type} [Group G] {M : Type} [AddCommGroup M]
    [DistribMulAction G M] (h2 : ∀ m : M, 2 • m = 0) :
    @SMulCommClass G (ZMod 2) M _ (AddCommGroup.zmodModule h2).toSMul := by
  let _ : Module (ZMod 2) M := AddCommGroup.zmodModule h2
  refine ⟨fun g a m => ?_⟩
  rw [← ZMod.natCast_zmod_val a, Nat.cast_smul_eq_nsmul (ZMod 2),
    Nat.cast_smul_eq_nsmul (ZMod 2), smul_comm]

/-! ### The Euler characteristic and the vanishing above degree two, any coefficient field -/

section EulerField

open ZInQ.Manuscript.RC.Limits (MilneADT_I_2_8)

variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F]
  [FiniteDimensional ℚ_[p] F] {k : Type} [Field k] (M : Type) [AddCommGroup M] [Module k M]
  [DistribMulAction (Field.absoluteGaloisGroup F) M]
  [SMulCommClass (Field.absoluteGaloisGroup F) k M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup F) M] [Finite M]

/-- **The local Euler characteristic for every coefficient field** (tex 3470–3480): for a
finite extension `F` of `ℚ_p`, `p ≠ 2`, a field `k` and a finite discrete `k[G_F]`-module `M`
of `2`-power exponent, `|H⁰| · |H²| = |H¹|` for the explicit continuous cohomology. From the
tree PRINT `MilneADT_I_2_8` (`𝔽₂`-coefficients, `euler_of_milne`) and the independence of the
coefficient ring (`card_contZ0_scalars`, `card_contH1_scalars`, `card_contH2_scalars`). Kind:
PROVED (from the PRINT). -/
theorem euler_field (h28 : MilneADT_I_2_8) (hp : p ≠ 2)
    (hexp : ∃ e : ℕ, ∀ m : M, 2 ^ e • m = 0) :
    Nat.card (contZ0 k (Field.absoluteGaloisGroup F) M) *
        Nat.card (ContH2 k (Field.absoluteGaloisGroup F) M) =
      Nat.card (H1WrelK k (Field.absoluteGaloisGroup F) M) := by
  have h2 : ∀ m : M, 2 • m = 0 := two_nsmul_eq_zero_of_field (k := k) hexp
  let _ : Module (ZMod 2) M := AddCommGroup.zmodModule h2
  have : SMulCommClass (Field.absoluteGaloisGroup F) (ZMod 2) M :=
    smulCommClass_zmod_two h2
  rw [card_contZ0_scalars (R := ZMod 2), card_contH2_scalars (R := ZMod 2),
    card_contH1_scalars (R := ZMod 2)]
  exact euler_of_milne p F M h28 hp

include p in
/-- **Cohomological dimension two for every coefficient field** (tex 3470–3480): under the
hypotheses of `euler_field`, the cohomology of `natCx (contCochains k G_F M)` vanishes in
degrees `n > 2`. From the tree PRINT `MilneADT_I_2_8` (`subsingleton_homology_of_milne`) and
`nonempty_contHomology_equiv`. Kind: PROVED (from the PRINT). -/
theorem subsingleton_homology_field (h28 : MilneADT_I_2_8)
    (hexp : ∃ e : ℕ, ∀ m : M, 2 ^ e • m = 0) (n : ℤ) (hn : 2 < n) :
    Subsingleton ((natCx (contCochains k (Field.absoluteGaloisGroup F) M)).toCC.homology n) := by
  have h2 : ∀ m : M, 2 • m = 0 := two_nsmul_eq_zero_of_field (k := k) hexp
  let _ : Module (ZMod 2) M := AddCommGroup.zmodModule h2
  have : SMulCommClass (Field.absoluteGaloisGroup F) (ZMod 2) M :=
    smulCommClass_zmod_two h2
  cases n with
  | negSucc n => omega
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast] at hn
    cases n with
    | zero => norm_num at hn
    | succ n =>
      have h2' : Subsingleton ((natCx (contCochains (ZMod 2) (Field.absoluteGaloisGroup F)
          M)).toCC.homology ((n + 1 : ℕ) : ℤ)) :=
        subsingleton_homology_of_milne p F M h28 _ (by omega)
      have : Subsingleton ((contCochains (ZMod 2) (Field.absoluteGaloisGroup F) M).homology
          (n + 1)) :=
        (ZInQ.Contrib.RC53Assist.ResidualBounds.natPositiveHomologyIso
          (contCochains (ZMod 2) (Field.absoluteGaloisGroup F) M)
            n).symm.toLinearEquiv.injective.subsingleton
      have : Subsingleton ((contCochains k (Field.absoluteGaloisGroup F) M).homology
          (n + 1)) :=
        (nonempty_contHomology_equiv (k := k) (R := ZMod 2)
          (n + 1)).some.injective.subsingleton
      exact (ZInQ.Contrib.RC53Assist.ResidualBounds.natPositiveHomologyIso
        (contCochains k (Field.absoluteGaloisGroup F) M)
          n).toLinearEquiv.injective.subsingleton

end EulerField

/-! ### Assembly for every coefficient field -/

section AssemblyField

open TauCeti ValuativeRel
open ZInQ.Contrib.CloudB3RC53.TameQuotient
open ZInQ.Manuscript.RC.Limits (MilneADT_I_2_8)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [PerfectField K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K] {k : Type} [Field k]
  {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (Field.absoluteGaloisGroup K) M]
  [SMulCommClass (Field.absoluteGaloisGroup K) k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup K) M]
  {n : ℕ} [NeZero n] [Fact (1 < n)] {a : K} {β : AlgebraicClosure K}
  {φ σ : Field.absoluteGaloisGroup K}

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **The tame comparison is a quasi-isomorphism for every coefficient field**
(tex 3470–3480): for a nonarchimedean local field `K` that is a finite extension of `ℚ_p`,
`p ≠ 2`, any coefficient field `k`, at `g = 1`, under the hypotheses of
`quasiIsoAt_tameCochainMap_one` together with a closed normal pro-`p` subgroup `P ≤ I` with
`I = closure(⟨σ⟩ P)`, odd residue characteristic and `M` of `2`-power exponent,
`tameCochainMap` is a quasi-isomorphism, given the tree PRINT `MilneADT_I_2_8` (degrees `≥ 3`:
`subsingleton_homology_field`; the order of `H²`: `euler_field`) and the GLUE statement
`TameH2Surjective` (degree `2`). Degrees `≤ 1` are PROVED in
`quasiIso_tameCochainMap_of_two_le`. Kind: PROVED (from the tree PRINT `MilneADT_I_2_8` and the
GLUE statement `TameH2Surjective`). -/
theorem quasiIso_tameCochainMap_field (h28 : MilneADT_I_2_8) (h2 : TameH2Surjective)
    (hp : p ≠ 2) [TopologicalSpace k] (X : TopRep.{0} k (UnramifiedGaloisGroup K))
    [ContinuousSMul (UnramifiedGaloisGroup K) X.V] [DiscreteTopology X.V] [Finite X.V]
    (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Field.absoluteGaloisGroup K) (x : X.V),
      f (localUnramifiedProjection K g • x) = g • f x)
    (hfs : Function.Surjective f)
    (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hφ : IsArithFrobeniusLift K φ) (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (hnM : ∀ m : M, n • m = 0) (hq : Odd (Nat.card 𝓀[K])) (Φ : M →ₗ[k] M)
    (hΦ : ∀ m, Φ m = φ • m) (hgσ : ∀ m, (LinearMap.id : M →ₗ[k] M) m = σ • m)
    (hg : (LinearMap.id : M →ₗ[k] M) ∘ₗ LinearMap.id = LinearMap.id)
    (hcomm : Φ ∘ₗ LinearMap.id = LinearMap.id ∘ₗ Φ)
    (hrel : φ * σ * φ⁻¹ = σ ^ Nat.card 𝓀[K])
    (P : Subgroup (Field.absoluteGaloisGroup K)) (hPn : P.Normal)
    (hPc : IsClosed (P : Set (Field.absoluteGaloisGroup K)))
    (hPp : TauCeti.IsProP (ringChar 𝓀[K]) P) (hPI : P ≤ inertiaSubgroup K)
    (hIσ : (Subgroup.zpowers σ ⊔ P).topologicalClosure = inertiaSubgroup K)
    (hp2 : ringChar 𝓀[K] ≠ 2) (hexp : ∃ e : ℕ, ∀ m : M, 2 ^ e • m = 0) :
    QuasiIso (GHom.toCC (tameCochainMap Φ LinearMap.id φ σ (Nat.card 𝓀[K]) hq hΦ hgσ hg hcomm
      hrel)) := by
  have : Finite M := Finite.of_surjective f hfs
  refine quasiIso_tameCochainMap_of_two_le X f hf hfs hn hβ hβ0 hφ hσI hζ hItriv hnM hq Φ hΦ
    hgσ hg hcomm hrel ?_
  intro i hi
  rcases eq_or_lt_of_le hi with h | h
  · subst h
    exact quasiIsoAt_tameCochainMap_two_of_surjective Φ φ σ _ hq hΦ (hItriv σ hσI) hgσ hg hcomm
      hrel (inertiaSubgroup K) hItriv (top_le_iff.mp
        (hφ.topologicalClosure_zpowers_sup_inertiaSubgroup.symm.le.trans
          (Subgroup.topologicalClosure_mono (sup_le_sup_right
            (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) _))))
      (tameH1_bijective_local X f hf hfs hn hβ hβ0 hφ hσI hζ hItriv hnM hq Φ hΦ hrel)
      (euler_field p K M h28 hp hexp)
      (h2 K k M φ σ P Φ _ hq hΦ (hItriv σ hσI) hrel hφ hσI rfl hp2 hPn hPc hPp hPI hIσ
        hItriv hexp)
  · exact quasiIsoAt_tameCochainMap_of_ge_three Φ LinearMap.id φ σ _ hq hΦ hgσ hg hcomm hrel i h
      (subsingleton_homology_field p K M h28 hexp i h)

end AssemblyField

end ZInQ.Manuscript.RC.Local
