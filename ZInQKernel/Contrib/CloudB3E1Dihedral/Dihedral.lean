import ZInQKernel.Contrib.CloudB3E1Dihedral.ConjNorm
import ZInQKernel.Contrib.CloudB3E2Norm.XiConj

/-!
# The generalized dihedral structure of ring class fields

Manuscript `diophantine_zq.tex`, tex 2778–2795: the conjugation inverts the ring-class
characters.

Lane E2's `RingClassDihedral f hf S hS κ τ hτ hSst` says that conjugation by `τ` inverts
`Gal(H_f/K)`: `ringClassRes (τ σ τ⁻¹) = (ringClassRes σ)⁻¹` for every `σ ∈ G_{K,S}`. Here `τ` is a
ring automorphism of `K̄` over a ring automorphism `κ ≠ 1` of the quadratic field `K`.

This file derives it from one named hypothesis, **`RingClassFieldConjStable`**: `τ` maps the copy
`H_f ⊆ K_S` of the ring class field onto itself (the ring class field is Galois over `ℚ`).
* `mem_ringClassOrder_conj`, `mem_conductor_conj`, `conj_mem_primeTo` (PROVED): `ℤ + f𝒪_K`, its
  conductor and the ideals prime to it are `κ`-stable.
* `artinClass_conj_mul` (PROVED): `Art(κ𝔭) · Art(𝔭) = 1` for every prime `𝔭` prime to the
  conductor, since `𝔭 · κ𝔭 = (N𝔭)` (`mul_smul_eq_span_absNorm`).
* `isArithFrobAt_galConj` (PROVED): Frobenius transport. If `g` is an arithmetic Frobenius at
  `Q`, then `t g t⁻¹` is one at `t(Q)`, for a ring automorphism `t` over `κ`.
* `galConj_ringClassArtin` (PROVED): in Tau Ceti's ring class field `R`, `t Art(𝔭) t⁻¹ = Art(κ𝔭)`.
  Both are arithmetic Frobenius elements at `t(Q)`, and `R/K` is unramified there
  (`isUnramifiedAt_ringClassField`), so they agree.
* `tauH`, `ringClassRes_conjGKS` (PROVED): under the stability, `τ` restricts to `H_f`, and
  `ringClassRes(τ σ τ⁻¹) = τ (σ|_{H_f}) τ⁻¹`.
* `tauR`, `autCongr_galConjFun`, `galConj_artinClass` (PROVED): transported to Tau Ceti's model,
  `τ Art(𝔭) τ⁻¹ = Art(κ𝔭)`.
* `galConj_eq_inv` (PROVED): `θ(g) = τ g τ⁻¹` is a homomorphism of `Gal(H_f/K)`, and it equals
  inversion. `θ(Art 𝔭) · Art 𝔭 = Art(κ𝔭) Art(𝔭) = 1`, and the Artin classes of primes generate,
  since every ideal prime to the conductor factors into such primes and the Artin map is onto.
* **`ringClassDihedral_of_stable`** (PROVED): `RingClassFieldConjStable → RingClassDihedral`.

Kinds: definitions and PROVED (from the named `RingClassFieldConjStable`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1Dihedral

open NumberField IsDedekindDomain Ideal
open ZInQ.Contrib.CloudB3E1RingClass
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.CoefModules
  (conjGKS conjGKS_apply tauS galConjFun galConj tauS_algebraMap KS galS)
open TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory
open scoped Pointwise

variable {K : Type} [Field K] [NumberField K]

/-! ### `κ`-stability of the order, its conductor and the ideals prime to it -/

section Stable

variable (κ : K ≃+* K) (f : ℕ) (hf : f ≠ 0)

/-- The ring automorphism of `𝒪_K` induced by `κ`. Kind: definition. -/
abbrev κO : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv κ

omit [NumberField K] in
theorem κO_natCast (n : ℕ) : κO κ (n : 𝓞 K) = n := map_natCast _ n

omit [NumberField K] in
theorem map_span_f : (span {(f : 𝓞 K)}).map (κO κ : 𝓞 K →+* 𝓞 K) = span {(f : 𝓞 K)} := by
  rw [Ideal.map_span, Set.image_singleton, RingHom.coe_coe, κO_natCast]

/-- `ℤ + f𝒪_K` is `κ`-stable. Kind: PROVED. -/
theorem mem_ringClassOrder_conj {x : 𝓞 K}
    (hx : (x : K) ∈ (ringClassOrder (K := K) f hf).toSubalgebra) :
    ((κO κ x : 𝓞 K) : K) ∈ (ringClassOrder (K := K) f hf).toSubalgebra := by
  rw [mem_ringClassOrder_iff] at hx ⊢
  obtain ⟨a, ha⟩ := hx
  refine ⟨a, ?_⟩
  have h := Ideal.mem_map_of_mem (κO κ : 𝓞 K →+* 𝓞 K) ha
  rw [map_span_f, RingHom.coe_coe, map_sub, map_intCast] at h
  exact h

/-- The conductor of `ℤ + f𝒪_K` is `κ`-stable. Kind: PROVED. -/
theorem mem_conductor_conj {x : 𝓞 K} (hx : x ∈ (ringClassOrder (K := K) f hf).conductor) :
    κO κ x ∈ (ringClassOrder (K := K) f hf).conductor := by
  rw [NumberFieldOrder.mem_conductor_iff] at hx ⊢
  intro y
  have h := mem_ringClassOrder_conj κ f hf (x := x * (κO κ).symm y) (by
    have := hx ((κO κ).symm y); exact_mod_cast this)
  rw [map_mul, RingEquiv.apply_symm_apply] at h
  exact_mod_cast h

theorem map_conductor :
    (ringClassOrder (K := K) f hf).conductor.map (κO κ : 𝓞 K →+* 𝓞 K) =
      (ringClassOrder (K := K) f hf).conductor := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact mem_conductor_conj κ f hf hx
  · intro x hx
    have h := mem_conductor_conj κ.symm f hf hx
    have e : (κO κ) ((κO κ.symm) x) = x := by
      apply RingOfIntegers.ext
      simp
    rw [← e]
    exact Ideal.mem_map_of_mem _ h

/-- **The `κ`-image of an ideal prime to the conductor is prime to it.** Kind: PROVED. -/
theorem conj_mem_primeTo {J : Ideal (𝓞 K)}
    (hJ : J ∈ integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus) :
    J.map (κO κ : 𝓞 K →+* 𝓞 K) ∈
      integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus := by
  rw [mem_integralIdealsPrimeTo_conductorModulus_iff] at hJ ⊢
  refine ⟨fun h => hJ.1 ((Ideal.map_eq_bot_iff_of_injective (κO κ).injective).mp h), ?_⟩
  rw [← map_conductor κ f hf, ← Ideal.map_sup, hJ.2, Ideal.map_top]

/-- The `κ`-image of an ideal prime to the conductor. Kind: definition. -/
def conjPrimeTo (J : integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus) :
    integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus :=
  ⟨(J : Ideal (𝓞 K)).map (κO κ : 𝓞 K →+* 𝓞 K), conj_mem_primeTo κ f hf J.2⟩

end Stable

/-! ### `Art(κ𝔭) · Art(𝔭) = 1` for every prime prime to the conductor -/

section ArtinConj

variable (f : ℕ) (hf : f ≠ 0) (S : Set (HeightOneSpectrum (𝓞 K)))
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S)

/-- **`Art(κ𝔭) · Art(𝔭) = 1`** for a prime `𝔭` prime to the conductor (tex 3683–3684).
Kind: PROVED. -/
theorem artinClass_conj_mul (hK : Module.finrank ℚ K = 2) (κ : K ≃+* K)
    (hκ : ringEquivAlg κ ≠ 1)
    (J : integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus)
    [(J : Ideal (𝓞 K)).IsPrime] :
    artinClass f hf S hS J * artinClass f hf S hS (conjPrimeTo κ f hf J) = 1 := by
  obtain ⟨σ, -, hσ⟩ := exists_conj hK
  have hJ0 : (J : Ideal (𝓞 K)) ≠ ⊥ :=
    ((mem_integralIdealsPrimeTo_conductorModulus_iff _).mp J.2).1
  refine artinClass_mul_eq_one f hf S hS _ _ ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℤ) ?_
  change (J : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)).map (κO κ : 𝓞 K →+* 𝓞 K) = _
  rw [map_mapRingEquiv_eq_smul, hσ _ hκ, mul_smul_eq_span_absNorm hK hσ _ hJ0]
  simp

end ArtinConj

/-! ### Frobenius transport along a semilinear automorphism -/

section Transport

variable {L : Type} [Field L] [NumberField L] [Algebra K L] (κ : K ≃+* K) (t : L ≃+* L)
  (ht : ∀ x : K, t (algebraMap K L x) = algebraMap K L (κ x))

/-- The ring automorphism of `𝒪_L` induced by `t`. Kind: definition. -/
abbrev tO : 𝓞 L ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv t

omit [NumberField K] [NumberField L] in
include ht in
/-- `t ∘ algebraMap = algebraMap ∘ κ` on rings of integers. Kind: PROVED. -/
theorem tO_algebraMap (x : 𝓞 K) :
    tO t (algebraMap (𝓞 K) (𝓞 L) x) = algebraMap (𝓞 K) (𝓞 L) (κO κ x) := by
  apply RingOfIntegers.ext
  change t (algebraMap K L (x : K)) = algebraMap K L (κ (x : K))
  exact ht x

omit [NumberField K] [NumberField L] in
include ht in
/-- `t(Q) ∩ 𝒪_K = κ(Q ∩ 𝒪_K)`. Kind: PROVED. -/
theorem under_map_tO (Q : Ideal (𝓞 L)) :
    (Q.map (tO t : 𝓞 L →+* 𝓞 L)).under (𝓞 K) = (Q.under (𝓞 K)).map (κO κ : 𝓞 K →+* 𝓞 K) := by
  ext x
  rw [Ideal.under, Ideal.mem_comap, Ideal.map_comap_of_equiv, Ideal.map_comap_of_equiv,
    Ideal.mem_comap, Ideal.under, Ideal.mem_comap]
  have h := tO_algebraMap κ t ht ((κO κ).symm x)
  rw [RingEquiv.apply_symm_apply] at h
  rw [← h, RingEquiv.symm_apply_apply]
  rfl

omit [NumberField K] in
/-- The residue fields of `I` and `κ(I)` have the same cardinality. Kind: PROVED. -/
theorem card_quot_map_κO (I : Ideal (𝓞 K)) :
    Nat.card (𝓞 K ⧸ I.map (κO κ : 𝓞 K →+* 𝓞 K)) = Nat.card (𝓞 K ⧸ I) :=
  Nat.card_congr (Ideal.quotientEquiv I _ (κO κ) rfl).toEquiv.symm

omit [NumberField K] [NumberField L] in
include ht in
/-- **Frobenius transport**: if `g` is an arithmetic Frobenius at `Q`, then `t g t⁻¹` is one at
`t(Q)`. Kind: PROVED. -/
theorem isArithFrobAt_galConj {g : L ≃ₐ[K] L} {Q : Ideal (𝓞 L)} (H : IsArithFrobAt (𝓞 K) g Q) :
    IsArithFrobAt (𝓞 K) (galConjFun κ t ht g) (Q.map (tO t : 𝓞 L →+* 𝓞 L)) := by
  intro y
  rw [under_map_tO κ t ht, card_quot_map_κO]
  set z := (tO t).symm y with hz
  have hy : y = tO t z := by rw [hz, RingEquiv.apply_symm_apply]
  have hg : (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) (galConjFun κ t ht g)) y =
      tO t ((MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) g) z) := by
    apply RingOfIntegers.ext
    rw [hy]
    change (galConjFun κ t ht g) (t ((z : 𝓞 L) : L)) = t (g (z : L))
    change t (g (t.symm (t (z : L)))) = t (g (z : L))
    rw [RingEquiv.symm_apply_apply]
  rw [hg, hy, ← map_pow, ← map_sub]
  exact Ideal.mem_map_of_mem _ (H z)

omit [NumberField K] in
/-- `Gal(L/K)` acts faithfully on `𝒪_L`. Kind: PROVED. -/
theorem eq_of_toAlgHom_eq {g₁ g₂ : L ≃ₐ[K] L}
    (h : MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) g₁ = MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) g₂) :
    g₁ = g₂ := by
  ext x
  obtain ⟨y, hy0, hint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ L).mpr
    (Algebra.IsAlgebraic.isAlgebraic x)).exists_integral_multiple
  have e := congrArg (fun φ => ((φ ⟨y • x, hint⟩ : 𝓞 L) : L)) h
  change g₁ (y • x) = g₂ (y • x) at e
  rw [map_zsmul, map_zsmul] at e
  exact smul_right_injective L hy0 e

end Transport

/-! ### In Tau Ceti's ring class field: `t Art(𝔭) t⁻¹ = Art(κ𝔭)` -/

section TauCetiModel

variable (f : ℕ) (hf : f ≠ 0) (κ : K ≃+* K)
  (t : ringClassField (ringClassOrder (K := K) f hf) ≃+*
    ringClassField (ringClassOrder (K := K) f hf))
  (ht : ∀ x : K, t (algebraMap K (ringClassField (ringClassOrder (K := K) f hf)) x) =
    algebraMap K (ringClassField (ringClassOrder (K := K) f hf)) (κ x))

/-- A nonzero prime is maximal. Kind: PROVED. -/
theorem isMaximal_of_primeTo
    (J : integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus)
    [hJ : (J : Ideal (𝓞 K)).IsPrime] : (J : Ideal (𝓞 K)).IsMaximal :=
  hJ.isMaximal ((mem_integralIdealsPrimeTo_conductorModulus_iff _).mp J.2).1

include ht in
/-- **`t Art(𝔭) t⁻¹ = Art(κ𝔭)`** in Tau Ceti's ring class field `R`, for a prime `𝔭` prime to the
conductor. Both sides are arithmetic Frobenius elements at `t(Q)` for a prime `Q` of `R` above `𝔭`
(`isArithFrobAt_galConj`, the splitting law), and `R/K` is unramified at `t(Q)`. Kind: PROVED. -/
theorem galConj_ringClassArtin
    (J : integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus)
    [hJ : (J : Ideal (𝓞 K)).IsPrime] :
    galConjFun κ t ht (ringClassArtinEquiv (ringClassOrder (K := K) f hf)
        ((ringClassOrder (K := K) f hf).picClass J)) =
      ringClassArtinEquiv (ringClassOrder (K := K) f hf)
        ((ringClassOrder (K := K) f hf).picClass (conjPrimeTo κ f hf J)) := by
  have := isMaximal_of_primeTo f hf J
  obtain ⟨Q, hQmax, hQover⟩ :=
    exists_maximal_ideal_liesOver_of_isIntegral
      (S := 𝓞 (ringClassField (ringClassOrder (K := K) f hf))) (J : Ideal (𝓞 K))
  have H1 := isArithFrobAt_ringClassArtinEquiv_picClass (ringClassOrder (K := K) f hf) J Q
  have H2 := isArithFrobAt_galConj κ t ht H1
  set Q' := Q.map (tO t : 𝓞 (ringClassField (ringClassOrder (K := K) f hf)) →+*
    𝓞 (ringClassField (ringClassOrder (K := K) f hf))) with hQ'
  have hQ'p : Q'.IsPrime := Ideal.map_isPrime_of_equiv _
  have hJ' : ((conjPrimeTo κ f hf J : _) : Ideal (𝓞 K)) = Q'.under (𝓞 K) := by
    rw [under_map_tO κ t ht, ← hQover.over]
    rfl
  have : Q'.LiesOver ((conjPrimeTo κ f hf J : _) : Ideal (𝓞 K)) := ⟨hJ'⟩
  have hJ'p : ((conjPrimeTo κ f hf J : _) : Ideal (𝓞 K)).IsPrime := by
    rw [hJ']; exact Ideal.IsPrime.under _ _
  have := isMaximal_of_primeTo f hf (conjPrimeTo κ f hf J)
  have H3 := isArithFrobAt_ringClassArtinEquiv_picClass (ringClassOrder (K := K) f hf)
    (conjPrimeTo κ f hf J) Q'
  let v : HeightOneSpectrum (𝓞 K) :=
    ⟨_, hJ'p, ((mem_integralIdealsPrimeTo_conductorModulus_iff _).mp (conjPrimeTo κ f hf J).2).1⟩
  have hv : ¬ v.asIdeal ∣ (ringClassOrder (K := K) f hf).conductor := by
    intro hd
    have hle := (Ideal.dvd_iff_le).mp hd
    have h2 := ((mem_integralIdealsPrimeTo_conductorModulus_iff _).mp (conjPrimeTo κ f hf J).2).2
    rw [sup_eq_left.mpr hle] at h2
    exact hJ'p.ne_top h2
  have : Q'.LiesOver v.asIdeal := ⟨hJ'⟩
  have := isUnramifiedAt_ringClassField (ringClassOrder (K := K) f hf) hv Q'
  apply eq_of_toAlgHom_eq
  exact AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt H2 H3 (Ideal.primeCompl_le_nonZeroDivisors Q')

end TauCetiModel

/-! ### The ring class field in `K_S`, `τ`-stable: assembly -/

section Assembly

variable (f : ℕ) (hf : f ≠ 0) (S : Set (HeightOneSpectrum (𝓞 K)))
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S) (κ : K ≃+* K)
  (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
  (hτ : ∀ x : K,
    τ (algebraMap K (AlgebraicClosure K) x) = algebraMap K (AlgebraicClosure K) (κ x))
  (hSst : ∀ v w : HeightOneSpectrum (𝓞 K),
    w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K) → (v ∈ S ↔ w ∈ S))

/-- **The named input: `τ` maps the ring class field `H_f ⊆ K_S` onto itself** (`H_f/ℚ` is
Galois; tex 2778–2795). Kind: definition (a statement, the remaining input). -/
def RingClassFieldConjStable : Prop :=
  ∀ x : KS K S, x ∈ ringClassFieldOf f hf S hS ↔ tauS K κ τ hτ S hSst x ∈ ringClassFieldOf f hf S hS

variable {f hf S hS κ τ hτ hSst}

/-- The restriction of `τ` to `H_f`. Kind: definition. -/
def tauH (hst : RingClassFieldConjStable f hf S hS κ τ hτ hSst) :
    ringClassFieldOf f hf S hS ≃+* ringClassFieldOf f hf S hS where
  toFun x := ⟨tauS K κ τ hτ S hSst (x : KS K S), (hst x).mp x.2⟩
  invFun y := ⟨(tauS K κ τ hτ S hSst).symm (y : KS K S), (hst _).mpr (by
    rw [RingEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext ((tauS K κ τ hτ S hSst).symm_apply_apply (x : KS K S))
  right_inv y := Subtype.ext ((tauS K κ τ hτ S hSst).apply_symm_apply (y : KS K S))
  map_mul' x y := Subtype.ext (map_mul (tauS K κ τ hτ S hSst) (x : KS K S) y)
  map_add' x y := Subtype.ext (map_add (tauS K κ τ hτ S hSst) (x : KS K S) y)

theorem tauH_algebraMap (hst : RingClassFieldConjStable f hf S hS κ τ hτ hSst) (a : K) :
    tauH hst (algebraMap K (ringClassFieldOf f hf S hS) a) =
      algebraMap K (ringClassFieldOf f hf S hS) (κ a) :=
  Subtype.ext (tauS_algebraMap K κ τ hτ S hSst a)

/-- **The restriction of `τ σ τ⁻¹` to `H_f` is `τ (σ|_{H_f}) τ⁻¹`.** Kind: PROVED. -/
theorem ringClassRes_conjGKS (hst : RingClassFieldConjStable f hf S hS κ τ hτ hSst)
    (σ : GKS K S) :
    ringClassRes f hf S hS (conjGKS K κ τ hτ S hSst σ) =
      galConjFun (K := K) (L := ringClassFieldOf f hf S hS) κ (tauH hst) (tauH_algebraMap hst)
        (ringClassRes f hf S hS σ) := by
  apply AlgEquiv.ext
  intro x
  have h1 := AlgEquiv.restrictNormal_commutes (galS K S (conjGKS K κ τ hτ S hSst σ))
    (ringClassFieldOf f hf S hS) x
  have h2 := AlgEquiv.restrictNormal_commutes (galS K S σ) (ringClassFieldOf f hf S hS)
    ((tauH hst).symm x)
  apply Subtype.ext
  change algebraMap (ringClassFieldOf f hf S hS) (KS K S)
      ((galS K S (conjGKS K κ τ hτ S hSst σ)).restrictNormal (ringClassFieldOf f hf S hS) x) =
    tauS K κ τ hτ S hSst (algebraMap (ringClassFieldOf f hf S hS) (KS K S)
      ((galS K S σ).restrictNormal (ringClassFieldOf f hf S hS) ((tauH hst).symm x)))
  rw [h1, h2]
  apply Subtype.ext
  exact conjGKS_apply K κ τ hτ S hSst σ x

/-- `τ` transported to Tau Ceti's ring class field `R` along `H_f ≃ R`. Kind: definition. -/
def tauR (hst : RingClassFieldConjStable f hf S hS κ τ hτ hSst) :
    ringClassField (ringClassOrder (K := K) f hf) ≃+*
      ringClassField (ringClassOrder (K := K) f hf) :=
  (ringClassFieldOfEquiv f hf S hS).toRingEquiv.symm.trans
    ((tauH hst).trans (ringClassFieldOfEquiv f hf S hS).toRingEquiv)

theorem tauR_algebraMap (hst : RingClassFieldConjStable f hf S hS κ τ hτ hSst) (a : K) :
    tauR hst (algebraMap K (ringClassField (ringClassOrder (K := K) f hf)) a) =
      algebraMap K (ringClassField (ringClassOrder (K := K) f hf)) (κ a) := by
  have e1 : (ringClassFieldOfEquiv f hf S hS).toRingEquiv.symm
      (algebraMap K (ringClassField (ringClassOrder (K := K) f hf)) a) =
      algebraMap K (ringClassFieldOf f hf S hS) a :=
    (ringClassFieldOfEquiv f hf S hS).symm.commutes a
  simp only [tauR, RingEquiv.trans_apply]
  rw [e1, tauH_algebraMap]
  exact (ringClassFieldOfEquiv f hf S hS).commutes (κ a)

/-- Transport of the conjugation along `H_f ≃ R`. Kind: PROVED. -/
theorem autCongr_galConjFun (hst : RingClassFieldConjStable f hf S hS κ τ hτ hSst)
    (g : ringClassGal f hf S hS) :
    AlgEquiv.autCongr (ringClassFieldOfEquiv f hf S hS)
        (galConjFun (K := K) (L := ringClassFieldOf f hf S hS) κ (tauH hst)
          (tauH_algebraMap hst) g) =
      galConjFun (K := K) (L := ringClassField (ringClassOrder (K := K) f hf)) κ (tauR hst)
        (tauR_algebraMap hst) (AlgEquiv.autCongr (ringClassFieldOfEquiv f hf S hS) g) := by
  apply AlgEquiv.ext
  intro r
  simp [tauR, galConjFun, AlgEquiv.autCongr_apply]

/-- **`θ(Art 𝔭) = Art(κ𝔭)`** in `Gal(H_f/K)`. Kind: PROVED. -/
theorem galConj_artinClass (hst : RingClassFieldConjStable f hf S hS κ τ hτ hSst)
    (J : integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus)
    [(J : Ideal (𝓞 K)).IsPrime] :
    galConjFun (K := K) (L := ringClassFieldOf f hf S hS) κ (tauH hst) (tauH_algebraMap hst)
        (artinClass f hf S hS J) = artinClass f hf S hS (conjPrimeTo κ f hf J) := by
  apply (AlgEquiv.autCongr (ringClassFieldOfEquiv f hf S hS)).injective
  rw [autCongr_galConjFun]
  have e : ∀ J', AlgEquiv.autCongr (ringClassFieldOfEquiv f hf S hS) (artinClass f hf S hS J') =
      ringClassArtinEquiv (ringClassOrder (K := K) f hf)
        ((ringClassOrder (K := K) f hf).picClass J') := by
    intro J'
    rw [artinClass, ringClassPicEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rw [e, e]
  exact galConj_ringClassArtin f hf κ (tauR hst) (tauR_algebraMap hst) J

/-- `artinClass` is multiplicative. Kind: PROVED. -/
theorem artinClass_mul
    (J J' : integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus) :
    artinClass f hf S hS (J * J') = artinClass f hf S hS J * artinClass f hf S hS J' := by
  simp only [artinClass, map_mul]

theorem artinClass_one : artinClass f hf S hS (1 : integralIdealsPrimeTo
    (ringClassOrder (K := K) f hf).conductorModulus) = 1 := by
  simp only [artinClass, map_one]

/-- **Conjugation by `τ` inverts `Gal(H_f/K)`** (tex 2778–2795): from `θ(Art 𝔭) = Art(κ𝔭) =
Art(𝔭)⁻¹` on the primes prime to the conductor, which generate. Kind: PROVED. -/
theorem galConj_eq_inv (hK : Module.finrank ℚ K = 2) (hκ : ringEquivAlg κ ≠ 1)
    (hst : RingClassFieldConjStable f hf S hS κ τ hτ hSst) (g : ringClassGal f hf S hS) :
    galConjFun (K := K) (L := ringClassFieldOf f hf S hS) κ (tauH hst) (tauH_algebraMap hst) g =
      g⁻¹ := by
  classical
  let θ := galConj (K := K) (L := ringClassFieldOf f hf S hS) κ (tauH hst) (tauH_algebraMap hst)
  let ψ : ringClassGal f hf S hS →* ringClassGal f hf S hS := θ.toMonoidHom * MonoidHom.id _
  have hψ : ∀ x, ψ x = galConjFun (K := K) (L := ringClassFieldOf f hf S hS) κ (tauH hst)
      (tauH_algebraMap hst) x * x := fun x => rfl
  have key : ∀ (I : Ideal (𝓞 K))
      (hI : I ∈ integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus),
      ψ (artinClass f hf S hS ⟨I, hI⟩) = 1 := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ =>
      intro hI
      exact absurd (Ideal.zero_eq_bot) ((mem_integralIdealsPrimeTo_conductorModulus_iff _).mp hI).1
    | h₂ x hx =>
      intro hI
      have hx1 : x = ⊤ := Ideal.isUnit_iff.mp hx
      subst hx1
      have : (⟨⊤, hI⟩ :
          integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus) = 1 :=
        Subtype.ext Ideal.one_eq_top.symm
      rw [this, artinClass_one, map_one]
    | h₃ a P ha hP ih =>
      intro hI
      have hI' := (mem_integralIdealsPrimeTo_conductorModulus_iff _).mp hI
      have hPmem : P ∈ integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus := by
        rw [mem_integralIdealsPrimeTo_conductorModulus_iff]
        refine ⟨hP.ne_zero, eq_top_iff.mpr ?_⟩
        rw [← hI'.2]
        exact sup_le_sup_right (Ideal.mul_le_left (I := P) (J := a)) _
      have hamem : a ∈ integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus := by
        rw [mem_integralIdealsPrimeTo_conductorModulus_iff]
        refine ⟨ha, eq_top_iff.mpr ?_⟩
        rw [← hI'.2]
        exact sup_le_sup_right (Ideal.mul_le_right (I := P) (J := a)) _
      have e : (⟨P * a, hI⟩ :
          integralIdealsPrimeTo (ringClassOrder (K := K) f hf).conductorModulus) =
          ⟨P, hPmem⟩ * ⟨a, hamem⟩ := Subtype.ext rfl
      rw [e, artinClass_mul, map_mul, ih hamem, mul_one]
      have : ((⟨P, hPmem⟩ : integralIdealsPrimeTo
          (ringClassOrder (K := K) f hf).conductorModulus) : Ideal (𝓞 K)).IsPrime :=
        Ideal.isPrime_of_prime hP
      rw [hψ, galConj_artinClass hst, mul_comm]
      exact artinClass_conj_mul f hf S hS hK κ hκ _
  obtain ⟨J, hJ⟩ := (ringClassOrder (K := K) f hf).picClass_surjective
    ((ringClassPicEquiv f hf S hS).symm g)
  have hg : g = artinClass f hf S hS J := by
    rw [artinClass, hJ, MulEquiv.apply_symm_apply]
  have h := key J J.2
  rw [hψ] at h
  rw [hg]
  exact eq_inv_of_mul_eq_one_left h

/-- **`RingClassDihedral` from the `τ`-stability of the ring class field** (tex 2778–2795; Cox,
Lemma 9.3, here proved): for `K` quadratic, `κ = τ|_K ≠ 1`, and `τ(H_f) = H_f`,
`ringClassRes(τ σ τ⁻¹) = (ringClassRes σ)⁻¹`. Kind: PROVED (from `RingClassFieldConjStable`). -/
theorem ringClassDihedral_of_stable (hK : Module.finrank ℚ K = 2) (hκ : ringEquivAlg κ ≠ 1)
    (hst : RingClassFieldConjStable f hf S hS κ τ hτ hSst) :
    ZInQ.Contrib.CloudB3E2.XiConj.RingClassDihedral f hf S hS κ τ hτ hSst := fun σ => by
  rw [ringClassRes_conjGKS hst σ]
  exact galConj_eq_inv hK hκ hst _

end Assembly

end ZInQ.Contrib.CloudB3E1Dihedral
