import ZInQKernel.Contrib.OneProof.RC.CoefModules.Ring
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Galois
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Kummer.SqrtMem

/-!
# Lane RC28 (coefficient modules), part 2: the characters `χ_h`, `Ψ_i` of `G_{K,S}`

Manuscript `diophantine_zq.tex` (11/5), tex 2725–2741 and the proof of Lemma
`ex:arith-conjugate-duality`, tex 2779–2796:

> `ξ_i : Gal(H_{r_i}/K) → ℤ/2^{n_i}ℤ`, `Ψ_i = (1+t)^{ξ_i}`, where `n_i` is large enough that
> `(1+t)^{2^{n_i}} = 1` in `A_i`. … Write `α_i = χ_hΨ_i`.

Everything is over the genuine `G_{K,S} = Gal(K_S/K)` of lane RC26 (`GKS K S`, the tree's
`GaloisGroupS K S` with its Krull topology), `K_S = unramifiedOutside K S ⊂ K̄`.

* `KS K S`: the field `K_S` as a type; `galS σ`: `σ ∈ G_{K,S}` as a `K`-automorphism of `K_S`.
* `isOpen_setOf_galS_apply_eq`: the stabilizer of an element of `K_S` is open (it is the fixing
  subgroup of the finite extension it generates).
* `IsOpenKer α`: a character `α : G_{K,S} → Aˣ` with open kernel (a continuous character into a
  discrete ring).
* `quadChar s`: **the quadratic character `χ_h`** of `K(√h)/K`, from a square root `s ∈ K_S` of
  `h ∈ Kˣ`: `σ s = χ_h(σ) s` (`quadChar_spec`); open kernel (`IsOpenKer`). The square root lies
  in `K_S` as soon as `S` contains the primes above `2` and `h` is a unit outside `S` up to
  squares (`exists_sqrt_mem_KS`, from the other group's `sqrtMemOfSelmer_proof`).
* `movingCharS ξ`: **the moving character `Ψ = (1 + t)^ξ`** with values in `A_i^×`, for a
  continuous `ξ : G_{K,S} → ℤ/2^{2i}` (lane RC10's `movingChar` with `n_i = 2i`, `one_add_tA_pow_two_pow`).
  The text's `ξ_i` is a character of the ring-class group `Gal(H_{r_i}/K)`; on `G_{K,S}` it is its
  inflation (`inflChar`, for any finite Galois `H ⊂ K_S`).
* `alphaChar`: `α_i = χ_h Ψ_i` (tex 2791).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CoefModules

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside GaloisGroupS)

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The field `K_S` (the maximal subextension of `K̄/K` unramified outside `S`) as a type. -/
abbrev KS : Type := ↥(unramifiedOutside K S)

/-- An element of `G_{K,S}` as a `K`-automorphism of `K_S`. -/
abbrev galS (σ : GKS K S) : KS K S ≃ₐ[K] KS K S := σ

/-- `G_{K,S} → Gal(K_S/K)`, the identity (`GKS` is a type synonym with frozen instances). -/
def galHom : GKS K S →* (KS K S ≃ₐ[K] KS K S) where
  toFun σ := σ
  map_one' := rfl
  map_mul' _ _ := rfl

omit [NumberField K] in
theorem galS_mul (σ τ : GKS K S) (x : KS K S) : galS K S (σ * τ) x = galS K S σ (galS K S τ x) :=
  rfl

omit [NumberField K] in
theorem galS_one (x : KS K S) : galS K S 1 x = x := rfl

omit [NumberField K] in
/-- Every element of `K_S` is integral over `K`. Kind: PROVED. -/
theorem isIntegral_KS (x : KS K S) : IsIntegral K x :=
  (IntermediateField.isIntegral_iff).mpr (Algebra.IsIntegral.isIntegral (x : AlgebraicClosure K))

/-- The fixing subgroup of an intermediate field of `K_S/K`, as a subgroup of `G_{K,S}`. -/
def fixS (L : IntermediateField K (KS K S)) : Subgroup (GKS K S) := L.fixingSubgroup

omit [NumberField K] in
/-- The fixing subgroup of a finite subextension is open (Krull topology). Kind: PROVED. -/
theorem isOpen_fixS (L : IntermediateField K (KS K S)) [FiniteDimensional K L] :
    IsOpen (fixS K S L : Set (GKS K S)) :=
  IntermediateField.fixingSubgroup_isOpen L

omit [NumberField K] in
theorem mem_fixS {L : IntermediateField K (KS K S)} {σ : GKS K S} :
    σ ∈ fixS K S L ↔ ∀ x ∈ L, galS K S σ x = x :=
  IntermediateField.mem_fixingSubgroup_iff _ _

omit [NumberField K] in
/-- An automorphism fixing `x` fixes `K(x)`. Kind: PROVED. -/
theorem mem_fixS_adjoin_iff (x : KS K S) (σ : GKS K S) :
    σ ∈ fixS K S (IntermediateField.adjoin K {x}) ↔ galS K S σ x = x := by
  rw [mem_fixS]
  constructor
  · intro hσ
    exact hσ x (IntermediateField.mem_adjoin_simple_self K x)
  · intro hσ y hy
    have hle : IntermediateField.adjoin K {x} ≤
        IntermediateField.fixedField (Subgroup.zpowers (galS K S σ)) := by
      rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
      rintro f ⟨n, rfl⟩
      change (galS K S σ ^ n) x = x
      induction n using Int.induction_on with
      | zero => rfl
      | succ n ih =>
        rw [zpow_add_one, AlgEquiv.mul_apply, hσ, ih]
      | pred n ih =>
        rw [zpow_sub_one, AlgEquiv.mul_apply]
        have : (galS K S σ)⁻¹ x = x := by
          rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, hσ]
        rw [this, ih]
    exact (IntermediateField.mem_fixedField_iff _ _).mp (hle hy) _ (Subgroup.mem_zpowers _)

/-- **The stabilizer in `G_{K,S}` of an element of `K_S` is open** (Krull topology): it is the
fixing subgroup of the finite extension `K(x)`. Kind: PROVED. -/
theorem isOpen_setOf_galS_apply_eq (x : KS K S) :
    IsOpen {σ : GKS K S | galS K S σ x = x} := by
  have : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_KS K S x)
  have heq : {σ : GKS K S | galS K S σ x = x} =
      (fixS K S (IntermediateField.adjoin K {x}) : Set (GKS K S)) := by
    ext σ
    exact (mem_fixS_adjoin_iff K S x σ).symm
  rw [heq]
  exact isOpen_fixS K S _

/-- The open subgroup of `G_{K,S}` fixing `x ∈ K_S`. -/
def stabS (x : KS K S) : Subgroup (GKS K S) := fixS K S (IntermediateField.adjoin K {x})

theorem isOpen_stabS (x : KS K S) : IsOpen (stabS K S x : Set (GKS K S)) := by
  have : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_KS K S x)
  exact isOpen_fixS K S _

omit [NumberField K] in
theorem mem_stabS {x : KS K S} {σ : GKS K S} : σ ∈ stabS K S x ↔ galS K S σ x = x :=
  mem_fixS_adjoin_iff K S x σ

/-! ### Characters with open kernel -/

/-- A character `α : G → Aˣ` of a topological group **with open kernel** (a continuous character
into a discrete coefficient ring). -/
class IsOpenKer {G A : Type} [Group G] [TopologicalSpace G] [Monoid A] (α : G →* Aˣ) : Prop where
  isOpen_ker : IsOpen (α.ker : Set G)

/-- The pointwise product of two characters (written out, to avoid instance unification
issues on the unit groups of quotient rings). -/
def charMul {G A : Type} [Group G] [CommMonoid A] (α β : G →* Aˣ) : G →* Aˣ where
  toFun g := α g * β g
  map_one' := by simp
  map_mul' g h := by rw [map_mul, map_mul, mul_mul_mul_comm]

theorem charMul_apply {G A : Type} [Group G] [CommMonoid A] (α β : G →* Aˣ) (g : G) :
    charMul α β g = α g * β g := rfl

/-- The inverse of a character. -/
def charInv {G A : Type} [Group G] [CommMonoid A] (α : G →* Aˣ) : G →* Aˣ where
  toFun g := (α g)⁻¹
  map_one' := by simp
  map_mul' g h := by rw [map_mul, mul_inv]

theorem charInv_apply {G A : Type} [Group G] [CommMonoid A] (α : G →* Aˣ) (g : G) :
    charInv α g = (α g)⁻¹ := rfl

theorem isOpenKer_charMul {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CommMonoid A] (α β : G →* Aˣ) [hα : IsOpenKer α] [hβ : IsOpenKer β] :
    IsOpenKer (charMul α β) := by
  refine ⟨Subgroup.isOpen_mono (H₁ := α.ker ⊓ β.ker) (fun g hg => ?_) ?_⟩
  · rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hg
    rw [MonoidHom.mem_ker, charMul_apply, hg.1, hg.2, mul_one]
  · rw [Subgroup.coe_inf]
    exact hα.isOpen_ker.inter hβ.isOpen_ker

instance isOpenKer_charMul_inst {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CommMonoid A] (α β : G →* Aˣ) [IsOpenKer α] [IsOpenKer β] : IsOpenKer (charMul α β) :=
  isOpenKer_charMul α β

instance isOpenKer_charInv {G A : Type} [Group G] [TopologicalSpace G] [CommMonoid A]
    (α : G →* Aˣ) [hα : IsOpenKer α] : IsOpenKer (charInv α) := by
  refine ⟨?_⟩
  have : (charInv α).ker = α.ker := by
    ext g
    simp [charInv_apply]
  rw [this]
  exact hα.isOpen_ker

instance isOpenKer_one {G A : Type} [Group G] [TopologicalSpace G] [Monoid A] :
    IsOpenKer (1 : G →* Aˣ) :=
  ⟨by
    have : (1 : G →* Aˣ).ker = ⊤ := by ext g; simp [MonoidHom.mem_ker]
    rw [this]
    exact isOpen_univ⟩

/-- Composing with a monoid map of the values keeps the kernel open. -/
theorem isOpenKer_map {G A B : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Monoid A] [Monoid B] (α : G →* Aˣ) [hα : IsOpenKer α] (f : Aˣ →* Bˣ) :
    IsOpenKer (f.comp α) :=
  ⟨Subgroup.isOpen_mono (H₁ := α.ker) (fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [MonoidHom.comp_apply, hg, map_one]) hα.isOpen_ker⟩

/-! ### The quadratic character `χ_h` -/

section Quad

variable {K S}
variable (s : KS K S) {h : K} (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)

include hs in
/-- `σ(√h) = ±√h`. Kind: PROVED. -/
theorem galS_sqrt (σ : GKS K S) : galS K S σ s = s ∨ galS K S σ s = -s := by
  have : (galS K S σ s) ^ 2 = s ^ 2 := by rw [← map_pow, hs, AlgEquiv.commutes]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp this

include hs0 in
theorem neg_ne_self_of_ne_zero : -s ≠ s := by
  intro h'
  have h2 : (2 : KS K S) * s = 0 := by linear_combination -h'
  exact hs0 ((mul_eq_zero.mp h2).resolve_left two_ne_zero)

open Classical in
/-- **The quadratic character `χ_h : G_{K,S} → {±1}`** of `K(√h)/K` (tex 2726, 2791), from a
square root `s ∈ K_S` of `h`: `χ_h(σ) = σ(s)/s`. -/
def quadChar : GKS K S →* ℤˣ where
  toFun σ := if galS K S σ s = s then 1 else -1
  map_one' := by simp [galS_one]
  map_mul' σ τ := by
    have hne := neg_ne_self_of_ne_zero s hs0
    rcases galS_sqrt s hs σ with h1 | h1 <;> rcases galS_sqrt s hs τ with h2 | h2
    · simp [galS_mul, h1, h2]
    · have : galS K S (σ * τ) s = -s := by rw [galS_mul, h2, map_neg, h1]
      simp [this, h1, h2, hne]
    · have : galS K S (σ * τ) s = -s := by rw [galS_mul, h2, h1]
      simp [this, h1, h2, hne]
    · have : galS K S (σ * τ) s = s := by rw [galS_mul, h2, map_neg, h1, neg_neg]
      simp [this, h1, h2, hne]

/-- **`σ(√h) = χ_h(σ) √h`.** Kind: PROVED. -/
theorem quadChar_spec (σ : GKS K S) :
    galS K S σ s = ((quadChar s hs hs0 σ : ℤˣ) : ℤ) • s := by
  have hne := neg_ne_self_of_ne_zero s hs0
  rcases galS_sqrt s hs σ with h1 | h1
  · simp [quadChar, h1]
  · simp [quadChar, h1, hne]

/-- `χ_h` has open kernel: its kernel is the stabilizer of `√h`. Kind: PROVED. -/
instance quadChar_isOpenKer : IsOpenKer (quadChar s hs hs0) := by
  refine ⟨?_⟩
  have : ((quadChar s hs hs0).ker : Set (GKS K S)) = {σ : GKS K S | galS K S σ s = s} := by
    ext σ
    have hne := neg_ne_self_of_ne_zero s hs0
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_ofPred_eq]
    rcases galS_sqrt s hs σ with h1 | h1
    · simp [quadChar, h1]
    · have hq : quadChar s hs hs0 σ = -1 := by simp [quadChar, h1, hne]
      rw [hq, h1]
      constructor
      · intro h'; exact absurd h' (by decide)
      · intro h'; exact absurd h' hne
  rw [this]
  exact isOpen_setOf_galS_apply_eq K S s

end Quad

/-- **A square root of `h` lies in `K_S`** when `S` contains the primes above `2` and `h` is a
Selmer class (`v(h)` even outside `S`; e.g. every prime dividing `h` lies in `S`): the other
group's `sqrtMemOfSelmer_proof` (Tau Ceti's radical criterion). Kind: PROVED. -/
theorem exists_sqrt_mem_KS (hS2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (h : Kˣ) (hsel : ZInQ.Contrib.CloudB3RC53.RankCounts.KummerS.sqClass h ∈
      IsDedekindDomain.selmerGroup (R := 𝓞 K) (K := K) (S := S) (n := 2)) :
    ∃ s : KS K S, s ^ 2 = algebraMap K (KS K S) h ∧ s ≠ 0 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) h)
    (by norm_num : 0 < 2)
  have hmem := ZInQ.Contrib.CloudB3RC53.RankCounts.KummerS.sqrtMemOfSelmer_proof K S hS2 h z hz hsel
  refine ⟨⟨z, hmem⟩, Subtype.ext (by simpa using hz), fun h0 => ?_⟩
  have hz0 : z = 0 := congrArg Subtype.val h0
  rw [hz0, zero_pow two_ne_zero] at hz
  exact h.ne_zero ((map_eq_zero_iff _ (algebraMap K (AlgebraicClosure K)).injective).mp hz.symm)

/-! ### The moving character `Ψ = (1 + t)^ξ` and `α = χ_h Ψ` -/

section Moving

variable {K S} (i : ℕ)

/-- `1 + t ∈ A_i^×`. -/
def onePlusT : (Acoef i)ˣ := (isUnit_one_add_tA i).unit

theorem onePlusT_pow : onePlusT i ^ (2 ^ (2 * i)) = 1 :=
  Units.ext (by simpa [onePlusT] using one_add_tA_pow_two_pow i)

/-- **The moving character `Ψ = (1 + t)^ξ : G_{K,S} → A_i^×`** (tex 2781–2783, lane RC10's
`movingChar` with `n_i = 2i`) for a character `ξ : G_{K,S} → ℤ/2^{2i}`. -/
def movingCharS (ξ : GKS K S →* Multiplicative (ZMod (2 ^ (2 * i)))) : GKS K S →* (Acoef i)ˣ :=
  movingChar (2 * i) (onePlusT i) (onePlusT_pow i) ξ

/-- `Ψ` has open kernel when `ξ` has (its kernel contains that of `ξ`). Kind: PROVED. -/
theorem movingCharS_isOpenKer (ξ : GKS K S →* Multiplicative (ZMod (2 ^ (2 * i))))
    (hξ : IsOpen (ξ.ker : Set (GKS K S))) : IsOpenKer (movingCharS i ξ) :=
  ⟨Subgroup.isOpen_mono (H₁ := ξ.ker) (fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [movingCharS, movingChar, hg]) hξ⟩

/-- tex 2786–2788: if conjugation `c` inverts `ξ`, it inverts `Ψ` (lane RC10's
`movingChar_conj`). Kind: PROVED. -/
theorem movingCharS_conj (ξ : GKS K S →* Multiplicative (ZMod (2 ^ (2 * i))))
    (c : GKS K S →* GKS K S) (hξ : ∀ g, ξ (c g) = (ξ g)⁻¹) (g : GKS K S) :
    movingCharS i ξ (c g) = (movingCharS i ξ g)⁻¹ :=
  movingChar_conj (2 * i) (onePlusT i) (onePlusT_pow i) ξ c hξ g

/-- `ℤˣ → A^×`. -/
def intUnitsTo (A : Type) [CommRing A] : ℤˣ →* Aˣ := Units.map (Int.castRingHom A).toMonoidHom

/-- **`α_i = χ_h Ψ_i`** (tex 2791) with values in `A_i^×`. -/
def alphaChar (χ : GKS K S →* ℤˣ) (ξ : GKS K S →* Multiplicative (ZMod (2 ^ (2 * i)))) :
    GKS K S →* (Acoef i)ˣ :=
  charMul ((intUnitsTo (Acoef i)).comp χ) (movingCharS i ξ)

/-- `α_i` has open kernel. Kind: PROVED. -/
theorem alphaChar_isOpenKer (χ : GKS K S →* ℤˣ) [IsOpenKer χ]
    (ξ : GKS K S →* Multiplicative (ZMod (2 ^ (2 * i)))) (hξ : IsOpen (ξ.ker : Set (GKS K S))) :
    IsOpenKer (alphaChar i χ ξ) := by
  have := isOpenKer_map χ (intUnitsTo (Acoef i))
  have := movingCharS_isOpenKer i ξ hξ
  exact isOpenKer_charMul _ _

end Moving

/-! ### Inflation from a finite Galois subextension (the ring-class field) -/

section Inflation

variable {K S}

/-- **Inflation of a character of `Gal(H/K)`** for a finite Galois `H ⊂ K_S` (the ring-class
field `H_{r_i}` of the text, tex 2781) to `G_{K,S}`, through the restriction `σ ↦ σ|_H`. -/
def inflChar (H : IntermediateField K (KS K S)) [Normal K H] {A : Type} [Monoid A]
    (ξ : (H ≃ₐ[K] H) →* A) : GKS K S →* A :=
  ξ.comp ((AlgEquiv.restrictNormalHom (F := K) (K₁ := KS K S) H).comp (galHom K S))

/-- The inflated character has open kernel when `H` is finite over `K` (its kernel contains the
fixing subgroup of `H`). Kind: PROVED. -/
theorem inflChar_isOpen_ker (H : IntermediateField K (KS K S)) [Normal K H] [FiniteDimensional K H]
    {A : Type} [Group A] (ξ : (H ≃ₐ[K] H) →* A) :
    IsOpen ((inflChar H ξ).ker : Set (GKS K S)) := by
  refine Subgroup.isOpen_mono (H₁ := fixS K S H) (fun σ hσ => ?_) (isOpen_fixS K S H)
  rw [MonoidHom.mem_ker]
  change ξ (AlgEquiv.restrictNormalHom (F := K) (K₁ := KS K S) H (galS K S σ)) = 1
  have : AlgEquiv.restrictNormalHom (F := K) (K₁ := KS K S) H (galS K S σ) = 1 := by
    ext x
    have h1 := AlgEquiv.restrictNormal_commutes (galS K S σ) H x
    have h2 : (galS K S σ) (algebraMap H (KS K S) x) = algebraMap H (KS K S) x :=
      (mem_fixS K S).mp hσ _ x.2
    rw [h2] at h1
    have h3 := (algebraMap H (KS K S)).injective h1
    exact congrArg (fun y : H => ((y : KS K S) : AlgebraicClosure K)) h3
  exact (congrArg ξ this).trans (map_one ξ)

end Inflation

end ZInQ.Manuscript.RC.CoefModules
