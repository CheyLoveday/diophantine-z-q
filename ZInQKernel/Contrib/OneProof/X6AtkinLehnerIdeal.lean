import ZInQKernel.Contrib.OneProof.GRX6AbPrint
import ZInQKernel.Contrib.OneProof.ElkiesX6StarEvery

/-!
# x6-coarse: the Atkin–Lehner clause of `X₀(6,1)` in its printed (ideal-quotient) form

The leaf `GRX6AbPrint.X6CoarseModuli` states the Atkin–Lehner clause in *twist form*: every automorphism `α` of
`𝒪` is induced by an automorphism of `X` acting on moduli by `(A, ι) ↦ (A, ι ∘ α)`. The printed definition of the
Atkin–Lehner involution `w_m` (Rotger, Trans. AMS 356 (2004); Elkies, *Shimura curve computations* (1998) p. 10:
`A ↦ A/ker I_p`; González–Rotger (2006) §2) is the *ideal-quotient form*:
`w_m(A, ι) = (A/A[I_m], ι_m)` with `I_m` the two-sided ideal of `𝒪` of reduced norm `m`, `A[I_m]` the subgroup
scheme killed by `I_m`, and `ι_m` the induced action.

This file
1. defines `I_m` concretely (`idealI k = {a ∈ 𝒪 : m ∣ nrd a}`, `m = |N k| = 1, 2, 3, 6`) and proves
   `I_m = 𝒪 μ_m` for `μ_m = 1, i, j, ij` (`mem_idealI_iff`; the ramified primes' ideals are principal);
2. defines `A[I](T)` on `T`-points for every `K`-scheme `T` (`InTors`), and "`φ : A → A'` is a quotient of `A` by
   `A[I]`" (`IsIdealQuotient`: an `𝒪`-equivariant isogeny whose scheme-theoretic kernel, as a functor of points,
   is `A[I]`);
3. proves that `ι(μ_m) : (A, ι) → (A, ι ∘ Ad μ_m)` is such a quotient (`canonical`);
4. states the printed clause (`IsAtkinLehnerIdeal`, `ALIdealClause`) and proves **printed ⇒ twist with no
   hypothesis** (`isAtkinLehner_of_ideal`, `alTwist_of_alIdeal`), and **twist ⇒ printed** from the textbook fact
   that an isogeny is the quotient by its kernel (`IsogenyQuotient`; `iso_of_quotient`, `alIdeal_of_alTwist`);
5. states `X6CoarseModuliIdeal`, the leaf with its Atkin–Lehner clause in printed form, and proves
   `X6CoarseModuliIdeal → X6CoarseModuli` (no hypothesis) and the converse from `IsogenyQuotient`;
6. compares the two Atkin–Lehner groups on a witness (`atkinLehnerWIdeal_subset`, `atkinLehnerW_eq_of_clause`);
7. proves that the Galois clause of `X6CoarseModuli` is exactly the naturality square of the coarse map at
   `Spec σ` (`galoisClause_iff_natural`, with the base change `bcAut` of a pair along `σ`);
8. restates Elkies' leaf with Elkies' isogeny-form `W` (`ElkiesX6StarEveryIdeal`) and proves
   `ElkiesPrint.ElkiesX6StarEvery` from it (`elkiesX6StarEvery_of_ideal'`).

No `sorry`; standard axioms only.
-/

set_option linter.style.longLine false

noncomputable section

namespace X6ALIdeal

open CategoryTheory AlgebraicGeometry Limits MonObj MonoidalCategory
open LeafQM LeafQM.AV
open LeafQM.AV.Pin.NormO (ei ej ui uj nrdZ two_dvd_mulCoord_ei three_dvd_mulCoord_ej)
open HDec.LeafQM.AV.Pin.Exact (nrd nrd_mul nrd_ofInt tt rep N nrd_tt conjO_apply rep_cover)

/-! ## 1. The two-sided ideals `I_m` of `𝒪` -/

theorem tt_mem (k : Fin 4) : ((tt k : Bˣ) : B) ∈ O := by
  fin_cases k
  · exact O.one_mem
  · exact ⟨ei, rfl⟩
  · exact ⟨ej, rfl⟩
  · exact O.mul_mem ⟨ei, rfl⟩ ⟨ej, rfl⟩

/-- `μ_m ∈ 𝒪`: `1, i, j, ij` for `k = 0, 1, 2, 3` (reduced norms `N k = 1, −2, 3, −6`). -/
def mu (k : Fin 4) : O := ⟨(tt k : B), tt_mem k⟩

/-- **The two-sided ideal `I_m` of `𝒪` of reduced norm `m = |N k|`** (`m = 1, 2, 3, 6`):
`I_m = {a ∈ 𝒪 : m ∣ nrd a}`. For a prime `p` ramified in `B` the unique two-sided prime of `𝒪` above `p` is
`{a : p ∣ nrd a}`, of reduced norm `p`, and `I_6 = I_2 I_3` (STANDARD: Vignéras, *Arithmétique des algèbres de
quaternions*, LNM 800, Ch. II §1; Voight, *Quaternion algebras*, Thm 13.3.11; locators UNVERIFIED). It is a
two-sided ideal since `nrd` is multiplicative and integral on `𝒪` (`mul_mem_idealI_left`, `mul_mem_idealI_right`),
and `I_m = 𝒪 μ_m` (`mem_idealI_iff`). -/
def idealI (k : Fin 4) : Set O := {a | ∃ c : ℤ, nrd (a : B) = (N k : ℚ) * c}

theorem nrd_O (a : O) : ∃ z : ℤ, nrd (a : B) = z := by
  obtain ⟨n, hn⟩ := a.2
  exact ⟨nrdZ n, by rw [hn, nrd_ofInt]; rfl⟩

theorem mul_mem_idealI_left (k : Fin 4) (b a : O) (ha : a ∈ idealI k) : b * a ∈ idealI k := by
  obtain ⟨c, hc⟩ := ha
  obtain ⟨z, hz⟩ := nrd_O b
  exact ⟨z * c, by rw [MulMemClass.coe_mul, nrd_mul, hc, hz]; push_cast; ring⟩

theorem mul_mem_idealI_right (k : Fin 4) (a b : O) (ha : a ∈ idealI k) : a * b ∈ idealI k := by
  obtain ⟨c, hc⟩ := ha
  obtain ⟨z, hz⟩ := nrd_O b
  exact ⟨c * z, by rw [MulMemClass.coe_mul, nrd_mul, hc, hz]; push_cast; ring⟩

theorem mu_mem (k : Fin 4) : mu k ∈ idealI k := ⟨1, by rw [mu, nrd_tt]; simp⟩

theorem left_i (n : Fin 4 → ℤ) (h : (2 : ℤ) ∣ nrdZ n) : ∃ w, ofInt n = ofInt w * ofInt ei := by
  have hw := two_dvd_mulCoord_ei n h
  choose w hw using hw
  refine ⟨w, ?_⟩
  rw [ofInt_mul]
  congr 1
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  have h3 := hw 3
  simp [mulCoord, ei] at h0 h1 h2 h3
  funext l
  fin_cases l <;> simp [mulCoord, ei] <;> omega

theorem left_j (n : Fin 4 → ℤ) (h : (3 : ℤ) ∣ nrdZ n) : ∃ w, ofInt n = ofInt w * ofInt ej := by
  have hw := three_dvd_mulCoord_ej n h
  choose w hw using hw
  refine ⟨-w, ?_⟩
  rw [ofInt_mul]
  congr 1
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  have h3 := hw 3
  simp [mulCoord, ej] at h0 h1 h2 h3
  funext l
  fin_cases l <;> simp [mulCoord, ej] <;> omega

theorem nrd_ofInt' (n : Fin 4 → ℤ) : nrd (ofInt n) = (nrdZ n : ℚ) := by rw [nrd_ofInt]; rfl

theorem nrdZ_ofInt_mul_ej (w : Fin 4 → ℤ) (n : Fin 4 → ℤ) (h : ofInt n = ofInt w * ofInt ej) :
    nrdZ n = nrdZ w * 3 := by
  have := congrArg nrd h
  rw [nrd_mul, nrd_ofInt', nrd_ofInt', nrd_ofInt'] at this
  have h3 : nrdZ ej = 3 := by simp [nrdZ, ej]
  rw [h3] at this
  exact_mod_cast this

/-- **`I_m = 𝒪 μ_m`**: the two-sided ideal of norm `m` is principal, generated by `μ_m = 1, i, j, ij`. -/
theorem mem_idealI_iff (k : Fin 4) (a : O) : a ∈ idealI k ↔ ∃ c : O, a = c * mu k := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨n, hn⟩ := a.2
    have hnz : (nrdZ n : ℚ) = (N k : ℚ) * c := by rw [← nrd_ofInt', ← hn, hc]
    fin_cases k
    · exact ⟨a, by apply Subtype.ext; simp [mu, tt]⟩
    · have h2 : nrdZ n = -2 * c := by
        have : (nrdZ n : ℚ) = ((-2 * c : ℤ) : ℚ) := by rw [hnz]; push_cast; simp [N]
        exact_mod_cast this
      obtain ⟨w, hw⟩ := left_i n ⟨-c, by rw [h2]; ring⟩
      refine ⟨⟨ofInt w, ⟨w, rfl⟩⟩, Subtype.ext ?_⟩
      rw [MulMemClass.coe_mul, hn, hw]
      rfl
    · have h3 : nrdZ n = 3 * c := by
        have : (nrdZ n : ℚ) = ((3 * c : ℤ) : ℚ) := by rw [hnz]; push_cast; simp [N]
        exact_mod_cast this
      obtain ⟨w, hw⟩ := left_j n ⟨c, h3⟩
      refine ⟨⟨ofInt w, ⟨w, rfl⟩⟩, Subtype.ext ?_⟩
      rw [MulMemClass.coe_mul, hn, hw]
      rfl
    · have h6 : nrdZ n = -6 * c := by
        have : (nrdZ n : ℚ) = ((-6 * c : ℤ) : ℚ) := by rw [hnz]; push_cast; simp [N]
        exact_mod_cast this
      obtain ⟨w, hw⟩ := left_j n ⟨-2 * c, by rw [h6]; ring⟩
      have hw3 := nrdZ_ofInt_mul_ej w n hw
      obtain ⟨w', hw'⟩ := left_i w ⟨-c, by omega⟩
      refine ⟨⟨ofInt w', ⟨w', rfl⟩⟩, Subtype.ext ?_⟩
      rw [MulMemClass.coe_mul, hn, hw, hw', _root_.mul_assoc]
      rfl
  · rintro ⟨c, rfl⟩
    obtain ⟨z, hz⟩ := nrd_O c
    refine ⟨z, ?_⟩
    rw [MulMemClass.coe_mul, nrd_mul, hz]
    change (z : ℚ) * nrd (tt k : B) = _
    rw [nrd_tt]
    ring

/-- `μ_m² = s_m ∈ ℤ`: `1, 2, −3, 6`. -/
def sq : Fin 4 → ℤ := ![1, 2, -3, 6]

theorem mu_mul_mu (k : Fin 4) : mu k * mu k = (sq k : O) := by
  apply Subtype.ext
  rw [MulMemClass.coe_mul, SubringClass.coe_intCast]
  change (tt k : B) * (tt k : B) = _
  fin_cases k
  · simp [tt, sq]
  · change ofInt ei * ofInt ei = _
    rw [ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei, sq, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  · change ofInt ej * ofInt ej = _
    rw [ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej, sq, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  · change (ofInt ei * ofInt ej) * (ofInt ei * ofInt ej) = _
    rw [ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei, ej, sq, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]

theorem sq_ne_zero (k : Fin 4) : sq k ≠ 0 := by
  fin_cases k <;> simp [sq]

/-- `Ad μ_m (a) · μ_m = μ_m · a`. -/
theorem rep_mul_mu (k : Fin 4) (a : O) : rep k a * mu k = mu k * a := by
  apply Subtype.ext
  rw [MulMemClass.coe_mul, MulMemClass.coe_mul]
  change ((rep k a : O) : B) * (tt k : B) = (tt k : B) * a
  rw [rep, conjO_apply]
  simp [_root_.mul_assoc]

/-! ## 2. `A[I]` on points, and quotients by `A[I]` -/

section Quot

variable {K : Type} [Field K]

/-- **`A[I](T)`**: the `T`-points `x` of `A` (for a `K`-scheme `T`) killed by every `ι(a)`, `a ∈ I`. As a functor
of `T` this is the subgroup scheme `A[I] = ⋂_{a ∈ I} ker ι(a)` of the print. -/
def InTors {A : PkgI3.AbVar K} (q : QMStr A) (I : Set O) {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ A.X) : Prop :=
  ∀ a ∈ I, x ≫ (q.iota a).hom = 1

/-- **`φ : (A, ι) → (A', ι')` is a quotient of `A` by `A[I]`**, with `ι'` the induced action: `φ` is
`𝒪`-equivariant (`ι'(a) ∘ φ = φ ∘ ι(a)`), an isogeny (`ψ ∘ φ = [n]`, `φ ∘ ψ = [n]` for some `ψ` and `n ≠ 0`), and
its scheme-theoretic kernel is `A[I]` (equality of subfunctors of `A` on all `K`-schemes `T`). A surjective
homomorphism of abelian varieties identifies its target with the quotient of the source by its kernel
(fppf quotient; Mumford, *Abelian varieties*, §7 Thm 4 and §12; STANDARD, locators UNVERIFIED), so every such
`(A', ι')` is isomorphic to the printed `(A/A[I], ι_I)`. -/
def IsIdealQuotient (P : QMPair K) (I : Set O) (P' : QMPair K) (φ : PkgI3.AbVar.Hom P.A P'.A) : Prop :=
  (∀ a : O, (P.q.iota a).hom ≫ φ.hom = φ.hom ≫ (P'.q.iota a).hom) ∧
  (∃ (ψ : PkgI3.AbVar.Hom P'.A P.A) (n : ℤ), n ≠ 0 ∧
    φ.hom ≫ ψ.hom = ((n : PkgI3.AbVar.End P.A)).hom ∧
    ψ.hom ≫ φ.hom = ((n : PkgI3.AbVar.End P'.A)).hom) ∧
  (∀ (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ P.A.X), x ≫ φ.hom = 1 ↔ InTors P.q I x)

/-- `ker ι(μ_m) = A[I_m]` on `T`-points. -/
theorem ker_mu (P : QMPair K) (k : Fin 4) (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ P.A.X) :
    x ≫ (P.q.iota (mu k)).hom = 1 ↔ InTors P.q (idealI k) x := by
  constructor
  · intro h a ha
    obtain ⟨c, rfl⟩ := (mem_idealI_iff k a).1 ha
    rw [map_mul]
    change x ≫ ((P.q.iota (mu k)).hom ≫ (P.q.iota c).hom) = 1
    rw [← Category.assoc, h, MonObj.one_comp]
  · intro h
    exact h (mu k) (mu_mem k)

theorem mu_equiv (P : QMPair K) (k : Fin 4) (a : O) :
    (P.q.iota a).hom ≫ (P.q.iota (mu k)).hom = (P.q.iota (mu k)).hom ≫ (P.q.iota (rep k a)).hom := by
  change (P.q.iota (mu k) * P.q.iota a).hom = (P.q.iota (rep k a) * P.q.iota (mu k)).hom
  rw [← map_mul, ← map_mul, rep_mul_mu]

theorem mu_isog (P : QMPair K) (k : Fin 4) :
    ∃ (ψ : PkgI3.AbVar.Hom P.A P.A) (n : ℤ), n ≠ 0 ∧
      (P.q.iota (mu k)).hom ≫ ψ.hom = ((n : PkgI3.AbVar.End P.A)).hom ∧
      ψ.hom ≫ (P.q.iota (mu k)).hom = ((n : PkgI3.AbVar.End P.A)).hom := by
  refine ⟨P.q.iota (mu k), sq k, sq_ne_zero k, ?_, ?_⟩ <;>
  · change (P.q.iota (mu k) * P.q.iota (mu k)).hom = _
    rw [← map_mul, mu_mul_mu, map_intCast]

/-- **At `D = 6` the quotient by `A[I_m]` is the twist**: `ι(μ_m) : (A, ι) → (A, ι ∘ Ad μ_m)` is a quotient of `A`
by `A[I_m]` (kernel `ker ι(μ_m) = A[𝒪 μ_m] = A[I_m]`, quasi-inverse `ι(μ_m)` with `μ_m² ∈ ℤ`). -/
theorem canonical (P : QMPair K) (k : Fin 4) :
    IsIdealQuotient P (idealI k) (P.twist (rep k)) (P.q.iota (mu k)) :=
  ⟨mu_equiv P k, mu_isog P k, ker_mu P k⟩

end Quot

/-! ## 3. The textbook fact: an isogeny is the quotient by its kernel -/

/-- **TEXTBOOK LEAF (isogenies are quotients by their kernels).** Over `ℚ̄`: let `f : A → A'` be an isogeny of
abelian varieties (`g ∘ f = [n]`, `f ∘ g = [n]`, `n ≠ 0`). Then every homomorphism `h : A → B` killing the
scheme-theoretic kernel of `f` (as a functor of points) factors through `f`, and `f` is an epimorphism of abelian
varieties. That is, `A' = A/ker f` with its universal property. Source: Mumford, *Abelian varieties* (1970),
§7 Thm 4 and §12 Thm 1 (quotients by finite subgroup schemes; locators UNVERIFIED); Milne, *Abelian varieties*
(2008), Prop. 8.1 (UNVERIFIED). Used only to show that the printed Atkin–Lehner clause is not stronger than the
twist clause (`alIdeal_of_alTwist`); the direction used by the consumers needs no hypothesis. -/
def IsogenyQuotient : Prop :=
  ∀ (A A' B : PkgI3.AbVar Qbar) (f : PkgI3.AbVar.Hom A A'),
    (∃ (g : PkgI3.AbVar.Hom A' A) (n : ℤ), n ≠ 0 ∧ f.hom ≫ g.hom = ((n : PkgI3.AbVar.End A)).hom ∧
      g.hom ≫ f.hom = ((n : PkgI3.AbVar.End A')).hom) →
    (∀ h : PkgI3.AbVar.Hom A B,
      (∀ (T : Over (Spec (CommRingCat.of Qbar))) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ≫ h.hom = 1) →
        ∃ χ : PkgI3.AbVar.Hom A' B, f.hom ≫ χ.hom = h.hom) ∧
    (∀ χ χ' : PkgI3.AbVar.Hom A' B, f.hom ≫ χ.hom = f.hom ≫ χ'.hom → χ = χ')

/-- **Uniqueness of the quotient: every quotient by `A[I_m]` is the twist** (from `IsogenyQuotient`). -/
theorem iso_of_quotient (hF : IsogenyQuotient) (P P' : QMPair Qbar) (k : Fin 4)
    (φ : PkgI3.AbVar.Hom P.A P'.A) (hφ : IsIdealQuotient P (idealI k) P' φ) :
    Nonempty (QMIso (P.twist (rep k)).q P'.q) := by
  obtain ⟨hφe, hφi, hφk⟩ := hφ
  have hμe := mu_equiv P k
  have hμi := mu_isog P k
  have hμk := ker_mu P k
  obtain ⟨χ1, h1⟩ := (hF P.A P'.A P.A φ hφi).1 (P.q.iota (mu k))
    (fun T x hx => (hμk T x).2 ((hφk T x).1 hx))
  obtain ⟨χ2, h2⟩ := (hF P.A P.A P'.A (P.q.iota (mu k)) hμi).1 φ
    (fun T x hx => (hφk T x).2 ((hμk T x).1 hx))
  have u1 := (hF P.A P'.A P'.A φ hφi).2
  have u2 := (hF P.A P.A P.A (P.q.iota (mu k)) hμi).2
  have e12 : χ1.hom ≫ χ2.hom = 𝟙 _ := by
    have := u1 (PkgI3.AbVar.Hom.mk' (χ1.hom ≫ χ2.hom)) (PkgI3.AbVar.Hom.mk' (𝟙 _)) (by
      simp only [PkgI3.AbVar.Hom.hom_mk']
      rw [reassoc_of% h1, h2, Category.comp_id])
    exact congrArg PkgI3.AbVar.Hom.hom this
  have e21 : χ2.hom ≫ χ1.hom = 𝟙 _ := by
    have := u2 (PkgI3.AbVar.Hom.mk' (χ2.hom ≫ χ1.hom)) (PkgI3.AbVar.Hom.mk' (𝟙 _)) (by
      simp only [PkgI3.AbVar.Hom.hom_mk']
      rw [reassoc_of% h2, h1, Category.comp_id])
    exact congrArg PkgI3.AbVar.Hom.hom this
  have u3 := (hF P.A P.A P'.A (P.q.iota (mu k)) hμi).2
  refine ⟨⟨χ2, χ1, e21, e12, fun a => ?_⟩⟩
  have := u3 (PkgI3.AbVar.Hom.mk' ((P.q.iota (rep k a)).hom ≫ χ2.hom))
    (PkgI3.AbVar.Hom.mk' (χ2.hom ≫ (P'.q.iota a).hom)) (by
      simp only [PkgI3.AbVar.Hom.hom_mk']
      rw [← reassoc_of% (hμe a), h2, hφe a, reassoc_of% h2])
  exact congrArg PkgI3.AbVar.Hom.hom this

/-! ## 4. The printed Atkin–Lehner clause, and the two directions -/

section Clause

variable {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}

/-- **`g` acts on moduli as the Atkin–Lehner involution `w_m` in its printed form** (`m = 1, 2, 3, 6` for
`k = 0, 1, 2, 3`): for every `ℚ̄`-point `x` with pair `(A, ι)`, `g(x)` is the class of `(A/A[I_m], ι_m)`, i.e.
of every quotient `(A', ι')` of `(A, ι)` by `A[I_m]` (`IsIdealQuotient`). Rotger, Trans. AMS 356 (2004);
Elkies (1998) p. 10 (`A ↦ A/ker I_p`); González–Rotger, J. Math. Soc. Japan 58 (2006) §2 (locators UNVERIFIED). -/
def IsAtkinLehnerIdeal (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (k : Fin 4) (g : X ≅ X) : Prop :=
  ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
    ∀ (P' : QMPair Qbar) (φ : PkgI3.AbVar.Hom P.A P'.A), IsIdealQuotient P (idealI k) P' φ →
      Ψ (x ≫ g.hom) = Quotient.mk _ P'

/-- The Atkin–Lehner group in printed form. -/
def atkinLehnerWIdeal (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) : Set (X ≅ X) :=
  {g | ∃ k : Fin 4, IsAtkinLehnerIdeal X Ψ k g}

/-- **The Atkin–Lehner clause, printed form**: each `w_m`, `m ∣ 6`, is an automorphism of `X` over `ℚ`. -/
def ALIdealClause (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) : Prop :=
  ∀ k : Fin 4, ∃ g : X ≅ X, IsAtkinLehnerIdeal X Ψ k g

/-- **The Atkin–Lehner clause, twist form** (the clause of `X6Props` and `X6CoarseModuli`, verbatim). -/
def ALTwistClause (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) : Prop :=
  ∀ α : O ≃+* O, ∃ g : X ≅ X, ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar),
    Ψ x = Quotient.mk _ P → Ψ (x ≫ g.hom) = Quotient.mk _ (P.twist α)

/-- **Printed ⇒ twist, pointwise (no hypothesis).** -/
theorem isAtkinLehner_of_ideal {k : Fin 4} {g : X ≅ X} (h : IsAtkinLehnerIdeal X Ψ k g) :
    HDec.QMSplit.Moduli.ElkiesX6Star.IsAtkinLehner X Ψ k g :=
  fun x P hP => h x P hP _ _ (canonical P k)

theorem atkinLehnerWIdeal_subset :
    atkinLehnerWIdeal X Ψ ⊆ HDec.QMSplit.Moduli.ElkiesX6Star.atkinLehnerW X Ψ :=
  fun _ ⟨k, hk⟩ => ⟨k, isAtkinLehner_of_ideal hk⟩

/-- Every `α ∈ Aut 𝒪` is a unit-inner twist of one Atkin–Lehner twist `Ad μ_m`, uniformly in the pair. -/
theorem rep_iso (α : O ≃+* O) : ∃ k : Fin 4, ∀ {K : Type} [Field K] {A : PkgI3.AbVar K} (q : QMStr A),
    Nonempty (QMIso (q.twist (rep k)) (q.twist α)) := by
  obtain ⟨k, v, hv⟩ := rep_cover α
  refine ⟨k, fun {K} _ {A} q => ?_⟩
  set w := rep k
  let u : Oˣ :=
    ⟨w.symm (v : O), w.symm ((v⁻¹ : Oˣ) : O),
      by rw [← map_mul, Units.mul_inv, map_one], by rw [← map_mul, Units.inv_mul, map_one]⟩
  have hα : ∀ a, α a = w (u * a * ↑u⁻¹) := fun a => by
    change α a = w (w.symm (v : O) * a * w.symm ((v⁻¹ : Oˣ) : O))
    rw [map_mul, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hv a]
  exact ⟨(HDec.G0ModField.innerIso q w u α hα).symm⟩

/-- **Printed ⇒ twist (no hypothesis).** -/
theorem alTwist_of_alIdeal (h : ALIdealClause X Ψ) : ALTwistClause X Ψ := by
  intro α
  obtain ⟨k, hk⟩ := rep_iso α
  obtain ⟨g, hg⟩ := h k
  refine ⟨g, fun x P hP => ?_⟩
  rw [isAtkinLehner_of_ideal hg x P hP]
  exact Quotient.sound (hk P.q)

/-- **Twist ⇒ printed, pointwise** (from `IsogenyQuotient`). -/
theorem isAtkinLehnerIdeal_of_twist (hF : IsogenyQuotient) {k : Fin 4} {g : X ≅ X}
    (h : HDec.QMSplit.Moduli.ElkiesX6Star.IsAtkinLehner X Ψ k g) : IsAtkinLehnerIdeal X Ψ k g := by
  intro x P hP P' φ hφ
  rw [h x P hP]
  exact Quotient.sound (iso_of_quotient hF P P' k φ hφ)

/-- **Twist ⇒ printed** (from `IsogenyQuotient`). -/
theorem alIdeal_of_alTwist (hF : IsogenyQuotient) (h : ALTwistClause X Ψ) : ALIdealClause X Ψ := by
  intro k
  obtain ⟨g, hg⟩ := h (rep k)
  exact ⟨g, isAtkinLehnerIdeal_of_twist hF hg⟩

theorem alIdeal_iff_alTwist (hF : IsogenyQuotient) : ALIdealClause X Ψ ↔ ALTwistClause X Ψ :=
  ⟨alTwist_of_alIdeal, alIdeal_of_alTwist hF⟩

theorem atkinLehnerW_eq_of_isogenyQuotient (hF : IsogenyQuotient) :
    atkinLehnerWIdeal X Ψ = HDec.QMSplit.Moduli.ElkiesX6Star.atkinLehnerW X Ψ :=
  Set.Subset.antisymm atkinLehnerWIdeal_subset fun _ ⟨k, hk⟩ => ⟨k, isAtkinLehnerIdeal_of_twist hF hk⟩

end Clause

/-! ## 5. Morphisms of curves are determined by their `ℚ̄`-points -/

theorem hom_ext_qbar {Y Z : Over (Spec (CommRingCat.of ℚ))} (hP : IsProper Y.hom)
    (hS : SmoothOfRelativeDimension 1 Y.hom) [IsSeparated Z.hom] (f g : Y ⟶ Z)
    (h : ∀ y : fieldPt Qbar ⟶ Y, y ≫ f = y ≫ g) : f = g := by
  have : Smooth Y.hom := hS.smooth
  have : IsReduced Y.left := HDec.QMSplit.Moduli.isReduced_of_smooth_domain Y.hom
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  apply Over.OverMorphism.ext
  refine ext_of_fromSpecResidueField_eq f.left g.left Z.hom (closedPoints Y.left) ?_ ?_
    (by rw [Over.w f, Over.w g])
  · rw [dense_iff_closure_eq]
    exact closure_closedPoints
  · intro x hx
    obtain ⟨emb, y0, hy0⟩ := HDec.ModelGlue.exists_qbarPt Y x hx
    have e := congrArg CommaMorphism.left (h y0)
    simp only [Over.comp_left] at e
    rw [hy0, Scheme.SpecToEquivOfField_symm_apply] at e
    dsimp only at e
    have : Surjective (Spec.map emb) := ⟨fun _ => ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
    have : Flat (Spec.map emb) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      algebraize [emb.hom]
      change Module.Flat _ _
      infer_instance
    have : Epi (Spec.map emb) := Flat.epi_of_flat_of_surjective _
    have e2 : (Spec.map emb ≫ Y.left.fromSpecResidueField x) ≫ f.left =
        (Spec.map emb ≫ Y.left.fromSpecResidueField x) ≫ g.left := e
    rw [Category.assoc, Category.assoc] at e2
    exact (cancel_epi _).1 e2

/-- **On a witness carrying the printed clause, the two Atkin–Lehner groups coincide (no hypothesis).** Each
`g ∈ W` of index `k` acts on `ℚ̄`-points as the `w_m` given by the printed clause, so equals it. -/
theorem atkinLehnerW_eq_of_clause {X : Over (Spec (CommRingCat.of ℚ))}
    {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} (hP : IsProper X.hom)
    (hS : SmoothOfRelativeDimension 1 X.hom) (hal : ALIdealClause X Ψ) :
    atkinLehnerWIdeal X Ψ = HDec.QMSplit.Moduli.ElkiesX6Star.atkinLehnerW X Ψ := by
  refine Set.Subset.antisymm atkinLehnerWIdeal_subset ?_
  rintro g ⟨k, hk⟩
  obtain ⟨g', hg'⟩ := hal k
  have hg'' := isAtkinLehner_of_ideal hg'
  have heq : g.hom = g'.hom := hom_ext_qbar hP hS _ _ fun x => by
    apply Ψ.injective
    obtain ⟨P, hP⟩ := Quotient.exists_rep (Ψ x)
    rw [hk x P hP.symm, hg'' x P hP.symm]
  have : g = g' := Iso.ext heq
  exact ⟨k, this ▸ hg'⟩

/-! ## 6. The Galois clause is the naturality square of the coarse map at `Spec σ` -/

section Galois

variable {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}

/-- **The Galois clause of `X6CoarseModuli`, verbatim** (existence form). -/
def GaloisClause (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) :
    Prop :=
  ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar),
    Ψ x = Quotient.mk _ P → ∃ Q : QMPair Qbar,
      Ψ (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x) = Quotient.mk _ Q ∧ IsBaseChangeOfPair (σ : Qbar →+* Qbar) P Q

/-- **Naturality of the coarse map at the morphism `Spec σ : Spec ℚ̄ → Spec ℚ̄` over `ℚ`** (Mumford, GIT Def. 5.6:
the coarse map is a natural transformation from the moduli functor to `Hom(−, X)`; for `σ` it says: if `Q` is the
base change of `P` along `σ`, the point classifying `Q` is the point classifying `P` composed with `Spec σ`). -/
def GaloisNatural (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) :
    Prop :=
  ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X) (P Q : QMPair Qbar),
    Ψ x = Quotient.mk _ P → IsBaseChangeOfPair (σ : Qbar →+* Qbar) P Q →
      Ψ (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x) = Quotient.mk _ Q

/-- The Lean clause gives the naturality square for every base change (base changes are unique up to isomorphism,
`ShimuraSplit.bc_uniquePair`). -/
theorem galoisNatural_of_clause (h : GaloisClause X Ψ) : GaloisNatural X Ψ := by
  intro σ x P Q hP hQ
  obtain ⟨Q', hQ', hbc⟩ := h σ x P hP
  rw [hQ']
  exact Quotient.sound (ShimuraSplit.bc_uniquePair hbc hQ)

/-- The base change of a QM pair along `σ : ℚ̄ → ℚ̄` (`AbVar.baseChange` along `σ`, with `ι_σ = endBC ∘ ι`). -/
def bcAut (σ : Qbar →+* Qbar) (P : QMPair Qbar) : QMPair Qbar :=
  letI : Algebra Qbar Qbar := σ.toAlgebra
  ⟨P.A.baseChange Qbar, by rw [PkgI3.AbVar.dim_baseChange]; exact P.surface,
   ⟨(HDec.G0ModField.KernelField.endBC P.A Qbar).comp P.q.iota,
    (HDec.G0ModField.KernelField.endBC_injective P.A Qbar).comp P.q.injective⟩⟩

theorem isBaseChange_bcAut (σ : Qbar →+* Qbar) (P : QMPair Qbar) :
    IsBaseChangeOfPair σ P (bcAut σ P) := by
  refine ⟨pullback.fst P.A.X.hom (Spec.map (CommRingCat.ofHom σ)), IsPullback.of_hasPullback _ _,
    fun a => ?_, ?_⟩
  · change ((Over.pullback (Spec.map (CommRingCat.ofHom σ))).map (P.q.iota a).hom).left ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (P.q.iota a).hom.left
    simp
  · rw [ShimuraSplit.pt_one_left, ShimuraSplit.pt_one_left]
    change (Functor.LaxMonoidal.ε (Over.pullback (Spec.map (CommRingCat.ofHom σ))) ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom σ))).map η[P.A.X]).left ≫ pullback.fst _ _ = _
    rw [Over.comp_left, Category.assoc]
    simp only [Over.pullback_map_left, pullback.lift_fst]
    rw [← Category.assoc]
    congr 1
    have hw : (Functor.LaxMonoidal.ε (Over.pullback (Spec.map (CommRingCat.ofHom σ)))).left ≫
        pullback.snd (𝟙_ (Over (Spec (CommRingCat.of Qbar)))).hom (Spec.map (CommRingCat.ofHom σ)) = 𝟙 _ :=
      Over.w (Functor.LaxMonoidal.ε (Over.pullback (Spec.map (CommRingCat.ofHom σ))))
    have key : pullback.fst (𝟙_ (Over (Spec (CommRingCat.of Qbar)))).hom (Spec.map (CommRingCat.ofHom σ)) ≫ 𝟙 _ =
        pullback.snd (𝟙_ (Over (Spec (CommRingCat.of Qbar)))).hom (Spec.map (CommRingCat.ofHom σ)) ≫
          Spec.map (CommRingCat.ofHom σ) := pullback.condition
    rw [Category.comp_id] at key
    rw [key, ← Category.assoc, hw, Category.id_comp]

theorem exists_bc_aut (σ : Qbar ≃ₐ[ℚ] Qbar) (P : QMPair Qbar) :
    ∃ Q : QMPair Qbar, IsBaseChangeOfPair (σ : Qbar →+* Qbar) P Q :=
  ⟨bcAut σ P, isBaseChange_bcAut σ P⟩

/-- Conversely the naturality square and the existence of a base change give the Lean clause. -/
theorem clause_of_galoisNatural (h : GaloisNatural X Ψ)
    (hE : ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (P : QMPair Qbar), ∃ Q : QMPair Qbar, IsBaseChangeOfPair (σ : Qbar →+* Qbar) P Q) :
    GaloisClause X Ψ := by
  intro σ x P hP
  obtain ⟨Q, hQ⟩ := hE σ P
  exact ⟨Q, h σ x P Q hP hQ, hQ⟩

/-- **The Galois clause is exactly the naturality square at `Spec σ`** (no hypothesis). -/
theorem galoisClause_iff_natural : GaloisClause X Ψ ↔ GaloisNatural X Ψ :=
  ⟨galoisNatural_of_clause, fun h => clause_of_galoisNatural h exists_bc_aut⟩

end Galois

/-! ## 7. The leaf with its Atkin–Lehner clause in printed form -/

/-- **LEAF `X6CoarseModuliIdeal` (printed form of `GRX6AbPrint.X6CoarseModuli`).** The clauses of
`X6CoarseModuli` (Shimura 1967; Deligne 1971; Buzzard 1997; Mumford GIT Def. 5.6; see its docstring), with
* the Atkin–Lehner clause in the printed ideal-quotient form: for each `m ∣ 6` some automorphism `w_m` of `X` over
  `ℚ` sends the class of `(A, ι)` to the class of `(A/A[I_m], ι_m)` (`ALIdealClause`; Rotger, Trans. AMS 356
  (2004); locators UNVERIFIED);
* the Galois clause in the literal form of the coarse map's naturality square at `Spec σ` (`GaloisNatural`;
  equivalent to the clause of `X6CoarseModuli` with no hypothesis, `galoisClause_iff_natural`). Implies `X6CoarseModuli` with no hypothesis (`x6CoarseModuli_of_ideal`) and follows from it
given `IsogenyQuotient` (`x6CoarseModuliIdeal_of_twist`). -/
def X6CoarseModuliIdeal : Prop :=
  ∃ (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)),
    IsProper X.hom ∧ SmoothOfRelativeDimension 1 X.hom ∧ Nonempty (fieldPt Qbar ⟶ X) ∧
    GaloisNatural X Ψ ∧
    ALIdealClause X Ψ ∧
    (∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
      ∀ 𝒜' : LeafQM.AV.R1UnivRigid.QMAbScheme S.left,
        (∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S), ∃ P : QML3 K,
          IsFibreOf 𝒜'.toQMFamily s.left P) →
        ∃ g : S ⟶ X, ∀ (s : fieldPt Qbar ⟶ S) (P : QML3 Qbar),
          IsFibreOf 𝒜'.toQMFamily s.left P → Ψ (s ≫ g) = Quotient.mk _ P.forget)

/-- **The leaf in printed form gives the leaf in twist form (no hypothesis).** -/
theorem x6CoarseModuli_of_ideal (h : X6CoarseModuliIdeal) : GRX6AbPrint.X6CoarseModuli := by
  obtain ⟨X, Ψ, hp, hs, hn, hgal, hal, huniv⟩ := h
  exact ⟨X, Ψ, hp, hs, hn, galoisClause_iff_natural.2 hgal, alTwist_of_alIdeal hal, huniv⟩

/-- **The leaf in twist form gives the printed form**, from `IsogenyQuotient`: the printed form is not stronger. -/
theorem x6CoarseModuliIdeal_of_twist (hF : IsogenyQuotient) (h : GRX6AbPrint.X6CoarseModuli) :
    X6CoarseModuliIdeal := by
  obtain ⟨X, Ψ, hp, hs, hn, hgal, hal, huniv⟩ := h
  exact ⟨X, Ψ, hp, hs, hn, galoisNatural_of_clause hgal, alIdeal_of_alTwist hF hal, huniv⟩

theorem x6CoarseModuliIdeal_iff (hF : IsogenyQuotient) : X6CoarseModuliIdeal ↔ GRX6AbPrint.X6CoarseModuli :=
  ⟨x6CoarseModuli_of_ideal, x6CoarseModuliIdeal_of_twist hF⟩

/-! ## 8. Elkies' statement with Elkies' (isogeny-form) Atkin–Lehner group -/

section Elkies

open HDec.QMSplit.Moduli

/-- `ℚ(X₆)^W` for the printed Atkin–Lehner group `W = atkinLehnerWIdeal` (Elkies p. 10: `w_p : A ↦ A/ker I_p`). -/
def fixedByWIdeal {X : Over (Spec (CommRingCat.of ℚ))} [IsIntegral X.left]
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) : Set X.left.functionField :=
  {φ | ∀ g ∈ atkinLehnerWIdeal X Ψ, ElkiesCoord.ffPullback (Z := X.left) ((Over.forget _).mapIso g) φ = φ}

theorem fixedByWIdeal_eq {X : Over (Spec (CommRingCat.of ℚ))} [IsIntegral X.left]
    {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} (hP : IsProper X.hom)
    (hS : SmoothOfRelativeDimension 1 X.hom) (hal : ALIdealClause X Ψ) :
    fixedByWIdeal Ψ = ElkiesCoord.fixedByW Ψ := by
  unfold fixedByWIdeal ElkiesCoord.fixedByW
  rw [atkinLehnerW_eq_of_clause hP hS hal]

/-- **LEAF `ElkiesX6StarEveryIdeal`** (Elkies, *Shimura curve computations*, ANTS-III, LNCS 1423 (1998), §3 with
`Σ = {2, 3}`: `X*(1) = X(1)/W`, p. 10, with `w_p : A ↦ A/ker I_p`; `X*(1) ≅ P¹_t`, p. 17; CM values Table 1 p. 26
and pp. 22–23; function field `ℚ(t)(√(−t), √(3(t − 1)))`, p. 17; locators verified by the lead from arXiv
math/0005160). The clauses of `ElkiesPrint.ElkiesX6StarEvery`, with Elkies' Atkin–Lehner group in his isogeny form
(`atkinLehnerWIdeal`: `w_m(A, ι) = (A/A[I_m], ι_m)`) instead of the twist form, on every witness of the moduli
description whose `X` carries the printed Atkin–Lehner automorphisms (`ALIdealClause`). Implies
`ElkiesX6StarEvery` from `X6CoarseModuliIdeal`, `ShimuraMainThmIDeligneY3AbU` and T5 (`elkiesX6StarEvery_of_ideal`),
and follows from it given `IsogenyQuotient` (`ideal_of_elkiesX6StarEvery`). -/
def ElkiesX6StarEveryIdeal : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ → X6Props Y Φ X Ψ fY → ALIdealClause X Ψ →
    ∃ t : ToP1 X.left,
      (∀ (_ : IsIntegral X.left) (hη : genericPoint X.left ∈ t.U),
        fixedByWIdeal Ψ =
          (Subfield.closure {X.left.presheaf.germ t.U _ hη t.f} : Set X.left.functionField)) ∧
      (∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
        (HasCM24 P.q → t.val (K := Qbar) x.left = OnePoint.some 0) ∧
        (HasCM4 P.q → t.val (K := Qbar) x.left = OnePoint.some 1) ∧
        (HasCM3 P.q → t.val (K := Qbar) x.left = OnePoint.infty)) ∧
      X6Glue.ElkiesCharts X t

/-- On a witness with the printed clause, the isogeny-form leaf gives the twist-form statement. -/
theorem every_at_of_ideal (h : ElkiesX6StarEveryIdeal) {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} {fY : Y ⟶ X}
    (h1 : LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ) (h6 : X6Props Y Φ X Ψ fY) (hal : ALIdealClause X Ψ) :
    ElkiesCoord.ElkiesX6StarFunctionField := by
  obtain ⟨t, hff, hcm, hc⟩ := h Y Φ X Ψ fY h1 h6 hal
  refine ⟨Y, Φ, X, Ψ, fY, t, h1, h6, fun hI hη => ?_, hcm, hc⟩
  rw [← fixedByWIdeal_eq h6.1 h6.2.1 hal]
  exact hff hI hη

/-- **`ElkiesX6StarEvery` from the isogeny-form leaf**, the printed coarse leaf `X6CoarseModuliIdeal`, the field
`shimuraMainThmIDeligneY3AbU` and T5. The witness is built as in `GRX6AbPrint.x6ModuliWitness_of_coarse` and keeps
the printed Atkin–Lehner clause; the two `W`'s agree on it (`atkinLehnerW_eq_of_clause`); then transport to every
witness (`ElkiesPrint.every_of_functionField`). -/
theorem elkiesX6StarEvery_of_ideal (h : ElkiesX6StarEveryIdeal) (hX : X6CoarseModuliIdeal)
    (hY : RayClassCFT.ShimuraMainThmIDeligneY3AbU) (hT : ObjBridge.TorsionStructure) :
    ElkiesPrint.ElkiesX6StarEvery := by
  obtain ⟨Y, Φ, h1, -⟩ := hY
  obtain ⟨X, Ψ, hp, hs, hn, hgal, hal, huniv⟩ := hX
  obtain ⟨hpY, hsY, -, -, ⟨𝒜, h𝒜⟩, -⟩ := id h1
  have hfib : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ Y), ∃ P : QML3 K,
      IsFibreOf 𝒜.toQMFamily s.left P := by
    intro K _ _ s
    obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ K s)
    exact ⟨P, h𝒜 K s P hP.symm⟩
  obtain ⟨g, hg⟩ := huniv Y hpY hsY 𝒜 hfib
  have h6 : X6Props Y Φ X Ψ g :=
    ⟨hp, hs, hn, galoisClause_iff_natural.2 hgal, alTwist_of_alIdeal hal, fun y P hP => hg y P (h𝒜 Qbar y P hP)⟩
  exact ElkiesPrint.every_of_functionField (every_at_of_ideal h h1 h6 hal) hT

/-- The same with T5 from the textbook field `mumfordTorsionAlgClosed` (the form used by the fold). -/
theorem elkiesX6StarEvery_of_ideal' (h : ElkiesX6StarEveryIdeal) (hX : X6CoarseModuliIdeal)
    (hY : RayClassCFT.ShimuraMainThmIDeligneY3AbU) (hM : AvSplit.MumfordTorsionAlgClosed) :
    ElkiesPrint.ElkiesX6StarEvery :=
  elkiesX6StarEvery_of_ideal h hX hY (ObjBridge.torsionStructure_iff.mpr (AvSplit.torsionStructure_of_mumford hM))

/-- **The isogeny-form leaf is not stronger than `ElkiesX6StarEvery`** (given `IsogenyQuotient`, the two `W`'s
agree on every witness). -/
theorem ideal_of_elkiesX6StarEvery (hF : IsogenyQuotient) (h : ElkiesPrint.ElkiesX6StarEvery) :
    ElkiesX6StarEveryIdeal := by
  intro Y Φ X Ψ fY h1 h6 _
  obtain ⟨t, hff, hcm, hc⟩ := h Y Φ X Ψ fY h1 h6
  refine ⟨t, fun hI hη => ?_, hcm, hc⟩
  unfold fixedByWIdeal
  rw [atkinLehnerW_eq_of_isogenyQuotient hF]
  exact hff hI hη

end Elkies


end X6ALIdeal
