import ZInQKernel.Contrib.OneProof.GRDict
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RingClass.Field

/-!
# gr512-bridge: González–Rotger Thm 5.12 over Tau Ceti's ring class field

The research field `gonzalezRotgerThm512X6 : GRDict.GonzalezRotgerThm512X6` states González–Rotger
Thm 5.12 at `(D, N) = (6, 1)` as a degree in `CommRing.Pic R`. The strict leaf review (11-17) rated it
GLUE (consequence) for two steps: (S2) the print says `ℚ(P) = H_R` (the ring class field), and the
degree form needs class field theory plus a `ClassGroup ≃ CommRing.Pic` bridge; (S1) `inertCount6 k`
(primes of `6` inert in `𝓞_k`) against González–Rotger's `D(R)`, defined by Eichler symbols of `R`.

This file

* states Thm 5.12 as printed (`GonzalezRotgerThm512X6RCF`): `ℚ(x) ≅ H_R` (Tau Ceti's
  `ringClassField`) if `D(R)N*(R) ≠ 1`, and `ℚ(x)` an index-two subfield of `H_R` otherwise, with
  `D(R)` read off `R` itself (`grD6`: the product of the `p ∣ 6` with `pR` prime in `R`, i.e. Eichler
  symbol `(R/p) = −1`; `N*(R) = 1` at `N = 1`);
* builds the Tau Ceti order of a subring of finite index of `𝓞_k` (`toOrder`) and proves the bridge
  `Pic O ≃* CommRing.Pic R` (`picEquiv`, from Mathlib's `ClassGroup.equivPic`);
* proves that `pR` is prime in `R` iff `p𝓞_k` is prime in `𝓞_k` for `p` prime to the conductor
  (`isPrime_span_iff`), so `grD6 R ≠ 1 ↔ inertCount6 k ≠ 0` (`grD6_ne_one_iff`);
* derives the old field exactly (`gonzalezRotgerThm512X6_of_rcf`), so no consumer changes.

No `sorry`; standard axioms only.
-/

set_option linter.style.longLine false

noncomputable section

namespace GR512Bridge

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
open NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory

/-! ## 1. Subrings of finite index of `𝓞_k` as Tau Ceti orders -/

section Order

variable {k : Type} [Field k] [NumberField k]

omit [NumberField k] in
/-- The conductor kills `𝓞_k / R`: `f·y ∈ R` for every algebraic integer `y`, `f = [𝓞_k : R]`. -/
theorem conductor_mul_mem (R : Subring k) {y : k} (hy : y ∈ integralClosure ℤ k) :
    (conductor R : k) * y ∈ R := by
  have hmem : y ∈ (integralClosure ℤ k).toSubring.toAddSubgroup := hy
  have h2 := R.toAddSubgroup.nsmul_relIndex_mem hmem
  rw [← nsmul_eq_mul]
  exact h2

/-- `R` as a `ℤ`-subalgebra of `k`. -/
def intSubalgebra (R : Subring k) : Subalgebra ℤ k :=
  { R.toSubsemiring with algebraMap_mem' := fun r => by simpa using intCast_mem R r }

/-- **The Tau Ceti order of a subring `R ⊆ 𝓞_k` of finite index** (`[𝓞_k : R] ≠ 0`). -/
def toOrder (R : Subring k) (hR : R ≤ (integralClosure ℤ k).toSubring) (hf : conductor R ≠ 0) :
    NumberFieldOrder k where
  toSubalgebra := intSubalgebra R
  finite := by
    have h : intSubalgebra R ≤ integralClosure ℤ k := fun x hx => hR hx
    have : Module.Finite ℤ (integralClosure ℤ k) := inferInstanceAs (Module.Finite ℤ (𝓞 k))
    exact Module.Finite.of_injective (Subalgebra.inclusion h).toLinearMap
      (Subalgebra.inclusion_injective h)
  spans := by
    apply top_unique
    rw [← (maximalNumberFieldOrder k).spans]
    apply Submodule.span_le.mpr
    intro y hy
    have hf' : ((conductor R : ℚ)) ≠ 0 := by exact_mod_cast hf
    have hmem : (conductor R : k) * y ∈ intSubalgebra R := conductor_mul_mem R hy
    have : y = (conductor R : ℚ)⁻¹ • ((conductor R : k) * y) := by
      rw [Algebra.smul_def, ← mul_assoc, map_inv₀, map_natCast,
        inv_mul_cancel₀ (by exact_mod_cast hf'), one_mul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem toOrder_toSubring (R : Subring k) (hR : R ≤ (integralClosure ℤ k).toSubring)
    (hf : conductor R ≠ 0) : (toOrder R hR hf).toSubalgebra.toSubring = R :=
  Subring.ext fun _ => Iff.rfl

end Order

/-! ## 2. The bridge `Pic O ≃* CommRing.Pic R` -/

section Pic

/-- Picard groups of isomorphic rings are isomorphic (`CommRing.Pic` is functorial). -/
def picCongr {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) :
    CommRing.Pic A ≃* CommRing.Pic B :=
  MonoidHom.toMulEquiv (CommRing.Pic.mapRingHom e.toRingHom) (CommRing.Pic.mapRingHom e.symm.toRingHom)
    (by
      rw [CommRing.Pic.mapRingHom_comp_mapRingHom]
      have : e.symm.toRingHom.comp e.toRingHom = RingHom.id A := by ext; simp
      rw [this, CommRing.Pic.mapRingHom_id])
    (by
      rw [CommRing.Pic.mapRingHom_comp_mapRingHom]
      have : e.toRingHom.comp e.symm.toRingHom = RingHom.id B := by ext; simp
      rw [this, CommRing.Pic.mapRingHom_id])

variable {k : Type} [Field k] [NumberField k]

/-- The order and the subring it was built from are the same ring. -/
def subringEquiv (O : NumberFieldOrder k) : O.toSubalgebra ≃+* O.toSubalgebra.toSubring where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- **The bridge**: Tau Ceti's Picard group of an order (`ClassGroup` of the order: invertible
fractional ideals modulo principal ones) is Mathlib's `CommRing.Pic` of the underlying subring
(`ClassGroup.equivPic`, valid for every domain, in particular for non-maximal orders). -/
def picEquiv (O : NumberFieldOrder k) : Pic O ≃* CommRing.Pic O.toSubalgebra.toSubring :=
  (ClassGroup.equivPic O.toSubalgebra).trans (picCongr (subringEquiv O))

theorem card_pic (O : NumberFieldOrder k) :
    Nat.card (Pic O) = Nat.card (CommRing.Pic O.toSubalgebra.toSubring) :=
  Nat.card_congr (picEquiv O).toEquiv

/-- **`[H_R : k] = #CommRing.Pic R`** (Tau Ceti's `finrank_ringClassField` and the bridge). -/
theorem finrank_ringClassField_eq_card_pic (O : NumberFieldOrder k) :
    Module.finrank k (ringClassField O) = Nat.card (CommRing.Pic O.toSubalgebra.toSubring) := by
  rw [finrank_ringClassField, card_pic]

end Pic

/-! ## 3. González–Rotger's `D(R)` at `D = 6` and `inertCount6` -/

section Eichler

variable {k : Type} [Field k] [NumberField k]

/-- **`pR` prime in `R` iff `p𝓞_k` prime in `𝓞_k`, for `p` prime to the conductor of `R`.** The map
`R → 𝓞_k / p𝓞_k` is onto with kernel `pR` (Bezout `af + bp = 1`, `f𝓞_k ⊆ R`). -/
theorem isPrime_span_iff (R : Subring k) (hR : R ≤ (integralClosure ℤ k).toSubring) (p : ℕ)
    (hp : Nat.Coprime (conductor R) p) :
    (Ideal.span {(p : R)}).IsPrime ↔ (Ideal.span {(p : 𝓞 k)}).IsPrime := by
  classical
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * (conductor R : ℤ) + b * p = 1 := by
    refine ⟨Nat.gcdA (conductor R) p, Nat.gcdB (conductor R) p, ?_⟩
    have := Nat.gcd_eq_gcd_ab (conductor R) p
    rw [hp.gcd_eq_one] at this
    push_cast at this
    linarith
  have hab' : (a : k) * (conductor R : k) + (b : k) * (p : k) = 1 := by
    have := congrArg (fun z : ℤ => (z : k)) hab
    push_cast at this
    exact this
  let ι : R →+* 𝓞 k :=
    { toFun := fun x => ⟨x, hR x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hι : ∀ x : R, ((ι x : 𝓞 k) : k) = x := fun _ => rfl
  have hι' : ∀ x : R, algebraMap (𝓞 k) k (ι x) = x := fun _ => rfl
  have key : ∀ z : 𝓞 k, (z : k) * (p : k) ∈ R → (z : k) ∈ R := by
    intro z hz
    have h1 : (conductor R : k) * z ∈ R := conductor_mul_mem R z.2
    have : (z : k) = a * ((conductor R : k) * z) + b * ((z : k) * p) := by
      linear_combination (-(z : k)) * hab'
    rw [this]
    exact R.add_mem (R.mul_mem (intCast_mem R a) h1) (R.mul_mem (intCast_mem R b) hz)
  have hcomap : Ideal.span {(p : R)} = (Ideal.span {(p : 𝓞 k)}).comap ι := by
    ext x
    rw [Ideal.mem_comap, Ideal.mem_span_singleton', Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨ι c, by rw [map_mul, map_natCast]⟩
    · rintro ⟨z, hz⟩
      have hzk : (z : k) * p = x := by
        have := congrArg (algebraMap (𝓞 k) k) hz
        rw [map_mul, map_natCast, hι'] at this
        exact this
      refine ⟨⟨z, key z (by rw [hzk]; exact x.2)⟩, ?_⟩
      apply Subtype.ext
      simp [← hzk]
  set φ := (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 k)})).comp ι with hφ
  have hsurj : Function.Surjective φ := by
    intro w
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
    have h1 : (conductor R : k) * y ∈ R := conductor_mul_mem R y.2
    refine ⟨(a : R) * ⟨_, h1⟩, ?_⟩
    rw [hφ, RingHom.comp_apply, Ideal.Quotient.eq, Ideal.mem_span_singleton']
    refine ⟨-(b : 𝓞 k) * y, ?_⟩
    apply RingOfIntegers.ext
    simp [hι]
    linear_combination (-(algebraMap (𝓞 k) k y)) * hab'
  have hker : RingHom.ker φ = Ideal.span {(p : R)} := by
    rw [hcomap, hφ, ← RingHom.comap_ker, Ideal.mk_ker]
  constructor
  · intro hP
    rw [← hker] at hP
    have := (Ideal.Quotient.isDomain_iff_prime (RingHom.ker φ)).mpr hP
    let e := RingHom.quotientKerEquivOfSurjective hsurj
    haveI : IsDomain (𝓞 k ⧸ Ideal.span {(p : 𝓞 k)}) :=
      Function.Injective.isDomain e.symm.toRingHom e.symm.injective
    exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  · intro hP
    rw [hcomap]
    exact Ideal.comap_isPrime ι _

open Classical in
/-- **González–Rotger's `D(R)` at `D = 6`** (J. Math. Soc. Japan 58 (2006) §5; the reading of the
definition is recorded in docs/research/gr512-bridge.md, S1): the product of the primes `p ∣ 6` with
Eichler symbol `(R/p) = −1`, i.e. with `pR` a prime ideal of `R` (`R/pR ≅ 𝔽_{p²}`; for `p ∣ f(R)`,
`R/pR ≅ 𝔽_p[ε]/(ε²)` and the symbol is `1`). Read on `R` itself, not on `k`. -/
def grD6 (R : Subring k) : ℕ :=
  (if (Ideal.span {(2 : R)}).IsPrime then 2 else 1) * (if (Ideal.span {(3 : R)}).IsPrime then 3 else 1)

/-- **S1 matched**: for an order of conductor prime to `6`, `D(R) ≠ 1` iff some `p ∣ 6` is inert in
`k` (`inertCount6 k ≠ 0`). -/
theorem grD6_ne_one_iff (R : Subring k) (hR : R ≤ (integralClosure ℤ k).toSubring)
    (hc : Nat.Coprime (conductor R) 6) : grD6 R ≠ 1 ↔ inertCount6 k ≠ 0 := by
  have h2 := isPrime_span_iff R hR 2 (Nat.Coprime.coprime_dvd_right (by norm_num) hc)
  have h3 := isPrime_span_iff R hR 3 (Nat.Coprime.coprime_dvd_right (by norm_num) hc)
  simp only [Nat.cast_ofNat] at h2 h3
  unfold grD6 inertCount6
  by_cases a2 : (Ideal.span {(2 : 𝓞 k)}).IsPrime <;>
  by_cases a3 : (Ideal.span {(3 : 𝓞 k)}).IsPrime <;>
  simp [a2, a3, h2, h3]

end Eichler

/-! ## 4. The leaf as printed, and the old field from it -/

/-- **LEAF (González–Rotger, *Non-elliptic Shimura curves of genus one*, J. Math. Soc. Japan 58
(2006), Thm 5.12, p. 946 (arXiv math/0612732 pp. 18–19; read by the locator audit,
docs/research/locators.md row "R5: fields of definition"), at `(D, N) = (6, 1)`, on every witness of
the moduli description; printed form).**

*Published statement* (as read by the audit): for `P ∈ CM(R) ⊂ X₀(D,N)`, `R` an order of conductor
prime to `DN`, `ℚ(P) = H_R`, the ring class field of `R`, if `D(R)N*(R) ≠ 1`, and otherwise `ℚ(P)` is a
specified subfield of `H_R` of index two.

*Lean form*: for every witness `(Y, Φ, X, Ψ, fY)` (`R1fpPropsAb`, `X6Props`), every imaginary quadratic
`k`, every order `O` of `k` (Tau Ceti's `NumberFieldOrder`) of conductor prime to `6`, and every
`ℚ̄`-point `x` of `X` that is a CM point by `O` in González–Rotger's sense (`GRDict.IsGRCMPoint`):
if `D(R) ≠ 1` (`grD6`; `N*(R) = 1` at `N = 1`), the residue field `ℚ(x)` is `ℚ`-isomorphic to the ring
class field `ringClassField O` (Tau Ceti: the class field of the kernel of `C_k → Pic O`); otherwise it
is `ℚ`-isomorphic to a subfield `F ⊆ H_R` with `[H_R : F] = 2`.

*Why not stronger*: an equality `ℚ(P) = H_R` of subfields of `ℂ` (or `ℚ̄`) gives a `ℚ`-isomorphism, and
"a specified subfield of index two" gives one of index two; `ℚ(x)` is `ℚ(σQ ∘ x)` (gr-dict §3.3); the
form on every witness is the canonical model's (gr-dict §3.3, clause R). -/
def GonzalezRotgerThm512X6RCF : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ → X6Props Y Φ X Ψ fY →
    ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
      Module.finrank ℚ k = 2 →
      ∀ O : NumberFieldOrder k, Nat.Coprime (conductor O.toSubalgebra.toSubring) 6 →
        ∀ x : fieldPt Qbar ⟶ X, GRDict.IsGRCMPoint Ψ O.toSubalgebra.toSubring x →
          (grD6 O.toSubalgebra.toSubring ≠ 1 →
            Nonempty (residueImage (X := X.left) x.left ≃ₐ[ℚ] ringClassField O)) ∧
          (grD6 O.toSubalgebra.toSubring = 1 →
            ∃ F : IntermediateField ℚ (ringClassField O),
              Module.finrank F (ringClassField O) = 2 ∧
              Nonempty (residueImage (X := X.left) x.left ≃ₐ[ℚ] F))

/-- **The old field `gonzalezRotgerThm512X6` from the printed form** (glue: `toOrder`, the bridge
`picEquiv`, `finrank_ringClassField`, the tower law, `grD6_ne_one_iff`). -/
theorem gonzalezRotgerThm512X6_of_rcf (h : GonzalezRotgerThm512X6RCF) :
    GRDict.GonzalezRotgerThm512X6 := by
  intro Y Φ X Ψ fY h1 h6 k _ _ _ hk R hR hc x hx
  have hf : conductor R ≠ 0 := by
    intro h0
    rw [h0] at hc
    norm_num at hc
  have hO : (toOrder R hR hf).toSubalgebra.toSubring = R := toOrder_toSubring R hR hf
  have hcO : Nat.Coprime (conductor (toOrder R hR hf).toSubalgebra.toSubring) 6 := by
    rw [hO]; exact hc
  have hxO : GRDict.IsGRCMPoint Ψ (toOrder R hR hf).toSubalgebra.toSubring x := by
    rw [hO]; exact hx
  obtain ⟨hA, hB⟩ := h Y Φ X Ψ fY h1 h6 k hk (toOrder R hR hf) hcO x hxO
  rw [hO] at hA hB
  have hdeg : Module.finrank ℚ (ringClassField (toOrder R hR hf)) =
      2 * Nat.card (CommRing.Pic R) := by
    rw [← Module.finrank_mul_finrank ℚ k (ringClassField (toOrder R hR hf)), hk,
      finrank_ringClassField_eq_card_pic, hO]
  have hiff := grD6_ne_one_iff R hR hc
  by_cases hi : inertCount6 k = 0
  · have hD : grD6 R = 1 := by
      by_contra hne
      exact (hiff.mp hne) hi
    obtain ⟨F, hF2, ⟨e⟩⟩ := hB hD
    refine ⟨?_, fun h' => absurd hi h'⟩
    rw [if_pos hi, one_mul, e.toLinearEquiv.finrank_eq]
    have : Module.Free ℚ F := Module.Free.of_divisionRing ℚ F
    have : Module.Free F (ringClassField (toOrder R hR hf)) := Module.Free.of_divisionRing _ _
    have := Module.finrank_mul_finrank ℚ F (ringClassField (toOrder R hR hf))
    rw [hF2, hdeg] at this
    omega
  · have hD : grD6 R ≠ 1 := hiff.mpr hi
    obtain ⟨e⟩ := hA hD
    refine ⟨?_, fun _ => ⟨?_⟩⟩
    · rw [if_neg hi, e.toLinearEquiv.finrank_eq, hdeg]
    · exact e.symm.toAlgHom.comp (IsScalarTower.toAlgHom ℚ k (ringClassField (toOrder R hR hf)))

end GR512Bridge

#print axioms GR512Bridge.gonzalezRotgerThm512X6_of_rcf
#print axioms GR512Bridge.picEquiv
#print axioms GR512Bridge.grD6_ne_one_iff
