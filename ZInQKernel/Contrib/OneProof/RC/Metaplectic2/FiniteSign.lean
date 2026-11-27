import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.FiniteAssembly

/-! The kernel of the restricted product consists of finite-support
tuples of common local signs; their product gives the central quotient.
This is on-the-spot (c), tex 8798–8807 and 8996–9004. -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Metaplectic WeilIndex Filter
open scoped Classical

variable (a b : Fin 3 → ℕ) [∀ i, NeZero (2 * a i)] [∀ i, NeZero (2 * b i)]

abbrev FiniteCenter := (finiteProjection a b).ker

theorem finiteCenter_cases (z : FiniteCenter a b) (p : Place) :
    (z : FiniteLocalCover a b) p = 1 ∨ (z : FiniteLocalCover a b) p = localSign p a b := by
  apply ((localProjection_kernel p a b).2 _).mp
  exact congrArg (fun k : FiniteSL => k p) z.property

theorem finiteCenter_central (z : FiniteCenter a b) (g : FiniteLocalCover a b) :
    Commute (z : FiniteLocalCover a b) g := by
  apply RestrictedProduct.ext
  intro p
  change (z : FiniteLocalCover a b) p * g p = g p * (z : FiniteLocalCover a b) p
  rcases finiteCenter_cases a b z p with h | h
  · rw [h, one_mul, mul_one]
  · rw [h]
    exact (localSign_central p a b (g p)).eq

def centralScalar (z : FiniteCenter a b) (p : Place) : ℂˣ :=
  if (z : FiniteLocalCover a b) p = 1 then 1 else -1

theorem centralScalar_finite (z : FiniteCenter a b) :
    (centralScalar a b z).HasFiniteMulSupport := by
  apply eventually_cofinite.mp
  filter_upwards [(z : FiniteLocalCover a b).2] with p hp
  rcases finiteCenter_cases a b z p with h | h
  · exact ite_eq_left h
  · have hf := (sectionSubgroup_fixes a b p _ hp).1
    change (localFirst p a b ((z : FiniteLocalCover a b) p) : LocalEnd p) (spherical p) =
      spherical p at hf
    rw [h] at hf
    change (negativeOperator p : LocalEnd p) (spherical p) = spherical p at hf
    exact (negativeOperator_not_fixed p hf).elim

theorem centralScalar_mul (x y : FiniteCenter a b) (p : Place) :
    centralScalar a b (x * y) p = centralScalar a b x p * centralScalar a b y p := by
  unfold centralScalar
  change (if (x : FiniteLocalCover a b) p * (y : FiniteLocalCover a b) p = 1 then _ else _) = _
  rcases finiteCenter_cases a b x p with hx | hx <;>
    rcases finiteCenter_cases a b y p with hy | hy <;>
    simp [hx, hy, (localProjection_kernel p a b).1, localSign_square]

def centralProduct : FiniteCenter a b →* ℂˣ where
  toFun z := ∏ᶠ p, centralScalar a b z p
  map_one' := finprod_eq_one_of_forall_eq_one fun _ => ite_eq_left rfl
  map_mul' x y := by
    conv_lhs => arg 1; intro p; rw [centralScalar_mul]
    exact finprod_mul_distrib (centralScalar_finite a b x) (centralScalar_finite a b y)

theorem centralProduct_cases (z : FiniteCenter a b) :
    centralProduct a b z = 1 ∨ centralProduct a b z = -1 := by
  change (∏ᶠ p, centralScalar a b z p) = 1 ∨ (∏ᶠ p, centralScalar a b z p) = -1
  rw [finprod_eq_prod _ (centralScalar_finite a b z)]
  induction (centralScalar_finite a b z).toFinset using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    rw [Finset.prod_insert hp]
    have h₁ : centralScalar a b z p = 1 ∨ centralScalar a b z p = -1 := by
      unfold centralScalar
      split
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases h₁ with h₁ | h₁ <;> rcases ih with h | h <;> rw [h₁, h] <;> simp

/-- The representative with its only nontrivial coordinate at two. -/
def singleSign : FiniteCenter a b := by
  let z : FiniteLocalCover a b := ⟨fun p => if p = dyadicPlace then localSign p a b else 1, by
    filter_upwards [(Set.finite_singleton dyadicPlace).compl_mem_cofinite] with p hp
    exact (ite_eq_right (show p ≠ dyadicPlace from hp)).symm ▸ (sectionSubgroup a b p).one_mem⟩
  refine ⟨z, ?_⟩
  apply RestrictedProduct.ext
  intro p
  change localProjection p a b (if p = dyadicPlace then localSign p a b else 1) = 1
  split
  · rfl
  · exact map_one _

theorem centralProduct_singleSign :
    centralProduct a b (singleSign a b) = -1 := by
  change (∏ᶠ p, centralScalar a b (singleSign a b) p) = -1
  rw [finprod_eq_single _ dyadicPlace]
  · exact ite_eq_right (by
      change (if dyadicPlace = dyadicPlace then localSign dyadicPlace a b else 1) ≠ 1
      rw [ite_eq_left rfl]
      exact (localProjection_kernel dyadicPlace a b).1)
  · intro p hp
    change (if (if p = dyadicPlace then localSign p a b else 1) = 1 then _ else _) = _
    rw [ite_eq_right hp, ite_eq_left rfl]

/-- The signs with total product one, as a central subgroup upstairs. -/
def neutralSigns : Subgroup (FiniteLocalCover a b) :=
  (centralProduct a b).ker.map (finiteProjection a b).ker.subtype

instance neutralSigns_normal : (neutralSigns a b).Normal where
  conj_mem x hx g := by
    obtain ⟨z, hz, rfl⟩ := hx
    change g * (z : FiniteLocalCover a b) * g⁻¹ ∈ neutralSigns a b
    rw [← (finiteCenter_central a b z g).eq, mul_assoc, mul_inv_cancel, mul_one]
    exact ⟨z, hz, rfl⟩

theorem neutralSigns_le_kernel : neutralSigns a b ≤ (finiteProjection a b).ker := by
  rintro _ ⟨z, _, rfl⟩
  exact z.property

abbrev FiniteCommon := FiniteLocalCover a b ⧸ neutralSigns a b
abbrev finiteQuotient := QuotientGroup.mk' (neutralSigns a b)

def commonProjection : FiniteCommon a b →* FiniteSL :=
  QuotientGroup.lift _ (finiteProjection a b) (neutralSigns_le_kernel a b)

theorem commonProjection_surjective : Function.Surjective (commonProjection a b) := by
  intro k
  obtain ⟨z, hz⟩ := finiteProjection_surjective a b k
  exact ⟨finiteQuotient a b z, hz⟩

def finiteSign : FiniteCommon a b := finiteQuotient a b (singleSign a b)

theorem finiteSign_central (g : FiniteCommon a b) : Commute (finiteSign a b) g := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (neutralSigns a b) g
  exact (finiteCenter_central a b (singleSign a b) x).map (finiteQuotient a b)

theorem commonProjection_kernel :
    finiteSign a b ≠ 1 ∧
      ∀ g, commonProjection a b g = 1 ↔ g = 1 ∨ g = finiteSign a b := by
  constructor
  · intro h
    obtain ⟨x, hx, he⟩ := (QuotientGroup.eq_one_iff _).mp h
    have e : x = singleSign a b := Subtype.ext he
    change centralProduct a b x = 1 at hx
    rw [e, centralProduct_singleSign] at hx
    have e := congrArg (fun u : ℂˣ => (u : ℂ)) hx
    norm_num at e
  · intro g
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (neutralSigns a b) g
    constructor
    · intro hz
      let x : FiniteCenter a b := ⟨z, hz⟩
      rcases centralProduct_cases a b x with h | h
      · exact Or.inl ((QuotientGroup.eq_one_iff _).mpr ⟨x, h, rfl⟩)
      · right
        have hm : centralProduct a b (x / singleSign a b) = 1 := by
          rw [map_div, h, centralProduct_singleSign, div_self']
        have hq := (QuotientGroup.eq_one_iff _).mpr
          (show z / (singleSign a b : FiniteLocalCover a b) ∈ neutralSigns a b from
            ⟨x / singleSign a b, hm, rfl⟩)
        exact div_eq_one.mp ((map_div (finiteQuotient a b) _ _).symm.trans hq)
    · rintro (h | h)
      · rw [h, map_one]
      · rw [h]
        exact (singleSign a b).property


end ZInQ.Manuscript.RC.Metaplectic2
