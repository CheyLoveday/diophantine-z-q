import ZInQKernel.Contrib.OneProof.RC.Height.Discharge
import Mathlib.GroupTheory.Torsion
import Mathlib.Data.ZMod.QuotientGroup

/-!
# Cokernel indices on the rank-one free quotients

The quotients use the full torsion subgroups of the point groups. The two
indices are cardinalities of actual cokernels of the induced point maps.
Generator coordinates identify these cokernels with integer quotients.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Height.FreeQuotientIndex

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- The quotient of an additive abelian group by its full torsion subgroup. -/
abbrev FreeQuotient (G : Type*) [AddCommGroup G] := G ⧸ AddCommGroup.torsion G

/-- The canonical projection to the quotient by full torsion. -/
def freeProjection (G : Type*) [AddCommGroup G] : G →+ FreeQuotient G :=
  QuotientAddGroup.mk' (AddCommGroup.torsion G)

theorem freeProjection_eq_zero_iff (x : G) :
    freeProjection G x = 0 ↔ IsOfFinAddOrder x :=
  (QuotientAddGroup.eq_zero_iff x).trans (AddCommGroup.mem_torsion x)

theorem freeProjection_eq_iff (x y : G) :
    freeProjection G x = freeProjection G y ↔ IsOfFinAddOrder (x - y) :=
  QuotientAddGroup.eq_iff_sub_mem.trans (AddCommGroup.mem_torsion (x - y))

/-- The map induced by the same additive map on the quotients by full torsion. -/
def inducedFreeMap (f : G →+ H) : FreeQuotient G →+ FreeQuotient H :=
  QuotientAddGroup.map (AddCommGroup.torsion G) (AddCommGroup.torsion H) f
    (AddCommGroup.le_comap_torsion f)

@[simp] theorem inducedFreeMap_projection (f : G →+ H) (x : G) :
    inducedFreeMap f (freeProjection G x) = freeProjection H (f x) := rfl

/-- The actual cokernel of the induced map on the torsion-free quotients. -/
abbrev FreeCokernel (f : G →+ H) :=
  FreeQuotient H ⧸ (inducedFreeMap f).range

/-- The canonical cokernel projection. -/
def cokernelProjection (f : G →+ H) : FreeQuotient H →+ FreeCokernel f :=
  QuotientAddGroup.mk' (inducedFreeMap f).range

/-- Multiples of the original generator, followed by the actual quotient map. -/
def generatorHom (g : G) : ℤ →+ FreeQuotient G where
  toFun n := freeProjection G (n • g)
  map_zero' := by rw [zero_zsmul, map_zero]
  map_add' m n := by rw [add_zsmul, map_add]

theorem generatorHom_injective (g : G) (hg : IsFreeGenerator g) :
    Function.Injective (generatorHom g) := by
  refine (injective_iff_map_eq_zero (generatorHom g)).2 ?_
  intro n hn
  have ht : IsOfFinAddOrder (n • g) := (freeProjection_eq_zero_iff (n • g)).1 hn
  exact eq_zero_of_isOfFinAddOrder_zsmul hg.1 ht

theorem generatorHom_surjective (g : G) (hg : IsFreeGenerator g) :
    Function.Surjective (generatorHom g) := by
  intro x
  obtain ⟨P, hP⟩ := QuotientAddGroup.mk'_surjective (AddCommGroup.torsion G) x
  obtain ⟨n, hn⟩ := hg.2 P
  refine ⟨n, ?_⟩
  exact ((freeProjection_eq_iff P (n • g)).2 hn).symm.trans hP

/-- Integer coordinates for the actual quotient, determined by the supplied generator. -/
def generatorEquiv (g : G) (hg : IsFreeGenerator g) : ℤ ≃+ FreeQuotient G :=
  AddEquiv.ofBijective (generatorHom g)
    ⟨generatorHom_injective g hg, generatorHom_surjective g hg⟩

@[simp] theorem generatorEquiv_apply (g : G) (hg : IsFreeGenerator g) (n : ℤ) :
    generatorEquiv g hg n = freeProjection G (n • g) := rfl

/-- The original torsion congruence determines the action on every free class. -/
theorem inducedFreeMap_generator (f : G →+ H) (gG : G) (gH : H)
    (hgG : IsFreeGenerator gG) (hgH : IsFreeGenerator gH) {a : ℤ}
    (ha : IsOfFinAddOrder (f gG - a • gH)) (n : ℤ) :
    inducedFreeMap f (generatorEquiv gG hgG n) = generatorEquiv gH hgH (n * a) := by
  change freeProjection H (f (n • gG)) = freeProjection H ((n * a) • gH)
  rw [map_zsmul, map_zsmul, map_zsmul, mul_smul]
  have hgen := (freeProjection_eq_iff (f gG) (a • gH)).2 ha
  rw [map_zsmul] at hgen
  exact congrArg (fun z : FreeQuotient H => n • z) hgen

/-- Residue coordinates on the original target free quotient. -/
def residueCoordinate (gH : H) (hgH : IsFreeGenerator gH) (a : ℤ) :
    FreeQuotient H →+ (ℤ ⧸ AddSubgroup.zmultiples a) :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples a)).comp
    (generatorEquiv gH hgH).symm.toAddMonoidHom

theorem residueCoordinate_surjective (gH : H) (hgH : IsFreeGenerator gH) (a : ℤ) :
    Function.Surjective (residueCoordinate gH hgH a) :=
  (QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples a)).comp
    (generatorEquiv gH hgH).symm.surjective

/-- The kernel is the image of the actual induced map, not a prescribed index subgroup. -/
theorem residueCoordinate_ker (f : G →+ H) (gG : G) (gH : H)
    (hgG : IsFreeGenerator gG) (hgH : IsFreeGenerator gH) {a : ℤ}
    (ha : IsOfFinAddOrder (f gG - a • gH)) :
    (residueCoordinate gH hgH a).ker = (inducedFreeMap f).range := by
  ext x
  constructor
  · intro hx
    have hx0 : (QuotientAddGroup.mk' (AddSubgroup.zmultiples a))
        ((generatorEquiv gH hgH).symm x) = 0 := hx
    have hxmem : (generatorEquiv gH hgH).symm x ∈ AddSubgroup.zmultiples a :=
      (QuotientAddGroup.eq_zero_iff _).1 hx0
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hxmem
    have hn' : n * a = (generatorEquiv gH hgH).symm x := by
      simpa only [Int.zsmul_eq_mul] using hn
    refine ⟨generatorEquiv gG hgG n, ?_⟩
    rw [inducedFreeMap_generator f gG gH hgG hgH ha n, hn', AddEquiv.apply_symm_apply]
  · rintro ⟨y, hy⟩
    obtain ⟨n, hn⟩ := (generatorEquiv gG hgG).surjective y
    change residueCoordinate gH hgH a x = 0
    rw [← hy, ← hn, inducedFreeMap_generator f gG gH hgG hgH ha n]
    change (QuotientAddGroup.mk' (AddSubgroup.zmultiples a))
      ((generatorEquiv gH hgH).symm (generatorEquiv gH hgH (n * a))) = 0
    rw [AddEquiv.symm_apply_apply]
    apply (QuotientAddGroup.eq_zero_iff (n * a)).2
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by simp only [Int.zsmul_eq_mul]⟩

/-- The actual cokernel is the integer quotient determined by the original map action. -/
def cokernelIntegerEquiv (f : G →+ H) (gG : G) (gH : H)
    (hgG : IsFreeGenerator gG) (hgH : IsFreeGenerator gH) {a : ℤ}
    (ha : IsOfFinAddOrder (f gG - a • gH)) :
    FreeCokernel f ≃+ (ℤ ⧸ AddSubgroup.zmultiples a) :=
  QuotientAddGroup.liftEquiv (inducedFreeMap f).range
    (residueCoordinate_surjective gH hgH a)
    (residueCoordinate_ker f gG gH hgG hgH ha).symm

@[simp] theorem cokernelIntegerEquiv_projection (f : G →+ H) (gG : G) (gH : H)
    (hgG : IsFreeGenerator gG) (hgH : IsFreeGenerator gH) {a : ℤ}
    (ha : IsOfFinAddOrder (f gG - a • gH)) (x : FreeQuotient H) :
    cokernelIntegerEquiv f gG gH hgG hgH ha (cokernelProjection f x) =
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples a))
        ((generatorEquiv gH hgH).symm x) := rfl

/-- Integer residue classes return to multiples of the original target generator. -/
theorem cokernelIntegerEquiv_symm_projection (f : G →+ H) (gG : G) (gH : H)
    (hgG : IsFreeGenerator gG) (hgH : IsFreeGenerator gH) {a : ℤ}
    (ha : IsOfFinAddOrder (f gG - a • gH)) (n : ℤ) :
    (cokernelIntegerEquiv f gG gH hgG hgH ha).symm
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples a)) n) =
      cokernelProjection f (generatorEquiv gH hgH n) := by
  apply (cokernelIntegerEquiv f gG gH hgG hgH ha).injective
  rw [AddEquiv.apply_symm_apply, cokernelIntegerEquiv_projection, AddEquiv.symm_apply_apply]

/-- The cyclic model is obtained after proving the actual cokernel equivalence. -/
def cokernelZModEquiv (f : G →+ H) (gG : G) (gH : H)
    (hgG : IsFreeGenerator gG) (hgH : IsFreeGenerator gH) {a : ℤ}
    (ha : IsOfFinAddOrder (f gG - a • gH)) : FreeCokernel f ≃+ ZMod a.natAbs :=
  (cokernelIntegerEquiv f gG gH hgG hgH ha).trans (Int.quotientZMultiplesEquivZMod a)

/-- Cardinality of the actual cokernel, derived from its integer-quotient equivalence. -/
theorem freeCokernel_card (f : G →+ H) (gG : G) (gH : H)
    (hgG : IsFreeGenerator gG) (hgH : IsFreeGenerator gH) {a : ℤ}
    (ha : IsOfFinAddOrder (f gG - a • gH)) : Nat.card (FreeCokernel f) = a.natAbs := by
  rw [Nat.card_congr (cokernelZModEquiv f gG gH hgG hgH ha).toEquiv, Nat.card_zmod]

theorem freeCokernel_finite (f : G →+ H) (gG : G) (gH : H)
    (hgG : IsFreeGenerator gG) (hgH : IsFreeGenerator gH) {a : ℤ}
    (ha : IsOfFinAddOrder (f gG - a • gH)) (ha0 : a ≠ 0) : Finite (FreeCokernel f) := by
  letI : NeZero a.natAbs := ⟨Int.natAbs_ne_zero.mpr ha0⟩
  exact Finite.of_injective (cokernelZModEquiv f gG gH hgG hgH ha).toEquiv
    (cokernelZModEquiv f gG gH hgG hgH ha).injective

section SumDifference

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Contrib.CloudB3RC53

variable {K : Type*} [Field K] [NumberField K] [DecidableEq K]
  [Algebra.IsQuadraticExtension ℚ K]
  (E : WeierstrassCurve ℚ) (h k : ℚ) (D : QuadData K k)
  [(qtwist E h).IsElliptic] [(qtwist E (h * k)).IsElliptic]

/-- The actual cokernel cardinality in the direction from the restriction point group to the product. -/
def sumDifferenceI : ℕ := Nat.card (FreeCokernel (diffMap E h k D))

/-- The actual cokernel cardinality in the direction from the product point group to the restriction. -/
def sumDifferenceJ : ℕ := Nat.card (FreeCokernel (sumMap E h k D))

/-- The quotient-index certificate for the same maps and the supplied genuine generators. -/
theorem actualCokernelIndex_sumDiff
    (gA : ((qtwist E h).baseChange K).toAffine.Point)
    (gB : ((qtwist E h).baseChange ℚ).toAffine.Point ×
      ((qtwist E (h * k)).baseChange ℚ).toAffine.Point)
    (hA : IsFreeGenerator gA) (hB : IsFreeGenerator gB) :
    ∃ α β : ℤ, IsOfFinAddOrder (diffMap E h k D gA - α • gB) ∧
      IsOfFinAddOrder (sumMap E h k D gB - β • gA) ∧ α * β = 2 ∧
      sumDifferenceI E h k D = α.natAbs ∧ sumDifferenceJ E h k D = β.natAbs ∧
      Nonempty (FreeCokernel (diffMap E h k D) ≃+ (ℤ ⧸ AddSubgroup.zmultiples α)) ∧
      Nonempty (FreeCokernel (sumMap E h k D) ≃+ (ℤ ⧸ AddSubgroup.zmultiples β)) ∧
      Finite (FreeCokernel (diffMap E h k D)) ∧ Finite (FreeCokernel (sumMap E h k D)) ∧
      sumDifferenceI E h k D * sumDifferenceJ E h k D = 2 := by
  obtain ⟨α, β, hα, hβ, hαβ, _⟩ := regulator_inputs_sumDiff E h k D gA gB hA hB
  have hα0 : α ≠ 0 := by
    intro hzero
    have htwo := hαβ
    rw [hzero, zero_mul] at htwo
    norm_num at htwo
  have hβ0 : β ≠ 0 := by
    intro hzero
    have htwo := hαβ
    rw [hzero, mul_zero] at htwo
    norm_num at htwo
  have hI : sumDifferenceI E h k D = α.natAbs :=
    freeCokernel_card (diffMap E h k D) gA gB hA hB hα
  have hJ : sumDifferenceJ E h k D = β.natAbs :=
    freeCokernel_card (sumMap E h k D) gB gA hB hA hβ
  refine ⟨α, β, hα, hβ, hαβ, hI, hJ,
    ⟨cokernelIntegerEquiv (diffMap E h k D) gA gB hA hB hα⟩,
    ⟨cokernelIntegerEquiv (sumMap E h k D) gB gA hB hA hβ⟩,
    freeCokernel_finite (diffMap E h k D) gA gB hA hB hα hα0,
    freeCokernel_finite (sumMap E h k D) gB gA hB hA hβ hβ0, ?_⟩
  rw [hI, hJ]
  exact ZInQ.Manuscript.RC.Central.isogenyIndex_mul hαβ

end SumDifference

end ZInQ.Manuscript.RC.Height.FreeQuotientIndex
