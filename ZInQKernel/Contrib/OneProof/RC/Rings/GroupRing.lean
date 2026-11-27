import ZInQKernel.Contrib.OneProof.RC.Rings.OValuation
import ZInQKernel.Contrib.OneProof.RC.Determinant.B3Bridge
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Artinian.Ring

/-!
# Lane RC20: the local group rings `𝒪[G]` and `𝔽₂((t))[G]`

Manuscript (`diophantine_zq.tex`, 11/5 version):
* tex 7501–7502: "The residue field of the local ring `B = 𝒪[G]` is `𝔽₂((t))`; the augmentation ideal
  of the finite two-group lies in its maximal ideal";
* tex 4635–4640: "After the inner limit and inversion of `t`, the ring `𝔽₂((t))[G]` is local with
  nilpotent augmentation ideal".

Setting (as in lane RC7's `GroupRingUnits.lean`): `G` is a finite commutative monoid with `g * g = 1`
for all `g` (a finite elementary abelian two-group; the manuscript's `G = 𝔽₂^b` is RC7's
`Determinant.SignGroup b`), and `aug : O[G] →ₐ[O] O` is RC7's augmentation.

* Generic part: for a local ring `O` in which `1 + 2y` is a unit for every `y`, the group ring `O[G]` is
  local (`isLocalRing_groupRing`), its maximal ideal is `aug⁻¹(𝔪_O)` (`maximalIdeal_groupRing`), the
  augmentation ideal lies in it (`ker_aug_le_maximalIdeal`), and `aug` induces an isomorphism of
  residue fields (`residueFieldGroupRingEquiv`).
* `B = 𝒪[G]` for the genuine `𝒪` (lane RC7's `OO`): local, maximal ideal `aug⁻¹((2))`
  (`maximalIdeal_B`), augmentation ideal inside it, residue field `𝔽₂((t))` (`residueFieldBEquiv`).
* `k[G]` for a field `k` of characteristic two (in particular `k = 𝔽₂((t))`): local, every element of
  the augmentation ideal squares to zero, the augmentation ideal is nilpotent and equals the maximal
  ideal, and the residue field is `k`.
* Non-vacuity for `G = 𝔽₂¹`: `g - 1` is a nonzero element of the augmentation ideal, of square zero over
  `𝔽₂((t))`.

Everything here is `PROVED`.
-/

namespace ZInQ.Manuscript.RC.Rings

open ZInQ.Manuscript.RC.Determinant

/-! ## The generic local group ring -/

section Generic

variable {O : Type*} [CommRing O] [IsLocalRing O] {G : Type*} [CommMonoid G] [Finite G]

/-- **Tex 7501–7502 (PROVED).** For a local ring `O` in which `1 + 2y` is always a unit and a finite
elementary abelian two-group `G`, the group ring `O[G]` is local: an element is a unit iff its
augmentation is (RC7's `isUnit_iff_isUnit_aug`), and the nonunits of `O` are closed under sums. -/
theorem isLocalRing_groupRing (h2 : ∀ y : O, IsUnit (1 + 2 * y)) (hG : ∀ g : G, g * g = 1) :
    IsLocalRing (MonoidAlgebra O G) := by
  refine IsLocalRing.of_nonunits_add fun a b ha hb => ?_
  simp only [mem_nonunits_iff, isUnit_iff_isUnit_aug h2 hG, map_add] at ha hb ⊢
  exact IsLocalRing.nonunits_add ha hb

/-- **Tex 7501–7502 (PROVED).** The maximal ideal of the local ring `O[G]` is the preimage under the
augmentation of the maximal ideal of `O` (for `O = 𝒪` this is `(2, I_G)`). -/
theorem maximalIdeal_groupRing (h2 : ∀ y : O, IsUnit (1 + 2 * y)) (hG : ∀ g : G, g * g = 1) :
    letI := isLocalRing_groupRing h2 hG
    IsLocalRing.maximalIdeal (MonoidAlgebra O G) =
      Ideal.comap (aug : MonoidAlgebra O G →ₐ[O] O) (IsLocalRing.maximalIdeal O) := by
  have := isLocalRing_groupRing h2 hG
  ext x
  rw [IsLocalRing.mem_maximalIdeal, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, mem_nonunits_iff, isUnit_iff_isUnit_aug h2 hG]

/-- **Tex 7501–7502 "the augmentation ideal of the finite two-group lies in its maximal ideal"
(PROVED).** -/
theorem ker_aug_le_maximalIdeal (h2 : ∀ y : O, IsUnit (1 + 2 * y)) (hG : ∀ g : G, g * g = 1) :
    letI := isLocalRing_groupRing h2 hG
    RingHom.ker (aug : MonoidAlgebra O G →ₐ[O] O) ≤ IsLocalRing.maximalIdeal (MonoidAlgebra O G) := by
  have := isLocalRing_groupRing h2 hG
  rw [maximalIdeal_groupRing h2 hG]
  intro x hx
  rw [RingHom.mem_ker] at hx
  rw [Ideal.mem_comap, hx]
  exact zero_mem _

omit [IsLocalRing O] in
/-- **Tex 7501–7502 (PROVED).** The augmentation is a local homomorphism `O[G] → O`. -/
theorem isLocalHom_aug (h2 : ∀ y : O, IsUnit (1 + 2 * y)) (hG : ∀ g : G, g * g = 1) :
    IsLocalHom (aug : MonoidAlgebra O G →ₐ[O] O).toRingHom :=
  ⟨fun s hs => (isUnit_iff_isUnit_aug h2 hG s).mpr hs⟩

/-- **Tex 7501–7502 (PROVED construction).** The augmentation induces an isomorphism from the residue
field of `O[G]` onto the residue field of `O`. -/
noncomputable def residueFieldGroupRingEquiv (h2 : ∀ y : O, IsUnit (1 + 2 * y))
    (hG : ∀ g : G, g * g = 1) :
    letI := isLocalRing_groupRing h2 hG
    IsLocalRing.ResidueField (MonoidAlgebra O G) ≃+* IsLocalRing.ResidueField O :=
  letI := isLocalRing_groupRing h2 hG
  letI := isLocalHom_aug h2 hG
  RingEquiv.ofBijective (IsLocalRing.ResidueField.map (aug : MonoidAlgebra O G →ₐ[O] O).toRingHom)
    ⟨RingHom.injective _, fun y => by
      obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective y
      refine ⟨IsLocalRing.residue (MonoidAlgebra O G) (MonoidAlgebra.single 1 c), ?_⟩
      rw [IsLocalRing.ResidueField.map_residue]
      simp⟩

/-- **Tex 7501–7502 (PROVED).** The residue isomorphism is induced by the augmentation. -/
theorem residueFieldGroupRingEquiv_residue (h2 : ∀ y : O, IsUnit (1 + 2 * y))
    (hG : ∀ g : G, g * g = 1) (s : MonoidAlgebra O G) :
    letI := isLocalRing_groupRing h2 hG
    residueFieldGroupRingEquiv h2 hG (IsLocalRing.residue (MonoidAlgebra O G) s) =
      IsLocalRing.residue O (aug s) := by
  have := isLocalRing_groupRing h2 hG
  have := isLocalHom_aug h2 hG
  exact IsLocalRing.ResidueField.map_residue _ s

end Generic

/-! ## `B = 𝒪[G]` -/

section B

variable {G : Type*} [CommMonoid G] [Finite G]

/-- **Tex 7501 "the local ring `B = 𝒪[G]`" (PROVED).** -/
theorem isLocalRing_B (hG : ∀ g : G, g * g = 1) : IsLocalRing (MonoidAlgebra OO G) :=
  isLocalRing_groupRing isUnit_one_add_two_mul_OO hG

/-- **Tex 7501–7502 (PROVED).** The maximal ideal of `B = 𝒪[G]` is `aug⁻¹((2)) = (2, I_G)`. -/
theorem maximalIdeal_B (hG : ∀ g : G, g * g = 1) :
    letI := isLocalRing_B hG
    IsLocalRing.maximalIdeal (MonoidAlgebra OO G) =
      Ideal.comap (aug : MonoidAlgebra OO G →ₐ[OO] OO) (Ideal.span {2}) := by
  rw [← maximalIdeal_OO]
  exact maximalIdeal_groupRing isUnit_one_add_two_mul_OO hG

/-- **Tex 7501–7502 "the augmentation ideal of the finite two-group lies in its maximal ideal"
(PROVED).** -/
theorem ker_aug_le_maximalIdeal_B (hG : ∀ g : G, g * g = 1) :
    letI := isLocalRing_B hG
    RingHom.ker (aug : MonoidAlgebra OO G →ₐ[OO] OO) ≤
      IsLocalRing.maximalIdeal (MonoidAlgebra OO G) :=
  ker_aug_le_maximalIdeal isUnit_one_add_two_mul_OO hG

/-- **Tex 7501 "The residue field of the local ring `B = 𝒪[G]` is `𝔽₂((t))`" (PROVED construction):**
the augmentation followed by `residueFieldOOEquiv`. -/
noncomputable def residueFieldBEquiv (hG : ∀ g : G, g * g = 1) :
    letI := isLocalRing_B hG
    IsLocalRing.ResidueField (MonoidAlgebra OO G) ≃+* LaurentSeries (ZMod 2) :=
  (residueFieldGroupRingEquiv isUnit_one_add_two_mul_OO hG).trans residueFieldOOEquiv

/-- **Tex 7501 (PROVED).** The residue isomorphism of `B` is the augmentation followed by the residue
isomorphism of `𝒪`. -/
theorem residueFieldBEquiv_residue (hG : ∀ g : G, g * g = 1) (s : MonoidAlgebra OO G) :
    letI := isLocalRing_B hG
    residueFieldBEquiv hG (IsLocalRing.residue (MonoidAlgebra OO G) s) =
      residueFieldOOEquiv (IsLocalRing.residue OO (aug s)) := by
  exact congrArg residueFieldOOEquiv (residueFieldGroupRingEquiv_residue isUnit_one_add_two_mul_OO hG s)

end B

/-! ## `k[G]` for a field of characteristic two, e.g. `𝔽₂((t))[G]` -/

section CharTwo

variable {k : Type*} [Field k] [CharP k 2] {G : Type*} [CommMonoid G] [Finite G]

/-- **Tex 4635–4640 (PROVED).** In characteristic two every `1 + 2y` is a unit (it equals `1`). -/
theorem isUnit_one_add_two_mul_charTwo (y : k) : IsUnit (1 + 2 * y) := by
  simp [CharTwo.two_eq_zero]

/-- **Tex 4637–4638 "the ring `𝔽₂((t))[G]` is local" (PROVED),** for any field of characteristic
two. -/
theorem isLocalRing_charTwo (hG : ∀ g : G, g * g = 1) : IsLocalRing (MonoidAlgebra k G) :=
  isLocalRing_groupRing isUnit_one_add_two_mul_charTwo hG

omit [Finite G] in
/-- **Tex 4637–4638 (PROVED).** Every element of the augmentation ideal of `k[G]` squares to zero
(`(g - 1)² = g² - 2g + 1 = 2(1 - g) = 0`). -/
theorem mul_self_eq_zero_of_mem_ker_aug (hG : ∀ g : G, g * g = 1) {y : MonoidAlgebra k G}
    (hy : y ∈ RingHom.ker (aug : MonoidAlgebra k G →ₐ[k] k)) : y * y = 0 := by
  obtain ⟨z, hz⟩ := sq_mem_two_of_aug_eq_zero hG y hy
  rw [hz]
  have : (2 : MonoidAlgebra k G) = algebraMap k _ 2 := (map_ofNat _ 2).symm
  rw [this, CharTwo.two_eq_zero, map_zero, zero_mul]

/-- **Tex 4638 "nilpotent augmentation ideal" (PROVED).** The augmentation ideal of `k[G]` is
nilpotent: it lies in the nilradical (each element squares to zero), and the nilradical of the
finite-dimensional, hence Artinian, algebra `k[G]` is nilpotent. -/
theorem isNilpotent_ker_aug (hG : ∀ g : G, g * g = 1) :
    IsNilpotent (RingHom.ker (aug : MonoidAlgebra k G →ₐ[k] k)) := by
  have : IsArtinianRing (MonoidAlgebra k G) := IsArtinianRing.of_finite k (MonoidAlgebra k G)
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_nilradical (R := MonoidAlgebra k G)
  have hle : RingHom.ker (aug : MonoidAlgebra k G →ₐ[k] k) ≤ nilradical (MonoidAlgebra k G) :=
    fun y hy => ⟨2, by rw [pow_two]; exact mul_self_eq_zero_of_mem_ker_aug hG hy⟩
  exact ⟨n, le_antisymm ((Ideal.pow_right_mono hle n).trans hn.le) bot_le⟩

/-- **Tex 4637–4638 (PROVED).** The augmentation ideal of `k[G]` is its maximal ideal. -/
theorem maximalIdeal_charTwo (hG : ∀ g : G, g * g = 1) :
    letI := isLocalRing_charTwo (k := k) hG
    IsLocalRing.maximalIdeal (MonoidAlgebra k G) = RingHom.ker (aug : MonoidAlgebra k G →ₐ[k] k) := by
  have := isLocalRing_charTwo (k := k) hG
  rw [maximalIdeal_groupRing isUnit_one_add_two_mul_charTwo hG, IsLocalRing.maximalIdeal_eq_bot]
  rfl

/-- **Tex 4637–4638 (PROVED construction).** The residue field of `k[G]` is `k`. -/
noncomputable def residueFieldCharTwoEquiv (hG : ∀ g : G, g * g = 1) :
    letI := isLocalRing_charTwo (k := k) hG
    IsLocalRing.ResidueField (MonoidAlgebra k G) ≃+* k :=
  letI := isLocalRing_charTwo (k := k) hG
  (residueFieldGroupRingEquiv isUnit_one_add_two_mul_charTwo hG).trans
    (RingEquiv.ofBijective (IsLocalRing.residue k) ⟨RingHom.injective _, IsLocalRing.residue_surjective⟩).symm

/-- **Tex 4637–4638 (PROVED).** The residue isomorphism of `k[G]` is induced by the augmentation. -/
theorem residueFieldCharTwoEquiv_residue (hG : ∀ g : G, g * g = 1) (s : MonoidAlgebra k G) :
    letI := isLocalRing_charTwo (k := k) hG
    residueFieldCharTwoEquiv hG (IsLocalRing.residue (MonoidAlgebra k G) s) = aug s := by
  have := isLocalRing_charTwo (k := k) hG
  simp only [residueFieldCharTwoEquiv, RingEquiv.trans_apply]
  rw [residueFieldGroupRingEquiv_residue, RingEquiv.symm_apply_eq]
  rfl

end CharTwo

/-! ## Non-vacuity: `G = 𝔽₂¹` -/

/-- **Tex 4635–4640 (PROVED).** `𝔽₂((t))` has characteristic two (`𝔽₂ → 𝔽₂((t))` is injective). -/
instance instCharPLaurentSeriesZModTwo : CharP (LaurentSeries (ZMod 2)) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (LaurentSeries (ZMod 2))).injective 2

/-- **Tex 7501 (PROVED).** `B = 𝒪[𝔽₂^b]` is a local ring (instance form). -/
instance instIsLocalRingBSignGroup (b : ℕ) : IsLocalRing (MonoidAlgebra OO (SignGroup b)) :=
  isLocalRing_B signGroup_mul_self

/-- **Tex 4637–4638 (PROVED).** `𝔽₂((t))[𝔽₂^b]` is a local ring (instance form). -/
instance instIsLocalRingLaurentSignGroup (b : ℕ) :
    IsLocalRing (MonoidAlgebra (LaurentSeries (ZMod 2)) (SignGroup b)) :=
  isLocalRing_charTwo signGroup_mul_self

/-- Tex 7501 for the manuscript's `G = 𝔽₂^b`, with the instance above. -/
noncomputable example (b : ℕ) :
    IsLocalRing.ResidueField (MonoidAlgebra OO (SignGroup b)) ≃+* LaurentSeries (ZMod 2) :=
  residueFieldBEquiv signGroup_mul_self

/-- Tex 4635–4640 for `G = 𝔽₂^b`: the augmentation ideal of `𝔽₂((t))[G]` is nilpotent and is the maximal
ideal. -/
example (b : ℕ) :
    IsNilpotent (RingHom.ker
      (aug : MonoidAlgebra (LaurentSeries (ZMod 2)) (SignGroup b) →ₐ[_] _)) ∧
    IsLocalRing.maximalIdeal (MonoidAlgebra (LaurentSeries (ZMod 2)) (SignGroup b)) =
      RingHom.ker (aug : MonoidAlgebra (LaurentSeries (ZMod 2)) (SignGroup b) →ₐ[_] _) :=
  ⟨isNilpotent_ker_aug signGroup_mul_self, maximalIdeal_charTwo signGroup_mul_self⟩

/-- The nontrivial element of the sign group `𝔽₂¹`. -/
def gOne : SignGroup 1 := Multiplicative.ofAdd (fun _ => 1)

/-- **Tex 4635–4640, 7501–7502 (PROVED; non-vacuity).** The hypotheses are satisfiable: the sign group
`G = 𝔽₂^b` of RC7 is a finite commutative monoid with `g * g = 1`. -/
theorem signGroup_hyp (b : ℕ) : Finite (SignGroup b) ∧ ∀ g : SignGroup b, g * g = 1 :=
  ⟨inferInstance, signGroup_mul_self⟩

/-- **Tex 4635–4640 (PROVED; non-vacuity).** Over `𝔽₂((t))` and for `G = 𝔽₂¹`, the element `g - 1`
is a nonzero element of the augmentation ideal with square zero; in particular the augmentation ideal
(= the maximal ideal) of `𝔽₂((t))[G]` is a nonzero nilpotent ideal. -/
theorem nonvacuous_charTwo :
    let y : MonoidAlgebra (LaurentSeries (ZMod 2)) (SignGroup 1) :=
      MonoidAlgebra.of _ _ gOne - 1
    y ≠ 0 ∧ y ∈ RingHom.ker (aug : MonoidAlgebra (LaurentSeries (ZMod 2)) (SignGroup 1) →ₐ[_] _) ∧
      y * y = 0 := by
  intro y
  have hker : y ∈ RingHom.ker
      (aug : MonoidAlgebra (LaurentSeries (ZMod 2)) (SignGroup 1) →ₐ[_] _) := by
    rw [RingHom.mem_ker]
    simp [y]
  refine ⟨?_, hker, mul_self_eq_zero_of_mem_ker_aug signGroup_mul_self hker⟩
  intro h
  have hne : gOne ≠ 1 := by
    intro h1
    have := congrFun (congrArg Multiplicative.toAdd h1) 0
    simp [gOne] at this
  have := congrArg
    (fun f : MonoidAlgebra (LaurentSeries (ZMod 2)) (SignGroup 1) => f.coeff gOne) h
  simp [y, MonoidAlgebra.coeff_sub, MonoidAlgebra.one_def, MonoidAlgebra.of_apply,
    MonoidAlgebra.coeff_single, hne] at this

/-- **Tex 7501–7502 (PROVED; non-vacuity).** Over `𝒪` and for `G = 𝔽₂¹`, `g - 1` is a nonzero element
of the augmentation ideal of `B = 𝒪[G]`, hence of its maximal ideal. -/
theorem nonvacuous_B :
    let y : MonoidAlgebra OO (SignGroup 1) := MonoidAlgebra.of _ _ gOne - 1
    y ≠ 0 ∧ y ∈ RingHom.ker (aug : MonoidAlgebra OO (SignGroup 1) →ₐ[OO] OO) := by
  intro y
  refine ⟨?_, by rw [RingHom.mem_ker]; simp [y]⟩
  intro h
  have hne : gOne ≠ 1 := by
    intro h1
    have := congrFun (congrArg Multiplicative.toAdd h1) 0
    simp [gOne] at this
  have := congrArg (fun f : MonoidAlgebra OO (SignGroup 1) => f.coeff gOne) h
  simp [y, MonoidAlgebra.coeff_sub, MonoidAlgebra.one_def, MonoidAlgebra.of_apply,
    MonoidAlgebra.coeff_single, hne] at this

end ZInQ.Manuscript.RC.Rings
