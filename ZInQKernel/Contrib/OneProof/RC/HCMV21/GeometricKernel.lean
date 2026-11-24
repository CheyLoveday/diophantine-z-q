import ZInQKernel.Contrib.OneProof.RC.HCMV21.GeometricOrders
import ZInQKernel.Contrib.OneProof.TateLatticeTorsion
import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Kernel
import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Descent
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_over_field

/-! Geometric quotient factorization for the prime-to-characteristic
part of the right-ideal dictionary. The geometric points suffice here
because the scheme kernel is étale. -/

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3.AbVar
open ZInQ.Contrib.MilneQuasiInverse ZInQ.DefFaltings
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

attribute [local instance] Kernel.kernelGroup

-- These three arguments are the small scheme and Tate calculations from
-- OneProof's GRUniformQuasiInverse, independent of its height and isogeny bounds.

/-- Geometric points over an algebraic closure detect equality of morphisms from a reduced
scheme locally of finite type over a field to a separated scheme over the same field. -/
private theorem overHom_ext_geometricPoints {K : Type} [Field K]
    {X Y : Over (Spec (.of K))} [LocallyOfFiniteType X.hom] [IsReduced X.left] [IsSeparated Y.hom]
    (f g : X ⟶ Y)
    (h : ∀ p : ptObj (K := K) (AlgebraicClosure K) ⟶ X, p ≫ f = p ≫ g) : f = g := by
  haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hd : Dense (closedPoints X.left) := by
    rw [dense_iff_closure_eq, ← Set.univ_inter (closedPoints X.left),
      JacobsonSpace.closure_inter_closedPoints_eq_closure isOpen_univ.isLocallyClosed, closure_univ]
  apply Over.OverMorphism.ext
  refine ext_of_fromSpecResidueField_eq f.left g.left Y.hom (closedPoints X.left) hd ?_
    (by rw [Over.w, Over.w])
  intro x hx
  let i := X.left.fromSpecResidueField x
  haveI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp hx
  let a : CommRingCat.of K ⟶ X.left.residueField x := Spec.preimage (i ≫ X.hom)
  have ha : Spec.map a = i ≫ X.hom := Spec.map_preimage _
  let : Algebra K (X.left.residueField x) := a.hom.toAlgebra
  haveI : IsFinite (i ≫ X.hom) :=
    (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace (f := i ≫ X.hom)).mpr inferInstance
  haveI : Module.Finite K (X.left.residueField x) := by
    change a.hom.Finite
    rw [← IsFinite.SpecMap_iff, ha]
    infer_instance
  let b : X.left.residueField x →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let j := Spec.map (CommRingCat.ofHom b.toRingHom)
  have hw : (j ≫ i) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) := by
    rw [Category.assoc, ← ha, ← Spec.map_comp]
    congr 1
    ext k
    exact b.commutes k
  let p : ptObj (K := K) (AlgebraicClosure K) ⟶ X := Over.homMk (j ≫ i) hw
  haveI : Surjective j := ⟨fun y => ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
  apply ext_of_isDominant_of_isSeparated Y.hom
    (by simp only [Category.assoc, Over.w]) j
  have hp := congrArg Over.Hom.left (h p)
  change (j ≫ i) ≫ f.left = (j ≫ i) ≫ g.left at hp
  simpa only [Category.assoc] using hp

private theorem homT_comp_eq_nsmul_id {K : Type} [Field K] {A B : PkgI3.AbVar K}
    (f : Hom A B) (r : Hom B A) (N ℓ : ℕ) [Fact ℓ.Prime]
    (h : f.hom ≫ r.hom = (𝟙 A.X : A.X ⟶ A.X) ^ N) :
    (homT (ℓ := ℓ) r).comp (homT (ℓ := ℓ) f) =
      N • (LinearMap.id : A.T ℓ →ₗ[ℤ_[ℓ]] A.T ℓ) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  change Additive.ofMul ((Additive.toMul (x.1 n) ≫ f.hom) ≫ r.hom) = (N • x).1 n
  rw [Category.assoc, h, MonObj.comp_pow, Category.comp_id]
  rfl

/-- For a quotient killed by `ℓ^n`, the reverse isogeny realizes the integral
Tate sublattice specified by the geometric kernel at coordinate `n`. -/
private theorem mem_range_homT_iff_coord_in_kernel {K : Type} [Field K] {A B : PkgI3.AbVar K}
    (f : Hom A B) (r : Hom B A) (ℓ n : ℕ) [Fact ℓ.Prime]
    (hfr : f.hom ≫ r.hom = (𝟙 A.X : A.X ⟶ A.X) ^ (ℓ ^ n))
    (hrf : r.hom ≫ f.hom = (𝟙 B.X : B.X ⟶ B.X) ^ (ℓ ^ n))
    (x : A.T ℓ) :
    x ∈ LinearMap.range (homT (ℓ := ℓ) r) ↔ Additive.toMul (x.1 n) ≫ f.hom = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    change (Additive.toMul (y.1 n) ≫ r.hom) ≫ f.hom = 1
    rw [Category.assoc, hrf, MonObj.comp_pow, Category.comp_id]
    exact congrArg Additive.toMul (PkgI3.Tate.pow_smul_eq_zero y.2 n)
  · intro hx
    let z := homT (ℓ := ℓ) f x
    have hz : z.1 n = 0 := congrArg Additive.ofMul hx
    obtain ⟨y, hy⟩ := (PkgI3.Tate.coord_eq_zero_iff z n).mp hz
    have he : z = (ℓ ^ n : ℕ) • y := by
      rw [hy, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    refine ⟨y, ?_⟩
    have hmul : (ℓ ^ n : ℕ) • x = (ℓ ^ n : ℕ) • homT (ℓ := ℓ) r y := by
      calc
        _ = homT (ℓ := ℓ) r z :=
          (congrArg (fun m : A.T ℓ →ₗ[ℤ_[ℓ]] A.T ℓ => m x)
            (homT_comp_eq_nsmul_id f r (ℓ ^ n) ℓ hfr)).symm
        _ = _ := by rw [he, map_nsmul]
    apply Subtype.ext
    funext j
    have hj := congrArg (fun v : A.T ℓ => v.1 (j + n)) hmul
    change (ℓ ^ n) • x.1 (j + n) = (ℓ ^ n) • (homT (ℓ := ℓ) r y).1 (j + n) at hj
    rw [PkgI3.Tate.pow_smul_shift x.2 n j,
      PkgI3.Tate.pow_smul_shift (homT (ℓ := ℓ) r y).2 n j] at hj
    exact hj.symm

/-- If the actual isogeny is étale, a group-scheme map killing its
geometric kernel descends uniquely along the isogeny. This is the
positive characteristic version of the kernel argument in
`GRUniformQuasiInverse`. -/
theorem existsUnique_factor_of_etale_kernel {k : Type} [Field k]
    {A B D : PkgI3.AbVar k} (f : Hom A B) (g : Hom A D)
    [IsFinite f.hom.left] [Etale f.hom.left] [Surjective f.hom.left]
    (h : ∀ P : A.Pt (AlgebraicClosure k), P ≫ f.hom = 1 → P ≫ g.hom = 1) :
    ∃! u : Hom B D, f.hom ≫ u.hom = g.hom := by
  let X := Kernel.kernelObject f.hom
  let i : X ⟶ A.X := Kernel.kernelInclusion f.hom
  have hi : i ≫ f.hom = 1 := Kernel.kernelInclusion_comp f.hom
  have hX : Etale X.hom := by
    rw [Kernel.kernel_hom_eq_snd f.hom]
    exact MorphismProperty.of_isPullback (P := @Etale) (Kernel.kernel_isPullback f.hom)
      inferInstance
  letI : Etale X.hom := hX
  haveI : IsReduced X.left := isReduced_of_smooth_over_field (show Smooth X.hom by infer_instance)
  have hk : i ≫ g.hom = 1 := by
    apply overHom_ext_geometricPoints
    intro P
    rw [MonObj.comp_one, ← Category.assoc]
    apply h
    rw [Category.assoc, hi, MonObj.comp_one]
  have hker (T : Over (Spec (.of k))) (P : T ⟶ A.X)
      (hP : P ≫ f.hom = 1) : P ≫ g.hom = 1 := by
    let v : T ⟶ X := (Kernel.kernelPointsEquiv f.hom T).symm ⟨P, hP⟩
    have hv : v ≫ i = P := Kernel.kernelPointsEquiv_symm_comp f.hom T P hP
    rw [← hv, Category.assoc, hk, MonObj.comp_one]
  haveI : EffectiveEpi f.hom :=
    Descent.GroupDescent.Construction.effectiveEpi_over_of_fpqc f.hom
  haveI : EffectiveEpi (f.hom ⊗ₘ f.hom) :=
    Descent.GroupDescent.Construction.effectiveEpi_tensor_over_of_fpqc f.hom f.hom
  obtain ⟨u, hu, hfu⟩ :=
    Descent.GroupKernelPowerDescent.Construction.groupHom_descends_of_kernel f.hom g.hom hker
  letI : IsMonHom u := hu
  refine ⟨Hom.mk' u, hfu, fun v hv => Hom.ext' ?_⟩
  apply (cancel_epi f.hom).mp
  exact hv.trans hfu.symm

/-- The source annihilator of an étale quotient is exactly the image of
the reverse Hom lattice under precomposition with the quotient map.
This is the left-ideal convention; it does not read the right-ideal
coordinates of the target by using the same generator. -/
theorem range_precomposeCurveMap_eq_annihilator {k : Type} [Field k]
    {A B : PkgI3.AbVar k} (f : Hom A B)
    [IsFinite f.hom.left] [Etale f.hom.left] [Surjective f.hom.left] :
    Set.range (precomposeCurveMap f) =
      (kernelAnnihilator A (geometricKernel (L := AlgebraicClosure k) f) : Set A.End) := by
  refine Set.Subset.antisymm (range_precomposeCurveMap_le_annihilator f) ?_
  intro g hg
  obtain ⟨u, hu, -⟩ := existsUnique_factor_of_etale_kernel f g (fun P hP => hg P hP)
  exact ⟨u, Hom.ext' hu⟩

/-- A factor map sends the specialized level subgroup onto the same
image as the second quotient map. -/
theorem factor_maps_level {k : Type} [Field k] {A B D : PkgI3.AbVar k}
    (f : Hom A B) (g : Hom A D) (u : Hom B D) (hu : f.hom ≫ u.hom = g.hom)
    (H : Subgroup (A.Pt k)) :
    (H.map (ptMap f)).map (ptMap u) = H.map (ptMap g) := by
  rw [Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro P
  change (P ≫ f.hom) ≫ u.hom = P ≫ g.hom
  rw [Category.assoc, hu]

/-- An existing factor map respects the levels when the level on the
intermediate curve is the image of the reference level. -/
theorem factor_mem_levelHom {k : Type} [Field k] {A B D : PkgI3.AbVar k}
    (f : Hom A B) (g : Hom A D) (u : Hom B D) (hu : f.hom ≫ u.hom = g.hom)
    (C : Subgroup (A.Pt k)) (T : Subgroup (D.Pt k)) (hg : g ∈ levelHom C T) :
    u ∈ levelHom (C.map (ptMap f)) T := by
  rintro _ ⟨P, hP, rfl⟩
  change (P ≫ f.hom) ≫ u.hom ∈ T
  rw [Category.assoc, hu]
  exact hg P hP

/-- The factor map respects endomorphism labels whenever the two
original quotients carry the labels of the source. The cancellation
uses the geometric epimorphism. -/
theorem factor_intertwines_label {k : Type} [Field k] {A B D : PkgI3.AbVar k}
    (f : Hom A B) (g : Hom A D) (u : Hom B D) [Epi f.hom]
    (hu : f.hom ≫ u.hom = g.hom)
    (a : A.End) (b : B.End) (d : D.End)
    (hb : f.hom ≫ b.hom = a.hom ≫ f.hom)
    (hd : g.hom ≫ d.hom = a.hom ≫ g.hom) :
    b.hom ≫ u.hom = u.hom ≫ d.hom := by
  apply (cancel_epi f.hom).mp
  calc
    f.hom ≫ (b.hom ≫ u.hom) = a.hom ≫ (f.hom ≫ u.hom) := by
      rw [← Category.assoc, hb, Category.assoc]
    _ = g.hom ≫ d.hom := by rw [hu, hd]
    _ = f.hom ≫ (u.hom ≫ d.hom) := by rw [← hu, Category.assoc]

/-- A finite étale quotient whose kernel is killed by `ℓ^n` gives the
integral lattice specified by that kernel at level `n`. The map back
is the factor of multiplication by `ℓ^n`; its existence uses the
scheme quotient, and the range calculation is the existing Tate
coordinate theorem. -/
theorem exists_homT_range_of_etale_kernel {k : Type} [Field k]
    {A B : PkgI3.AbVar k} (f : Hom A B)
    [IsFinite f.hom.left] [Etale f.hom.left] [Surjective f.hom.left]
    (ℓ n : ℕ) [Fact ℓ.Prime]
    (hk : ∀ P : A.Pt (AlgebraicClosure k), P ≫ f.hom = 1 → P ^ (ℓ ^ n) = 1) :
    ∃ r : Hom B A, ∀ x : A.T ℓ,
      x ∈ LinearMap.range (homT (ℓ := ℓ) r) ↔ Additive.toMul (x.1 n) ≫ f.hom = 1 := by
  haveI : IsMonHom ((𝟙 A.X : A.X ⟶ A.X) ^ (ℓ ^ n)) :=
    Descent.GroupDescent.Construction.groupHom_pow_isMonHom _ _
  let m : Hom A A := Hom.mk' ((𝟙 A.X : A.X ⟶ A.X) ^ (ℓ ^ n))
  obtain ⟨r, hr, -⟩ := existsUnique_factor_of_etale_kernel f m (fun P hP => by
    change P ≫ (𝟙 A.X : A.X ⟶ A.X) ^ (ℓ ^ n) = 1
    rw [MonObj.comp_pow, Category.comp_id]
    exact hk P hP)
  haveI : EffectiveEpi f.hom :=
    Descent.GroupDescent.Construction.effectiveEpi_over_of_fpqc f.hom
  change f.hom ≫ r.hom = (𝟙 A.X : A.X ⟶ A.X) ^ (ℓ ^ n) at hr
  have hrf : r.hom ≫ f.hom = (𝟙 B.X : B.X ⟶ B.X) ^ (ℓ ^ n) := by
    apply (cancel_epi f.hom).mp
    rw [← Category.assoc, hr, MonObj.pow_comp, Category.id_comp, MonObj.comp_pow, Category.comp_id]
  exact ⟨r, mem_range_homT_iff_coord_in_kernel f r ℓ n hr hrf⟩

/-- Integral saturation at a prime away from the characteristic:
divisibility on the Tate module descends to divisibility of the curve
map, provided the indicated multiplication isogeny is finite étale
and the prime is surjective on geometric points. -/
theorem exists_eq_nsmul_of_etale_homT_dvd {k : Type} [Field k] {A B : PkgI3.AbVar k}
    (f : Hom A B) (ℓ n : ℕ) [Fact ℓ.Prime]
    [IsFinite ((((ℓ ^ n : ℕ) : ℤ) : A.End).hom).left]
    [Etale ((((ℓ ^ n : ℕ) : ℤ) : A.End).hom).left]
    [Surjective ((((ℓ ^ n : ℕ) : ℤ) : A.End).hom).left]
    (hsurj : Function.Surjective (fun x : Additive (A.Pt (AlgebraicClosure k)) => ℓ • x))
    (h : ∀ x : A.T ℓ, ∃ y : B.T ℓ, homT f x = (ℓ : ℤ_[ℓ]) ^ n • y) :
    ∃ g : Hom A B, f = (ℓ ^ n : ℕ) • g := by
  let m : A.End := (((ℓ ^ n : ℕ) : ℤ) : A.End)
  obtain ⟨r, hr, -⟩ := existsUnique_factor_of_etale_kernel m f (fun P hP => by
    have hp : ℓ ^ n • Additive.ofMul P = 0 := by
      change P ≫ ((((ℓ ^ n : ℕ) : ℤ) : A.End).hom) = 1 at hP
      rw [AvSplit.comp_natCast_hom' A P (ℓ ^ n)] at hP
      exact congrArg Additive.ofMul hP
    obtain ⟨x, hx⟩ := ZInQ.Contrib.TateLatticeTorsion.exists_tateCoord_of_torsion hsurj hp
    have hZero := (PkgI3.Tate.coord_eq_zero_iff (homT f x) n).mpr (h x)
    change Additive.ofMul (Additive.toMul (x.1 n) ≫ f.hom) = 0 at hZero
    rw [hx] at hZero
    exact congrArg Additive.toMul hZero)
  refine ⟨r, Hom.ext' ?_⟩
  change f.hom = r.hom ^ (ℓ ^ n)
  rw [← hr]
  change (((ℓ ^ n : ℕ) : ℤ) : A.End).hom ≫ r.hom = r.hom ^ (ℓ ^ n)
  rw [← Category.id_comp (_ ≫ r.hom), ← Category.assoc, AvSplit.comp_natCast_hom',
    MonObj.pow_comp, Category.id_comp]

/-- The preimage of a geometric level subgroup in the integral Tate
module, read at its torsion exponent. -/
def tateLevelPreimage {k : Type} [Field k] (A : PkgI3.AbVar k)
    (ℓ e : ℕ) [Fact ℓ.Prime] (C : Subgroup (A.Pt (AlgebraicClosure k))) :
    Set (A.T ℓ) :=
  {x | Additive.toMul (x.1 e) ∈ C}

/-- For an actual geometric map, preserving the level is equivalent to
mapping the preimages in the Tate modules into one another. The reverse
implication uses surjectivity on geometric `ℓ`-division to lift a given
point of the source level. -/
theorem mem_levelHom_iff_tateLevelPreimage_mapsTo {k : Type} [Field k]
    {A B : PkgI3.AbVar k} (f : Hom A B) (ℓ e : ℕ) [Fact ℓ.Prime]
    (C : Subgroup (A.Pt (AlgebraicClosure k))) (D : Subgroup (B.Pt (AlgebraicClosure k)))
    (hC : ∀ P ∈ C, P ^ (ℓ ^ e) = 1)
    (hsurj : Function.Surjective (fun x : Additive (A.Pt (AlgebraicClosure k)) => ℓ • x)) :
    f ∈ levelHom C D ↔ Set.MapsTo (homT (ℓ := ℓ) f)
      (tateLevelPreimage A ℓ e C) (tateLevelPreimage B ℓ e D) := by
  constructor
  · intro h x hx
    change Additive.toMul (x.1 e) ≫ f.hom ∈ D
    exact h _ hx
  · intro h P hP
    have hz : ℓ ^ e • Additive.ofMul P = 0 := congrArg Additive.ofMul (hC P hP)
    obtain ⟨x, hx⟩ := ZInQ.Contrib.TateLatticeTorsion.exists_tateCoord_of_torsion hsurj hz
    have hxC : x ∈ tateLevelPreimage A ℓ e C := by
      change Additive.toMul (x.1 e) ∈ C
      rw [hx]
      exact hP
    have hD := h hxC
    change Additive.toMul (x.1 e) ≫ f.hom ∈ D at hD
    rwa [hx] at hD

end ZInQ.Manuscript.RC.HCMV21
