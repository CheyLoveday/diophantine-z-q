import ZInQKernel.Contrib.OneProof.DegEqDetTate

/-! degpoly-proof scratch, part A: kernel points over any field extension `L ⊇ k` (`k` algebraically
closed) are in bijection with the fibre `ψ⁻¹(e₀)` of a finite endomorphism. -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

namespace DegPolyScratch

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

section General

variable {k : Type} [Field k] [IsAlgClosed k] {X : Scheme} (s : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType s]

/-- A morphism `Spec L → X` through a closed point `x` is determined by its composite to `Spec k`. -/
theorem eq_of_closed_aux (L : Type) [Field L] (h : Spec (CommRingCat.of L) ⟶ X) (x : X)
    (hx : IsClosed {x}) (hh : h (IsLocalRing.closedPoint L) = x)
    (c : CommRingCat.of k ⟶ CommRingCat.of L) (hc : h ≫ s = Spec.map c) :
    h = Spec.map ((residueFieldIsoBase s x hx).hom ≫ c) ≫ X.fromSpecResidueField x := by
  subst hh
  have e := (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField L X h)
  set φ := X.descResidueField (Scheme.stalkClosedPointTo h) with hφ
  have h1 : (residueFieldIsoBase s _ hx).inv ≫ φ = c := by
    apply Spec.map_injective
    rw [Spec.map_comp, SpecMap_residueFieldIsoBase_inv, ← Category.assoc, e, hc]
  rw [← h1, Iso.hom_inv_id_assoc]
  exact e.symm

theorem eq_of_closed (L : Type) [Field L] (h h' : Spec (CommRingCat.of L) ⟶ X) (x : X)
    (hx : IsClosed {x}) (hh : h (IsLocalRing.closedPoint L) = x)
    (hh' : h' (IsLocalRing.closedPoint L) = x) (hs : h ≫ s = h' ≫ s) : h = h' := by
  have hc := (Spec.map_preimage (h ≫ s)).symm
  rw [eq_of_closed_aux s L h x hx hh _ hc,
    eq_of_closed_aux s L h' x hx hh' _ (by rw [← hs]; exact hc)]

/-- The image of a `k`-point is a closed point. -/
theorem isClosed_of_section (p : Spec (CommRingCat.of k) ⟶ X) (hp : p ≫ s = 𝟙 _) :
    IsClosed {p (IsLocalRing.closedPoint k)} :=
  ((pointEquivClosedPoint s) ⟨p, hp⟩).2

/-- A point of a discrete closed fibre is closed. -/
theorem isClosed_of_mem_fibre {Y : Scheme} (f : X ⟶ Y) [LocallyQuasiFinite f] (y : Y)
    (hy : IsClosed {y}) (x : X) (hx : f x = y) : IsClosed {x} := by
  have hF : IsClosed (f ⁻¹' {y}) := hy.preimage f.continuous
  haveI : DiscreteTopology (f ⁻¹' {y}) := (f.isDiscrete_preimage_singleton y).to_subtype
  rw [← closure_subset_iff_isClosed]
  intro z hz
  have hzF : z ∈ f ⁻¹' {y} := (closure_minimal (by simpa using hx) hF) hz
  have hsp : x ⤳ z := specializes_iff_mem_closure.mpr hz
  have hsp' : (⟨x, hx⟩ : f ⁻¹' {y}) ⤳ ⟨z, hzF⟩ :=
    (Topology.IsInducing.subtypeVal.specializes_iff).mp hsp
  rw [Set.mem_singleton_iff]
  exact (congrArg Subtype.val hsp'.eq).symm

end General

section AbVarPts

variable {k : Type} [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k)

instance : LocallyOfFiniteType A.X.hom := inferInstance

/-- Two `L`-points through the same closed point are equal. -/
theorem pt_eq_of_closed (L : Type) [Field L] [Algebra k L] (P Q : A.Pt L) (x : A.X.left)
    (hx : IsClosed {x}) (hP : P.left (IsLocalRing.closedPoint L) = x)
    (hQ : Q.left (IsLocalRing.closedPoint L) = x) : P = Q := by
  apply Over.OverMorphism.ext
  exact eq_of_closed A.X.hom L P.left Q.left x hx hP hQ ((Over.w P).trans (Over.w Q).symm)

/-- The image of the identity point. -/
def e0 : A.X.left := (1 : A.Pt k).left (IsLocalRing.closedPoint k)

instance : Subsingleton ↥(𝟙_ (Over (Spec (CommRingCat.of k)))).left := by
  change Subsingleton (PrimeSpectrum k)
  infer_instance

theorem one_left_apply (L : Type) [Field L] [Algebra k L] :
    (1 : A.Pt L).left (IsLocalRing.closedPoint L) = e0 A := by
  rw [e0, Hom.one_def, Hom.one_def]
  change (η[A.X]).left ((toUnit (PkgI3.AbVar.ptObj (K := k) L)).left (IsLocalRing.closedPoint L)) =
    (η[A.X]).left ((toUnit (PkgI3.AbVar.ptObj (K := k) k)).left (IsLocalRing.closedPoint k))
  congr 1
  exact Subsingleton.elim _ _

theorem isClosed_e0 : IsClosed {e0 A} := by
  apply isClosed_of_section A.X.hom
  refine (Over.w (1 : A.Pt k)).trans ?_
  simp [PkgI3.AbVar.ptObj, Algebra.algebraMap_self]

variable {A} (ψ : PkgI3.AbVar.End A)

theorem mem_fibre_of_ker (L : Type) [Field L] [Algebra k L] (P : A.Pt L) (hP : P ≫ ψ.hom = 1) :
    ψ.hom.left (P.left (IsLocalRing.closedPoint L)) = e0 A := by
  rw [← one_left_apply A L, ← hP]
  rfl

/-- The fibre `ψ⁻¹(e₀)`. -/
def Fibre : Type := {x : A.X.left // ψ.hom.left x = e0 A}

variable [IsFinite ψ.hom.left]

theorem isClosed_of_fibre (x : A.X.left) (hx : ψ.hom.left x = e0 A) : IsClosed {x} :=
  isClosed_of_mem_fibre ψ.hom.left (e0 A) (isClosed_e0 A) x hx

instance : Finite (Fibre ψ) :=
  (ψ.hom.left.finite_preimage_singleton (e0 A)).to_subtype

/-- Kernel points to fibre points. -/
def kerToFibre (L : Type) [Field L] [Algebra k L] :
    (PkgI3.AbVar.ptMap (L := L) ψ).ker → Fibre ψ := fun P =>
  ⟨P.1.left (IsLocalRing.closedPoint L), mem_fibre_of_ker ψ L P.1 P.2⟩

theorem kerToFibre_injective (L : Type) [Field L] [Algebra k L] :
    Function.Injective (kerToFibre ψ L) := by
  intro P Q h
  have h' := congrArg Subtype.val h
  apply Subtype.ext
  exact pt_eq_of_closed A L P.1 Q.1 _ (isClosed_of_fibre ψ _ (kerToFibre ψ L P).2) rfl h'.symm

/-- The `L`-point through a fibre point. -/
def ptOfFibre (L : Type) [Field L] [Algebra k L] (x : Fibre ψ) : A.Pt L :=
  Over.homMk ((PkgI3.AbVar.ptObj (K := k) L).hom ≫
    pointOfClosedPoint A.X.hom x.1 (isClosed_of_fibre ψ x.1 x.2)) (by
      rw [Category.assoc, pointOfClosedPoint_comp, Category.comp_id])

theorem ptOfFibre_apply (L : Type) [Field L] [Algebra k L] (x : Fibre ψ) :
    (ptOfFibre ψ L x).left (IsLocalRing.closedPoint L) = x.1 := by
  change (pointOfClosedPoint A.X.hom x.1 _) _ = _
  exact pointOfClosedPoint_apply _ _ _ _

theorem ptOfFibre_mem (L : Type) [Field L] [Algebra k L] (x : Fibre ψ) :
    ptOfFibre ψ L x ≫ ψ.hom = 1 := by
  refine pt_eq_of_closed A L _ _ (e0 A) (isClosed_e0 A) ?_ (one_left_apply A L)
  change ψ.hom.left ((ptOfFibre ψ L x).left (IsLocalRing.closedPoint L)) = _
  rw [ptOfFibre_apply]
  exact x.2

theorem kerToFibre_surjective (L : Type) [Field L] [Algebra k L] :
    Function.Surjective (kerToFibre ψ L) := fun x =>
  ⟨⟨ptOfFibre ψ L x, ptOfFibre_mem ψ L x⟩, Subtype.ext (ptOfFibre_apply ψ L x)⟩

/-- **`#ker ψ(L) = #ψ⁻¹(e₀)` for every field `L ⊇ k`.** -/
theorem card_ker_eq (L : Type) [Field L] [Algebra k L] :
    Nat.card (PkgI3.AbVar.ptMap (L := L) ψ).ker = Nat.card (Fibre ψ) :=
  Nat.card_congr (Equiv.ofBijective _ ⟨kerToFibre_injective ψ L, kerToFibre_surjective ψ L⟩)

theorem finite_ker (L : Type) [Field L] [Algebra k L] :
    Finite (PkgI3.AbVar.ptMap (L := L) ψ).ker :=
  Finite.of_injective _ (kerToFibre_injective ψ L)

end AbVarPts

end DegPolyScratch
