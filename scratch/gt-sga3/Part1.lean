import ZInQKernel.OneProof.H.TailZ19
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Morphisms.SmoothSourceDescent
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.RingTheory.RegularLocalRing.Domain

open CategoryTheory AlgebraicGeometry Limits Topology TopologicalSpace

namespace SGA3IdComp

/-! ## Part 1: topology -/

section Top

variable {X : Type*} [TopologicalSpace X]

/-- The union of two open irreducible sets that meet is irreducible. -/
theorem isIrreducible_union_of_open {V W : Set X} (hV : IsIrreducible V) (hW : IsIrreducible W)
    (hVo : IsOpen V) (_hWo : IsOpen W) (hVW : (V ∩ W).Nonempty) : IsIrreducible (V ∪ W) := by
  refine ⟨hV.nonempty.mono Set.subset_union_left, ?_⟩
  intro u v hu hv hu' hv'
  -- `u` meets `V` iff it meets `W`
  have toV : ∀ {u : Set X}, IsOpen u → ((V ∪ W) ∩ u).Nonempty → (V ∩ u).Nonempty := by
    intro u hu h
    obtain ⟨z, hz | hz, hzu⟩ := h
    · exact ⟨z, hz, hzu⟩
    · obtain ⟨y, hyW, hyu, hyV⟩ := hW.2 u V hu hVo ⟨z, hz, hzu⟩ (hVW.mono fun a h => ⟨h.2, h.1⟩)
      exact ⟨y, hyV, hyu⟩
  obtain ⟨y, hyV, hyu, hyv⟩ := hV.2 u v hu hv (toV hu hu') (toV hv hv')
  exact ⟨y, Or.inl hyV, hyu, hyv⟩

/-- In a space where every point has an open compact irreducible neighbourhood, any two points of a
connected component lie in a common open compact irreducible set. -/
theorem exists_irred_of_mem_connectedComponent
    (h : ∀ x : X, ∃ V : Set X, IsOpen V ∧ IsCompact V ∧ IsIrreducible V ∧ x ∈ V)
    {x y : X} (hy : y ∈ connectedComponent x) :
    ∃ V : Set X, IsOpen V ∧ IsCompact V ∧ IsIrreducible V ∧ x ∈ V ∧ y ∈ V := by
  let R : Set X := {y | ∃ V : Set X, IsOpen V ∧ IsCompact V ∧ IsIrreducible V ∧ x ∈ V ∧ y ∈ V}
  have hRo : IsOpen R := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨V, hVo, hVc, hVi, hxV, hyV⟩
    exact ⟨V, fun z hz => ⟨V, hVo, hVc, hVi, hxV, hz⟩, hVo, hyV⟩
  have hRc : IsClosed R := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨W, hWo, hWc, hWi, hyW⟩ := h y
    refine ⟨W, ?_, hWo, hyW⟩
    rintro z hzW ⟨V, hVo, hVc, hVi, hxV, hzV⟩
    exact hy ⟨V ∪ W, hVo.union hWo, hVc.union hWc,
      isIrreducible_union_of_open hVi hWi hVo hWo ⟨z, hzV, hzW⟩, Or.inl hxV, Or.inr hyW⟩
  have hxR : x ∈ R := by
    obtain ⟨V, hVo, hVc, hVi, hxV⟩ := h x
    exact ⟨V, hVo, hVc, hVi, hxV, hxV⟩
  exact (IsClopen.connectedComponent_subset ⟨hRc, hRo⟩ hxR) hy

/-- In a noetherian quasi-sober space, a point whose generizations form a preirreducible set has an
open irreducible neighbourhood. -/
theorem exists_isOpen_isIrreducible_of_generizations [NoetherianSpace X] [QuasiSober X] (x : X)
    (hx : IsPreirreducible {y : X | y ⤳ x}) :
    ∃ V : Set X, IsOpen V ∧ IsIrreducible V ∧ x ∈ V := by
  have hgen : IsIrreducible {y : X | y ⤳ x} := ⟨⟨x, specializes_rfl⟩, hx⟩
  obtain ⟨Z, hZ, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hgen
  -- every irreducible component containing `x` is `Z`
  have huniq : ∀ Z' ∈ irreducibleComponents X, x ∈ Z' → Z' = Z := by
    intro Z' hZ' hxZ'
    have hirr : IsIrreducible Z' := hZ'.1
    have hgp : IsGenericPoint hirr.genericPoint Z' := by
      have := hirr.isGenericPoint_genericPoint_closure
      rwa [(isClosed_of_mem_irreducibleComponents Z' hZ').closure_eq] at this
    have hη : hirr.genericPoint ⤳ x := by
      rw [specializes_iff_mem_closure, hgp.def]
      exact hxZ'
    have hZ'Z : Z' ⊆ Z := by
      rw [← hgp.def]
      exact (isClosed_of_mem_irreducibleComponents Z hZ).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr (hsub hη))
    exact ((hZ'.2 hZ.1 hZ'Z).antisymm hZ'Z).symm
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  let V : Set X := (⋃₀ (irreducibleComponents X \ {Z}))ᶜ
  have hVo : IsOpen V := by
    show IsOpen (⋃₀ (irreducibleComponents X \ {Z}))ᶜ
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact hfin.sdiff.isClosed_biUnion fun W hW => isClosed_of_mem_irreducibleComponents W hW.1
  have hxV : x ∈ V := by
    rintro ⟨Z', ⟨hZ', hne⟩, hxZ'⟩
    exact hne (huniq Z' hZ' hxZ')
  have hVZ : V ⊆ Z := by
    intro y hy
    obtain ⟨Z', hZ', hyZ'⟩ := Set.mem_sUnion.mp (sUnion_irreducibleComponents (X := X) ▸ Set.mem_univ y)
    by_cases h : Z' = Z
    · exact h ▸ hyZ'
    · exact absurd ⟨Z', ⟨hZ', h⟩, hyZ'⟩ hy
  exact ⟨V, hVo, hZ.1.2.subset_irreducible ⟨x, hxV⟩ hVo le_rfl hVZ, hxV⟩

end Top

/-! ## Part 2: schemes whose stalks are domains -/

section Sch

/-- In a locally noetherian scheme whose stalks are domains, every point has an open, compact,
irreducible neighbourhood. -/
theorem exists_irred_nbhd (X : Scheme.{0}) [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) (x : X) :
    ∃ V : Set X, IsOpen V ∧ IsCompact V ∧ IsIrreducible V ∧ x ∈ V := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hN : NoetherianSpace U := noetherianSpace_of_isAffineOpen U hU
  -- the generizations of `x` form an irreducible set
  have hgenX : IsIrreducible {y : X | y ⤳ x} := by
    rw [← Scheme.range_fromSpecStalk]
    have := hX x
    have hi := (IrreducibleSpace.isIrreducible_univ (Spec (X.presheaf.stalk x))).image _
      (X.fromSpecStalk x).continuous.continuousOn
    rwa [Set.image_univ] at hi
  have hemb : IsOpenEmbedding (Subtype.val : U → X) := U.isOpen.isOpenEmbedding_subtypeVal
  have : QuasiSober U := hemb.quasiSober
  let x' : U := ⟨x, hxU⟩
  have hgenU : IsPreirreducible {y : U | y ⤳ x'} := by
    have h := hgenX.2.preimage hemb
    convert h using 1
    ext y
    exact (hemb.isInducing.specializes_iff).symm
  obtain ⟨V', hV'o, hV'i, hxV'⟩ := @exists_isOpen_isIrreducible_of_generizations U _ hN _ x' hgenU
  exact ⟨Subtype.val '' V', hemb.isOpenMap _ hV'o,
    (@NoetherianSpace.isCompact U _ hN V').image continuous_subtype_val,
    hV'i.image _ continuous_subtype_val.continuousOn, ⟨x', hxV', rfl⟩⟩

end Sch

end SGA3IdComp
