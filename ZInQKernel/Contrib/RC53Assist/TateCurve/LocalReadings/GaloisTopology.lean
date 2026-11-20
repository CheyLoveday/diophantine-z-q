import ZInQKernel.Contrib.RC53Assist.TateCurve.LocalReadings.ResidueFrobenius

/-!
# Finite element lifts and compact residue images

A homomorphism of Galois groups is continuous when each target element has an
algebraic source lift whose stabilizer fixes it. Finite bases turn this condition
into an open subgroup in the preimage of every Krull neighborhood.

A closed image of an open subgroup containing residue Frobenius is the whole
residue Galois group. Pulling back and using the kernel proves the local
open-subgroup formulation; surjectivity need not be assumed separately.

Kinds: proved statements only.
Locators: the Krull topology and infinite Galois correspondence; Serre,
*Local Fields*, I, §8 and III, §5, rather than the chapter in Cassels--Fröhlich.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open scoped Topology

/-- **PROVED**: elementwise algebraic lifts make a Galois-group homomorphism
continuous. Locator: finite-basis neighborhoods for the Krull topology. -/
theorem continuous_galoisHom_of_element_lifts {K F k L : Type*}
    [Field K] [Field F] [Field k] [Field L] [Algebra K F] [Algebra k L]
    [Algebra.IsIntegral K F] (f : (F ≃ₐ[K] F) →* (L ≃ₐ[k] L))
    (hlift : ∀ y : L, ∃ x : F, ∀ σ : F ≃ₐ[K] F, σ x = x → f σ y = y) :
    Continuous f := by
  apply continuous_of_tendsto_nhds_one f
  rw [Filter.tendsto_def]
  intro s hs
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff k L s).mp hs
  letI : FiniteDimensional k E := hE
  let b := Module.finBasis k E
  choose x hx using fun i => hlift (E.val (b i))
  let U : Subgroup (F ≃ₐ[K] F) := ⨅ i, MulAction.stabilizer (F ≃ₐ[K] F) (x i)
  have hU : IsOpen (U : Set (F ≃ₐ[K] F)) := by
    simpa only [U, Subgroup.coe_iInf] using
      (isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral (x i))
  apply Filter.mem_of_superset (hU.mem_nhds U.one_mem)
  intro σ hσ
  apply hsub
  change f σ ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have hb : ∀ i, f σ (E.val (b i)) = E.val (b i) := by
    intro i
    apply hx i σ
    have hm := (Subgroup.mem_iInf.mp hσ) i
    exact MulAction.mem_stabilizer_iff.mp hm
  have hlin : (f σ).toLinearMap.comp E.val.toLinearMap = E.val.toLinearMap := by
    apply b.ext
    exact hb
  exact LinearMap.congr_fun hlin (⟨y, hy⟩ : E)

/-- **PROVED**: in a compact topological group with a continuous residue action,
an open subgroup containing the residue kernel and arithmetic Frobenius is all
of the group. Surjectivity of the residue homomorphism is not an input.
Locator: Serre, *Local Fields*, I, §8; compact images and infinite Galois theory. -/
theorem compact_subgroup_eq_top_of_residue_frobenius (p : ℕ) [Fact p.Prime]
    {G L : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [Field L] [Algebra (ZMod p) L] [IsGalois (ZMod p) L]
    (r : G →* (L ≃ₐ[ZMod p] L)) (hr : Continuous r) (σ : G)
    (hF : ∀ y : L, r σ y = y ^ p) (H : Subgroup G) (hH : IsOpen (H : Set G))
    (hker : r.ker ≤ H) (hσ : σ ∈ H) : H = ⊤ := by
  have hclosed : IsClosed (H.map r : Set (L ≃ₐ[ZMod p] L)) := by
    simpa only [Subgroup.coe_map] using ((H.isClosed_of_isOpen hH).isCompact.image hr).isClosed
  have hmap : H.map r = ⊤ :=
    primeField_closed_subgroup_eq_top p L (r σ) hF (H.map r) hclosed
      (Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩)
  have hpre := Subgroup.comap_map_eq r H
  rw [hmap, Subgroup.comap_top, sup_eq_left.mpr hker] at hpre
  exact hpre.symm

end ZInQ.Contrib.RC53Assist.TateCurve
