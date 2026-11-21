import ZInQKernel.Contrib.OneProof.RC.HCMV21.DeuringHomRank
import ZInQKernel.Contrib.OneProof.RC.HCMV21.TateHomLattice

/-! The level-one maximal order and geometric Tate rank supply the
integral Hom calculation. The second lattice of a level chain comes
from the reverse map of the same geometric level isogeny. -/

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory AlgebraicGeometry PkgI3.AbVar ZInQ.DefFaltings
open scoped CategoryTheory.MonObj

variable {k : Type} [Field k] {A A' B B' : PkgI3.AbVar k}

private theorem nonempty_tate_basis_two (hT : PkgI3.TateModuleFree)
    (X : PkgI3.AbVar k) (hX : X.dim = 1) (p : ℕ) [Fact p.Prime] (hp : (p : k) ≠ 0) :
    Nonempty (Module.Basis (Fin 2) ℤ_[p] (X.T p)) := by
  obtain ⟨hFree, hFinite, hRank⟩ := hT k X p hp
  have hRank' : ((Module.finrank ℤ_[p] (X.T p) : ℕ∞) : WithBot ℕ∞) = 2 := by
    simpa only [hX, mul_one] using hRank
  exact ⟨Module.finBasisOfFinrankEq _ _ (WithTop.coe_inj.mp (WithBot.coe_inj.mp hRank'))⟩

/-- Away from the detector the geometric Hom action spans the whole
integral Tate Hom module. Deuring is used at level one and the two
geometric epimorphisms identify the Hom rank. -/
theorem span_homT_eq_top_of_deuring (h : DeuringSupersingularEndOrder)
    (hT : PkgI3.TateModuleFree)
    (q p : ℕ) [Fact q.Prime] [Fact p.Prime] [IsAlgClosed k] [CharP k q] (hp : (p : k) ≠ 0)
    (hA : A.dim = 1) (hB : B.dim = 1) (hss : ∀ P : B.Pt k, P ^ q = 1 → P = 1)
    (f : Hom A B) (g : Hom B A) [Epi f.hom] [Epi g.hom] :
    Submodule.span ℤ_[p] (Set.range (tateHom p A B)) = ⊤ := by
  obtain ⟨e⟩ := end_basis_of_deuring h q hB hss
  obtain ⟨b⟩ := hom_basis_of_epi_both_ways f g e
  obtain ⟨c⟩ := nonempty_tate_basis_two hT A hA p hp
  obtain ⟨d⟩ := nonempty_tate_basis_two hT B hB p hp
  exact span_homT_eq_top_of_basis p 4 hp b ((c.linearMap d).reindex finProdFinEquiv)

/-- The second lattice may be read through the actual level quotient.
The ranges of its reverse map on Tate modules replace the torsion
preimages, so both integral conditions belong to a single isogeny
diagram. -/
theorem span_levelHom_eq_tate_quotient_chain
    (u : Hom A A') (v : Hom B B')
    [IsFinite u.hom.left] [Etale u.hom.left] [Surjective u.hom.left]
    [IsFinite v.hom.left] [Etale v.hom.left] [Surjective v.hom.left]
    (p n : ℕ) [Fact p.Prime] (hp : (p : k) ≠ 0)
    (hA : ∀ P : A.Pt (AlgebraicClosure k), P ≫ u.hom = 1 → P ^ (p ^ n) = 1)
    (hB : ∀ P : B.Pt (AlgebraicClosure k), P ≫ v.hom = 1 → P ^ (p ^ n) = 1)
    (hfull : Submodule.span ℤ_[p] (Set.range (tateHom p A B)) = ⊤) :
    ∃ (u' : Hom A' A) (v' : Hom B' B),
      (Submodule.span ℤ_[p] (tateHom p A B '' (levelHom
        (geometricKernel (L := AlgebraicClosure k) u)
        (geometricKernel (L := AlgebraicClosure k) v) : Set (Hom A B))) :
          Set (A.T p →ₗ[ℤ_[p]] B.T p)) =
        {φ : A.T p →ₗ[ℤ_[p]] B.T p | Set.MapsTo (⇑φ)
          (LinearMap.range (homT (ℓ := p) u')) (LinearMap.range (homT (ℓ := p) v'))} := by
  obtain ⟨u', hu⟩ := exists_homT_range_of_etale_kernel u p n hA
  obtain ⟨v', hv⟩ := exists_homT_range_of_etale_kernel v p n hB
  have hu' : (LinearMap.range (homT (ℓ := p) u') : Set (A.T p)) =
      tateLevelPreimage A p n (geometricKernel (L := AlgebraicClosure k) u) :=
    Set.ext hu
  have hv' : (LinearMap.range (homT (ℓ := p) v') : Set (B.T p)) =
      tateLevelPreimage B p n (geometricKernel (L := AlgebraicClosure k) v) :=
    Set.ext hv
  refine ⟨u', v', ?_⟩
  rw [hu', hv']
  exact span_levelHom_eq_tateLevelMaps p n hp _ _ hA hfull

private theorem homT_reverse_comp_eq {X Y : PkgI3.AbVar k}
    (f : Hom X Y) (g : Hom Y X) (m p : ℕ) [Fact p.Prime]
    (h : f.hom ≫ g.hom = ((m : ℤ) : X.End).hom) (x : X.T p) :
    homT (ℓ := p) g (homT f x) = (m : ℤ_[p]) • x := by
  rw [Nat.cast_smul_eq_nsmul ℤ_[p]]
  apply Subtype.ext
  funext n
  change Additive.ofMul ((Additive.toMul (x.1 n) ≫ f.hom) ≫ g.hom) = m • x.1 n
  rw [Category.assoc, h, AvSplit.comp_natCast_hom']
  rfl

/-- The local kernel of an actual quotient determines the integral
range of its reverse map on Tate modules, even for a composite
degree. The prime-to-`p` factor of the degree is an integral unit. -/
theorem mem_tateRange_reverse_iff
    (u : Hom A B) (v : Hom B A) (p m n : ℕ) [Fact p.Prime] (c : ℤ_[p]ˣ)
    (hm : (m : ℤ_[p]) = (p : ℤ_[p]) ^ n * c)
    (hu : u.hom ≫ v.hom = ((m : ℤ) : A.End).hom)
    (hv : v.hom ≫ u.hom = ((m : ℤ) : B.End).hom)
    (x : A.T p) :
    x ∈ LinearMap.range (homT (ℓ := p) v) ↔
      Additive.toMul (x.1 n) ∈ geometricKernel (L := AlgebraicClosure k) u := by
  have htest : Additive.toMul (x.1 n) ∈ geometricKernel (L := AlgebraicClosure k) u ↔
      ∃ y : B.T p, homT u x = (p : ℤ_[p]) ^ n • y := by
    change ((Additive.toMul (x.1 n) ≫ u.hom) = 1) ↔ _
    exact (Additive.ofMul.injective.eq_iff).symm.trans
      (PkgI3.Tate.coord_eq_zero_iff (homT u x) n)
  rw [htest]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(c : ℤ_[p]) • y, by rw [homT_reverse_comp_eq v u m p hv, hm, mul_smul]⟩
  · rintro ⟨y, hy⟩
    have h := homT_reverse_comp_eq u v m p hu x
    rw [hy, map_smul, hm, mul_smul] at h
    have hcancel (z w : A.T p) (he : (p : ℤ_[p]) ^ n • z = (p : ℤ_[p]) ^ n • w) : z = w := by
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul ℤ_[p], Nat.cast_smul_eq_nsmul ℤ_[p]] at he
      apply Subtype.ext
      funext j
      have hh := congrArg (fun t : A.T p => t.1 (j + n)) he
      change p ^ n • z.1 (j + n) = p ^ n • w.1 (j + n) at hh
      rwa [PkgI3.Tate.pow_smul_shift z.2 n j, PkgI3.Tate.pow_smul_shift w.2 n j] at hh
    have hz := hcancel _ _ h
    exact ⟨(↑c⁻¹ : ℤ_[p]) • y, by rw [map_smul, hz, smul_smul, Units.inv_mul, one_smul]⟩

private theorem span_levelHom_eq_span_primary (p n r : ℕ) [Fact p.Prime]
    (hr : IsUnit (r : ℤ_[p]))
    (C : Subgroup (A.Pt (AlgebraicClosure k))) (D : Subgroup (B.Pt (AlgebraicClosure k)))
    (hC : ∀ P ∈ C, P ^ (r * p ^ n) = 1) :
    Submodule.span ℤ_[p] (tateHom p A B '' (levelHom C D : Set (Hom A B))) =
      Submodule.span ℤ_[p] (tateHom p A B '' (levelHom (C ⊓ (powMonoidHom (p ^ n)).ker)
        (D ⊓ (powMonoidHom (p ^ n)).ker) : Set (Hom A B))) := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨f, hf, rfl⟩
    refine ⟨f, fun P hP => ⟨hf P hP.1, ?_⟩, rfl⟩
    change (P ≫ f.hom) ^ (p ^ n) = 1
    have hh : P ^ (p ^ n) = 1 := hP.2
    rw [← MonObj.pow_comp, hh, MonObj.one_comp]
  · apply Submodule.span_le.mpr
    rintro _ ⟨f, hf, rfl⟩
    have hf' : r • f ∈ levelHom C D := by
      intro P hP
      have hp : P ^ r ∈ C ⊓ (powMonoidHom (p ^ n)).ker :=
        ⟨C.pow_mem hP r, by change (P ^ r) ^ (p ^ n) = 1; rw [← pow_mul]; exact hC P hP⟩
      change P ≫ f.hom ^ r ∈ D
      rw [MonObj.comp_pow, ← MonObj.pow_comp]
      exact (hf (P ^ r) hp).1
    let L := Submodule.span ℤ_[p] (tateHom p A B '' (levelHom C D : Set (Hom A B)))
    have h : tateHom p A B (r • f) ∈ L := Submodule.subset_span ⟨_, hf', rfl⟩
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℤ_[p]] at h
    have hinv : (↑hr.unit⁻¹ : ℤ_[p]) * (r : ℤ_[p]) = 1 :=
      (congrArg ((↑hr.unit⁻¹ : ℤ_[p]) * ·) hr.unit_spec.symm).trans (Units.inv_mul hr.unit)
    change tateHom p A B f ∈ L
    simpa only [smul_smul, hinv, one_smul] using L.smul_mem (↑hr.unit⁻¹ : ℤ_[p]) h

/-- For a composite cyclic level, the `p`-primary calculation applies
directly to both full level isogenies. No separate geometric quotient
by the `p`-primary part is required. -/
theorem span_levelHom_eq_tate_composite_quotient_chain
    (u : Hom A A') (u' : Hom A' A) (v : Hom B B') (v' : Hom B' B)
    (N p n r : ℕ) [Fact p.Prime] (hp : (p : k) ≠ 0)
    (hN : N = r * p ^ n) (hr : IsUnit (r : ℤ_[p]))
    (hu : u.hom ≫ u'.hom = ((N : ℤ) : A.End).hom)
    (hu' : u'.hom ≫ u.hom = ((N : ℤ) : A'.End).hom)
    (hv : v.hom ≫ v'.hom = ((N : ℤ) : B.End).hom)
    (hv' : v'.hom ≫ v.hom = ((N : ℤ) : B'.End).hom)
    (hfull : Submodule.span ℤ_[p] (Set.range (tateHom p A B)) = ⊤) :
    (Submodule.span ℤ_[p] (tateHom p A B '' (levelHom
      (geometricKernel (L := AlgebraicClosure k) u)
      (geometricKernel (L := AlgebraicClosure k) v) : Set (Hom A B))) :
        Set (A.T p →ₗ[ℤ_[p]] B.T p)) =
      {φ : A.T p →ₗ[ℤ_[p]] B.T p | Set.MapsTo (⇑φ)
        (LinearMap.range (homT (ℓ := p) u')) (LinearMap.range (homT (ℓ := p) v'))} := by
  let C := geometricKernel (L := AlgebraicClosure k) u
  let D := geometricKernel (L := AlgebraicClosure k) v
  have hC : ∀ P ∈ C, P ^ (r * p ^ n) = 1 := by
    intro P hP
    change P ≫ u.hom = 1 at hP
    rw [← hN, ← AvSplit.comp_natCast_hom' A P N, ← hu, ← Category.assoc, hP, MonObj.one_comp]
  have hN' : (N : ℤ_[p]) = (p : ℤ_[p]) ^ n * (hr.unit : ℤ_[p]) := by
    rw [hN, Nat.cast_mul, Nat.cast_pow, hr.unit_spec, mul_comm]
  have hrange {X Y : PkgI3.AbVar k} (f : Hom X Y) (g : Hom Y X)
      (h : f.hom ≫ g.hom = ((N : ℤ) : X.End).hom)
      (h' : g.hom ≫ f.hom = ((N : ℤ) : Y.End).hom) :
      (LinearMap.range (homT (ℓ := p) g) : Set (X.T p)) =
        tateLevelPreimage X p n (geometricKernel (L := AlgebraicClosure k) f ⊓
          (powMonoidHom (p ^ n)).ker) := by
    ext x
    rw [SetLike.mem_coe, mem_tateRange_reverse_iff f g p N n hr.unit hN' h h' x]
    change Additive.toMul (x.1 n) ∈ geometricKernel (L := AlgebraicClosure k) f ↔
      Additive.toMul (x.1 n) ∈ geometricKernel (L := AlgebraicClosure k) f ⊓ (powMonoidHom (p ^ n)).ker
    exact ⟨fun hx => ⟨hx, congrArg Additive.toMul (PkgI3.Tate.pow_smul_eq_zero x.2 n)⟩,
      fun hx => hx.1⟩
  change (Submodule.span ℤ_[p] (tateHom p A B '' (levelHom C D : Set (Hom A B))) :
    Set (A.T p →ₗ[ℤ_[p]] B.T p)) = _
  rw [span_levelHom_eq_span_primary p n r hr C D hC, hrange u u' hu hu', hrange v v' hv hv']
  exact span_levelHom_eq_tateLevelMaps p n hp _ _ (fun _ hP => hP.2) hfull

end ZInQ.Manuscript.RC.HCMV21
