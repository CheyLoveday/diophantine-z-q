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

end ZInQ.Manuscript.RC.HCMV21
