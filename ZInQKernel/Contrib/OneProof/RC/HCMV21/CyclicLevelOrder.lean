import ZInQKernel.Contrib.OneProof.RC.HCMV21.LevelIntersection
import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceTateLevel

/-! The endomorphism order of an actual cyclic enhancement. The level quotient
gives the second integrality condition. The split Tate chains and the
unchanged division completion give the level (tex 8464–8469, 9136–9146). -/

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory AlgebraicGeometry Eichler PkgI3.AbVar ZInQ.DefFaltings
open ZInQ.Contrib.MilneQuasiInverse
open scoped CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {A B : PkgI3.AbVar k} {a b : ℚ}

/-- In the source quaternion coordinates the enhanced order is the
intersection with the quotient endomorphism ring. The term on the right
is the pullback of the quotient ring along the quasi-isogeny, expressed
using the reverse isogeny divided by the kernel exponent. -/
theorem levelOrder_eq_intersection_of_levelQuotient
    (S : Order a b) (j : A.End ≃+* S.ring)
    (u : Hom A B) [IsFinite u.hom.left] [Etale u.hom.left] [Surjective u.hom.left]
    (v : Hom B A)
    (N : ℕ) (hN : N ≠ 0) (hNk : (N : k) ≠ 0)
    (huv : u.hom ≫ v.hom = ((N : ℤ) : A.End).hom)
    (hvu : v.hom ≫ u.hom = ((N : ℤ) : B.End).hom)
    (hC : ∀ x ∈ geometricKernel (L := k) u, x ^ N = 1) :
    let embed := S.ring.subtype.comp j.toRingHom
    ((levelOrderOfEndOrder S j (geometricKernel (L := k) u) N hN hC).ring : Set (Eichler.B a b)) =
      (S.ring : Set (Eichler.B a b)) ∩ Set.range (fun g : B.End =>
        (N : ℚ)⁻¹ • embed (Hom.mk' ((u.hom ≫ g.hom) ≫ v.hom))) := by
  let embed := S.ring.subtype.comp j.toRingHom
  let C := geometricKernel (L := k) u
  have hbase : C.map (levelPointsToClosure A) = geometricKernel (L := AlgebraicClosure k) u := by
    ext Q
    constructor
    · rintro ⟨P, hP, rfl⟩
      change ((geometricPointSourceIso k).hom ≫ P) ≫ u.hom = 1
      rw [Category.assoc, show P ≫ u.hom = 1 from hP, MonObj.comp_one]
    · intro hQ
      let P : A.Pt k := (geometricPointSourceIso k).inv ≫ Q
      have hP : (geometricPointSourceIso k).hom ≫ P = Q := by
        change (geometricPointSourceIso k).hom ≫ (geometricPointSourceIso k).inv ≫ Q = Q
        rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      refine ⟨P, ?_, hP⟩
      change P ≫ u.hom = 1
      apply (levelPointsToClosure_injective B)
      rw [map_one]
      change (geometricPointSourceIso k).hom ≫ (P ≫ u.hom) = 1
      rw [← Category.assoc, hP]
      exact hQ
  have hmem (f : A.End) : f ∈ levelEnd A C ↔ ∃ g : B.End, u.hom ≫ g.hom = f.hom ≫ u.hom := by
    rw [levelEnd_iff_levelHom_closure, hbase]
    exact Iff.of_eq (congrArg (fun s : Set A.End => f ∈ s)
      (levelEnd_eq_intersection_of_levelQuotient u))
  have hmul (f : A.End) :
      embed (Hom.mk' ((f.hom ≫ u.hom) ≫ v.hom)) = (N : ℚ) • embed f := by
    have hf : Hom.mk' ((f.hom ≫ u.hom) ≫ v.hom) = N • f := by
      apply Hom.ext'
      change (f.hom ≫ u.hom) ≫ v.hom = f.hom ^ N
      rw [Category.assoc, huv, AvSplit.comp_natCast_hom']
    rw [hf, map_nsmul, Nat.cast_smul_eq_nsmul]
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  ext x
  change x ∈ embed '' (levelEnd A C : Set A.End) ↔
    x ∈ (S.ring : Set (Eichler.B a b)) ∩ Set.range (fun g : B.End =>
      (N : ℚ)⁻¹ • embed (Hom.mk' ((u.hom ≫ g.hom) ≫ v.hom)))
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨g, hg⟩ := (hmem f).mp hf
    refine ⟨(j f).property, g, ?_⟩
    change (N : ℚ)⁻¹ • embed (Hom.mk' ((u.hom ≫ g.hom) ≫ v.hom)) = embed f
    have hgv : (Hom.mk' ((u.hom ≫ g.hom) ≫ v.hom) : A.End) =
        Hom.mk' ((f.hom ≫ u.hom) ≫ v.hom) :=
      Hom.ext' (congrArg (· ≫ v.hom) hg)
    rw [hgv, hmul, smul_smul, inv_mul_cancel₀ hN', one_smul]
  · rintro ⟨hx, g, hg⟩
    let f := j.symm ⟨x, hx⟩
    have hf : embed f = x := congrArg Subtype.val (j.apply_symm_apply ⟨x, hx⟩)
    refine ⟨f, (hmem f).mpr ⟨g, ?_⟩, hf⟩
    have he : embed (Hom.mk' ((u.hom ≫ g.hom) ≫ v.hom)) =
        embed (Hom.mk' ((f.hom ≫ u.hom) ≫ v.hom)) := by
      rw [hmul, hf, ← hg, smul_smul, mul_inv_cancel₀ hN', one_smul]
    have hj : Function.Injective embed := Subtype.val_injective.comp j.injective
    have he' : (u.hom ≫ g.hom) ≫ v.hom = (f.hom ≫ u.hom) ≫ v.hom :=
      congrArg Hom.hom (hj he)
    let mult : A.End := ((N : ℤ) : A.End)
    obtain ⟨hfinite, hetale, hsurj⟩ := finiteEtale_mul_of_ne_zero A N hNk
    let : IsFinite mult.hom.left := hfinite
    let : Etale mult.hom.left := hetale
    let : Surjective mult.hom.left := hsurj
    have : EffectiveEpi mult.hom :=
      Descent.GroupDescent.Construction.effectiveEpi_over_of_fpqc mult.hom
    have hpow : mult.hom = (𝟙 A.X : A.X ⟶ A.X) ^ N := by
      simpa only [Category.id_comp] using AvSplit.comp_natCast_hom' A (𝟙 A.X) N
    have hscale (w : Hom A B) : (w.hom ≫ v.hom) ≫ u.hom = mult.hom ≫ w.hom := by
      rw [Category.assoc, hvu, AvSplit.comp_natCast_hom', hpow, MonObj.pow_comp, Category.id_comp]
    let l : Hom A B := Hom.mk' (u.hom ≫ g.hom)
    let r : Hom A B := Hom.mk' (f.hom ≫ u.hom)
    have hcleared : (l.hom ≫ v.hom) ≫ u.hom = (r.hom ≫ v.hom) ≫ u.hom :=
      congrArg (fun w : A.X ⟶ A.X => w ≫ u.hom) he'
    rw [hscale l, hscale r] at hcleared
    exact (cancel_epi mult.hom).mp hcleared

/-- A cyclic geometric level subgroup gives an Eichler order of the full level.
At the characteristic prime its completion is the maximal level-one order,
and at every other prime it is the stabilizer of the integral Tate chain. -/
theorem levelOrderOfEndOrder_isEichler (hT : PkgI3.TateModuleFree)
    (q : ℕ) [Fact q.Prime] [CharP k q]
    (hdim : A.dim = 1) (S : Order a b) (j : A.End ≃+* S.ring)
    (hmax : ∀ T : Order a b, S.ring ≤ T.ring → T.ring ≤ S.ring)
    (N : ℕ) (hN : 0 < N) (hcop : N.Coprime q)
    (P : A.Pt k) (hP : orderOf P = N) :
    let hC : ∀ x ∈ Subgroup.zpowers P, x ^ N = 1 :=
      fun _ hx => orderOf_dvd_iff_pow_eq_one.mp (hP ▸ orderOf_dvd_of_mem_zpowers hx)
    IsEichler q N (levelOrderOfEndOrder S j (Subgroup.zpowers P) N hN.ne' hC) := by
  intro hC
  refine ⟨Fact.out, hN, hcop, ?_, ?_⟩
  · intro p hp he
    subst p
    have hqN : IsUnit (N : ℤ_[q]) :=
      PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hcop.symm)
    rw [levelOrderOfEndOrder_completion_eq S j (Subgroup.zpowers P) N hN.ne' hC q hqN]
    exact completion_maximal_of_order_maximal S hmax ⟨q, Fact.out⟩
  · intro p hp hpq
    have hpk : (p : k) ≠ 0 := by
      intro hz
      have hd := (CharP.cast_eq_zero_iff k q p).mp hz
      exact hpq ((Nat.prime_dvd_prime_iff_eq Fact.out hp.out).mp hd).symm
    let bE := S.basis.map j.symm.toAddEquiv.toIntLinearEquiv
    obtain ⟨hFree, hFinite, hRank⟩ := hT k A p hpk
    have hRank' : ((Module.finrank ℤ_[p] (A.T p) : ℕ∞) : WithBot ℕ∞) = 2 := by
      simpa only [hdim, mul_one] using hRank
    let bT := Module.finBasisOfFinrankEq ℤ_[p] (A.T p)
      (WithTop.coe_inj.mp (WithBot.coe_inj.mp hRank'))
    exact splitProfile_of_cyclicReference ⟨p, hp.out⟩ hpk N hN.ne' P hP _
      (S.ring.subtype.comp j.toRingHom) rfl bE bT

end ZInQ.Manuscript.RC.HCMV21
