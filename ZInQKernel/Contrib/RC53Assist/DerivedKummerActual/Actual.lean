import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.DualQuasiIso
import ZInQKernel.Contrib.CloudB3RC53.Torsion.KummerIdentification
import Mathlib
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Selmer
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.Dual
import ZInQKernel.Contrib.CloudB3RC53.Duality.KummerTruncIsotropy
import ZInQKernel.Contrib.RC53Assist.DerivedKummer.ComparisonAlgebra
import ZInQKernel.Contrib.RC53Assist.DerivedKummer.LocalDuality
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Comp
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Basic
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Bilinear
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Galois
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.CupOne
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Basic
import ZInQKernel.Contrib.RC53Assist.DerivedKummer.DegreeZero
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.KummerImage
import ZInQKernel.Contrib.CloudB3RC53.Mattuck.Two
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Data.ZMod.QuotientRing
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TauCetiComparison
import ZInQKernel.Contrib.TauCeti.Algebra.Module.Torsion.TateModule
import ZInQKernel.Contrib.TauCeti.FieldTheory.GaloisCohomology.Kummer

/-!
# The two-adic completion of the actual point group

The completion is the inverse limit of the quotients by powers of two.
Its scalar action is induced by the canonical finite residue maps. Reduction
of the completion agrees with reduction of the point group, without a
finiteness hypothesis. The torsion comparison retains rational torsion.
-/

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual

open ZInQ.Contrib.CloudB3RC53.Duality
open ZInQ.Contrib.RC53Assist.DerivedKummer

/-- The ideal defining two-adic completion of an additive group. -/
def twoIdeal : Ideal ℤ := Ideal.span {(2 : ℤ)}

/-- The powers of the defining ideal have their usual generators. -/
theorem twoIdeal_pow (a : ℕ) :
    twoIdeal ^ a = Ideal.span {((2 ^ a : ℕ) : ℤ)} := by
  simp [twoIdeal, Ideal.span_singleton_pow]

/-- The defining ideal is finitely generated. -/
theorem twoIdeal_fg : twoIdeal.FG := twoIdeal.fg_of_isNoetherianRing

/-- The finite residue ring written as a quotient of the integers. -/
def residueSection (a : ℕ) : ZMod (2 ^ a) →+* ℤ ⧸ twoIdeal ^ a :=
  (Ideal.quotEquivOfEq (twoIdeal_pow a).symm).toRingHom.comp
    (Int.quotientSpanNatEquivZMod (2 ^ a)).symm.toRingHom

/-- The canonical residue of a two-adic integer. -/
def integerResidue (a : ℕ) : ℤ_[2] →+* ℤ ⧸ twoIdeal ^ a :=
  (residueSection a).comp (PadicInt.toZModPow a)

/-- The finite residue maps commute with the quotient transitions. -/
theorem integerResidue_compatible {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow twoIdeal h).comp (integerResidue n) = integerResidue m := by
  unfold integerResidue
  rw [← RingHom.comp_assoc]
  have hs : (Ideal.Quotient.factorPow twoIdeal h).comp (residueSection n) =
      (residueSection m).comp (ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2 ^ m))) :=
    Subsingleton.elim _ _
  rw [hs, RingHom.comp_assoc, PadicInt.zmod_cast_comp_toZModPow m n h]

/-- Two-adic integers act through their compatible finite residues. -/
def padicToIntegerCompletion : ℤ_[2] →+* AdicCompletion twoIdeal ℤ :=
  AdicCompletion.liftRingHom twoIdeal integerResidue integerResidue_compatible

/-- The actual two-adic completion of an additive group. -/
abbrev PointCompletion (P : Type*) [AddCommGroup P] := AdicCompletion twoIdeal P

instance pointCompletionModule (P : Type*) [AddCommGroup P] :
    Module ℤ_[2] (PointCompletion P) :=
  Module.compHom (PointCompletion P) padicToIntegerCompletion

/-- The canonical map from points to their completion. -/
abbrev completePoint (P : Type*) [AddCommGroup P] : P →ₗ[ℤ] PointCompletion P :=
  AdicCompletion.of twoIdeal P

/-- The subgroup of points divisible by the indicated power of two. -/
abbrev pointPowSub (P : Type*) [AddCommGroup P] (a : ℕ) : Submodule ℤ P :=
  twoIdeal ^ a • ⊤

/-- Membership in the defining filtration is actual divisibility of points. -/
theorem mem_pointPowSub (P : Type*) [AddCommGroup P] (a : ℕ) (x : P) :
    x ∈ pointPowSub P a ↔ ∃ y : P, (2 ^ a : ℕ) • y = x := by
  rw [pointPowSub, twoIdeal_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and, Nat.cast_smul_eq_nsmul]

/-- The additive subgroup underlying the filtration is the multiplication image. -/
theorem pointPowSub_toAddSubgroup (P : Type*) [AddCommGroup P] (a : ℕ) :
    (pointPowSub P a).toAddSubgroup = (nsmulAddMonoidHom (α := P) (2 ^ a)).range := by
  ext x
  exact mem_pointPowSub P a x

/-- The finite levels of the completion are the actual point quotients. -/
def pointLevelEquiv (P : Type*) [AddCommGroup P] (a : ℕ) :
    (P ⧸ pointPowSub P a) ≃+ TateDualityData.pointMod (P := P) (2 ^ a) :=
  QuotientAddGroup.quotientAddEquivOfEq (pointPowSub_toAddSubgroup P a)

/-- The level dictionary is the identity on point representatives. -/
theorem pointLevelEquiv_mk (P : Type*) [AddCommGroup P] (a : ℕ) (x : P) :
    pointLevelEquiv P a (Submodule.Quotient.mk x) = QuotientAddGroup.mk x := rfl

/-- Integer and two-adic scalar multiplication give the same multiplication image. -/
theorem completion_nSub_toAddSubgroup (P : Type*) [AddCommGroup P] (a : ℕ) :
    (nSub ((2 : ℤ_[2]) ^ a) (PointCompletion P)).toAddSubgroup =
      (pointPowSub (PointCompletion P) a).toAddSubgroup := by
  ext x
  rw [Submodule.mem_toAddSubgroup, mem_nSub, Submodule.mem_toAddSubgroup,
    mem_pointPowSub]
  have hpow : ((2 ^ a : ℕ) : ℤ_[2]) = (2 : ℤ_[2]) ^ a := by simp
  rw [← hpow]
  simp only [Nat.cast_smul_eq_nsmul]

/-- The actual kernel of a completion projection is precisely the scalar image. -/
theorem completion_eval_ker (P : Type*) [AddCommGroup P] (a : ℕ) :
    (nSub ((2 : ℤ_[2]) ^ a) (PointCompletion P)).toAddSubgroup =
      (AdicCompletion.eval twoIdeal P a).toAddMonoidHom.ker := by
  rw [completion_nSub_toAddSubgroup]
  change (twoIdeal ^ a • (⊤ : Submodule ℤ (AdicCompletion twoIdeal P))).toAddSubgroup = _
  rw [AdicCompletion.pow_smul_top_eq_ker_eval twoIdeal_fg]
  rfl

/-- The completion modulo a power of two is canonically the actual point quotient. -/
def completionQuotientEquiv (P : Type*) [AddCommGroup P] (a : ℕ) :
    (PointCompletion P ⧸ nSub ((2 : ℤ_[2]) ^ a) (PointCompletion P)) ≃+
      TateDualityData.pointMod (P := P) (2 ^ a) :=
  (QuotientAddGroup.liftEquiv _ (AdicCompletion.eval_surjective twoIdeal P a)
    (completion_eval_ker P a)).trans (pointLevelEquiv P a)

/-- Reduction is evaluation of the actual compatible quotient family. -/
theorem completionQuotientEquiv_mk (P : Type*) [AddCommGroup P] (a : ℕ)
    (x : PointCompletion P) :
    completionQuotientEquiv P a (Submodule.Quotient.mk x) = pointLevelEquiv P a (x.val a) := rfl

/-- The completion comparison agrees with the point quotient on every point. -/
theorem completionQuotientEquiv_completePoint (P : Type*) [AddCommGroup P] (a : ℕ) (x : P) :
    completionQuotientEquiv P a (Submodule.Quotient.mk (completePoint P x)) =
      QuotientAddGroup.mk x := rfl

/-- The degree-one identification required for the actual elliptic point group. -/
def etaOne {F : Type} [Field F] [DecidableEq F] (B : WeierstrassCurve F) :
    (PointCompletion B.toAffine.Point ⧸ nSub (2 : ℤ_[2]) (PointCompletion B.toAffine.Point)) ≃+
      TateDualityData.pointMod (P := B.toAffine.Point) 2 :=
  completionQuotientEquiv B.toAffine.Point 1

/-- The actual degree-one identification has the canonical point evaluation. -/
theorem etaOne_completePoint {F : Type} [Field F] [DecidableEq F] (B : WeierstrassCurve F)
    (p : B.toAffine.Point) :
    etaOne B (Submodule.Quotient.mk (completePoint B.toAffine.Point p)) =
      QuotientAddGroup.mk p := rfl

/-- Powers of two act by the corresponding natural multiplication. -/
theorem twoPower_smul (P : Type*) [AddCommGroup P] [Module ℤ_[2] P]
    (a : ℕ) (x : P) : (2 : ℤ_[2]) ^ a • x = (2 ^ a : ℕ) • x := by
  have hpow : ((2 ^ a : ℕ) : ℤ_[2]) = (2 : ℤ_[2]) ^ a := by simp
  rw [← hpow, Nat.cast_smul_eq_nsmul]

/-- Bounded primary torsion cannot be infinitely divisible in the point group. -/
theorem point_torsion_mem_powSub_eq_zero (P : Type*) [AddCommGroup P] (e a : ℕ)
    (hbound : ∀ (k : ℕ) (x : P), (2 ^ k : ℕ) • x = 0 → (2 ^ e : ℕ) • x = 0)
    (x : P) (hx : (2 ^ a : ℕ) • x = 0) (hmem : x ∈ pointPowSub P (e + a)) : x = 0 := by
  obtain ⟨y, hy⟩ := (mem_pointPowSub P (e + a) x).1 hmem
  have hy' : (2 ^ (e + a + a) : ℕ) • y = 0 := by
    rw [pow_add, mul_nsmul, hy, hx]
  have hy0 := hbound (e + a + a) y hy'
  rw [← hy, pow_add, mul_nsmul, hy0, nsmul_zero]

/-- On torsion, one sufficiently deep actual projection detects the completion. -/
theorem completion_torsion_detect (P : Type*) [AddCommGroup P] (e a : ℕ)
    (hbound : ∀ (k : ℕ) (x : P), (2 ^ k : ℕ) • x = 0 → (2 ^ e : ℕ) • x = 0)
    (x : PointCompletion P) (hx : (2 ^ a : ℕ) • x = 0) (heval : x.val (e + a) = 0) : x = 0 := by
  apply AdicCompletion.ext
  intro n
  obtain ⟨s, hs⟩ := (pointPowSub P (n + e + a)).mkQ_surjective (x.val (n + e + a))
  have hslo : (Submodule.Quotient.mk s : P ⧸ pointPowSub P (e + a)) = x.val (e + a) := by
    have h := x.property (show e + a ≤ n + e + a by omega)
    rw [← hs] at h
    exact h
  have hs0 : s ∈ pointPowSub P (e + a) :=
    (Submodule.Quotient.mk_eq_zero _).1 (hslo.trans heval)
  obtain ⟨r, hr⟩ := (mem_pointPowSub P (e + a) s).1 hs0
  have hsa : (Submodule.Quotient.mk ((2 ^ a : ℕ) • s) :
      P ⧸ pointPowSub P (n + e + a)) = 0 := by
    have h := congrArg (fun y : PointCompletion P => y.val (n + e + a)) hx
    change (2 ^ a : ℕ) • x.val (n + e + a) = 0 at h
    rw [← hs] at h
    exact h
  obtain ⟨t, ht⟩ := (mem_pointPowSub P (n + e + a) ((2 ^ a : ℕ) • s)).1
    ((Submodule.Quotient.mk_eq_zero _).1 hsa)
  have hrel : (2 ^ (e + a) : ℕ) • ((2 ^ a : ℕ) • r - (2 ^ n : ℕ) • t) = 0 := by
    rw [nsmul_sub, smul_comm (2 ^ (e + a) : ℕ) (2 ^ a : ℕ), hr]
    have hm : (2 ^ (e + a) : ℕ) • ((2 ^ n : ℕ) • t) = (2 ^ (n + e + a) : ℕ) • t := by
      rw [← mul_nsmul', ← pow_add, show e + a + n = n + e + a by omega]
    rw [hm, ht, sub_self]
  have heq : (2 ^ e : ℕ) • ((2 ^ a : ℕ) • r) = (2 ^ e : ℕ) • ((2 ^ n : ℕ) • t) :=
    sub_eq_zero.mp (by simpa only [nsmul_sub] using hbound (e + a) _ hrel)
  have htn : (2 ^ n : ℕ) • ((2 ^ e : ℕ) • t) = s := by
    calc
      (2 ^ n : ℕ) • ((2 ^ e : ℕ) • t) = (2 ^ e : ℕ) • ((2 ^ n : ℕ) • t) := smul_comm _ _ _
      _ = (2 ^ e : ℕ) • ((2 ^ a : ℕ) • r) := heq.symm
      _ = s := by rw [← mul_nsmul', ← pow_add, hr]
  have hsn : (Submodule.Quotient.mk s : P ⧸ pointPowSub P n) = x.val n := by
    have h := x.property (show n ≤ n + e + a by omega)
    rw [← hs] at h
    exact h
  change x.val n = 0
  rw [← hsn, Submodule.Quotient.mk_eq_zero]
  exact (mem_pointPowSub P n s).2 ⟨(2 ^ e : ℕ) • t, htn⟩

/-- The actual map carrying rational torsion into the completion. -/
def torsionToCompletion (P : Type*) [AddCommGroup P] (a : ℕ) :
    AddSubgroup.torsionBy P (2 ^ a : ℕ) →+
      torsionN ((2 : ℤ_[2]) ^ a) (PointCompletion P) where
  toFun t := ⟨completePoint P t, by
    change (2 : ℤ_[2]) ^ a • completePoint P t = 0
    rw [twoPower_smul, ← map_nsmul]
    exact congrArg (completePoint P) (AddSubgroup.torsionBy.nsmul_iff.mp t.2)⟩
  map_zero' := Subtype.ext (map_zero (completePoint P))
  map_add' t u := Subtype.ext (map_add (completePoint P) (t : P) (u : P))

/-- The torsion inclusion is the actual completion map on underlying points. -/
theorem torsionToCompletion_apply (P : Type*) [AddCommGroup P] (a : ℕ)
    (t : AddSubgroup.torsionBy P (2 ^ a : ℕ)) :
    (torsionToCompletion P a t : PointCompletion P) = completePoint P t := rfl

/-- Bounded primary torsion is retained injectively by completion. -/
theorem torsionToCompletion_injective (P : Type*) [AddCommGroup P] (e a : ℕ)
    (hbound : ∀ (k : ℕ) (x : P), (2 ^ k : ℕ) • x = 0 → (2 ^ e : ℕ) • x = 0) :
    Function.Injective (torsionToCompletion P a) := by
  intro t u h
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hoff : completePoint P ((t : P) - u) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val h)
  have hmem : (t : P) - u ∈ pointPowSub P (e + a) := by
    have h := congrArg (fun x : PointCompletion P => x.val (e + a)) hoff
    exact (Submodule.Quotient.mk_eq_zero _).1 h
  exact point_torsion_mem_powSub_eq_zero P e a hbound _ (by
    rw [nsmul_sub, AddSubgroup.torsionBy.nsmul_iff.mp t.2,
      AddSubgroup.torsionBy.nsmul_iff.mp u.2, sub_zero]) hmem

/-- Every torsion element of the actual completion lifts to rational torsion. -/
theorem torsionToCompletion_surjective (P : Type*) [AddCommGroup P] (e a : ℕ)
    (hbound : ∀ (k : ℕ) (x : P), (2 ^ k : ℕ) • x = 0 → (2 ^ e : ℕ) • x = 0) :
    Function.Surjective (torsionToCompletion P a) := by
  rintro ⟨x, hx⟩
  have hx0 : (2 ^ a : ℕ) • x = 0 := by
    change (2 : ℤ_[2]) ^ a • x = 0 at hx
    rwa [twoPower_smul] at hx
  obtain ⟨s, hs⟩ := (pointPowSub P (e + a + a)).mkQ_surjective (x.val (e + a + a))
  have hsa : (Submodule.Quotient.mk ((2 ^ a : ℕ) • s) :
      P ⧸ pointPowSub P (e + a + a)) = 0 := by
    have h := congrArg (fun y : PointCompletion P => y.val (e + a + a)) hx0
    change (2 ^ a : ℕ) • x.val (e + a + a) = 0 at h
    rw [← hs] at h
    exact h
  obtain ⟨q, hq⟩ := (mem_pointPowSub P (e + a + a) ((2 ^ a : ℕ) • s)).1
    ((Submodule.Quotient.mk_eq_zero _).1 hsa)
  let t : P := s - (2 ^ (e + a) : ℕ) • q
  have ht0 : (2 ^ a : ℕ) • t = 0 := by
    dsimp [t]
    rw [nsmul_sub, ← mul_nsmul', ← pow_add]
    have he : a + (e + a) = e + a + a := by omega
    rw [he, hq, sub_self]
  have hslo : (Submodule.Quotient.mk s : P ⧸ pointPowSub P (e + a)) = x.val (e + a) := by
    have h := x.property (show e + a ≤ e + a + a by omega)
    rw [← hs] at h
    exact h
  have hte : (completePoint P t).val (e + a) = x.val (e + a) := by
    change (Submodule.Quotient.mk t : P ⧸ pointPowSub P (e + a)) = x.val (e + a)
    calc
      Submodule.Quotient.mk t = Submodule.Quotient.mk s := by
        rw [Submodule.Quotient.eq]
        apply (mem_pointPowSub P (e + a) (t - s)).2
        refine ⟨-q, ?_⟩
        dsimp [t]
        rw [smul_neg]
        abel
      _ = x.val (e + a) := hslo
  have hz : x - completePoint P t = 0 :=
    completion_torsion_detect P e a hbound _ (by
      rw [nsmul_sub, hx0, ← map_nsmul, ht0, map_zero, sub_self]) (by
      change x.val (e + a) - (completePoint P t).val (e + a) = 0
      rw [hte, sub_self])
  exact ⟨⟨t, AddSubgroup.torsionBy.nsmul_iff.mpr ht0⟩,
    Subtype.ext (sub_eq_zero.mp hz).symm⟩

/-- The actual completion torsion is rational torsion, with its inclusion fixed. -/
def completionTorsionEquiv (P : Type*) [AddCommGroup P] (e a : ℕ)
    (hbound : ∀ (k : ℕ) (x : P), (2 ^ k : ℕ) • x = 0 → (2 ^ e : ℕ) • x = 0) :
    torsionN ((2 : ℤ_[2]) ^ a) (PointCompletion P) ≃+
      AddSubgroup.torsionBy P (2 ^ a : ℕ) :=
  (AddEquiv.ofBijective (torsionToCompletion P a)
    ⟨torsionToCompletion_injective P e a hbound,
      torsionToCompletion_surjective P e a hbound⟩).symm

/-- The inverse torsion dictionary sends a rational point to its completion. -/
theorem completionTorsionEquiv_symm_apply (P : Type*) [AddCommGroup P] (e a : ℕ)
    (hbound : ∀ (k : ℕ) (x : P), (2 ^ k : ℕ) • x = 0 → (2 ^ e : ℕ) • x = 0)
    (t : AddSubgroup.torsionBy P (2 ^ a : ℕ)) :
    (completionTorsionEquiv P e a hbound).symm t = torsionToCompletion P a t := rfl

/-- A finite-index subgroup without two-torsion has bounded primary torsion. -/
theorem boundedTwoPrimary_of_finiteIndex (P : Type*) [AddCommGroup P] (U : AddSubgroup P)
    [U.FiniteIndex] (hU : ∀ x ∈ U, (2 : ℕ) • x = 0 → x = 0) :
    ∃ e : ℕ, ∀ (k : ℕ) (x : P), (2 ^ k : ℕ) • x = 0 → (2 ^ e : ℕ) • x = 0 := by
  have hUpow : ∀ (k : ℕ) (x : P), x ∈ U → (2 ^ k : ℕ) • x = 0 → x = 0 := by
    intro k
    induction k with
    | zero => intro x _ hx; simpa only [pow_zero, one_nsmul] using hx
    | succ k ih =>
      intro x hxu hx
      have h2 : (2 : ℕ) • ((2 ^ k : ℕ) • x) = 0 := by
        simpa only [pow_succ, mul_nsmul] using hx
      exact ih x hxu (hU _ (U.nsmul_mem hxu _) h2)
  obtain ⟨e, u, hu, hindex⟩ := Nat.exists_eq_two_pow_mul_odd
    (inferInstance : U.FiniteIndex).index_ne_zero
  refine ⟨e, fun k x hx => ?_⟩
  have him : U.index • x = 0 := hUpow k _ (U.nsmul_index_mem x) (by
    rw [smul_comm (2 ^ k : ℕ) U.index, hx, nsmul_zero])
  have huy : u • ((2 ^ e : ℕ) • x) = 0 := by
    simpa only [hindex, mul_nsmul] using him
  have hky : (2 ^ k : ℕ) • ((2 ^ e : ℕ) • x) = 0 := by
    rw [smul_comm (2 ^ k : ℕ) (2 ^ e : ℕ), hx, nsmul_zero]
  have hcop : IsCoprime (u : ℤ) ((2 ^ k : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_two_right.mpr hu).pow_right k)
  obtain ⟨r, s, hrs⟩ := hcop
  calc
    (2 ^ e : ℕ) • x = (1 : ℤ) • ((2 ^ e : ℕ) • x) := by rw [one_smul]
    _ = (r * (u : ℤ) + s * ((2 ^ k : ℕ) : ℤ)) • ((2 ^ e : ℕ) • x) := by rw [hrs]
    _ = 0 := by
      rw [add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul,
        huy, hky, smul_zero, smul_zero, zero_add]

section ActualLocalPoints

open NumberField IsDedekindDomain

/-- The primary torsion of an integral elliptic model over an actual completion is bounded. -/
theorem boundedTwoPrimary_integral_local (K : Type) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) [hdec : DecidableEq (w.adicCompletion K)]
    (C : WeierstrassCurve (w.adicCompletionIntegers K))
    [(C.baseChange (w.adicCompletion K)).IsElliptic] :
    ∃ e : ℕ, ∀ (k : ℕ) (p : (C.baseChange (w.adicCompletion K)).toAffine.Point),
      (2 ^ k : ℕ) • p = 0 → (2 ^ e : ℕ) • p = 0 := by
  have hd : hdec = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst hdec
  classical
  by_cases h2 : (2 : 𝓞 K) ∈ w.asIdeal
  · have hOver : w.asIdeal.LiesOver
        (ZInQ.Contrib.CloudB3RC53.RankCounts.vP ZInQ.Contrib.CloudB3RC53.Mattuck.two).asIdeal := by
      rw [ZInQ.Contrib.CloudB3RC53.RankCounts.vP_asIdeal]
      change w.asIdeal.LiesOver (Ideal.span {(2 : ℤ)})
      exact (Ideal.liesOver_span_iff (inferInstance : w.asIdeal.IsPrime).ne_top
        (Nat.prime_iff_prime_int.mp Nat.prime_two)).mpr (by simpa using h2)
    letI := hOver
    letI := ZInQ.Contrib.CloudB3RC53.Mattuck.finiteIndex_latticeU K w C
    exact boundedTwoPrimary_of_finiteIndex _ (ZInQ.Contrib.CloudB3RC53.Mattuck.latticeU K w C)
      (ZInQ.Contrib.CloudB3RC53.Mattuck.latticeU_noTwoTorsion K w C)
  · letI := ZInQ.Contrib.CloudB3RC53.Mattuck.finiteIndex_kerReduction w C
    have hb := C.nsmul_kerReduction_bijective w (n := 2) (by exact_mod_cast h2)
    apply boundedTwoPrimary_of_finiteIndex _ (C.kerReduction w)
    intro p hp hpp
    have h : (2 : ℕ) • (⟨p, hp⟩ : C.kerReduction w) = (2 : ℕ) • (0 : C.kerReduction w) :=
      Subtype.ext (by simpa using hpp)
    exact congrArg Subtype.val (hb.1 h)

/-- Boundedness of primary torsion holds for every elliptic curve over the actual completion. -/
theorem boundedTwoPrimary_local (K : Type) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]
    (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic] :
    ∃ e : ℕ, ∀ (k : ℕ) (p : B.toAffine.Point),
      (2 ^ k : ℕ) • p = 0 → (2 ^ e : ℕ) • p = 0 := by
  classical
  obtain ⟨D, hD⟩ := WeierstrassCurve.exists_smul_isIntegral (w.adicCompletionIntegers K) B
  letI : WeierstrassCurve.IsIntegral (w.adicCompletionIntegers K) (D • B) := hD
  let C : WeierstrassCurve (w.adicCompletionIntegers K) :=
    (D • B).integralModel (w.adicCompletionIntegers K)
  have hC : C.baseChange (w.adicCompletion K) = D • B :=
    WeierstrassCurve.baseChange_integralModel_eq (w.adicCompletionIntegers K) (D • B)
  letI : (C.baseChange (w.adicCompletion K)).IsElliptic :=
    hC.symm ▸ (inferInstance : (D • B).IsElliptic)
  obtain ⟨e, he⟩ := boundedTwoPrimary_integral_local K w C
  let φ : (C.baseChange (w.adicCompletion K)).toAffine.Point ≃+ B.toAffine.Point :=
    (AddEquiv.cast (M := fun V : WeierstrassCurve (w.adicCompletion K) => V.toAffine.Point) hC).trans
      (WeierstrassCurve.Affine.Point.addEquivVariableChange B D)
  refine ⟨e, fun k p hp => ?_⟩
  have hq : (2 ^ k : ℕ) • φ.symm p = 0 := φ.injective (by
    rw [map_nsmul, φ.apply_symm_apply, hp, map_zero])
  simpa only [map_nsmul, φ.apply_symm_apply, map_zero] using congrArg φ (he k (φ.symm p) hq)

/-- Every finite primary torsion level of the actual elliptic point completion is rational. -/
def etaPowerZero (K : Type) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]
    (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic] (a : ℕ) :
    torsionN ((2 : ℤ_[2]) ^ a) (PointCompletion B.toAffine.Point) ≃+
      AddSubgroup.torsionBy B.toAffine.Point (2 ^ a : ℕ) :=
  let h := boundedTwoPrimary_local K w B
  completionTorsionEquiv B.toAffine.Point h.choose a h.choose_spec

/-- The degree-zero identification for the actual elliptic point completion. -/
def etaZero (K : Type) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]
    (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic] :
    torsionN (2 : ℤ_[2]) (PointCompletion B.toAffine.Point) ≃+
      AddSubgroup.torsionBy B.toAffine.Point 2 :=
  etaPowerZero K w B 1

/-- The actual degree-zero inverse is the genuine rational-torsion inclusion into completion. -/
theorem etaZero_symm_apply (K : Type) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]
    (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]
    (t : AddSubgroup.torsionBy B.toAffine.Point 2) :
    (etaZero K w B).symm t = torsionToCompletion B.toAffine.Point 1 t := rfl

/-- Rational torsion survives unchanged under the actual completion identification. -/
theorem etaZero_torsionToCompletion (K : Type) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]
    (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]
    (t : AddSubgroup.torsionBy B.toAffine.Point 2) :
    etaZero K w B (torsionToCompletion B.toAffine.Point 1 t) = t :=
  (etaZero K w B).apply_symm_apply t

/-- The completion identification followed by the canonical fixed-torsion map. -/
def completionTorsionToH0 (K : Type) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]
    (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic] :
    torsionN (2 : ℤ_[2]) (PointCompletion B.toAffine.Point) ≃+
      TauCeti.ContCohomology.H0 (TauCeti.AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) :=
  (etaZero K w B).trans (DegreeZero.torsionH0Equiv B 2)

/-- The completion-to-invariants dictionary is the actual base-field coefficient map. -/
theorem completionTorsionToH0_torsionToCompletion (K : Type) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]
    (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]
    (t : AddSubgroup.torsionBy B.toAffine.Point 2) :
    (completionTorsionToH0 K w B (torsionToCompletion B.toAffine.Point 1 t) : B.TorsionCoeff 2) =
      B.baseTorsionCoeff 2 t := by
  exact congrArg (B.baseTorsionCoeff 2) (etaZero_torsionToCompletion K w B t)

/-- Both identifications specialize to the genuine local quadratic twist. -/
def localTwistEtaZero {K : Type} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic] (h : K) (hh : h ≠ 0)
    (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)] :
    torsionN (2 : ℤ_[2])
        (PointCompletion (ZInQ.Manuscript.RC.KummerMaps.localTwist W h w).toAffine.Point) ≃+
      AddSubgroup.torsionBy (ZInQ.Manuscript.RC.KummerMaps.localTwist W h w).toAffine.Point 2 :=
  haveI := ZInQ.Manuscript.RC.KummerMaps.isElliptic_localTwist W hh w
  etaZero K w (ZInQ.Manuscript.RC.KummerMaps.localTwist W h w)

end ActualLocalPoints

/-- The ideal defining the scalar-adic topology on the completed point module. -/
def scalarTwoIdeal : Ideal ℤ_[2] := Ideal.span {(2 : ℤ_[2])}

/-- The completed point module is genuinely two-adically complete. -/
theorem pointCompletion_adicComplete (P : Type*) [AddCommGroup P] :
    IsAdicComplete scalarTwoIdeal (PointCompletion P) := by
  haveI : IsAdicComplete twoIdeal (PointCompletion P) :=
    AdicCompletion.isAdicComplete (M := P) twoIdeal_fg
  have hI : twoIdeal.map (algebraMap ℤ ℤ_[2]) = scalarTwoIdeal := by
    simp [twoIdeal, scalarTwoIdeal, Ideal.map_span]
  rw [← hI]
  exact (IsAdicComplete.map_algebraMap_iff twoIdeal (PointCompletion P)).mpr inferInstance

/-- Scalar two-adic integers are complete for the defining scalar ideal. -/
theorem scalar_adicComplete : IsAdicComplete scalarTwoIdeal ℤ_[2] := by
  simpa [scalarTwoIdeal, PadicInt.maximalIdeal_eq_span_p] using
    (inferInstance : IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[2]) ℤ_[2])

/-- A finite free scalar module is precomplete, with its genuine completion map. -/
theorem scalarPi_precomplete (n : ℕ) : IsPrecomplete scalarTwoIdeal (Fin n → ℤ_[2]) := by
  haveI : IsAdicComplete scalarTwoIdeal ℤ_[2] := scalar_adicComplete
  apply (AdicCompletion.of_surjective_iff).mp
  intro x
  let y : Fin n → ℤ_[2] := fun i => (AdicCompletion.ofLinearEquiv scalarTwoIdeal ℤ_[2]).symm
    (AdicCompletion.piEquivFin scalarTwoIdeal n x i)
  refine ⟨y, ?_⟩
  apply (AdicCompletion.piEquivFin scalarTwoIdeal n).injective
  funext i
  change AdicCompletion.map scalarTwoIdeal (LinearMap.proj i)
    (AdicCompletion.of scalarTwoIdeal (Fin n → ℤ_[2]) y) = _
  rw [AdicCompletion.map_of]
  exact AdicCompletion.of_ofLinearEquiv_symm scalarTwoIdeal _

/-- The scalar ideal image is precisely multiplication by two. -/
theorem scalarTwoIdeal_smul_top (P : Type*) [AddCommGroup P] [Module ℤ_[2] P] :
    scalarTwoIdeal • (⊤ : Submodule ℤ_[2] P) = nSub (2 : ℤ_[2]) P := by
  ext x
  rw [scalarTwoIdeal, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists, mem_nSub]
  simp only [Submodule.mem_top, true_and]

/-- Finite reduction and actual completeness give finite generation of the completed point module. -/
theorem pointCompletion_finite (P : Type*) [AddCommGroup P]
    [Finite (TateDualityData.pointMod (P := P) 2)] : Module.Finite ℤ_[2] (PointCompletion P) := by
  classical
  haveI : Finite (PointCompletion P ⧸ nSub (2 : ℤ_[2]) (PointCompletion P)) :=
    Finite.of_equiv _ (completionQuotientEquiv P 1).symm.toEquiv
  haveI : Finite (PointCompletion P ⧸ scalarTwoIdeal • (⊤ : Submodule ℤ_[2] (PointCompletion P))) := by
    rw [scalarTwoIdeal_smul_top]
    infer_instance
  let Q := PointCompletion P ⧸ scalarTwoIdeal • (⊤ : Submodule ℤ_[2] (PointCompletion P))
  haveI : Module.Finite ℤ_[2] Q := inferInstance
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := ℤ_[2]) (M := Q)
  choose s hs using fun i : Fin n =>
    (scalarTwoIdeal • (⊤ : Submodule ℤ_[2] (PointCompletion P))).mkQ_surjective (v i)
  let f : (Fin n → ℤ_[2]) →ₗ[ℤ_[2]] PointCompletion P := Fintype.linearCombination ℤ_[2] s
  have hf : (scalarTwoIdeal • (⊤ : Submodule ℤ_[2] (PointCompletion P))).mkQ ∘ₗ f =
      Fintype.linearCombination ℤ_[2] v := by
    ext x
    simp [f, Fintype.linearCombination_apply, map_sum, hs]
  have hsurj : Function.Surjective
      ((scalarTwoIdeal • (⊤ : Submodule ℤ_[2] (PointCompletion P))).mkQ ∘ₗ f) := by
    rw [hf, ← LinearMap.range_eq_top, Fintype.range_linearCombination, hv]
  haveI := pointCompletion_adicComplete P
  haveI := scalarPi_precomplete n
  exact Module.Finite.of_surjective f (surjective_of_mkQ_comp_surjective hsurj)

/-- A finite free presentation of the actual completion, including its torsion relations. -/
structure FinitePointPresentation (P : Type*) [AddCommGroup P] where
  rankZero : ℕ
  rankOne : ℕ
  f : (Fin rankOne → ℤ_[2]) →ₗ[ℤ_[2]] (Fin rankZero → ℤ_[2])
  g : (Fin rankZero → ℤ_[2]) →ₗ[ℤ_[2]] PointCompletion P
  complex : g.comp f = 0
  injective : Function.Injective f
  surjective : Function.Surjective g
  exact : ∀ y, g y = 0 → ∃ x, f x = y

/-- The actual completed point module has a finite free presentation. -/
theorem finitePointPresentation_nonempty (P : Type*) [AddCommGroup P]
    [Finite (TateDualityData.pointMod (P := P) 2)] : Nonempty (FinitePointPresentation P) := by
  classical
  haveI := pointCompletion_finite P
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ_[2]) (M := PointCompletion P)
  let g : (Fin n → ℤ_[2]) →ₗ[ℤ_[2]] PointCompletion P := Fintype.linearCombination ℤ_[2] s
  have hg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hs]
  obtain ⟨m, b⟩ := (LinearMap.ker g).basisOfPid (Pi.basisFun ℤ_[2] (Fin n))
  let f : (Fin m → ℤ_[2]) →ₗ[ℤ_[2]] (Fin n → ℤ_[2]) :=
    (LinearMap.ker g).subtype.comp b.equivFun.symm.toLinearMap
  refine ⟨⟨n, m, f, g, ?_, ?_, hg, ?_⟩⟩
  · apply LinearMap.ext
    intro x
    exact (b.equivFun.symm x).2
  · exact (LinearMap.ker g).subtype_injective.comp b.equivFun.symm.injective
  · intro y hy
    refine ⟨b.equivFun ⟨y, hy⟩, ?_⟩
    change ((b.equivFun.symm (b.equivFun ⟨y, hy⟩) : LinearMap.ker g) : Fin n → ℤ_[2]) = y
    rw [b.equivFun.symm_apply_apply]

/-- No power of two is a zero divisor on the free degree-one term of the presentation. -/
theorem finitePi_twoPower_regular (n a : ℕ) : IsSMulRegular (Fin n → ℤ_[2]) ((2 : ℤ_[2]) ^ a) := by
  intro x y h
  funext i
  have hi := congrFun h i
  change (2 : ℤ_[2]) ^ a * x i = (2 : ℤ_[2]) ^ a * y i at hi
  exact mul_left_cancel₀ (pow_ne_zero a (by norm_num)) hi

/-- The standard module quotient and the point quotient have the same multiplication image. -/
def modNTwoPointEquiv (P : Type*) [AddCommGroup P] :
    ModN P 2 ≃+ TateDualityData.pointMod (P := P) 2 :=
  QuotientAddGroup.quotientAddEquivOfEq
    (ZInQ.Contrib.CloudB3RC53.Mattuck.toAddSubgroup_range_lsmul (A := P))

/-- Rational two-torsion is finite for an elliptic curve over a field. -/
theorem finite_submoduleTwoTorsion {F : Type} [Field F] [DecidableEq F]
    (B : WeierstrassCurve F) [B.IsElliptic] :
    Finite (Submodule.torsionBy ℤ B.toAffine.Point 2) := by
  haveI : Finite (AddSubgroup.torsionBy B.toAffine.Point (2 : ℤ)) :=
    WeierstrassCurve.finite_torsionBy B (by norm_num)
  let f : Submodule.torsionBy ℤ B.toAffine.Point 2 → AddSubgroup.torsionBy B.toAffine.Point (2 : ℤ) :=
    fun t => ⟨t, by
      change (2 : ℤ) • (t : B.toAffine.Point) = 0
      exact (Submodule.mem_torsionBy_iff _ _).mp t.2⟩
  exact Finite.of_injective f (fun a b h => Subtype.ext (congrArg Subtype.val h))

section FiniteActualLocalPoints

open NumberField IsDedekindDomain

/-- An actual integral local elliptic model has finite quotient by doubling. -/
theorem finite_pointModTwo_integral_local (K : Type) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) [hdec : DecidableEq (w.adicCompletion K)]
    (C : WeierstrassCurve (w.adicCompletionIntegers K))
    [(C.baseChange (w.adicCompletion K)).IsElliptic] :
    Finite (TateDualityData.pointMod (P := (C.baseChange (w.adicCompletion K)).toAffine.Point) 2) := by
  have hd : hdec = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst hdec
  classical
  haveI := finite_submoduleTwoTorsion (C.baseChange (w.adicCompletion K))
  have htpos : 0 < Nat.card (Submodule.torsionBy ℤ (C.baseChange (w.adicCompletion K)).toAffine.Point 2) :=
    Nat.card_pos
  have hcard : Nat.card (ModN (C.baseChange (w.adicCompletion K)).toAffine.Point 2) ≠ 0 := by
    by_cases h2 : (2 : 𝓞 K) ∈ w.asIdeal
    · have hOver : w.asIdeal.LiesOver
          (ZInQ.Contrib.CloudB3RC53.RankCounts.vP ZInQ.Contrib.CloudB3RC53.Mattuck.two).asIdeal := by
        rw [ZInQ.Contrib.CloudB3RC53.RankCounts.vP_asIdeal]
        change w.asIdeal.LiesOver (Ideal.span {(2 : ℤ)})
        exact (Ideal.liesOver_span_iff (inferInstance : w.asIdeal.IsPrime).ne_top
          (Nat.prime_iff_prime_int.mp Nat.prime_two)).mpr (by simpa using h2)
      letI := hOver
      letI := ZInQ.Contrib.CloudB3RC53.Mattuck.finiteIndex_latticeU K w C
      letI := ZInQ.Contrib.CloudB3RC53.RankCounts.qpAlg K ZInQ.Contrib.CloudB3RC53.Mattuck.two w
      have hc := ZInQ.Contrib.CloudB3RC53.Mattuck.card_modN_two_of_lattice
        (ZInQ.Contrib.CloudB3RC53.Mattuck.latticeU K w C)
        (ZInQ.Contrib.CloudB3RC53.Mattuck.latticeU_noTwoTorsion K w C)
        (ZInQ.Contrib.CloudB3RC53.Mattuck.card_modN_latticeU K w C)
      rw [hc]
      exact mul_ne_zero htpos.ne' (pow_ne_zero _ (by decide))
    · rw [ZInQ.Contrib.CloudB3RC53.Mattuck.card_modN_two_eq_card_twoTorsion w C h2]
      exact htpos.ne'
  haveI : Finite (ModN (C.baseChange (w.adicCompletion K)).toAffine.Point 2) :=
    Nat.finite_of_card_ne_zero hcard
  exact Finite.of_equiv _ (modNTwoPointEquiv (C.baseChange (w.adicCompletion K)).toAffine.Point).toEquiv

/-- The quotient by doubling is finite for every elliptic curve over the actual completion. -/
theorem finite_pointModTwo_local (K : Type) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]
    (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic] :
    Finite (TateDualityData.pointMod (P := B.toAffine.Point) 2) := by
  classical
  obtain ⟨D, hD⟩ := WeierstrassCurve.exists_smul_isIntegral (w.adicCompletionIntegers K) B
  letI : WeierstrassCurve.IsIntegral (w.adicCompletionIntegers K) (D • B) := hD
  let C : WeierstrassCurve (w.adicCompletionIntegers K) :=
    (D • B).integralModel (w.adicCompletionIntegers K)
  have hC : C.baseChange (w.adicCompletion K) = D • B :=
    WeierstrassCurve.baseChange_integralModel_eq (w.adicCompletionIntegers K) (D • B)
  letI : (C.baseChange (w.adicCompletion K)).IsElliptic :=
    hC.symm ▸ (inferInstance : (D • B).IsElliptic)
  haveI := finite_pointModTwo_integral_local K w C
  let φ : (C.baseChange (w.adicCompletion K)).toAffine.Point ≃+ B.toAffine.Point :=
    (AddEquiv.cast (M := fun V : WeierstrassCurve (w.adicCompletion K) => V.toAffine.Point) hC).trans
      (WeierstrassCurve.Affine.Point.addEquivVariableChange B D)
  apply Nat.finite_of_card_ne_zero
  rw [← Nat.card_congr (modNTwoPointEquiv B.toAffine.Point).toEquiv,
    ← ZInQ.Contrib.CloudB3RC53.Mattuck.natCard_modN_two_congr φ,
    Nat.card_congr (modNTwoPointEquiv (C.baseChange (w.adicCompletion K)).toAffine.Point).toEquiv]
  exact Nat.card_pos.ne'

/-- The actual completed point module is finite over the two-adic integers. -/
theorem actualPointCompletion_finite (K : Type) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]
    (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic] :
    Module.Finite ℤ_[2] (PointCompletion B.toAffine.Point) :=
  haveI := finite_pointModTwo_local K w B
  pointCompletion_finite B.toAffine.Point

/-- A selected finite free presentation of the genuine point completion. -/
def actualLocalPresentation (K : Type) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]
    (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic] :
    FinitePointPresentation B.toAffine.Point :=
  haveI := finite_pointModTwo_local K w B
  (finitePointPresentation_nonempty B.toAffine.Point).some

end FiniteActualLocalPoints

section ActualDerivedComparisons

open NumberField IsDedekindDomain TauCeti TauCeti.ContCohomology

variable (K : Type) [Field K] [NumberField K]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]
  (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]
  (I : FinitePointPresentation B.toAffine.Point)

/-- Degree zero of the actual free-presentation reduction, retaining all rational two-torsion. -/
def actualReductionH0Identification : reductionH0 I.f ≃+ AddSubgroup.torsionBy B.toAffine.Point 2 :=
  derivedH0Identification B I.f I.g I.complex I.injective I.surjective I.exact
    (finitePi_twoPower_regular I.rankZero 1) (etaZero K w B)

/-- Degree one of the actual free-presentation reduction is the actual point quotient. -/
def actualReductionH1Identification :
    reductionH1 I.f ≃+ TateDualityData.pointMod (P := B.toAffine.Point) 2 :=
  derivedH1Identification B I.f I.g I.complex I.surjective I.exact (etaOne B)

/-- The two perfect comparisons now use the actual completion and an actual finite free presentation.
The only arithmetic parameters are the existing local duality statements. -/
theorem actualDerived_modTwo_comparisons_of_print
    (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (h2 : IsUnit (2 : w.adicCompletion K)) :
    (∃ e : (H1 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) ⧸
        (B.kummerMap 2 h2).range) ≃+ (reductionH1 I.f →+ RationalCircle),
      ∀ (y : H1 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2))
        (r : reductionH1 I.f) (p : B.toAffine.Point),
        actualReductionH1Identification K w B I r = QuotientAddGroup.mk p →
        e (QuotientAddGroup.mk y) r = localTatePairing B 2 h2 (B.kummerMap 2 h2 p) y) ∧
    (∃ e : H2 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) ≃+
        (reductionH0 I.f →+ RationalCircle),
      ∀ (y : H2 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2))
        (r : reductionH0 I.f),
        e y r = localH2TorsionValue B 2 h2 y (actualReductionH0Identification K w B I r)) :=
  derived_modTwo_comparisons_of_print B I.f I.g hM hF h2 I.complex I.injective I.surjective
    I.exact (finitePi_twoPower_regular I.rankZero 1) (etaZero K w B) (etaOne B)

/-- The finite scalar Kummer condition retains the torsion of the actual completion in degree zero. -/
def genuineScalarH0 (a : ℕ) :
    torsionN ((2 : ℤ_[2]) ^ a) (PointCompletion B.toAffine.Point) ≃+
      (ZInQ.Manuscript.RC.CoefModules.kummerCondition (w.adicCompletion K) B (2 ^ a)).toCC.homology 0 :=
  (etaPowerZero K w B a).trans
    (ZInQ.Manuscript.RC.CoefModules.kummerH0AddEquiv (w.adicCompletion K) B (2 ^ a))

/-- The finite scalar Kummer condition has the actual completed point quotient in degree one. -/
def genuineScalarH1 (a : ℕ) :
    (PointCompletion B.toAffine.Point ⧸ nSub ((2 : ℤ_[2]) ^ a) (PointCompletion B.toAffine.Point)) ≃+
      (ZInQ.Manuscript.RC.CoefModules.kummerCondition (w.adicCompletion K) B (2 ^ a)).toCC.homology 1 :=
  (completionQuotientEquiv B.toAffine.Point a).trans
    (ZInQ.Manuscript.RC.CoefModules.kummerH1AddEquiv (w.adicCompletion K) B (2 ^ a))

/-- The degree-one dictionary uses the existing Kummer cocycle class of each actual point. -/
theorem genuineScalarH1_completePoint (a : ℕ) (p : B.toAffine.Point) :
    genuineScalarH1 K w B a (Submodule.Quotient.mk (completePoint B.toAffine.Point p)) =
      ZInQ.Manuscript.RC.CoefModules.kummerH1AddEquiv (w.adicCompletion K) B (2 ^ a)
        (QuotientAddGroup.mk p) := rfl

end ActualDerivedComparisons

section GenuineFiniteMaps

open scoped Classical
open NumberField IsDedekindDomain CategoryTheory
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α]
  (hFull : FullTorsion K S W (2 ^ i)) (v : Places K S)
  (hα : IsLocallyQuadAt i α (quadChar s hs hs0) v.1)

/-- The genuine finite Kummer map, factored through the actual completed point quotient.
The coefficient map and Kummer map are the existing quadratic-twist maps. -/
def genuineCompletionKummerMap :
    (PointCompletion (localTwist W h v.1).toAffine.Point ⧸
      nSub ((2 : ℤ_[2]) ^ i) (PointCompletion (localTwist W h v.1).toAffine.Point)) →+
      (locAt K S (Acoef i) (Mcoef K S W i α) v).toCC.homology 1 :=
  (QuotientAddGroup.lift (nsmulAddMonoidHom (α := (localTwist W h v.1).toAffine.Point) (2 ^ i)).range
    (actualKummerMap W i s hs hs0 α hFull v hα) (by
      rintro _ ⟨p, rfl⟩
      exact actualKummerMap_nsmul W i s hs hs0 α hFull v hα p)).comp
    (completionQuotientEquiv (localTwist W h v.1).toAffine.Point i).toAddMonoidHom

/-- On an actual point, the factored map is exactly the genuine Kummer map. -/
theorem genuineCompletionKummerMap_completePoint (p : (localTwist W h v.1).toAffine.Point) :
    genuineCompletionKummerMap W i s hs hs0 α hFull v hα
      (Submodule.Quotient.mk (completePoint (localTwist W h v.1).toAffine.Point p)) =
      actualKummerMap W i s hs hs0 α hFull v hα p := rfl

/-- Completion changes neither the genuine Kummer map nor its image. -/
theorem genuineCompletionKummerMap_range :
    Set.range (genuineCompletionKummerMap W i s hs hs0 α hFull v hα) =
      Set.range (actualKummerMap W i s hs hs0 α hFull v hα) := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨p, hp⟩ := QuotientAddGroup.mk'_surjective
      (nsmulAddMonoidHom (α := (localTwist W h v.1).toAffine.Point) (2 ^ i)).range
      (completionQuotientEquiv (localTwist W h v.1).toAffine.Point i q)
    have hq : q = Submodule.Quotient.mk (completePoint (localTwist W h v.1).toAffine.Point p) :=
      (completionQuotientEquiv (localTwist W h v.1).toAffine.Point i).injective (by
        rw [completionQuotientEquiv_completePoint]
        exact hp.symm)
    exact ⟨p, by rw [hq, genuineCompletionKummerMap_completePoint]⟩
  · rintro ⟨p, rfl⟩
    exact ⟨Submodule.Quotient.mk (completePoint (localTwist W h v.1).toAffine.Point p),
      genuineCompletionKummerMap_completePoint W i s hs hs0 α hFull v hα p⟩

/-- The existing actual local condition is the scalar span of the genuine completed-point Kummer image. -/
theorem actualKummerAt_range_eq_completionSpan :
    LinearMap.range (HomologicalComplex.homologyMap
      (GHom.toCC (actualKummerAt W i s hs hs0 α hFull v hα).i) 1).hom =
      Submodule.span (Acoef i) (Set.range (genuineCompletionKummerMap W i s hs hs0 α hFull v hα)) := by
  rw [actualKummerAt_range_eq_span, genuineCompletionKummerMap_range]

end GenuineFiniteMaps

end ZInQ.Contrib.RC53Assist.DerivedKummerActual

end

/-!
# Finite cochain identifications and the local invariant

The finite Kummer cocycles over the algebraic closure are identified with the
Kummer classes over the separable closure. The comparison preserves the actual
coefficient inclusions and the actual rational torsion. These are cochain and
cohomology identifications, not additional local-duality assumptions.
-/

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace

open TauCeti TauCeti.ContCohomology
open ZInQ.Contrib.CloudB3RC53.Duality
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.SelmerComplex

section Closure

variable (F : Type) [Field F] [CharZero F]

/-- In characteristic zero the canonical separable-closure inclusion is an isomorphism. -/
def closureEquiv : SeparableClosure F ≃ₐ[F] AlgebraicClosure F :=
  AlgEquiv.ofBijective (separableClosure F (AlgebraicClosure F)).val
    ⟨Subtype.val_injective, fun x => ⟨⟨x, Algebra.IsSeparable.isSeparable F x⟩, rfl⟩⟩

/-- The closure identification is the canonical inclusion, not a chosen unrelated embedding. -/
theorem closureEquiv_apply (x : SeparableClosure F) : closureEquiv F x = (x : AlgebraicClosure F) := rfl

variable [DecidableEq F] (B : WeierstrassCurve F)

/-- The actual point coefficients in the two closure descriptions. -/
def pointCoeffToAlg : B.PointCoeff ≃+ PtAlg F B :=
  B.pointCoeffEquiv.symm.trans
    ((WeierstrassCurve.Affine.Point.mapEquiv B (closureEquiv F)).trans (ptEquiv F B))

/-- The coefficient dictionary preserves the rational point inclusion. -/
theorem pointCoeffToAlg_base (p : B.toAffine.Point) :
    pointCoeffToAlg F B (B.basePointCoeff p) = basePt F B p := by
  classical
  rcases p with _ | ⟨x, y, hxy⟩
  · rw [← WeierstrassCurve.Affine.Point.zero_def, map_zero, map_zero, map_zero]
  · rw [B.basePointCoeff_some hxy, basePt_some (F := F) (B := B) hxy]
    change ptEquiv F B (WeierstrassCurve.Affine.Point.map (closureEquiv F).toAlgHom
      (.some (algebraMap F (SeparableClosure F) x) (algebraMap F (SeparableClosure F) y)
        ((B.toAffine.baseChange_nonsingular (Algebra.ofId F (SeparableClosure F)).injective x y).2 hxy))) = _
    erw [WeierstrassCurve.Affine.Point.map_some]
    congr 1
    exact (B.toAffine.baseChange_nonsingular
      (Algebra.ofId F (SeparableClosure F)).injective x y).2 hxy

/-- The closure comparison intertwines the actual absolute Galois actions. -/
theorem pointCoeffToAlg_smul (σ : Field.absoluteGaloisGroup F) (p : B.PointCoeff) :
    pointCoeffToAlg F B (absoluteGaloisGroupRestrictEquiv F σ • p) = σ • pointCoeffToAlg F B p := by
  classical
  obtain ⟨p, rfl⟩ := B.pointCoeffEquiv.surjective p
  rw [B.smul_pointCoeffEquiv]
  change ptEquiv F B (WeierstrassCurve.Affine.Point.map (closureEquiv F).toAlgHom
      (WeierstrassCurve.Affine.Point.map (absoluteGaloisGroupRestrictEquiv F σ).toAlgHom p)) =
    σ • ptEquiv F B (WeierstrassCurve.Affine.Point.map (closureEquiv F).toAlgHom p)
  rw [smul_ptEquiv, WeierstrassCurve.Affine.Point.map_map, WeierstrassCurve.Affine.Point.map_map]
  have hc : (closureEquiv F).toAlgHom.comp (absoluteGaloisGroupRestrictEquiv F σ).toAlgHom =
      σ.toAlgHom.comp (closureEquiv F).toAlgHom := by
    ext x
    exact coe_absoluteGaloisGroupRestrictEquiv_apply F σ x
  rw [hc]

/-- The dictionary restricted to the genuine finite torsion coefficient modules. -/
def torsionCoeffToAlg (n : ℕ) : B.TorsionCoeff n ≃+ TorsAlg F B n :=
  AddEquiv.torsionByCongr (pointCoeffToAlg F B) n

/-- Underlying torsion points are sent through the actual point coefficient dictionary. -/
theorem torsionCoeffToAlg_coe (n : ℕ) (t : B.TorsionCoeff n) :
    (torsionCoeffToAlg F B n t : PtAlg F B) = pointCoeffToAlg F B t := rfl

/-- The finite coefficient dictionary is Galois-equivariant. -/
theorem torsionCoeffToAlg_smul (n : ℕ) (σ : Field.absoluteGaloisGroup F) (t : B.TorsionCoeff n) :
    torsionCoeffToAlg F B n (absoluteGaloisGroupRestrictEquiv F σ • t) = σ • torsionCoeffToAlg F B n t := by
  apply Subtype.ext
  exact pointCoeffToAlg_smul F B σ t

/-- Rational finite torsion is carried to the genuine algebraic-closure torsion inclusion. -/
theorem torsionCoeffToAlg_base (n : ℕ) (t : AddSubgroup.torsionBy B.toAffine.Point n) :
    torsionCoeffToAlg F B n (B.baseTorsionCoeff n t) = baseTors F B n t := by
  apply Subtype.ext
  exact pointCoeffToAlg_base F B t

/-- The actual degree-one cohomology in the two closure descriptions. -/
def hOneToAlg (n : ℕ) :
    H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff n) ≃+
      H1 (Field.absoluteGaloisGroup F) (TorsAlg F B n) :=
  explicitMap1Equiv _ _ _ _ (absoluteGaloisGroupRestrictEquiv F) (torsionCoeffToAlg F B n)
    continuous_of_discreteTopology continuous_of_discreteTopology (torsionCoeffToAlg_smul F B n)

/-- The actual degree-two cohomology in the two closure descriptions. -/
def hTwoToAlg (n : ℕ) :
    H2 (AbsoluteGaloisGroup F) (B.TorsionCoeff n) ≃+
      H2 (Field.absoluteGaloisGroup F) (TorsAlg F B n) :=
  explicitMap2Equiv _ _ _ _ (absoluteGaloisGroupRestrictEquiv F) (torsionCoeffToAlg F B n)
    continuous_of_discreteTopology continuous_of_discreteTopology (torsionCoeffToAlg_smul F B n)

variable [B.IsElliptic] (n : ℕ) [NeZero n] (hn : IsUnit (n : F))

/-- The local duality Kummer class is exactly the class of the existing genuine finite Kummer cocycle. -/
theorem hOneToAlg_kummerMap (p : B.toAffine.Point) :
    hOneToAlg F B n (B.kummerMap n hn p) =
      kerToH1 (k := ℤ) (G := Field.absoluteGaloisGroup F) (M := TorsAlg F B n)
        ⟨kummerCocycle F B n p, kummerCocycle_isCocycle F B n p⟩ := by
  let q : B.PointCoeff := (pointCoeffToAlg F B).symm (divPt F B n p)
  have hq : n • q = B.basePointCoeff p := (pointCoeffToAlg F B).injective (by
    rw [map_nsmul, pointCoeffToAlg_base]
    change n • pointCoeffToAlg F B ((pointCoeffToAlg F B).symm (divPt F B n p)) = basePt F B p
    rw [(pointCoeffToAlg F B).apply_symm_apply, nsmul_divPt])
  rw [B.kummerMap_eq_H1pi hn hq]
  erw [hOneToAlg, explicitMap1Equiv_apply, explicitMap1_mk, kerToH1_apply]
  apply congrArg (H1pi (Field.absoluteGaloisGroup F) (TorsAlg F B n))
  apply Subtype.ext
  funext σ
  apply Subtype.ext
  change pointCoeffToAlg F B (absoluteGaloisGroupRestrictEquiv F σ • q - q) =
    σ • divPt F B n p - divPt F B n p
  rw [map_sub, pointCoeffToAlg_smul]
  change σ • pointCoeffToAlg F B ((pointCoeffToAlg F B).symm (divPt F B n p)) -
    pointCoeffToAlg F B ((pointCoeffToAlg F B).symm (divPt F B n p)) = _
  rw [(pointCoeffToAlg F B).apply_symm_apply]

end Closure

section KummerBrauer

open TauCeti.ClassFieldTheory

variable (F : Type) [Field F] (n : ℕ) (hn : IsUnit (n : F))

/-- The genuine finite roots-of-unity coefficient module is killed by its level. -/
theorem kummerCoeff_nsmul (t : KummerCoeff F n) : n • t = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change (t.toMul : (SeparableClosure F)ˣ) ^ n = 1
  exact (mem_rootsOfUnity n _).1 t.toMul.2

include hn in
/-- Hilbert ninety makes the actual finite-to-Brauer coefficient map injective. -/
theorem kummerToBr_injective : Function.Injective (kummerToBr (F := F) n) := by
  haveI := subsingleton_H1_unitsCoeff F
  apply (unitsRepH2Equiv F).injective.comp
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hm : x ∈ (TauCeti.kummerShortExact F n hn).explicitDelta1.range := by
    rw [(TauCeti.kummerShortExact F n hn).explicitLongExact_H2A,
      TauCeti.kummerShortExact_inclDistribMulActionHom]
    exact hx
  obtain ⟨y, hy⟩ := hm
  have hy0 : y = 0 := Subsingleton.elim _ _
  simpa only [hy0, map_zero] using hy.symm

include hn in
/-- The image of the genuine finite-to-Brauer map is exactly the indicated Brauer torsion. -/
theorem kummerToBr_range :
    (kummerToBr (F := F) n).range = AddSubgroup.torsionBy (Br F) n := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul,
      nsmul_H2_eq_zero (kummerCoeff_nsmul F n), map_zero]
  · intro hz
    let y : H2 (AbsoluteGaloisGroup F) (UnitsCoeff F) := (unitsRepH2Equiv F).symm z
    have hy : n • y = 0 := (unitsRepH2Equiv F).injective (by
      rw [map_nsmul, (unitsRepH2Equiv F).apply_symm_apply,
        AddSubgroup.torsionBy.nsmul_iff.mp hz, map_zero])
    have hp : explicitCoeff2 (AbsoluteGaloisGroup F) (UnitsCoeff F)
        (TauCeti.kummerShortExact F n hn).projDistribMulActionHom
        continuous_of_discreteTopology y = 0 := by
      rw [explicitCoeff2_eq_nsmul _ _ _ _ (fun t => unitsCoeffPow_eq_nsmul F n t)]
      exact hy
    have hm : y ∈ (explicitCoeff2 (AbsoluteGaloisGroup F) (KummerCoeff F n)
        (kummerCoeffInclHom F n) continuous_of_discreteTopology).range := by
      rw [← TauCeti.kummerShortExact_inclDistribMulActionHom F n hn,
        (TauCeti.kummerShortExact F n hn).explicitLongExact_H2B]
      exact hp
    obtain ⟨x, hx⟩ := hm
    refine ⟨x, ?_⟩
    change unitsRepH2Equiv F (explicitCoeff2 (AbsoluteGaloisGroup F) (KummerCoeff F n)
      (kummerCoeffInclHom F n) continuous_of_discreteTopology x) = z
    rw [hx, (unitsRepH2Equiv F).apply_symm_apply]

/-- The canonical coefficient inclusion identifies finite local cohomology with Brauer torsion. -/
def kummerBrauerEquiv :
    H2 (AbsoluteGaloisGroup F) (KummerCoeff F n) ≃+ AddSubgroup.torsionBy (Br F) n :=
  AddEquiv.ofBijective ((kummerToBr (F := F) n).codRestrict _ (fun x => by
    rw [← kummerToBr_range F n hn]
    exact ⟨x, rfl⟩)) ⟨
      fun x y h => kummerToBr_injective F n hn (congrArg Subtype.val h),
      fun z => by
        obtain ⟨x, hx⟩ : (z : Br F) ∈ (kummerToBr (F := F) n).range := by
          rw [kummerToBr_range F n hn]
          exact z.2
        exact ⟨x, Subtype.ext hx⟩⟩

/-- The finite Brauer dictionary is the actual coefficient inclusion on every class. -/
theorem kummerBrauerEquiv_coe (x : H2 (AbsoluteGaloisGroup F) (KummerCoeff F n)) :
    (kummerBrauerEquiv F n hn x : Br F) = kummerToBr n x := rfl

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [NeZero n]

/-- The genuine finite local invariant, with values in the correct finite residue ring. -/
def finiteInvariant : H2 (AbsoluteGaloisGroup F) (KummerCoeff F n) ≃+ ZMod n :=
  ((kummerBrauerEquiv F n hn).trans (AddEquiv.torsionByCongr (invMap F) n)).trans
    (circleTorsionEquiv n)

/-- The finite trace has the canonical inclusion into the rational circle as its normalization. -/
theorem finiteInvariant_toRat (x : H2 (AbsoluteGaloisGroup F) (KummerCoeff F n)) :
    ZMod.toRatAddCircle n (finiteInvariant F n hn x) = invMap F (kummerToBr n x) := by
  exact circleTorsionEquiv_toRat n _

/-- The actual normalized finite local invariant detects the entire degree-two class. -/
theorem finiteInvariant_eq_zero_iff (x : H2 (AbsoluteGaloisGroup F) (KummerCoeff F n)) :
    finiteInvariant F n hn x = 0 ↔ x = 0 :=
  (finiteInvariant F n hn).map_eq_zero_iff

end KummerBrauer

/-- The rational circle is injective as an integer module, by ordinary divisibility. -/
theorem rationalCircle_injective : Module.Injective ℤ RationalCircle := by
  haveI : Fact (0 < (1 : ℚ)) := ⟨by norm_num⟩
  exact (Module.Baer.of_divisible RationalCircle).injective

section FiniteCochainTrace

open TauCeti.ClassFieldTheory

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (n : ℕ) [NeZero n] (hn : IsUnit (n : F))

instance kummerCoeff_zmod_smulComm :
    SMulCommClass (AbsoluteGaloisGroup F) (ZMod n) (KummerCoeff F n) where
  smul_comm σ r t := ZMod.map_smul
    ({ toFun := fun u : KummerCoeff F n => σ • u
       map_zero' := smul_zero σ
       map_add' := smul_add σ } : KummerCoeff F n →+ KummerCoeff F n) r t

/-- The genuine continuous local roots-of-unity cochain complex at the given finite level. -/
abbrev finiteComplex := contCochains (ZMod n) (AbsoluteGaloisGroup F) (KummerCoeff F n)

/-- The canonical local invariant on all degree-two cycles of the genuine finite complex. -/
def cycleTraceCharacter :
    LinearMap.ker ((finiteComplex F n).d 2 3).hom →ₗ[ℤ] RationalCircle :=
  ((invMap F).toAddMonoidHom.comp ((kummerToBr (F := F) n).comp
    (kerToH2 (k := ZMod n) (G := AbsoluteGaloisGroup F) (M := KummerCoeff F n)))).toIntLinearMap

/-- A fixed extension of the actual cycle invariant to finite degree-two cochains.
The extension on noncycles is immaterial; its values on every cycle are specified. -/
def traceCharacterExtension :
    {t : (finiteComplex F n).X 2 →ₗ[ℤ] RationalCircle //
      t ∘ₗ (LinearMap.ker ((finiteComplex F n).d 2 3).hom).subtype.restrictScalars ℤ =
        cycleTraceCharacter F n} := by
  haveI := rationalCircle_injective
  exact ⟨(Module.Injective.extension_property ℤ RationalCircle _ _
    ((LinearMap.ker ((finiteComplex F n).d 2 3).hom).subtype.restrictScalars ℤ)
    (Submodule.subtype_injective _) (cycleTraceCharacter F n)).choose,
    (Module.Injective.extension_property ℤ RationalCircle _ _
      ((LinearMap.ker ((finiteComplex F n).d 2 3).hom).subtype.restrictScalars ℤ)
      (Submodule.subtype_injective _) (cycleTraceCharacter F n)).choose_spec⟩

/-- Every finite cochain is killed by the finite coefficient level. -/
theorem finiteCochain_nsmul (c : (finiteComplex F n).X 2) : n • c = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]

/-- The fixed cochain invariant has values in the finite torsion of the rational circle. -/
theorem traceCharacterExtension_torsion (c : (finiteComplex F n).X 2) :
    n • (traceCharacterExtension F n).val c = 0 := by
  rw [← map_nsmul, finiteCochain_nsmul, map_zero]

/-- The actual finite coefficient-valued local trace on the genuine cochain complex. -/
def finiteCochainTrace : (finiteComplex F n).X 2 →ₗ[ZMod n] ZMod n :=
  ((circleTorsionEquiv n).toAddMonoidHom.comp
    ((traceCharacterExtension F n).val.toAddMonoidHom.codRestrict
      (AddSubgroup.torsionBy RationalCircle n)
      (fun c => AddSubgroup.torsionBy.nsmul_iff.mpr (traceCharacterExtension_torsion F n c)))).toZModLinearMap n

/-- The normalization holds on all cochains, before any Kummer-image assertion. -/
theorem finiteCochainTrace_toRat (c : (finiteComplex F n).X 2) :
    ZMod.toRatAddCircle n (finiteCochainTrace F n c) = (traceCharacterExtension F n).val c :=
  circleTorsionEquiv_toRat n _

/-- On every actual cocycle the fixed trace is the genuine Brauer invariant. -/
theorem finiteCochainTrace_cocycle
    (c : LinearMap.ker ((finiteComplex F n).d 2 3).hom) :
    finiteCochainTrace F n c.val = finiteInvariant F n hn (kerToH2 c) := by
  apply ZMod.toRatAddCircle_injective n
  rw [finiteCochainTrace_toRat, finiteInvariant_toRat]
  exact LinearMap.congr_fun (traceCharacterExtension F n).property c

include hn in
/-- The actual finite local trace kills every actual boundary. -/
theorem finiteCochainTrace_boundary (c : (finiteComplex F n).X 1) :
    finiteCochainTrace F n (((finiteComplex F n).d 1 2).hom c) = 0 := by
  let z : LinearMap.ker ((finiteComplex F n).d 2 3).hom :=
    ⟨((finiteComplex F n).d 1 2).hom c, by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
        (finiteComplex F n).d_comp_d]
      rfl⟩
  have hclass : kerToH2 z = 0 := (kerToH2_eq_zero_iff z).2 ⟨c, rfl⟩
  have ht := finiteCochainTrace_cocycle F n hn z
  rw [hclass, map_zero] at ht
  exact ht

include hn in
/-- The kernel of the actual finite local trace on cycles is exactly the actual boundaries. -/
theorem finiteCochainTrace_kernel (z : (finiteComplex F n).X 2)
    (hz : ((finiteComplex F n).d 2 3).hom z = 0) (ht : finiteCochainTrace F n z = 0) :
    ∃ c : (finiteComplex F n).X 1, ((finiteComplex F n).d 1 2).hom c = z := by
  have hc : kerToH2 (⟨z, hz⟩ : LinearMap.ker ((finiteComplex F n).d 2 3).hom) = 0 :=
    (finiteInvariant_eq_zero_iff F n hn _).1
      ((finiteCochainTrace_cocycle F n hn ⟨z, hz⟩).symm.trans ht)
  exact (kerToH2_eq_zero_iff _).1 hc

include hn in
/-- A genuine degree-two local cocycle has finite trace one. -/
theorem finiteCochainTrace_onto_one :
    ∃ z : (finiteComplex F n).X 2, ((finiteComplex F n).d 2 3).hom z = 0 ∧
      finiteCochainTrace F n z = 1 := by
  obtain ⟨z, hz⟩ := kerToH2_surjective (k := ZMod n) (G := AbsoluteGaloisGroup F)
    (M := KummerCoeff F n) ((finiteInvariant F n hn).symm 1)
  exact ⟨z, z.2, (finiteCochainTrace_cocycle F n hn z).trans
    (by rw [hz, (finiteInvariant F n hn).apply_symm_apply])⟩

include hn in
/-- The fixed finite trace supplies the complete trace-isomorphism interface on the genuine target. -/
theorem finiteCochainTrace_inducesIsoH2 :
    InducesIsoH2 (C := natCx (finiteComplex F n)) (finiteCochainTrace F n) :=
  ⟨finiteCochainTrace_kernel F n hn, finiteCochainTrace_onto_one F n hn⟩

end FiniteCochainTrace

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace

end

/-!
# Fixed coefficient and cochain reductions of the actual Tate module

The coefficient reduction is the projection of the actual compatible torsion
family. It induces fixed continuous cochain maps and fixed degree-one class
maps. For the local quadratic twist their finite targets are exactly the
torsion coefficients of the genuine finite Kummer condition.
-/

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction

open TauCeti TauCeti.ContCohomology CategoryTheory
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules

section Coefficients

variable (G A : Type) [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- The actual action on point coefficients, as an additive homomorphism. -/
def coefficientAction (σ : G) : A →+ A where
  toFun a := σ • a
  map_zero' := smul_zero σ
  map_add' := smul_add σ

/-- The actual two-adic Tate module with its specified Galois action. -/
def IntegralTateCoeff (_G : Type) (A : Type) [AddCommGroup A] : Type := TateModule 2 A

instance integralAddCommGroup : AddCommGroup (IntegralTateCoeff G A) :=
  inferInstanceAs (AddCommGroup (TateModule 2 A))

instance integralModule : Module ℤ_[2] (IntegralTateCoeff G A) :=
  inferInstanceAs (Module ℤ_[2] (TateModule 2 A))

instance integralTopologicalSpace : TopologicalSpace (IntegralTateCoeff G A) :=
  inferInstanceAs (TopologicalSpace (TateModule 2 A))

instance integralTopologicalAddGroup : IsTopologicalAddGroup (IntegralTateCoeff G A) :=
  inferInstanceAs (IsTopologicalAddGroup (TateModule 2 A))

instance integralContinuousScalar : ContinuousSMul ℤ_[2] (IntegralTateCoeff G A) :=
  inferInstanceAs (ContinuousSMul ℤ_[2] (TateModule 2 A))

instance integralGaloisAction : DistribMulAction G (IntegralTateCoeff G A) where
  smul σ x := TateModule.map (coefficientAction G A σ) x
  one_smul x := TateModule.ext fun a => Subtype.ext (by
    change (1 : G) • (TateModule.proj a x : A) = (TateModule.proj a x : A)
    exact one_smul _ _)
  mul_smul σ τ x := TateModule.ext fun a => Subtype.ext (by
    change (σ * τ) • (TateModule.proj a x : A) = σ • (τ • (TateModule.proj a x : A))
    exact mul_smul _ _ _)
  smul_zero σ := map_zero (TateModule.map (coefficientAction G A σ))
  smul_add σ x y := map_add (TateModule.map (coefficientAction G A σ)) x y

instance integralScalarComm : SMulCommClass G ℤ_[2] (IntegralTateCoeff G A) where
  smul_comm σ r x := (TateModule.mapLinearMap (coefficientAction G A σ)).map_smul r x

/-- The actual finite torsion level with its specified Galois action. -/
def FiniteTateCoeff (_G : Type) (A : Type) [AddCommGroup A] (a : ℕ) : Type := TateModuleLevel 2 A a

instance finiteAddCommGroup (a : ℕ) : AddCommGroup (FiniteTateCoeff G A a) :=
  inferInstanceAs (AddCommGroup (TateModuleLevel 2 A a))

instance finiteZModModule (a : ℕ) : Module (ZMod (2 ^ a)) (FiniteTateCoeff G A a) :=
  inferInstanceAs (Module (ZMod (2 ^ a)) (TateModuleLevel 2 A a))

instance finiteModule (a : ℕ) : Module ℤ_[2] (FiniteTateCoeff G A a) :=
  Module.compHom (FiniteTateCoeff G A a) (PadicInt.toZModPow a)

instance finiteTopologicalSpace (a : ℕ) : TopologicalSpace (FiniteTateCoeff G A a) := ⊥

instance finiteDiscreteTopology (a : ℕ) : DiscreteTopology (FiniteTateCoeff G A a) := ⟨rfl⟩

instance finiteGaloisAction (a : ℕ) : DistribMulAction G (FiniteTateCoeff G A a) where
  smul σ t := TateModule.levelMap (coefficientAction G A σ) a t
  one_smul t := Subtype.ext (one_smul G (t : TateModuleLevel 2 A a).val)
  mul_smul σ τ t := Subtype.ext (mul_smul σ τ (t : TateModuleLevel 2 A a).val)
  smul_zero σ := map_zero (TateModule.levelMap (coefficientAction G A σ) a)
  smul_add σ t u := map_add (TateModule.levelMap (coefficientAction G A σ) a) t u

instance finiteScalarComm (a : ℕ) : SMulCommClass G ℤ_[2] (FiniteTateCoeff G A a) where
  smul_comm σ r t := ZMod.map_smul
    (TateModule.levelMap (coefficientAction G A σ) a) (PadicInt.toZModPow a r) t

/-- The fixed coefficient reduction is the actual Tate-module projection. -/
def coefficientProjection (a : ℕ) : IntegralTateCoeff G A →ₗ[ℤ_[2]] FiniteTateCoeff G A a where
  toFun x := TateModule.proj a x
  map_add' x y := map_add (TateModule.proj a) x y
  map_smul' r x := TateModule.proj_smul r x a

/-- The coefficient projection intertwines the actual Galois actions. -/
theorem coefficientProjection_smul (a : ℕ) (σ : G) (x : IntegralTateCoeff G A) :
    coefficientProjection G A a (σ • x) = σ • coefficientProjection G A a x := rfl

/-- The coefficient reduction uses the canonical residue of every two-adic scalar. -/
theorem coefficientProjection_scalar (a : ℕ) (r : ℤ_[2]) (x : IntegralTateCoeff G A) :
    coefficientProjection G A a (r • x) = PadicInt.toZModPow a r • coefficientProjection G A a x :=
  TateModule.proj_smul r x a

/-- The coefficient projection is locally constant, hence continuous into finite coefficients. -/
theorem coefficientProjection_continuous (a : ℕ) : Continuous (coefficientProjection G A a) := by
  have h : IsLocallyConstant (coefficientProjection G A a) := TateModule.isLocallyConstant_proj a
  exact h.continuous

/-- The transition between genuine finite Tate levels is multiplication by two. -/
def coefficientTransition (a : ℕ) : FiniteTateCoeff G A (a + 1) →ₗ[ℤ_[2]] FiniteTateCoeff G A a where
  toFun t := tateModuleTransition 2 A a t
  map_add' t u := map_add (tateModuleTransition 2 A a) t u
  map_smul' r t := by
    let y : TateModuleLevel 2 A (a + 1) := t
    change tateModuleTransition 2 A a (PadicInt.toZModPow (a + 1) r • y) =
      PadicInt.toZModPow a r • tateModuleTransition 2 A a y
    rw [← PadicInt.cast_toZModPow a (a + 1) a.le_succ r]
    let c := PadicInt.toZModPow (a + 1) r
    rw [show PadicInt.toZModPow (a + 1) r = c from rfl]
    rw [← c.intCast_zmod_cast, Int.cast_smul_eq_zsmul, map_zsmul]
    rw [ZMod.cast_intCast (R := ZMod (2 ^ a)) (pow_dvd_pow 2 a.le_succ), Int.cast_smul_eq_zsmul]

/-- The finite transition intertwines the actual Galois action. -/
theorem coefficientTransition_smul (a : ℕ) (σ : G) (t : FiniteTateCoeff G A (a + 1)) :
    coefficientTransition G A a (σ • t) = σ • coefficientTransition G A a t := by
  apply Subtype.ext
  change (2 : ℕ) • (σ • (t : TateModuleLevel 2 A (a + 1)).val) =
    σ • ((2 : ℕ) • (t : TateModuleLevel 2 A (a + 1)).val)
  exact smul_comm _ _ _

/-- The fixed integral projections are compatible with the genuine finite transitions. -/
theorem coefficientProjection_succ (a : ℕ) (x : IntegralTateCoeff G A) :
    coefficientTransition G A a (coefficientProjection G A (a + 1) x) =
      coefficientProjection G A a x := TateModule.proj_succ x a

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul G A]

instance integralContinuousGalois : ContinuousSMul G (IntegralTateCoeff G A) where
  continuous_smul := TateModule.continuous_map_apply (p := 2)
    (f := coefficientAction G A) (fun a t =>
      (IsLocallyConstant.iff_continuous _).2 (continuous_id.smul continuous_const))

instance finiteContinuousGalois (a : ℕ) : ContinuousSMul G (FiniteTateCoeff G A a) := by
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro t
  have hc : Continuous (fun σ : G => σ • (t : TateModuleLevel 2 A a).val) :=
    continuous_id.smul continuous_const
  have ho := hc.isOpen_preimage {(t : TateModuleLevel 2 A a).val} (isOpen_discrete _)
  convert ho using 1
  ext σ
  exact Subtype.ext_iff

end Coefficients

section Cochains

variable (G A : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup A] [DistribMulAction G A] [TopologicalSpace A] [DiscreteTopology A]
  [ContinuousSMul G A]

/-- The actual continuous cochains with integral Tate-module coefficients. -/
abbrev integralComplex := contCochains ℤ_[2] G (IntegralTateCoeff G A)

/-- The actual continuous cochains at a fixed finite Tate-module level. -/
abbrev finiteIntegralComplex (a : ℕ) := contCochains ℤ_[2] G (FiniteTateCoeff G A a)

/-- The fixed coefficient reduction induces the fixed genuine continuous cochain reduction. -/
def reduceCochains (a : ℕ) : integralComplex G A ⟶ finiteIntegralComplex G A a :=
  contCochainsMap (ContinuousMonoidHom.id G) (coefficientProjection G A a)
    (coefficientProjection_continuous G A a) (coefficientProjection_smul G A a)

/-- Cochain reduction is pointwise projection of the actual compatible torsion family. -/
theorem reduceCochains_apply (a k : ℕ) (c : (integralComplex G A).X k) (s : Fin k → G) :
    cfun (((reduceCochains G A a).f k).hom c) s = coefficientProjection G A a (cfun c s) := rfl

/-- The two actual differentials commute with the fixed cochain reduction. -/
theorem reduceCochains_d (a k : ℕ) (c : (integralComplex G A).X k) :
    ((reduceCochains G A a).f (k + 1)).hom (((integralComplex G A).d k (k + 1)).hom c) =
      ((finiteIntegralComplex G A a).d k (k + 1)).hom (((reduceCochains G A a).f k).hom c) := by
  have h := congrArg (fun f => f.hom c) ((reduceCochains G A a).comm k (k + 1))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h.symm

/-- The fixed reduction restricted to actual degree-one cycles. -/
def reduceOneCycle (a : ℕ) :
    LinearMap.ker ((integralComplex G A).d 1 2).hom →ₗ[ℤ_[2]]
      LinearMap.ker ((finiteIntegralComplex G A a).d 1 2).hom where
  toFun c := ⟨((reduceCochains G A a).f 1).hom c, by
    change ((finiteIntegralComplex G A a).d 1 2).hom (((reduceCochains G A a).f 1).hom c.val) = 0
    rw [← reduceCochains_d, c.2, map_zero]⟩
  map_add' c d := Subtype.ext (map_add ((reduceCochains G A a).f 1).hom c.val d.val)
  map_smul' r c := Subtype.ext (map_smul ((reduceCochains G A a).f 1).hom r c.val)

/-- The independently defined, genuine finite class reduction of integral degree-one cycles. -/
def reducedOneClass (a : ℕ) :
    LinearMap.ker ((integralComplex G A).d 1 2).hom →+
      H1 G (FiniteTateCoeff G A a) :=
  (kerToH1 (k := ℤ_[2]) (G := G) (M := FiniteTateCoeff G A a)).comp
    (reduceOneCycle G A a).toAddMonoidHom

/-- The fixed reduction restricted to actual degree-two cycles. -/
def reduceTwoCycle (a : ℕ) :
    LinearMap.ker ((integralComplex G A).d 2 3).hom →ₗ[ℤ_[2]]
      LinearMap.ker ((finiteIntegralComplex G A a).d 2 3).hom where
  toFun c := ⟨((reduceCochains G A a).f 2).hom c, by
    change ((finiteIntegralComplex G A a).d 2 3).hom (((reduceCochains G A a).f 2).hom c.val) = 0
    rw [← reduceCochains_d, c.2, map_zero]⟩
  map_add' c d := Subtype.ext (map_add ((reduceCochains G A a).f 2).hom c.val d.val)
  map_smul' r c := Subtype.ext (map_smul ((reduceCochains G A a).f 2).hom r c.val)

/-- The independently defined, genuine finite class reduction of integral degree-two cycles. -/
def reducedTwoClass (a : ℕ) :
    LinearMap.ker ((integralComplex G A).d 2 3).hom →+
      H2 G (FiniteTateCoeff G A a) :=
  (kerToH2 (k := ℤ_[2]) (G := G) (M := FiniteTateCoeff G A a)).comp
    (reduceTwoCycle G A a).toAddMonoidHom

/-- The fixed degree-one reduction on the actual integral cohomology group. -/
def cohomologyOneReduction (a : ℕ) :
    (integralComplex G A).homology 1 →+ H1 G (FiniteTateCoeff G A a) :=
  (contH1AddEquiv ℤ_[2] G (FiniteTateCoeff G A a)).toAddMonoidHom.comp
    (HomologicalComplex.homologyMap (reduceCochains G A a) 1).hom.toAddMonoidHom

/-- The fixed degree-two reduction on the actual integral cohomology group. -/
def cohomologyTwoReduction (a : ℕ) :
    (integralComplex G A).homology 2 →+ H2 G (FiniteTateCoeff G A a) :=
  (contH2AddEquiv ℤ_[2] G (FiniteTateCoeff G A a)).toAddMonoidHom.comp
    (HomologicalComplex.homologyMap (reduceCochains G A a) 2).hom.toAddMonoidHom

/-- The genuine finite coefficient transition induces the genuine finite cochain transition. -/
def transitionCochains (a : ℕ) : finiteIntegralComplex G A (a + 1) ⟶ finiteIntegralComplex G A a :=
  contCochainsMap (ContinuousMonoidHom.id G) (coefficientTransition G A a)
    continuous_of_discreteTopology (coefficientTransition_smul G A a)

/-- Finite cochain transitions commute with the actual differentials. -/
theorem transitionCochains_d (a k : ℕ) (c : (finiteIntegralComplex G A (a + 1)).X k) :
    ((transitionCochains G A a).f (k + 1)).hom
        (((finiteIntegralComplex G A (a + 1)).d k (k + 1)).hom c) =
      ((finiteIntegralComplex G A a).d k (k + 1)).hom (((transitionCochains G A a).f k).hom c) := by
  have h := congrArg (fun f => f.hom c) ((transitionCochains G A a).comm k (k + 1))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h.symm

/-- The actual integral cochain reductions form a compatible finite-level family. -/
theorem reduceCochains_succ (a k : ℕ) (c : (integralComplex G A).X k) :
    ((transitionCochains G A a).f k).hom (((reduceCochains G A (a + 1)).f k).hom c) =
      ((reduceCochains G A a).f k).hom c := by
  apply Subtype.ext
  funext s
  exact coefficientProjection_succ G A a (cfun c s)

/-- Compatible genuine finite continuous cochains assemble into an actual integral continuous cochain. -/
def liftCompatibleCochains (k : ℕ) (c : ∀ a : ℕ, (finiteIntegralComplex G A a).X k)
    (hc : ∀ a : ℕ, ((transitionCochains G A a).f k).hom (c (a + 1)) = c a) :
    (integralComplex G A).X k :=
  ⟨fun s => TateModule.mk (fun a => (show TateModuleLevel 2 A a from
        (cfun (c a) s : FiniteTateCoeff G A a))) (fun a => by
      have h := congrArg (fun v => cfun v s) (hc a)
      exact h), by
    apply TateModule.continuous_iff.mpr
    intro a
    have h : IsLocallyConstant (cfun (c a) : (Fin k → G) → FiniteTateCoeff G A a) :=
      (IsLocallyConstant.iff_continuous _).2 (c a).2
    exact h⟩

/-- The assembled actual integral cochain has the prescribed finite projections. -/
theorem liftCompatibleCochains_projection (k : ℕ) (c : ∀ a : ℕ, (finiteIntegralComplex G A a).X k)
    (hc : ∀ a : ℕ, ((transitionCochains G A a).f k).hom (c (a + 1)) = c a) (a : ℕ) :
    ((reduceCochains G A a).f k).hom (liftCompatibleCochains G A k c hc) = c a := by
  apply Subtype.ext
  funext s
  rfl

/-- Actual integral continuous cochains are determined by their actual finite projections. -/
theorem integralCochain_ext (k : ℕ) (c d : (integralComplex G A).X k)
    (h : ∀ a : ℕ, ((reduceCochains G A a).f k).hom c = ((reduceCochains G A a).f k).hom d) : c = d := by
  apply Subtype.ext
  funext s
  apply TateModule.ext
  intro a
  exact congrArg (fun v => cfun v s) (h a)

/-- A finite coefficient transition induces the corresponding actual class transition. -/
def transitionCoefficientHom (a : ℕ) :
    FiniteTateCoeff G A (a + 1) →+[G] FiniteTateCoeff G A a :=
  { (coefficientTransition G A a).toAddMonoidHom with map_smul' := coefficientTransition_smul G A a }

/-- The fixed finite transition on actual first cohomology. -/
def transitionH1 (a : ℕ) : H1 G (FiniteTateCoeff G A (a + 1)) →+ H1 G (FiniteTateCoeff G A a) :=
  explicitCoeff1 G (FiniteTateCoeff G A (a + 1)) (transitionCoefficientHom G A a)
    continuous_of_discreteTopology

/-- Finite cochain transitions restricted to actual cocycles. -/
def transitionCycle (a k : ℕ) :
    LinearMap.ker ((finiteIntegralComplex G A (a + 1)).d k (k + 1)).hom →ₗ[ℤ_[2]]
      LinearMap.ker ((finiteIntegralComplex G A a).d k (k + 1)).hom where
  toFun c := ⟨((transitionCochains G A a).f k).hom c, by
    change ((finiteIntegralComplex G A a).d k (k + 1)).hom
      (((transitionCochains G A a).f k).hom c.val) = 0
    rw [← transitionCochains_d, c.2, map_zero]⟩
  map_add' c d := Subtype.ext (map_add ((transitionCochains G A a).f k).hom c.val d.val)
  map_smul' r c := Subtype.ext (map_smul ((transitionCochains G A a).f k).hom r c.val)

/-- The cochain and class transitions agree on every actual degree-one cocycle. -/
theorem transitionH1_kerToH1 (a : ℕ)
    (c : LinearMap.ker ((finiteIntegralComplex G A (a + 1)).d 1 2).hom) :
    transitionH1 G A a (kerToH1 c) = kerToH1 (transitionCycle G A a 1 c) := by
  erw [transitionH1, kerToH1_apply, explicitCoeff1_mk]

/-- Surjectivity of the actual finite coefficient map gives surjectivity on continuous cochains. -/
theorem transitionCochains_surjective (a k : ℕ)
    (hcoeff : Function.Surjective (coefficientTransition G A a)) :
    Function.Surjective ((transitionCochains G A a).f k).hom := by
  choose s hs using hcoeff
  intro c
  let d : (finiteIntegralComplex G A (a + 1)).X k :=
    ⟨fun x => s (cfun c x), (continuous_of_discreteTopology (f := s)).comp c.2⟩
  exact ⟨d, Subtype.ext (funext fun x => hs (cfun c x))⟩

/-- Actual class surjectivity and actual coefficient surjectivity lift genuine one-cocycles. -/
theorem transitionOneCycle_surjective (a : ℕ)
    (hcoeff : Function.Surjective (coefficientTransition G A a))
    (hclass : Function.Surjective (transitionH1 G A a)) :
    Function.Surjective (transitionCycle G A a 1) := by
  intro c
  obtain ⟨y, hy⟩ := hclass (kerToH1 c)
  obtain ⟨z, hz⟩ := kerToH1_surjective (k := ℤ_[2]) (G := G)
    (M := FiniteTateCoeff G A (a + 1)) y
  have hdiff : kerToH1 (transitionCycle G A a 1 z - c) = 0 := by
    rw [map_sub, ← transitionH1_kerToH1, hz, hy, sub_self]
  obtain ⟨q, hq⟩ := (kerToH1_eq_zero_iff _).1 hdiff
  obtain ⟨q', hq'⟩ := transitionCochains_surjective G A a 0 hcoeff q
  let z' : LinearMap.ker ((finiteIntegralComplex G A (a + 1)).d 1 2).hom :=
    ⟨z.val - ((finiteIntegralComplex G A (a + 1)).d 0 1).hom q', by
      rw [LinearMap.mem_ker, map_sub, z.2, zero_sub, neg_eq_zero]
      have h := congrArg (fun f => f.hom q') ((finiteIntegralComplex G A (a + 1)).d_comp_d 0 1 2)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] using h⟩
  refine ⟨z', Subtype.ext ?_⟩
  change ((transitionCochains G A a).f 1).hom
    (z.val - ((finiteIntegralComplex G A (a + 1)).d 0 1).hom q') = c.val
  rw [map_sub, transitionCochains_d, hq']
  change (transitionCycle G A a 1 z).val - ((finiteIntegralComplex G A a).d 0 1).hom q = c.val
  rw [hq]
  exact sub_sub_cancel _ _

/-- Compatible finite primitives lift to an actual integral primitive when genuine one-cocycles lift. -/
theorem integral_boundary_of_finite_boundaries
    (hlift : ∀ a : ℕ, Function.Surjective (transitionCycle G A a 1))
    (z : (integralComplex G A).X 2)
    (hzero : ∀ a : ℕ, ∃ b : (finiteIntegralComplex G A a).X 1,
      ((finiteIntegralComplex G A a).d 1 2).hom b = ((reduceCochains G A a).f 2).hom z) :
    ∃ b : (integralComplex G A).X 1, ((integralComplex G A).d 1 2).hom b = z := by
  classical
  choose u hu using hzero
  have step : ∀ (a : ℕ) (b : (finiteIntegralComplex G A a).X 1),
      ((finiteIntegralComplex G A a).d 1 2).hom b = ((reduceCochains G A a).f 2).hom z →
      ∃ b' : (finiteIntegralComplex G A (a + 1)).X 1,
        ((finiteIntegralComplex G A (a + 1)).d 1 2).hom b' =
          ((reduceCochains G A (a + 1)).f 2).hom z ∧
        ((transitionCochains G A a).f 1).hom b' = b := by
    intro a b hb
    let r : LinearMap.ker ((finiteIntegralComplex G A a).d 1 2).hom :=
      ⟨((transitionCochains G A a).f 1).hom (u (a + 1)) - b, by
        rw [LinearMap.mem_ker, map_sub, ← transitionCochains_d, hu (a + 1), hb,
          reduceCochains_succ, sub_self]⟩
    obtain ⟨v, hv⟩ := hlift a r
    refine ⟨u (a + 1) - v.val, ?_, ?_⟩
    · rw [map_sub, hu (a + 1), v.2, sub_zero]
    · rw [map_sub]
      have hv' := congrArg Subtype.val hv
      change ((transitionCochains G A a).f 1).hom v.val =
        ((transitionCochains G A a).f 1).hom (u (a + 1)) - b at hv'
      rw [hv', sub_sub_cancel]
  let b : ∀ a : ℕ, {c : (finiteIntegralComplex G A a).X 1 //
      ((finiteIntegralComplex G A a).d 1 2).hom c = ((reduceCochains G A a).f 2).hom z} :=
    fun a => Nat.rec (motive := fun a => {c : (finiteIntegralComplex G A a).X 1 //
      ((finiteIntegralComplex G A a).d 1 2).hom c = ((reduceCochains G A a).f 2).hom z})
      ⟨u 0, hu 0⟩
      (fun a c => ⟨(step a c.val c.2).choose, (step a c.val c.2).choose_spec.1⟩) a
  have hb : ∀ a : ℕ, ((transitionCochains G A a).f 1).hom (b (a + 1)).val = (b a).val :=
    fun a => (step a (b a).val (b a).2).choose_spec.2
  refine ⟨liftCompatibleCochains G A 1 (fun a => (b a).val) hb, ?_⟩
  apply integralCochain_ext G A 2
  intro a
  rw [reduceCochains_d, liftCompatibleCochains_projection]
  exact (b a).2

end Cochains

section ActualEllipticCoefficients

open scoped Classical

variable (F : Type) [Field F] [CharZero F] [DecidableEq F] (B : WeierstrassCurve F)

/-- Integral local cochains of the actual elliptic Tate module over the algebraic closure. -/
abbrev actualIntegralComplex := integralComplex (Field.absoluteGaloisGroup F) (PtAlg F B)

/-- The finite-level dictionary is exactly the torsion coefficient module of the genuine Kummer maps. -/
def actualLevelEquiv (a : ℕ) :
    FiniteTateCoeff (Field.absoluteGaloisGroup F) (PtAlg F B) a ≃+ TorsAlg F B (2 ^ a) :=
  AddEquiv.refl _

/-- The dictionary intertwines the genuine finite Galois action. -/
theorem actualLevelEquiv_smul (a : ℕ) (σ : Field.absoluteGaloisGroup F)
    (t : FiniteTateCoeff (Field.absoluteGaloisGroup F) (PtAlg F B) a) :
    actualLevelEquiv F B a (σ • t) = σ • actualLevelEquiv F B a t := rfl

/-- The fixed actual finite Kummer-coefficient class reduction of integral local cycles. -/
def actualH1Reduction (a : ℕ) :
    LinearMap.ker ((actualIntegralComplex F B).d 1 2).hom →+
      H1 (Field.absoluteGaloisGroup F) (TorsAlg F B (2 ^ a)) :=
  (explicitCoeff1Equiv (Field.absoluteGaloisGroup F)
    (FiniteTateCoeff (Field.absoluteGaloisGroup F) (PtAlg F B) a) (actualLevelEquiv F B a)
    continuous_of_discreteTopology continuous_of_discreteTopology (actualLevelEquiv_smul F B a)).toAddMonoidHom.comp
      (reducedOneClass (Field.absoluteGaloisGroup F) (PtAlg F B) a)

/-- The fixed actual degree-two Kummer-coefficient class reduction of integral local cycles. -/
def actualH2Reduction (a : ℕ) :
    LinearMap.ker ((actualIntegralComplex F B).d 2 3).hom →+
      H2 (Field.absoluteGaloisGroup F) (TorsAlg F B (2 ^ a)) :=
  (explicitCoeff2Equiv (Field.absoluteGaloisGroup F)
    (FiniteTateCoeff (Field.absoluteGaloisGroup F) (PtAlg F B) a) (actualLevelEquiv F B a)
    continuous_of_discreteTopology continuous_of_discreteTopology (actualLevelEquiv_smul F B a)).toAddMonoidHom.comp
      (reducedTwoClass (Field.absoluteGaloisGroup F) (PtAlg F B) a)

/-- The fixed actual degree-one class reduction from integral local cohomology to the genuine finite coefficients. -/
def actualH1ReductionOnHomology (a : ℕ) :
    (actualIntegralComplex F B).homology 1 →+
      H1 (Field.absoluteGaloisGroup F) (TorsAlg F B (2 ^ a)) :=
  (explicitCoeff1Equiv (Field.absoluteGaloisGroup F)
    (FiniteTateCoeff (Field.absoluteGaloisGroup F) (PtAlg F B) a) (actualLevelEquiv F B a)
    continuous_of_discreteTopology continuous_of_discreteTopology (actualLevelEquiv_smul F B a)).toAddMonoidHom.comp
      (cohomologyOneReduction (Field.absoluteGaloisGroup F) (PtAlg F B) a)

/-- The fixed actual degree-two class reduction from integral local cohomology to the genuine finite coefficients. -/
def actualH2ReductionOnHomology (a : ℕ) :
    (actualIntegralComplex F B).homology 2 →+
      H2 (Field.absoluteGaloisGroup F) (TorsAlg F B (2 ^ a)) :=
  (explicitCoeff2Equiv (Field.absoluteGaloisGroup F)
    (FiniteTateCoeff (Field.absoluteGaloisGroup F) (PtAlg F B) a) (actualLevelEquiv F B a)
    continuous_of_discreteTopology continuous_of_discreteTopology (actualLevelEquiv_smul F B a)).toAddMonoidHom.comp
      (cohomologyTwoReduction (Field.absoluteGaloisGroup F) (PtAlg F B) a)

end ActualEllipticCoefficients

section ActualRootsOfUnity

variable (F : Type) [Field F]

/-- The actual integral local trace target, with Tate-module roots-of-unity coefficients. -/
abbrev actualTraceComplex := integralComplex (AbsoluteGaloisGroup F) (UnitsCoeff F)

/-- The finite trace-coefficient dictionary is the actual roots-of-unity inclusion. -/
def actualMuLevelEquiv (a : ℕ) :
    FiniteTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F) a ≃+ KummerCoeff F (2 ^ a) where
  toFun t := Additive.ofMul ⟨((t : TateModuleLevel 2 (UnitsCoeff F) a).val).toMul, by
    have h := congrArg Additive.toMul
      (AddSubgroup.torsionBy.nsmul_iff.mp (t : TateModuleLevel 2 (UnitsCoeff F) a).2)
    exact (mem_rootsOfUnity (2 ^ a) _).2 (by simpa only [toMul_nsmul, toMul_zero] using h)⟩
  invFun t := ⟨Additive.ofMul (t.toMul : (SeparableClosure F)ˣ), by
    apply AddSubgroup.torsionBy.nsmul_iff.mpr
    apply Additive.toMul.injective
    change (t.toMul : (SeparableClosure F)ˣ) ^ (2 ^ a) = 1
    exact (mem_rootsOfUnity (2 ^ a) _).1 t.toMul.2⟩
  left_inv t := Subtype.ext rfl
  right_inv t := Additive.toMul.injective (Subtype.ext rfl)
  map_add' t u := Additive.toMul.injective (Subtype.ext rfl)

/-- The trace-coefficient dictionary intertwines the actual Galois action. -/
theorem actualMuLevelEquiv_smul (a : ℕ) (σ : AbsoluteGaloisGroup F)
    (t : FiniteTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F) a) :
    actualMuLevelEquiv F a (σ • t) = σ • actualMuLevelEquiv F a t := rfl

/-- The genuine second-cohomology dictionary for finite roots-of-unity coefficients. -/
def actualMuH2Equiv (a : ℕ) :
    H2 (AbsoluteGaloisGroup F) (FiniteTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F) a) ≃+
      H2 (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ a)) :=
  explicitCoeff2Equiv (AbsoluteGaloisGroup F)
    (FiniteTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F) a) (actualMuLevelEquiv F a)
    continuous_of_discreteTopology continuous_of_discreteTopology (actualMuLevelEquiv_smul F a)

/-- The fixed reduction of actual integral trace-target cycles to the actual finite local class group. -/
def actualMuH2Reduction (a : ℕ) :
    LinearMap.ker ((actualTraceComplex F).d 2 3).hom →+
      H2 (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ a)) :=
  (actualMuH2Equiv F a).toAddMonoidHom.comp
    (reducedTwoClass (AbsoluteGaloisGroup F) (UnitsCoeff F) a)

/-- The fixed reduction of the actual integral trace-target cohomology. -/
def actualMuH2ReductionOnHomology (a : ℕ) :
    (actualTraceComplex F).homology 2 →+ H2 (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ a)) :=
  (explicitCoeff2Equiv (AbsoluteGaloisGroup F)
    (FiniteTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F) a) (actualMuLevelEquiv F a)
    continuous_of_discreteTopology continuous_of_discreteTopology (actualMuLevelEquiv_smul F a)).toAddMonoidHom.comp
      (cohomologyTwoReduction (AbsoluteGaloisGroup F) (UnitsCoeff F) a)

/-- The genuine first-cohomology dictionary for finite roots-of-unity coefficients. -/
def actualMuH1Equiv (a : ℕ) :
    H1 (AbsoluteGaloisGroup F) (FiniteTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F) a) ≃+
      H1 (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ a)) :=
  explicitCoeff1Equiv (AbsoluteGaloisGroup F)
    (FiniteTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F) a) (actualMuLevelEquiv F a)
    continuous_of_discreteTopology continuous_of_discreteTopology (actualMuLevelEquiv_smul F a)

/-- The actual finite trace-coefficient transitions are the genuine roots-of-unity power maps. -/
theorem actualMuLevelEquiv_transition (a : ℕ)
    (t : FiniteTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F) (a + 1)) :
    actualMuLevelEquiv F a (coefficientTransition (AbsoluteGaloisGroup F) (UnitsCoeff F) a t) =
      kummerCoeffPow F (pow_dvd_pow 2 a.le_succ) (actualMuLevelEquiv F (a + 1) t) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change (((t : TateModuleLevel 2 (UnitsCoeff F) (a + 1)).val).toMul : (SeparableClosure F)ˣ) ^ 2 =
    (((t : TateModuleLevel 2 (UnitsCoeff F) (a + 1)).val).toMul : (SeparableClosure F)ˣ) ^
      (2 ^ (a + 1) / 2 ^ a)
  have hdiv : 2 ^ (a + 1) / 2 ^ a = 2 := by
    rw [pow_succ, Nat.mul_div_right 2 (pow_pos (by decide) a)]
  exact congrArg (fun k : ℕ =>
    (((t : TateModuleLevel 2 (UnitsCoeff F) (a + 1)).val).toMul : (SeparableClosure F)ˣ) ^ k) hdiv.symm

/-- The two genuine finite-level descriptions induce exactly the same transition on classes. -/
theorem actualMuH1Equiv_transition (a : ℕ)
    (y : H1 (AbsoluteGaloisGroup F) (FiniteTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F) (a + 1))) :
    actualMuH1Equiv F a (transitionH1 (AbsoluteGaloisGroup F) (UnitsCoeff F) a y) =
      explicitCoeff1 (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ (a + 1)))
        (kummerCoeffPow F (pow_dvd_pow 2 a.le_succ)) continuous_of_discreteTopology
        (actualMuH1Equiv F (a + 1) y) := by
  induction y using QuotientAddGroup.induction_on with
  | H c =>
    erw [actualMuH1Equiv, explicitCoeff1Equiv_apply, transitionH1, explicitCoeff1_mk,
      explicitCoeff1_mk]
    apply congrArg (H1pi (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ a)))
    apply Subtype.ext
    funext σ
    exact actualMuLevelEquiv_transition F a ((c : AbsoluteGaloisGroup F → _) σ)

variable [CharZero F]

/-- The genuine finite trace-coefficient transition is surjective in characteristic zero. -/
theorem actualMuTransition_surjective (a : ℕ) :
    Function.Surjective (coefficientTransition (AbsoluteGaloisGroup F) (UnitsCoeff F) a) := by
  intro t
  obtain ⟨u, hu⟩ := unitsCoeffPow_surjective F 2 (isUnit_iff_ne_zero.mpr two_ne_zero)
    (t : TateModuleLevel 2 (UnitsCoeff F) a).val
  rw [unitsCoeffPow_eq_nsmul] at hu
  have hmem : u ∈ AddSubgroup.torsionBy (UnitsCoeff F) ((2 ^ (a + 1) : ℕ) : ℤ) := by
    rw [AddSubgroup.torsionBy.nsmul_iff, pow_succ, mul_nsmul', hu]
    exact AddSubgroup.torsionBy.nsmul_iff.mp (t : TateModuleLevel 2 (UnitsCoeff F) a).2
  exact ⟨⟨u, hmem⟩, Subtype.ext hu⟩

/-- The genuine finite local trace-coefficient map is surjective on first cohomology. -/
theorem actualMuH1Transition_surjective (a : ℕ) :
    Function.Surjective (transitionH1 (AbsoluteGaloisGroup F) (UnitsCoeff F) a) := by
  intro y
  have hn : IsUnit (((2 ^ (a + 1) : ℕ) : F)) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (pow_ne_zero _ (by decide)))
  obtain ⟨z, hz⟩ := explicitCoeff1_kummerCoeffPow_surjective hn (pow_dvd_pow 2 a.le_succ)
    (actualMuH1Equiv F a y)
  refine ⟨(actualMuH1Equiv F (a + 1)).symm z, ?_⟩
  apply (actualMuH1Equiv F a).injective
  rw [actualMuH1Equiv_transition, (actualMuH1Equiv F (a + 1)).apply_symm_apply, hz]

/-- Genuine finite one-cocycles of the local trace target lift through the next finite level. -/
theorem actualMuOneCycleTransition_surjective (a : ℕ) :
    Function.Surjective (transitionCycle (AbsoluteGaloisGroup F) (UnitsCoeff F) a 1) :=
  transitionOneCycle_surjective (AbsoluteGaloisGroup F) (UnitsCoeff F) a
    (actualMuTransition_surjective F a) (actualMuH1Transition_surjective F a)

/-- Fixed reduction of a genuine integral target cycle vanishes precisely when its projected finite class vanishes. -/
theorem actualMuH2Reduction_eq_zero_iff (a : ℕ)
    (z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom) :
    actualMuH2Reduction F a z = 0 ↔
      kerToH2 (reduceTwoCycle (AbsoluteGaloisGroup F) (UnitsCoeff F) a z) = 0 :=
  (actualMuH2Equiv F a).map_eq_zero_iff

/-- The actual integral local trace-target boundary criterion, proved from the fixed finite reductions. -/
theorem actualMuH2Reduction_all_zero_iff_boundary
    (z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom) :
    (∀ a : ℕ, actualMuH2Reduction F a z = 0) ↔
      ∃ b : (actualTraceComplex F).X 1, ((actualTraceComplex F).d 1 2).hom b = z.val := by
  constructor
  · intro hzero
    apply integral_boundary_of_finite_boundaries (AbsoluteGaloisGroup F) (UnitsCoeff F)
      (actualMuOneCycleTransition_surjective F) z.val
    intro a
    exact (kerToH2_eq_zero_iff _).1 ((actualMuH2Reduction_eq_zero_iff F a z).1 (hzero a))
  · rintro ⟨b, hb⟩ a
    apply (actualMuH2Reduction_eq_zero_iff F a z).2
    apply (kerToH2_eq_zero_iff _).2
    refine ⟨((reduceCochains (AbsoluteGaloisGroup F) (UnitsCoeff F) a).f 1).hom b, ?_⟩
    change ((finiteIntegralComplex (AbsoluteGaloisGroup F) (UnitsCoeff F) a).d 1 2).hom
      (((reduceCochains (AbsoluteGaloisGroup F) (UnitsCoeff F) a).f 1).hom b) =
        ((reduceCochains (AbsoluteGaloisGroup F) (UnitsCoeff F) a).f 2).hom z.val
    rw [← reduceCochains_d, hb]

end ActualRootsOfUnity

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction

end

noncomputable section

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer

open CategoryTheory TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.CloudB3RC53.Duality ZInQ.Contrib.RC53Assist.DerivedKummer

/-- A fixed Cauchy sequence of actual points representing an element of the actual completion. -/
def representatives (P : Type*) [AddCommGroup P] (x : PointCompletion P) :
    AdicCompletion.AdicCauchySequence twoIdeal P :=
  (AdicCompletion.mk_surjective twoIdeal P x).choose

/-- The fixed representatives evaluate to the prescribed actual finite point classes. -/
theorem representatives_mk (P : Type*) [AddCommGroup P] (x : PointCompletion P) (a : ℕ) :
    (Submodule.Quotient.mk (representatives P x a) : P ⧸ pointPowSub P a) = x.val a :=
  congrArg (fun y : PointCompletion P => y.val a) (AdicCompletion.mk_surjective twoIdeal P x).choose_spec

/-- The rational difference between successive actual point representatives. -/
def stepPoint (P : Type*) [AddCommGroup P] (x : PointCompletion P) (a : ℕ) : P :=
  ((mem_pointPowSub P a (representatives P x (a + 1) - representatives P x a)).1
    ((Submodule.Quotient.eq (pointPowSub P a)).1
      (AdicCompletion.AdicCauchySequence.mk_eq_mk a.le_succ (representatives P x)))).choose

/-- Successive fixed representatives differ by the indicated actual multiple of a point. -/
theorem stepPoint_mul (P : Type*) [AddCommGroup P] (x : PointCompletion P) (a : ℕ) :
    (2 ^ a : ℕ) • stepPoint P x a = representatives P x (a + 1) - representatives P x a :=
  ((mem_pointPowSub P a (representatives P x (a + 1) - representatives P x a)).1
    ((Submodule.Quotient.eq (pointPowSub P a)).1
      (AdicCompletion.AdicCauchySequence.mk_eq_mk a.le_succ (representatives P x)))).choose_spec

section Elliptic

variable (F : Type) [Field F] [CharZero F] [DecidableEq F]
  (B : WeierstrassCurve F) [B.IsElliptic]

/-- A fixed half of an actual geometric point, supplied by the genuine geometric divisibility theorem. -/
def halve (Q : PtAlg F B) : PtAlg F B := (exists_nsmul_eq (F := F) (B := B) 2 Q).choose

/-- The geometric half is a genuine division point. -/
theorem two_halve (Q : PtAlg F B) : (2 : ℕ) • halve F B Q = Q :=
  (exists_nsmul_eq (F := F) (B := B) 2 Q).choose_spec

/-- Fixed division points of the actual Cauchy representatives, compatible up to rational points. -/
def divisionFamily (x : PointCompletion B.toAffine.Point) : ℕ → PtAlg F B
  | 0 => basePt F B (representatives B.toAffine.Point x 0)
  | a + 1 => halve F B (divisionFamily x a + basePt F B (stepPoint B.toAffine.Point x a))

/-- The transition between division points is the fixed rational correction. -/
theorem divisionFamily_two (x : PointCompletion B.toAffine.Point) (a : ℕ) :
    (2 : ℕ) • divisionFamily F B x (a + 1) =
      divisionFamily F B x a + basePt F B (stepPoint B.toAffine.Point x a) :=
  two_halve F B _

/-- Every fixed division point divides its actual rational point representative. -/
theorem divisionFamily_power (x : PointCompletion B.toAffine.Point) (a : ℕ) :
    (2 ^ a : ℕ) • divisionFamily F B x a = basePt F B (representatives B.toAffine.Point x a) := by
  induction a with
  | zero => simp [divisionFamily]
  | succ a ih =>
    rw [pow_succ, mul_nsmul', divisionFamily_two, nsmul_add, ih, ← map_nsmul, stepPoint_mul, map_sub]
    abel

/-- The actual integral Kummer values assemble the existing genuine finite Kummer functions. -/
def integralKummerValue (x : PointCompletion B.toAffine.Point) (σ : Field.absoluteGaloisGroup F) :
    IntegralTateCoeff (Field.absoluteGaloisGroup F) (PtAlg F B) :=
  TateModule.mk (fun a => (show TateModuleLevel 2 (PtAlg F B) a from
    kummerFunOf F B (2 ^ a) (divisionFamily_power F B x a) σ)) (fun a => by
      apply Subtype.ext
      change (2 : ℕ) • (σ • divisionFamily F B x (a + 1) - divisionFamily F B x (a + 1)) =
        σ • divisionFamily F B x a - divisionFamily F B x a
      rw [nsmul_sub, smul_comm (2 : ℕ) σ, divisionFamily_two, smul_add, smul_basePt]
      abel)

/-- The fixed integral coefficient projection is exactly the genuine finite Kummer function. -/
theorem integralKummerValue_projection (x : PointCompletion B.toAffine.Point) (a : ℕ)
    (σ : Field.absoluteGaloisGroup F) :
    actualLevelEquiv F B a (coefficientProjection (Field.absoluteGaloisGroup F) (PtAlg F B) a
      (integralKummerValue F B x σ)) =
      kummerFunOf F B (2 ^ a) (divisionFamily_power F B x a) σ := rfl

/-- The actual integral local Kummer cochain is assembled from the genuine finite division-point cochains. -/
def integralKummerCochain (x : PointCompletion B.toAffine.Point) : (actualIntegralComplex F B).X 1 :=
  ⟨fun s => integralKummerValue F B x (s 0), by
    apply TateModule.continuous_iff.mpr
    intro a
    have h : IsLocallyConstant (fun s : Fin 1 → Field.absoluteGaloisGroup F =>
        kummerFunOf F B (2 ^ a) (divisionFamily_power F B x a) (s 0)) :=
      (IsLocallyConstant.iff_continuous _).2
        (kummerCocycleOf F B (2 ^ a) (divisionFamily_power F B x a)).2
    exact h⟩

/-- Every fixed integral Kummer cochain is an actual integral one-cocycle. -/
theorem integralKummerCochain_isCycle (x : PointCompletion B.toAffine.Point) :
    ((actualIntegralComplex F B).d 1 2).hom (integralKummerCochain F B x) = 0 := by
  apply integralCochain_ext (Field.absoluteGaloisGroup F) (PtAlg F B) 2
  intro a
  rw [reduceCochains_d, map_zero]
  apply contCochains_ext
  intro s
  have hvec : s = ![s 0, s 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hvec, contFun_d12, contFun_zero_apply]
  apply Subtype.ext
  change s 0 • (s 1 • divisionFamily F B x a - divisionFamily F B x a) -
      ((s 0 * s 1) • divisionFamily F B x a - divisionFamily F B x a) +
      (s 0 • divisionFamily F B x a - divisionFamily F B x a) = 0
  rw [smul_sub, mul_smul]
  abel

/-- The fixed integral Kummer one-cocycle, with its genuine cochain and its cycle proof. -/
def integralKummerCycle (x : PointCompletion B.toAffine.Point) :
    LinearMap.ker ((actualIntegralComplex F B).d 1 2).hom :=
  ⟨integralKummerCochain F B x, integralKummerCochain_isCycle F B x⟩

/-- The actual finite cochain projection is the existing genuine division-point Kummer cochain. -/
theorem integralKummerCochain_projection (x : PointCompletion B.toAffine.Point) (a : ℕ)
    (s : Fin 1 → Field.absoluteGaloisGroup F) :
    actualLevelEquiv F B a (cfun
      (((reduceCochains (Field.absoluteGaloisGroup F) (PtAlg F B) a).f 1).hom
        (integralKummerCochain F B x)) s) =
      cfun (kummerCocycleOf F B (2 ^ a) (divisionFamily_power F B x a)) s := rfl

/-- Fixed genuine integral reduction gives exactly the genuine finite Kummer class of the fixed point representative. -/
theorem integralKummerCycle_class (x : PointCompletion B.toAffine.Point) (a : ℕ) :
    actualH1Reduction F B a (integralKummerCycle F B x) =
      hOneToAlg F B (2 ^ a) (B.kummerMap (2 ^ a)
        (isUnit_iff_ne_zero.mpr (natCast_ne_zero_of_charZero F (2 ^ a)))
        (representatives B.toAffine.Point x a)) := by
  let q : B.PointCoeff := (pointCoeffToAlg F B).symm (divisionFamily F B x a)
  have hq : (2 ^ a : ℕ) • q = B.basePointCoeff (representatives B.toAffine.Point x a) :=
    (pointCoeffToAlg F B).injective (by
      rw [map_nsmul, pointCoeffToAlg_base]
      change (2 ^ a : ℕ) • pointCoeffToAlg F B ((pointCoeffToAlg F B).symm (divisionFamily F B x a)) = _
      rw [(pointCoeffToAlg F B).apply_symm_apply, divisionFamily_power])
  rw [B.kummerMap_eq_H1pi _ hq]
  unfold actualH1Reduction reducedOneClass
  erw [explicitCoeff1Equiv_apply, kerToH1_apply, explicitCoeff1_mk,
    hOneToAlg, explicitMap1Equiv_apply, explicitMap1_mk]
  apply congrArg (H1pi (Field.absoluteGaloisGroup F) (TorsAlg F B (2 ^ a)))
  apply Subtype.ext
  funext σ
  apply Subtype.ext
  change σ • divisionFamily F B x a - divisionFamily F B x a =
    pointCoeffToAlg F B (absoluteGaloisGroupRestrictEquiv F σ • q - q)
  rw [map_sub, pointCoeffToAlg_smul]
  change _ = σ • pointCoeffToAlg F B ((pointCoeffToAlg F B).symm (divisionFamily F B x a)) -
    pointCoeffToAlg F B ((pointCoeffToAlg F B).symm (divisionFamily F B x a))
  rw [(pointCoeffToAlg F B).apply_symm_apply]
  all_goals exact continuous_of_discreteTopology

/-- Finite genuine Tate cochains see a two-adic scalar through its fixed actual finite residue. -/
theorem finiteCochain_smul_repr (a k : ℕ) (r : ℤ_[2])
    (c : (finiteIntegralComplex (Field.absoluteGaloisGroup F) (PtAlg F B) a).X k) :
    r • c = (PadicInt.toZModPow a r).val • c := by
  apply Subtype.ext
  funext s
  let v : FiniteTateCoeff (Field.absoluteGaloisGroup F) (PtAlg F B) a := cfun c s
  let z : ZMod (2 ^ a) := PadicInt.toZModPow a r
  change z • v = z.val • v
  simpa only [Nat.cast_smul_eq_nsmul] using
    congrArg (fun t : ZMod (2 ^ a) => t • v) (ZMod.natCast_zmod_val z).symm

/-- The fixed actual class reduction is semilinear along the actual finite scalar reduction. -/
theorem actualH1Reduction_smul (a : ℕ) (r : ℤ_[2])
    (c : LinearMap.ker ((actualIntegralComplex F B).d 1 2).hom) :
    actualH1Reduction F B a (r • c) =
      (PadicInt.toZModPow a r).val • actualH1Reduction F B a c := by
  have h : reduceOneCycle (Field.absoluteGaloisGroup F) (PtAlg F B) a (r • c) =
      (PadicInt.toZModPow a r).val • reduceOneCycle (Field.absoluteGaloisGroup F) (PtAlg F B) a c := by
    rw [map_smul]
    apply Subtype.ext
    exact finiteCochain_smul_repr F B a 1 r _
  let ψ := (explicitCoeff1Equiv (Field.absoluteGaloisGroup F)
    (FiniteTateCoeff (Field.absoluteGaloisGroup F) (PtAlg F B) a) (actualLevelEquiv F B a)
    continuous_of_discreteTopology continuous_of_discreteTopology (actualLevelEquiv_smul F B a)).toAddMonoidHom
  change ψ (kerToH1 (reduceOneCycle (Field.absoluteGaloisGroup F) (PtAlg F B) a (r • c))) =
    (PadicInt.toZModPow a r).val • ψ (kerToH1 (reduceOneCycle (Field.absoluteGaloisGroup F) (PtAlg F B) a c))
  rw [h, map_nsmul, map_nsmul]

/-- The genuine finite Kummer class of the actual completed point, defined by its fixed actual quotient evaluation. -/
def completionKummerClass (a : ℕ) : PointCompletion B.toAffine.Point →+
    H1 (Field.absoluteGaloisGroup F) (TorsAlg F B (2 ^ a)) :=
  (hOneToAlg F B (2 ^ a)).toAddMonoidHom.comp
    ((B.kummerClassMap (2 ^ a)
      (isUnit_iff_ne_zero.mpr (natCast_ne_zero_of_charZero F (2 ^ a)))).comp
      ((completionQuotientEquiv B.toAffine.Point a).toAddMonoidHom.comp
        (nSub ((2 : ℤ_[2]) ^ a) (PointCompletion B.toAffine.Point)).mkQ.toAddMonoidHom))

/-- The genuine finite completed-point Kummer class is computed on the fixed rational representative. -/
theorem completionKummerClass_representatives (a : ℕ) (x : PointCompletion B.toAffine.Point) :
    completionKummerClass F B a x =
      hOneToAlg F B (2 ^ a) (B.kummerMap (2 ^ a)
        (isUnit_iff_ne_zero.mpr (natCast_ne_zero_of_charZero F (2 ^ a)))
        (representatives B.toAffine.Point x a)) := by
  change hOneToAlg F B (2 ^ a) (B.kummerClassMap (2 ^ a) _
    (completionQuotientEquiv B.toAffine.Point a (Submodule.Quotient.mk x))) = _
  rw [completionQuotientEquiv_mk, ← representatives_mk B.toAffine.Point x a,
    pointLevelEquiv_mk, B.kummerClassMap_mk]

/-- The fixed actual integral Kummer cycle reduces to the fixed actual completed-point Kummer class. -/
theorem integralKummerCycle_reduction (a : ℕ) (x : PointCompletion B.toAffine.Point) :
    actualH1Reduction F B a (integralKummerCycle F B x) = completionKummerClass F B a x := by
  rw [integralKummerCycle_class, completionKummerClass_representatives]

/-- The genuine completed-point Kummer class sees scalars through the fixed actual finite residue. -/
theorem completionKummerClass_smul (a : ℕ) (r : ℤ_[2]) (x : PointCompletion B.toAffine.Point) :
    completionKummerClass F B a (r • x) =
      (PadicInt.toZModPow a r).val • completionKummerClass F B a x := by
  let k : ℕ := (PadicInt.toZModPow a r).val
  have hd : (2 : ℤ_[2]) ^ a ∣ r - (k : ℤ_[2]) := by
    simpa only [k, PadicInt.val_toZModPow_eq_appr, Nat.cast_ofNat] using PadicInt.dvd_sub_appr r a
  obtain ⟨s, hs⟩ := hd
  have hmem : r • x - k • x ∈ nSub ((2 : ℤ_[2]) ^ a) (PointCompletion B.toAffine.Point) := by
    rw [← Nat.cast_smul_eq_nsmul (R := ℤ_[2]), ← sub_smul, hs, mul_smul]
    exact mem_nSub.mpr ⟨s • x, rfl⟩
  have hq : (Submodule.Quotient.mk (r • x) :
      PointCompletion B.toAffine.Point ⧸ nSub ((2 : ℤ_[2]) ^ a) (PointCompletion B.toAffine.Point)) =
      k • Submodule.Quotient.mk x := by
    rw [← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.eq _).2 hmem
  change hOneToAlg F B (2 ^ a) (B.kummerClassMap (2 ^ a) _
      (completionQuotientEquiv B.toAffine.Point a (Submodule.Quotient.mk (r • x)))) =
    k • hOneToAlg F B (2 ^ a) (B.kummerClassMap (2 ^ a) _
      (completionQuotientEquiv B.toAffine.Point a (Submodule.Quotient.mk x)))
  simp only [hq, map_nsmul]

/-- The fixed based degree-one integral Kummer lift is formed from the genuine completed-point Kummer cycles of the fixed basis images. -/
def basedKummerOne (r : ℕ) (g : (Fin r → ℤ_[2]) →ₗ[ℤ_[2]] PointCompletion B.toAffine.Point) :
    (Fin r → ℤ_[2]) →ₗ[ℤ_[2]] LinearMap.ker ((actualIntegralComplex F B).d 1 2).hom :=
  Fintype.linearCombination ℤ_[2]
    (fun i => integralKummerCycle F B (g (Pi.single i 1)))

/-- Reduction of the actual based degree-one Kummer lift is exactly the genuine Kummer class of its prescribed completed point. -/
theorem basedKummerOne_reduction (r : ℕ)
    (g : (Fin r → ℤ_[2]) →ₗ[ℤ_[2]] PointCompletion B.toAffine.Point)
    (a : ℕ) (u : Fin r → ℤ_[2]) :
    actualH1Reduction F B a (basedKummerOne F B r g u) = completionKummerClass F B a (g u) := by
  have hu : (∑ i : Fin r, u i • (Pi.single i 1 : Fin r → ℤ_[2])) = u := by
    ext j
    simp [Pi.single_apply]
  calc
    actualH1Reduction F B a (basedKummerOne F B r g u) =
        ∑ i : Fin r, (PadicInt.toZModPow a (u i)).val •
          completionKummerClass F B a (g (Pi.single i 1)) := by
      simp only [basedKummerOne, Fintype.linearCombination_apply, map_sum,
        actualH1Reduction_smul, integralKummerCycle_reduction]
    _ = completionKummerClass F B a (∑ i : Fin r, u i • g (Pi.single i 1)) := by
      simp only [map_sum, completionKummerClass_smul]
    _ = completionKummerClass F B a (g u) := by
      congr 1
      simpa only [map_sum, map_smul] using congrArg g hu

end Elliptic

section CompactPrimitives

variable (G A : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup A] [DistribMulAction G A] [TopologicalSpace A] [DiscreteTopology A]
  [ContinuousSMul G A] [CompactSpace (IntegralTateCoeff G A)]

/-- Fixed finite primitives lift to a genuine integral degree-zero primitive by compactness of the actual Tate coefficient module. -/
theorem integral_one_boundary_of_finite_boundaries
    (hproj : ∀ a : ℕ, Function.Surjective (coefficientProjection G A a))
    (c : (integralComplex G A).X 1)
    (hzero : ∀ a : ℕ, ∃ b : (finiteIntegralComplex G A a).X 0,
      ((finiteIntegralComplex G A a).d 0 1).hom b = ((reduceCochains G A a).f 1).hom c) :
    ∃ b : (integralComplex G A).X 0, ((integralComplex G A).d 0 1).hom b = c := by
  let S : ℕ → Set (IntegralTateCoeff G A) := fun a => {x | ∀ σ : G,
    σ • coefficientProjection G A a x - coefficientProjection G A a x =
      cfun (((reduceCochains G A a).f 1).hom c) (fun _ => σ)}
  have hclosed (a : ℕ) : IsClosed (S a) := by
    have hS : S a = ⋂ σ : G, {x | σ • coefficientProjection G A a x - coefficientProjection G A a x =
        cfun (((reduceCochains G A a).f 1).hom c) (fun _ => σ)} := by
      ext x
      simp only [S, Set.mem_setOf_eq, Set.mem_iInter]
    rw [hS]
    exact isClosed_iInter fun σ => isClosed_eq
      (((coefficientProjection_continuous G A a).const_smul σ).sub
        (coefficientProjection_continuous G A a)) continuous_const
  have hnonempty (a : ℕ) : (S a).Nonempty := by
    obtain ⟨b, hb⟩ := hzero a
    obtain ⟨x, hx⟩ := hproj a (cfun b Fin.elim0)
    refine ⟨x, ?_⟩
    intro σ
    rw [hx]
    have h := congrArg (fun y => cfun y (fun _ => σ)) hb
    exact (contFun_d01 (k := ℤ_[2]) (G := G) (M := FiniteTateCoeff G A a) b σ).symm.trans h
  have hstep (a : ℕ) : S (a + 1) ⊆ S a := by
    intro x hx σ
    have h := congrArg (coefficientTransition G A a) (hx σ)
    simp only [map_sub, coefficientTransition_smul, coefficientProjection_succ] at h
    have hc := congrArg (fun y => cfun y (fun _ => σ)) (reduceCochains_succ G A a 1 c)
    exact h.trans hc
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    S hstep hnonempty (hclosed 0).isCompact hclosed
  let b : (integralComplex G A).X 0 := ⟨fun _ => x, continuous_const⟩
  refine ⟨b, ?_⟩
  apply integralCochain_ext G A 1
  intro a
  rw [reduceCochains_d]
  apply contCochains_ext
  intro s
  have hs : s = fun _ => s 0 := by
    funext i
    have hi : i = 0 := by
      apply Fin.ext
      omega
    rw [hi]
  rw [hs, contFun_d01]
  exact (Set.mem_iInter.mp hx a) (s 0)

end CompactPrimitives

section EllipticPrimitives

variable (F : Type) [Field F] [CharZero F] [DecidableEq F]
  (B : WeierstrassCurve F) [B.IsElliptic]

/-- The actual geometric Tate levels have the genuine elliptic-curve torsion cardinalities. -/
theorem geometricLevel_card (a : ℕ) : Nat.card (TateModuleLevel 2 (PtAlg F B) a) = (2 ^ a) ^ 2 := by
  let e := AddEquiv.torsionByCongr (ptEquiv F B) ((2 ^ a : ℕ) : ℤ)
  calc
    Nat.card (TateModuleLevel 2 (PtAlg F B) a) =
        Nat.card (TateModuleLevel 2 (B.baseChange (AlgebraicClosure F)).toAffine.Point a) :=
      Nat.card_congr e.symm.toEquiv
    _ = (2 ^ a) ^ 2 := (B.baseChange (AlgebraicClosure F)).natCard_tateModuleLevel two_ne_zero a

/-- The fixed genuine integral point-coefficient projections are surjective. -/
theorem actualCoefficientProjection_surjective (a : ℕ) :
    Function.Surjective (coefficientProjection (Field.absoluteGaloisGroup F) (PtAlg F B) a) :=
  TateModule.proj_surjective
    (TateModule.tateModuleTransition_surjective_of_natCard (by decide) (geometricLevel_card F B)) a

/-- The genuine geometric integral coefficient module is compact. -/
theorem actualIntegralCoeff_compact :
    CompactSpace (IntegralTateCoeff (Field.absoluteGaloisGroup F) (PtAlg F B)) := by
  haveI (a : ℕ) : Finite (TateModuleLevel 2 (PtAlg F B) a) :=
    Nat.finite_of_card_ne_zero (by rw [geometricLevel_card F B]; positivity)
  exact inferInstanceAs (CompactSpace (TateModule 2 (PtAlg F B)))

/-- The fixed finite class reduction is zero precisely when the projected genuine class is zero. -/
theorem actualH1Reduction_eq_zero_iff (a : ℕ)
    (c : LinearMap.ker ((actualIntegralComplex F B).d 1 2).hom) :
    actualH1Reduction F B a c = 0 ↔
      kerToH1 (reduceOneCycle (Field.absoluteGaloisGroup F) (PtAlg F B) a c) = 0 :=
  (explicitCoeff1Equiv (Field.absoluteGaloisGroup F)
    (FiniteTateCoeff (Field.absoluteGaloisGroup F) (PtAlg F B) a) (actualLevelEquiv F B a)
    continuous_of_discreteTopology continuous_of_discreteTopology (actualLevelEquiv_smul F B a)).map_eq_zero_iff

/-- The genuine integral one-cocycle boundary criterion, using the fixed actual reductions and actual coefficient compactness. -/
theorem actualH1Reduction_all_zero_iff_boundary
    (c : LinearMap.ker ((actualIntegralComplex F B).d 1 2).hom) :
    (∀ a : ℕ, actualH1Reduction F B a c = 0) ↔
      ∃ b : (actualIntegralComplex F B).X 0, ((actualIntegralComplex F B).d 0 1).hom b = c.val := by
  constructor
  · intro hzero
    haveI := actualIntegralCoeff_compact F B
    apply integral_one_boundary_of_finite_boundaries (Field.absoluteGaloisGroup F) (PtAlg F B)
      (actualCoefficientProjection_surjective F B) c.val
    intro a
    exact (kerToH1_eq_zero_iff _).1 ((actualH1Reduction_eq_zero_iff F B a c).1 (hzero a))
  · rintro ⟨b, hb⟩ a
    apply (actualH1Reduction_eq_zero_iff F B a c).2
    apply (kerToH1_eq_zero_iff _).2
    refine ⟨((reduceCochains (Field.absoluteGaloisGroup F) (PtAlg F B) a).f 0).hom b, ?_⟩
    change ((finiteIntegralComplex (Field.absoluteGaloisGroup F) (PtAlg F B) a).d 0 1).hom
      (((reduceCochains (Field.absoluteGaloisGroup F) (PtAlg F B) a).f 0).hom b) =
        ((reduceCochains (Field.absoluteGaloisGroup F) (PtAlg F B) a).f 1).hom c.val
    rw [← reduceCochains_d, hb]

/-- A relation of the actual completed-point presentation has a genuine integral degree-zero primitive. -/
theorem basedKummerOne_relation (r1 r0 : ℕ)
    (f : (Fin r1 → ℤ_[2]) →ₗ[ℤ_[2]] (Fin r0 → ℤ_[2]))
    (g : (Fin r0 → ℤ_[2]) →ₗ[ℤ_[2]] PointCompletion B.toAffine.Point)
    (hfg : g.comp f = 0) (u : Fin r1 → ℤ_[2]) :
    ∃ b : (actualIntegralComplex F B).X 0,
      ((actualIntegralComplex F B).d 0 1).hom b = (basedKummerOne F B r0 g (f u)).val := by
  apply (actualH1Reduction_all_zero_iff_boundary F B _).1
  intro a
  rw [basedKummerOne_reduction]
  have h := LinearMap.congr_fun hfg u
  change g (f u) = 0 at h
  rw [h, map_zero]

/-- The fixed primitive of an actual presentation relation. -/
def relationPrimitive (r1 r0 : ℕ)
    (f : (Fin r1 → ℤ_[2]) →ₗ[ℤ_[2]] (Fin r0 → ℤ_[2]))
    (g : (Fin r0 → ℤ_[2]) →ₗ[ℤ_[2]] PointCompletion B.toAffine.Point)
    (hfg : g.comp f = 0) (u : Fin r1 → ℤ_[2]) : (actualIntegralComplex F B).X 0 :=
  (basedKummerOne_relation F B r1 r0 f g hfg u).choose

/-- The fixed relation primitive realizes the prescribed genuine integral Kummer relation. -/
theorem relationPrimitive_d (r1 r0 : ℕ)
    (f : (Fin r1 → ℤ_[2]) →ₗ[ℤ_[2]] (Fin r0 → ℤ_[2]))
    (g : (Fin r0 → ℤ_[2]) →ₗ[ℤ_[2]] PointCompletion B.toAffine.Point)
    (hfg : g.comp f = 0) (u : Fin r1 → ℤ_[2]) :
    ((actualIntegralComplex F B).d 0 1).hom (relationPrimitive F B r1 r0 f g hfg u) =
      (basedKummerOne F B r0 g (f u)).val :=
  (basedKummerOne_relation F B r1 r0 f g hfg u).choose_spec

/-- The fixed based degree-zero map of the actual integral Kummer presentation. -/
def basedKummerZero (r1 r0 : ℕ)
    (f : (Fin r1 → ℤ_[2]) →ₗ[ℤ_[2]] (Fin r0 → ℤ_[2]))
    (g : (Fin r0 → ℤ_[2]) →ₗ[ℤ_[2]] PointCompletion B.toAffine.Point)
    (hfg : g.comp f = 0) : (Fin r1 → ℤ_[2]) →ₗ[ℤ_[2]] (actualIntegralComplex F B).X 0 :=
  Fintype.linearCombination ℤ_[2]
    (fun i => relationPrimitive F B r1 r0 f g hfg (Pi.single i 1))

/-- The actual based degree-zero and degree-one maps satisfy the genuine cochain comparison square. -/
theorem basedKummerZero_d (r1 r0 : ℕ)
    (f : (Fin r1 → ℤ_[2]) →ₗ[ℤ_[2]] (Fin r0 → ℤ_[2]))
    (g : (Fin r0 → ℤ_[2]) →ₗ[ℤ_[2]] PointCompletion B.toAffine.Point)
    (hfg : g.comp f = 0) (u : Fin r1 → ℤ_[2]) :
    ((actualIntegralComplex F B).d 0 1).hom (basedKummerZero F B r1 r0 f g hfg u) =
      (basedKummerOne F B r0 g (f u)).val := by
  have hu : (∑ i : Fin r1, u i • (Pi.single i 1 : Fin r1 → ℤ_[2])) = u := by
    ext j
    simp [Pi.single_apply]
  let K : (Fin r0 → ℤ_[2]) →ₗ[ℤ_[2]] (actualIntegralComplex F B).X 1 :=
    (LinearMap.ker ((actualIntegralComplex F B).d 1 2).hom).subtype.comp
      (basedKummerOne F B r0 g)
  calc
    ((actualIntegralComplex F B).d 0 1).hom (basedKummerZero F B r1 r0 f g hfg u) =
        ∑ i : Fin r1, u i • (basedKummerOne F B r0 g (f (Pi.single i 1))).val := by
      simp only [basedKummerZero, Fintype.linearCombination_apply, map_sum, map_smul,
        relationPrimitive_d]
    _ = (basedKummerOne F B r0 g (f u)).val := by
      simpa only [K, LinearMap.comp_apply, map_sum, map_smul, Submodule.subtype_apply] using congrArg (K.comp f) hu

end EllipticPrimitives

section ActualLocalKummer

open NumberField IsDedekindDomain

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]

/-- The degree-one map for the fixed actual local completed-point presentation. -/
def actualLocalKummerOne :
    (Fin (actualLocalPresentation K w B).rankZero → ℤ_[2]) →ₗ[ℤ_[2]]
      LinearMap.ker ((actualIntegralComplex (w.adicCompletion K) B).d 1 2).hom :=
  basedKummerOne (w.adicCompletion K) B (actualLocalPresentation K w B).rankZero
    (actualLocalPresentation K w B).g

/-- The degree-zero map for the same fixed actual local presentation. -/
def actualLocalKummerZero :
    (Fin (actualLocalPresentation K w B).rankOne → ℤ_[2]) →ₗ[ℤ_[2]]
      (actualIntegralComplex (w.adicCompletion K) B).X 0 :=
  basedKummerZero (w.adicCompletion K) B (actualLocalPresentation K w B).rankOne
    (actualLocalPresentation K w B).rankZero (actualLocalPresentation K w B).f
    (actualLocalPresentation K w B).g (actualLocalPresentation K w B).complex

/-- The actual local maps satisfy the genuine integral cochain square of the actual presentation. -/
theorem actualLocalKummerZero_d
    (u : Fin (actualLocalPresentation K w B).rankOne → ℤ_[2]) :
    ((actualIntegralComplex (w.adicCompletion K) B).d 0 1).hom (actualLocalKummerZero K w B u) =
      (actualLocalKummerOne K w B ((actualLocalPresentation K w B).f u)).val :=
  basedKummerZero_d (w.adicCompletion K) B _ _ _ _ _ u

/-- The fixed genuine finite reduction of the actual local degree-one cochain map. -/
def actualLocalReduction (a : ℕ) :
    (Fin (actualLocalPresentation K w B).rankZero → ℤ_[2]) →+
      H1 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff (2 ^ a)) :=
  (hOneToAlg (w.adicCompletion K) B (2 ^ a)).symm.toAddMonoidHom.comp
    ((actualH1Reduction (w.adicCompletion K) B a).comp
      (actualLocalKummerOne K w B).toAddMonoidHom)

/-- The fixed actual local reduction is exactly the genuine Kummer map of its fixed rational representative. -/
theorem actualLocalReduction_apply (a : ℕ)
    (u : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2]) :
    actualLocalReduction K w B a u = B.kummerMap (2 ^ a)
      (isUnit_iff_ne_zero.mpr (natCast_ne_zero_of_charZero (w.adicCompletion K) (2 ^ a)))
      (representatives B.toAffine.Point ((actualLocalPresentation K w B).g u) a) := by
  change (hOneToAlg (w.adicCompletion K) B (2 ^ a)).symm
    (actualH1Reduction (w.adicCompletion K) B a
      (basedKummerOne (w.adicCompletion K) B (actualLocalPresentation K w B).rankZero
        (actualLocalPresentation K w B).g u)) = _
  rw [basedKummerOne_reduction, completionKummerClass_representatives,
    (hOneToAlg (w.adicCompletion K) B (2 ^ a)).symm_apply_apply]

/-- The classes of the fixed actual integral local cochain map lie in the genuine Kummer image at every finite level. -/
theorem actualLocalReduction_mem_genuine_Kummer (a : ℕ)
    (u : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2]) :
    actualLocalReduction K w B a u ∈ (B.kummerMap (2 ^ a)
      (isUnit_iff_ne_zero.mpr (natCast_ne_zero_of_charZero (w.adicCompletion K) (2 ^ a)))).range := by
  refine ⟨representatives B.toAffine.Point ((actualLocalPresentation K w B).g u) a, ?_⟩
  exact (actualLocalReduction_apply K w B a u).symm

end ActualLocalKummer

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.WeilLevel

open WeierstrassCurve WeierstrassCurve.Affine TauCeti TauCeti.Isogeny AlgebraicGeometry IsDedekindDomain

variable {F : Type} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- Every function-field pullback fixes actual constant points. -/
theorem map_constant_point (φ : Isogeny W W) (P : (W⁄F).toAffine.Point) :
    Point.map φ.fieldPullback (Point.baseChange (W' := W) F W.FunctionField P) =
      Point.baseChange (W' := W) F W.FunctionField P := by
  change Point.map φ.fieldPullback (Point.map (Algebra.ofId F W.FunctionField) P) = _
  rw [Point.map_map]
  have h : φ.fieldPullback.comp (Algebra.ofId F W.FunctionField) = Algebra.ofId F W.FunctionField :=
    Subsingleton.elim _ _
  rw [h]

/-- Multiplication pullback intertwines translation by a point with translation by its multiple. -/
theorem multiplication_translation {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    (P : (W⁄F).toAffine.Point) :
    (translation W P).toAlgHom.comp (mulByIntIsogeny W hn).fieldPullback =
      (mulByIntIsogeny W hn).fieldPullback.comp (translation W (n • P)).toAlgHom := by
  apply map_genericPoint_injective W
  change Point.map ((translation W P).toAlgHom.comp (mulByIntIsogeny W hn).fieldPullback) W.genericPoint =
    Point.map ((mulByIntIsogeny W hn).fieldPullback.comp (translation W (n • P)).toAlgHom) W.genericPoint
  rw [← Point.map_map, ← Point.map_map, map_mulByIntIsogeny_genericPoint,
    map_zsmul, map_translation_genericPoint, translatedGenericPoint_def,
    zsmul_add, map_translation_genericPoint, translatedGenericPoint_def, map_add,
    map_mulByIntIsogeny_genericPoint, map_constant_point, ← map_zsmul]

/-- Pullback of actual divisors with the actual function-field algebra structure fixed explicitly. -/
def pullDivisor (φ : Isogeny W W) : Divisor F W.FunctionField →+ Divisor F W.FunctionField :=
  letI := φ.fieldPullback.toRingHom.toAlgebra
  φ.divisorPullback (fun _ => rfl)

/-- Actual divisor pullback is contravariantly compatible with composition. -/
theorem pullDivisor_comp (φ ψ : Isogeny W W) (D : Divisor F W.FunctionField) :
    pullDivisor W φ (pullDivisor W ψ D) = pullDivisor W (ψ.comp φ) D :=
  @Isogeny.divisorPullback_comp F _ W W φ φ.fieldPullback.toRingHom.toAlgebra (fun _ => rfl)
    W ψ ψ.fieldPullback.toRingHom.toAlgebra (ψ.comp φ).fieldPullback.toRingHom.toAlgebra
    (fun _ => rfl) (fun _ => rfl) D

/-- Actual pullback carries a principal divisor to the divisor of the genuine pulled-back function. -/
theorem pullDivisor_principal (φ : Isogeny W W) (g : W.FunctionFieldˣ) :
    pullDivisor W φ (Divisor.principal W.isFunctionField g) =
      Divisor.principal W.isFunctionField (Units.map φ.fieldPullback.toMonoidHom g) :=
  @Isogeny.divisorPullback_principal F _ W W φ φ.fieldPullback.toRingHom.toAlgebra (fun _ => rfl) g

/-- The actual divisor difference of a point and the origin. -/
def pointDifference (Q : W.Point) : Divisor F W.FunctionField :=
  WeilDivisor.ofPoint (W.pointEquivDegreeOnePlace Q).1 - WeilDivisor.ofPoint (Place.infinity W)

/-- The divisor used by the actual Weil pairing at an integral multiplication index. -/
def levelDivisor {n : ℤ} (hn : psiFunctionField W n ≠ 0) (Q : W.Point) : Divisor F W.FunctionField :=
  pullDivisor W (mulByIntIsogeny W hn) (pointDifference W Q)

/-- The explicit actual pullback description is the genuine Weil-pairing divisor. -/
theorem levelDivisor_eq_weil {n : ℤ} (hn : psiFunctionField W n ≠ 0) (Q : W.Point) :
    levelDivisor W hn Q = Isogeny.weilPairingDivisor W hn Q := by
  rw [Isogeny.weilPairingDivisor_def]
  change pullDivisor W (mulByIntIsogeny W hn)
      (WeilDivisor.ofPoint (W.pointEquivDegreeOnePlace Q).1 - WeilDivisor.ofPoint (Place.infinity W)) =
    pullDivisor W (mulByIntIsogeny W hn) (WeilDivisor.ofPoint (W.pointEquivDegreeOnePlace Q).1) -
      pullDivisor W (mulByIntIsogeny W hn) (WeilDivisor.ofPoint (Place.infinity W))
  exact map_sub _ _ _

/-- Pulling back a genuine Weil-pairing divisor changes its multiplication index by composition. -/
theorem levelDivisor_mul {n m : ℤ} (hn : psiFunctionField W n ≠ 0)
    (hm : psiFunctionField W m ≠ 0) (hnm : psiFunctionField W (n * m) ≠ 0) (Q : W.Point) :
    pullDivisor W (mulByIntIsogeny W hm) (levelDivisor W hn Q) = levelDivisor W hnm Q := by
  change pullDivisor W (mulByIntIsogeny W hm)
      (pullDivisor W (mulByIntIsogeny W hn) (pointDifference W Q)) =
    pullDivisor W (mulByIntIsogeny W hnm) (pointDifference W Q)
  rw [pullDivisor_comp, mulByIntIsogeny_comp_mulByIntIsogeny W hn hm hnm]

section ChangeOfLevel

variable (N m : ℕ)

/-- The actual inclusion of lower-level torsion in a higher multiplication level. -/
def torsionInclude (T : AddSubgroup.torsionBy W.Point (N : ℤ)) :
    AddSubgroup.torsionBy W.Point ((N * m : ℕ) : ℤ) :=
  ⟨T.val, by
    rw [AddSubgroup.torsionBy.nsmul_iff, Nat.mul_comm, mul_nsmul',
      AddSubgroup.torsionBy.nsmul_iff.mp T.2, smul_zero]⟩

/-- The actual coefficient transition multiplies a geometric torsion point by the level ratio. -/
def torsionMultiply (S : AddSubgroup.torsionBy W.Point ((N * m : ℕ) : ℤ)) :
    AddSubgroup.torsionBy W.Point (N : ℤ) :=
  ⟨(m : ℕ) • S.val, by
    rw [AddSubgroup.torsionBy.nsmul_iff, ← mul_nsmul']
    exact AddSubgroup.torsionBy.nsmul_iff.mp S.2⟩

variable [IsSepClosed F] [NeZero N] [NeZero m]
  (hN : (N : F) ≠ 0) (hm : (m : F) ≠ 0)

/-- The genuine Weil pairing at a composite level restricts to the lower-level pairing after multiplying its first argument by the level ratio. -/
theorem weilPairing_change_level
    (S : AddSubgroup.torsionBy W.Point ((N * m : ℕ) : ℤ))
    (T : AddSubgroup.torsionBy W.Point (N : ℤ)) :
    ((Isogeny.weilPairing W (N * m) (by simpa only [Nat.cast_mul] using mul_ne_zero hN hm)
      S (torsionInclude W N m T)).toMul : Fˣ) =
      ((Isogeny.weilPairing W N hN (torsionMultiply W N m S) T).toMul : Fˣ) := by
  have hNI : ((N : ℤ) : F) ≠ 0 := by simpa only [Int.cast_natCast] using hN
  have hmI : ((m : ℤ) : F) ≠ 0 := by simpa only [Int.cast_natCast] using hm
  let hn := psiFunctionField_ne_zero W hNI
  let hmi := psiFunctionField_ne_zero W hmI
  have hnmi : psiFunctionField W ((N : ℤ) * (m : ℤ)) ≠ 0 :=
    psiFunctionField_ne_zero W (by simpa only [Int.cast_mul] using mul_ne_zero hNI hmI)
  have hT : (N : ℤ) • T.val = 0 := by
    rw [natCast_zsmul]
    exact AddSubgroup.torsionBy.nsmul_iff.mp T.2
  obtain ⟨g, hg⟩ := exists_principal_eq_weilPairingDivisor W hNI hT
  let φ := mulByIntIsogeny W hmi
  let g' : W.FunctionFieldˣ := Units.map φ.fieldPullback.toMonoidHom g
  have hg' : Divisor.principal W.isFunctionField g' =
      Isogeny.weilPairingDivisor W hnmi (torsionInclude W N m T).val := by
    rw [← pullDivisor_principal, hg, ← levelDivisor_eq_weil, levelDivisor_mul W hn hmi hnmi,
      levelDivisor_eq_weil]
    rfl
  apply Units.ext
  apply (algebraMap F W.FunctionField).injective
  rw [Isogeny.algebraMap_weilPairing W (N * m) _ hg', Isogeny.algebraMap_weilPairing W N hN hg]
  have htranslation := multiplication_translation W hmi (Point.equivBaseChangeSelf W S.val)
  have hp : (m : ℤ) • Point.equivBaseChangeSelf W S.val =
      Point.equivBaseChangeSelf W ((m : ℕ) • S.val) := by
    rw [← map_zsmul, natCast_zsmul]
  rw [hp] at htranslation
  have ht := congrArg (fun f : W.FunctionField →ₐ[F] W.FunctionField => f (g : W.FunctionField)) htranslation
  change translation W (Point.equivBaseChangeSelf W S.val) (φ.fieldPullback g) =
      φ.fieldPullback (translation W (Point.equivBaseChangeSelf W ((m : ℕ) • S.val)) g) at ht
  change translation W (Point.equivBaseChangeSelf W S.val) (φ.fieldPullback g) / φ.fieldPullback g = _
  have hlow : algebraMap F W.FunctionField
      ((Isogeny.weilPairing W N hN (torsionMultiply W N m S) T).toMul : Fˣ) =
        translation W (Point.equivBaseChangeSelf W ((m : ℕ) • S.val)) g / g :=
    Isogeny.algebraMap_weilPairing W N hN (S := torsionMultiply W N m S) (T := T) hg
  rw [ht, ← map_div₀]
  change φ.fieldPullback
      (translation W (Point.equivBaseChangeSelf W ((m : ℕ) • S.val)) g / g) =
    translation W (Point.equivBaseChangeSelf W ((m : ℕ) • S.val)) g / g
  rw [← hlow]
  exact φ.fieldPullback.commutes _

/-- Multiplying both actual torsion arguments by the level ratio reduces the genuine Weil pairing by the same power. -/
theorem weilPairing_multiplication_transition
    (S T : AddSubgroup.torsionBy W.Point ((N * m : ℕ) : ℤ)) :
    ((Isogeny.weilPairing W N hN (torsionMultiply W N m S) (torsionMultiply W N m T)).toMul : Fˣ) =
      ((Isogeny.weilPairing W (N * m) (by simpa only [Nat.cast_mul] using mul_ne_zero hN hm) S T).toMul : Fˣ) ^ m := by
  rw [← weilPairing_change_level W N m hN hm S (torsionMultiply W N m T)]
  have h : torsionInclude W N m (torsionMultiply W N m T) = (m : ℕ) • T := Subtype.ext rfl
  rw [h, map_nsmul, toMul_nsmul, SubmonoidClass.coe_pow]

end ChangeOfLevel

section TatePairing

variable [IsSepClosed F] [CharZero F]

/-- Changing an equal coefficient index and equal underlying torsion points does not change the genuine Weil value. -/
theorem weilPairing_index_congr {N M : ℕ} [NeZero N] [NeZero M] (h : N = M)
    (hN : (N : F) ≠ 0) (hM : (M : F) ≠ 0)
    (S T : AddSubgroup.torsionBy W.Point (N : ℤ))
    (S' T' : AddSubgroup.torsionBy W.Point (M : ℤ))
    (hS : S.val = S'.val) (hT : T.val = T'.val) :
    ((Isogeny.weilPairing W N hN S T).toMul : Fˣ) =
      ((Isogeny.weilPairing W M hM S' T').toMul : Fˣ) := by
  subst M
  have hs : S = S' := Subtype.ext hS
  have ht : T = T' := Subtype.ext hT
  subst S'
  subst T'
  rfl

/-- The genuine inclusion of roots of unity into the corresponding torsion level of multiplicative coefficients. -/
def rootsAsLevel (N : ℕ) : Additive (rootsOfUnity N F) →+ AddSubgroup.torsionBy (Additive Fˣ) (N : ℤ) where
  toFun z := ⟨Additive.ofMul (z.toMul : Fˣ), by
    apply AddSubgroup.torsionBy.nsmul_iff.mpr
    apply Additive.toMul.injective
    change (z.toMul : Fˣ) ^ N = 1
    exact (mem_rootsOfUnity N _).mp z.toMul.2⟩
  map_zero' := Subtype.ext rfl
  map_add' z z' := Subtype.ext rfl

/-- The actual finite Weil pairing, with its values read in the genuine multiplicative Tate level. -/
def finiteWeilLevel (a : ℕ) : TateModuleLevel 2 W.Point a →+ TateModuleLevel 2 W.Point a →+
    TateModuleLevel 2 (Additive Fˣ) a :=
  (AddMonoidHom.compHom (rootsAsLevel (F := F) (2 ^ a))).comp
    (Isogeny.weilPairing W (2 ^ a) (Nat.cast_ne_zero.mpr (pow_ne_zero _ (by decide))))

/-- The actual finite Weil values are compatible with the genuine Tate-module transitions. -/
theorem finiteWeilLevel_transition (a : ℕ)
    (S T : TateModuleLevel 2 W.Point (a + 1)) :
    tateModuleTransition 2 (Additive Fˣ) a (finiteWeilLevel W (a + 1) S T) =
      finiteWeilLevel W a (tateModuleTransition 2 W.Point a S) (tateModuleTransition 2 W.Point a T) := by
  let S' : AddSubgroup.torsionBy W.Point (((2 ^ a : ℕ) * 2 : ℕ) : ℤ) :=
    ⟨S.val, by simpa only [pow_succ] using S.2⟩
  let T' : AddSubgroup.torsionBy W.Point (((2 ^ a : ℕ) * 2 : ℕ) : ℤ) :=
    ⟨T.val, by simpa only [pow_succ] using T.2⟩
  have hN : (2 ^ a : F) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hN' : ((2 ^ a : ℕ) : F) ≠ 0 := by simpa using hN
  have hbig : ((2 ^ (a + 1) : ℕ) : F) ≠ 0 := by simp
  have hprod : (((2 ^ a : ℕ) * 2 : ℕ) : F) ≠ 0 := by simp
  have hindex := weilPairing_index_congr W (pow_succ 2 a) hbig hprod S T S' T' rfl rfl
  have h := weilPairing_multiplication_transition W (2 ^ a) 2 hN' two_ne_zero S' T'
  apply Subtype.ext
  apply Additive.toMul.injective
  change ((Isogeny.weilPairing W (2 ^ (a + 1)) hbig S T).toMul : Fˣ) ^ 2 =
    ((Isogeny.weilPairing W (2 ^ a) hN' (tateModuleTransition 2 W.Point a S)
      (tateModuleTransition 2 W.Point a T)).toMul : Fˣ)
  rw [hindex, ← h]
  rfl

/-- The genuine integral Weil value is the compatible family of actual finite Weil values. -/
def tateWeilValue (x y : TateModule 2 W.Point) : TateModule 2 (Additive Fˣ) :=
  TateModule.mk (fun a => finiteWeilLevel W a (TateModule.proj a x) (TateModule.proj a y)) (fun a => by
    rw [finiteWeilLevel_transition, TateModule.proj_succ, TateModule.proj_succ])

/-- Integral Weil projection is exactly the actual finite Weil pairing. -/
theorem tateWeilValue_projection (x y : TateModule 2 W.Point) (a : ℕ) :
    TateModule.proj a (tateWeilValue W x y) = finiteWeilLevel W a (TateModule.proj a x) (TateModule.proj a y) := rfl

/-- The genuine integral Weil pairing is bilinear over the actual two-adic scalar ring. -/
def tateWeilBilin : TateModule 2 W.Point →ₗ[ℤ_[2]] TateModule 2 W.Point →ₗ[ℤ_[2]] TateModule 2 (Additive Fˣ) :=
  LinearMap.mk₂ ℤ_[2] (tateWeilValue W)
    (fun x x' y => by
      apply TateModule.ext
      intro a
      simp only [tateWeilValue_projection, map_add, AddMonoidHom.add_apply])
    (fun r x y => by
      apply TateModule.ext
      intro a
      simp only [tateWeilValue_projection, TateModule.proj_smul]
      exact ZMod.map_smul ((finiteWeilLevel W a).flip (TateModule.proj a y))
        (PadicInt.toZModPow a r) (TateModule.proj a x))
    (fun x y y' => by
      apply TateModule.ext
      intro a
      simp only [tateWeilValue_projection, map_add])
    (fun r x y => by
      apply TateModule.ext
      intro a
      simp only [tateWeilValue_projection, TateModule.proj_smul]
      exact ZMod.map_smul (finiteWeilLevel W a (TateModule.proj a x))
        (PadicInt.toZModPow a r) (TateModule.proj a y))

/-- The bilinear integral pairing is the genuine compatible finite Weil family. -/
theorem tateWeilBilin_apply (x y : TateModule 2 W.Point) :
    tateWeilBilin W x y = tateWeilValue W x y := rfl

/-- The genuine integral Weil pairing is jointly continuous for the inverse-limit topologies. -/
theorem continuous_tateWeilValue :
    Continuous (fun p : TateModule 2 W.Point × TateModule 2 W.Point => tateWeilValue W p.1 p.2) := by
  apply TateModule.continuous_iff.mpr
  intro a
  have h1 : IsLocallyConstant (fun p : TateModule 2 W.Point × TateModule 2 W.Point => TateModule.proj a p.1) :=
    (TateModule.isLocallyConstant_proj a).comp_continuous continuous_fst
  have h2 : IsLocallyConstant (fun p : TateModule 2 W.Point × TateModule 2 W.Point => TateModule.proj a p.2) :=
    (TateModule.isLocallyConstant_proj a).comp_continuous continuous_snd
  exact h1.comp₂ h2 (fun x y => finiteWeilLevel W a x y)

end TatePairing

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.WeilLevel

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing

open CategoryTheory TauCeti TauCeti.ContCohomology
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.WeilLevel
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules

variable (F : Type) [Field F] [CharZero F] [DecidableEq F]
  (B : WeierstrassCurve F) [B.IsElliptic]

/-- The actual integral Tate coefficients in the separable-closure description. -/
abbrev pointTate := IntegralTateCoeff (AbsoluteGaloisGroup F) B.PointCoeff

/-- The actual integral roots-of-unity Tate coefficients of the local trace target. -/
abbrev muTate := IntegralTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F)

/-- The canonical actual point-coefficient dictionary induces the genuine integral geometric dictionary. -/
def pointTateToGeometric : pointTate F B →ₗ[ℤ_[2]]
    TateModule 2 (B.baseChange (SeparableClosure F)).toAffine.Point :=
  TateModule.mapLinearMap B.pointCoeffEquiv.symm.toAddMonoidHom

/-- The integral pairing on the actual point-coefficient Tate modules is the genuine integral Weil pairing. -/
def coefficientWeilPairing : pointTate F B →ₗ[ℤ_[2]] pointTate F B →ₗ[ℤ_[2]] muTate F :=
  ((tateWeilBilin (B.baseChange (SeparableClosure F))).compl₂ (pointTateToGeometric F B)).comp
    (pointTateToGeometric F B)

/-- The genuine finite point-coefficient dictionary in the separable-closure description. -/
def pointLevelEquiv (a : ℕ) : FiniteTateCoeff (AbsoluteGaloisGroup F) B.PointCoeff a ≃+
    B.TorsionCoeff (2 ^ a) := AddEquiv.refl _

/-- The finite point-coefficient dictionary intertwines the actual Galois action. -/
theorem pointLevelEquiv_smul (a : ℕ) (σ : AbsoluteGaloisGroup F)
    (t : FiniteTateCoeff (AbsoluteGaloisGroup F) B.PointCoeff a) :
    pointLevelEquiv F B a (σ • t) = σ • pointLevelEquiv F B a t := rfl

/-- The fixed actual integral coefficient projection reduces the integral pairing to the genuine finite Weil pairing. -/
theorem coefficientWeilPairing_projection (a : ℕ) (x y : pointTate F B) :
    actualMuLevelEquiv F a (coefficientProjection (AbsoluteGaloisGroup F) (UnitsCoeff F) a
      (coefficientWeilPairing F B x y)) =
      B.torsionCoeffWeilPairing (2 ^ a) (twoPower_isUnit F a)
        (pointLevelEquiv F B a (coefficientProjection (AbsoluteGaloisGroup F) B.PointCoeff a x))
        (pointLevelEquiv F B a (coefficientProjection (AbsoluteGaloisGroup F) B.PointCoeff a y)) := by
  erw [B.torsionCoeffWeilPairing_apply (2 ^ a) (twoPower_isUnit F a)
    (Nat.cast_ne_zero.mpr (pow_ne_zero _ (by decide)))]

/-- The genuine integral pairing intertwines the actual absolute Galois action. -/
theorem coefficientWeilPairing_smul (σ : AbsoluteGaloisGroup F) (x y : pointTate F B) :
    coefficientWeilPairing F B (σ • x) (σ • y) = σ • coefficientWeilPairing F B x y := by
  apply TateModule.ext
  intro a
  apply (actualMuLevelEquiv F a).injective
  change actualMuLevelEquiv F a (coefficientProjection (AbsoluteGaloisGroup F) (UnitsCoeff F) a
      (coefficientWeilPairing F B (σ • x) (σ • y))) =
    actualMuLevelEquiv F a (coefficientProjection (AbsoluteGaloisGroup F) (UnitsCoeff F) a
      (σ • coefficientWeilPairing F B x y))
  rw [coefficientWeilPairing_projection,
    coefficientProjection_smul (AbsoluteGaloisGroup F) (UnitsCoeff F) a σ,
    actualMuLevelEquiv_smul, coefficientWeilPairing_projection,
    coefficientProjection_smul (AbsoluteGaloisGroup F) B.PointCoeff a σ x,
    coefficientProjection_smul (AbsoluteGaloisGroup F) B.PointCoeff a σ y,
    pointLevelEquiv_smul, pointLevelEquiv_smul]
  exact B.torsionCoeffWeilPairing_smul (2 ^ a) (twoPower_isUnit F a) σ _ _

/-- The actual point-coefficient Tate dictionary is continuous for the genuine inverse-limit topologies. -/
theorem pointTateToGeometric_continuous : Continuous (pointTateToGeometric F B) := by
  apply TateModule.continuous_iff.mpr
  intro a
  exact (TateModule.isLocallyConstant_proj a).comp
    (TateModule.levelMap B.pointCoeffEquiv.symm.toAddMonoidHom a)

/-- The actual integral Weil coefficient pairing is jointly continuous. -/
theorem coefficientWeilPairing_continuous :
    Continuous (fun p : pointTate F B × pointTate F B => coefficientWeilPairing F B p.1 p.2) :=
  (continuous_tateWeilValue (B.baseChange (SeparableClosure F))).comp
    ((pointTateToGeometric_continuous F B).comp continuous_fst |>.prodMk
      ((pointTateToGeometric_continuous F B).comp continuous_snd))

/-- The actual integral local cochain complex in the separable-closure description. -/
abbrev pointComplex := integralComplex (AbsoluteGaloisGroup F) B.PointCoeff

/-- The genuine integral cup product is the continuous cochain pairing induced by the actual Tate-Weil coefficients. -/
def integralCupPair : NatPair (pointComplex F B) (pointComplex F B) (actualTraceComplex F) :=
  contNatPair (coefficientWeilPairing F B) (coefficientWeilPairing_smul F B)
    (coefficientWeilPairing_continuous F B)

/-- The actual integral cup cochain in bidegree one. -/
def integralCupOne : (pointComplex F B).X 1 →ₗ[ℤ_[2]] (pointComplex F B).X 1 →ₗ[ℤ_[2]]
    (actualTraceComplex F).X 2 :=
  (integralCupPair F B).P 1 1 2 rfl

/-- The genuine integral cup product of actual one-cocycles is an actual two-cocycle. -/
theorem integralCupOne_isCycle
    (u v : LinearMap.ker ((pointComplex F B).d 1 2).hom) :
    ((actualTraceComplex F).d 2 3).hom (integralCupOne F B u.val v.val) = 0 := by
  have h := (integralCupPair F B).leib 1 1 2 rfl u.val v.val
  rw [u.2, v.2, LinearMap.map_zero₂, map_zero, smul_zero, add_zero] at h
  exact h

/-- The actual integral cup product on actual continuous one-cocycles. -/
def integralCupCycle (u v : LinearMap.ker ((pointComplex F B).d 1 2).hom) :
    LinearMap.ker ((actualTraceComplex F).d 2 3).hom :=
  ⟨integralCupOne F B u.val v.val, integralCupOne_isCycle F B u v⟩

/-- The fixed genuine finite class reduction in the separable-closure point-coefficient description. -/
def pointH1Reduction (a : ℕ) : LinearMap.ker ((pointComplex F B).d 1 2).hom →+
    H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff (2 ^ a)) :=
  (explicitCoeff1Equiv (AbsoluteGaloisGroup F)
    (FiniteTateCoeff (AbsoluteGaloisGroup F) B.PointCoeff a) (pointLevelEquiv F B a)
    continuous_of_discreteTopology continuous_of_discreteTopology (pointLevelEquiv_smul F B a)).toAddMonoidHom.comp
      (reducedOneClass (AbsoluteGaloisGroup F) B.PointCoeff a)

/-- The fixed finite one-cocycle underlying the actual point-class reduction. -/
def pointReductionZ1 (a : ℕ) (u : LinearMap.ker ((pointComplex F B).d 1 2).hom) :
    Z1 (AbsoluteGaloisGroup F) (B.TorsionCoeff (2 ^ a)) :=
  cocyclesMap1 (AbsoluteGaloisGroup F) (FiniteTateCoeff (AbsoluteGaloisGroup F) B.PointCoeff a)
    (AbsoluteGaloisGroup F) (B.TorsionCoeff (2 ^ a)) (ContinuousMonoidHom.id _)
    (pointLevelEquiv F B a).toAddMonoidHom continuous_of_discreteTopology (pointLevelEquiv_smul F B a)
    ⟨fun σ => cfun (reduceOneCycle (AbsoluteGaloisGroup F) B.PointCoeff a u).val (fun _ => σ),
      mem_Z1_of_d_eq_zero _ (reduceOneCycle (AbsoluteGaloisGroup F) B.PointCoeff a u).2⟩

/-- The fixed actual point-class reduction is the class of its specific finite cocycle. -/
theorem pointH1Reduction_class (a : ℕ) (u : LinearMap.ker ((pointComplex F B).d 1 2).hom) :
    pointH1Reduction F B a u = H1pi (AbsoluteGaloisGroup F) (B.TorsionCoeff (2 ^ a))
      (pointReductionZ1 F B a u) := rfl

/-- The fixed finite two-cocycle underlying reduction of the genuine integral trace target. -/
def muReductionZ2 (a : ℕ) (z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom) :
    Z2 (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ a)) :=
  cocyclesMap2 (AbsoluteGaloisGroup F) (FiniteTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F) a)
    (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ a)) (ContinuousMonoidHom.id _)
    (actualMuLevelEquiv F a).toAddMonoidHom continuous_of_discreteTopology (actualMuLevelEquiv_smul F a)
    ⟨fun p => cfun (reduceTwoCycle (AbsoluteGaloisGroup F) (UnitsCoeff F) a z).val ![p.1, p.2],
      mem_Z2_of_d_eq_zero _ (reduceTwoCycle (AbsoluteGaloisGroup F) (UnitsCoeff F) a z).2⟩

/-- The fixed trace-target class reduction is the class of its specific finite cocycle. -/
theorem muH2Reduction_class (a : ℕ) (z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom) :
    actualMuH2Reduction F a z = H2pi (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ a))
      (muReductionZ2 F a z) := rfl

/-- Fixed reduction of the actual integral cup is the cup of the fixed genuine finite reductions. -/
theorem integralCupCycle_reduction (a : ℕ)
    (u v : LinearMap.ker ((pointComplex F B).d 1 2).hom) :
    actualMuH2Reduction F a (integralCupCycle F B u v) =
      ZInQ.Contrib.CloudB3RC53.Duality.localWeilCup B (2 ^ a) (twoPower_isUnit F a)
        (pointH1Reduction F B a u) (pointH1Reduction F B a v) := by
  rw [muH2Reduction_class, pointH1Reduction_class, pointH1Reduction_class]
  change H2pi (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ a))
      (muReductionZ2 F a (integralCupCycle F B u v)) =
    ZInQ.Contrib.CloudB3RC53.Duality.cupH (B.torsionCoeffWeilPairing (2 ^ a) (twoPower_isUnit F a))
      (fun σ x y => B.torsionCoeffWeilPairing_smul (2 ^ a) (twoPower_isUnit F a) σ x y)
      (H1pi (AbsoluteGaloisGroup F) (B.TorsionCoeff (2 ^ a)) (pointReductionZ1 F B a u))
      (H1pi (AbsoluteGaloisGroup F) (B.TorsionCoeff (2 ^ a)) (pointReductionZ1 F B a v))
  rw [ZInQ.Contrib.CloudB3RC53.Duality.cupH_mk]
  apply congrArg (H2pi (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ a)))
  apply Subtype.ext
  funext p
  obtain ⟨σ, τ⟩ := p
  have hc : cfun (integralCupOne F B u.val v.val) ![σ, τ] =
      coefficientWeilPairing F B (cfun u.val (fun _ => σ)) (σ • cfun v.val (fun _ => τ)) := by
    change cupFun (coefficientWeilPairing F B) 1 1 2 rfl (cfun u.val) (cfun v.val) ![σ, τ] = _
    exact cupFun_one_one_apply (coefficientWeilPairing F B) (cfun u.val) (cfun v.val) ![σ, τ]
  change actualMuLevelEquiv F a
      (coefficientProjection (AbsoluteGaloisGroup F) (UnitsCoeff F) a
        (cfun (integralCupOne F B u.val v.val) ![σ, τ])) =
    B.torsionCoeffWeilPairing (2 ^ a) (twoPower_isUnit F a)
      (pointLevelEquiv F B a (coefficientProjection (AbsoluteGaloisGroup F) B.PointCoeff a
        (cfun u.val (fun _ => σ))))
      (σ • pointLevelEquiv F B a (coefficientProjection (AbsoluteGaloisGroup F) B.PointCoeff a
        (cfun v.val (fun _ => τ))))
  rw [hc, coefficientWeilPairing_projection, coefficientProjection_smul, pointLevelEquiv_smul]
  all_goals exact continuous_of_discreteTopology

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralTrace

open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.CloudB3RC53.Duality
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules

/-- The canonical rational-circle characters commute with the actual successive finite residue maps. -/
theorem rationalCharacter_transition (a : ℕ) (z : ZMod (2 ^ (a + 1))) :
    ZMod.toRatAddCircle (2 ^ a) ((ZMod.castHom (pow_dvd_pow 2 a.le_succ) (ZMod (2 ^ a))) z) =
      (2 : ℕ) • ZMod.toRatAddCircle (2 ^ (a + 1)) z := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  rw [map_intCast, ZMod.toRatAddCircle_intCast, ZMod.toRatAddCircle_intCast, ← AddCircle.coe_nsmul]
  congr 1
  simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
  field_simp
  push_cast
  ring

variable (F : Type) [Field F]

/-- The actual finite roots-of-unity transition on second cohomology. -/
def finiteMuH2Transition (a : ℕ) :
    H2 (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ (a + 1))) →+
      H2 (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ a)) :=
  explicitCoeff2 (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ (a + 1)))
    (kummerCoeffPow F (pow_dvd_pow 2 a.le_succ)) continuous_of_discreteTopology

/-- The actual power map on multiplicative coefficient modules. -/
def unitPowerHom (m : ℕ) : UnitsCoeff F →+[AbsoluteGaloisGroup F] UnitsCoeff F :=
  { unitsCoeffPow F m with map_smul' := unitsCoeffPow_equivariant F m }

/-- Actual roots-of-unity inclusions intertwine the genuine coefficient power map and the actual multiplication map on units. -/
theorem coefficientIncl_power (a : ℕ) :
    (kummerCoeffInclHom F (2 ^ a)).comp (kummerCoeffPow F (pow_dvd_pow 2 a.le_succ)) =
      (unitPowerHom F 2).comp (kummerCoeffInclHom F (2 ^ (a + 1))) := by
  apply DFunLike.ext
  intro z
  apply Additive.toMul.injective
  change (z.toMul : (SeparableClosure F)ˣ) ^ (2 ^ (a + 1) / 2 ^ a) =
    (z.toMul : (SeparableClosure F)ˣ) ^ 2
  have h : 2 ^ (a + 1) / 2 ^ a = 2 := by
    rw [pow_succ, Nat.mul_div_right 2 (pow_pos (by decide) a)]
  rw [h]

/-- The fixed genuine finite cohomology transition becomes multiplication by two under the actual Brauer map. -/
theorem kummerToBr_transition (a : ℕ)
    (z : H2 (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ (a + 1)))) :
    kummerToBr (2 ^ a) (finiteMuH2Transition F a z) = (2 : ℕ) • kummerToBr (2 ^ (a + 1)) z := by
  change unitsRepH2Equiv F
      ((explicitCoeff2 (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ a))
        (kummerCoeffInclHom F (2 ^ a)) continuous_of_discreteTopology)
          (finiteMuH2Transition F a z)) = _
  have h := explicitCoeff2_comp (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ (a + 1)))
    (kummerCoeffPow F (pow_dvd_pow 2 a.le_succ)) (kummerCoeffInclHom F (2 ^ a))
    continuous_of_discreteTopology continuous_of_discreteTopology
  have h' := explicitCoeff2_comp (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ (a + 1)))
    (kummerCoeffInclHom F (2 ^ (a + 1))) (unitPowerHom F 2)
    continuous_of_discreteTopology continuous_of_discreteTopology
  change unitsRepH2Equiv F
    (((explicitCoeff2 (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ a))
      (kummerCoeffInclHom F (2 ^ a)) continuous_of_discreteTopology).comp
        (explicitCoeff2 (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ (a + 1)))
          (kummerCoeffPow F (pow_dvd_pow 2 a.le_succ)) continuous_of_discreteTopology)) z) = _
  rw [← h]
  have hco := congrArg (fun f : KummerCoeff F (2 ^ (a + 1)) →+[AbsoluteGaloisGroup F] UnitsCoeff F =>
    explicitCoeff2 (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ (a + 1))) f
      continuous_of_discreteTopology) (coefficientIncl_power F a)
  erw [hco, h', AddMonoidHom.comp_apply]
  rw [explicitCoeff2_eq_nsmul _ _ _ _ (fun t => by
    change unitsCoeffPow F 2 t = (2 : ℕ) • t
    rw [unitsCoeffPow_eq_nsmul])]
  change (unitsRepH2Equiv F).toAddMonoidHom
      ((2 : ℕ) • explicitCoeff2 (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ (a + 1)))
        (kummerCoeffInclHom F (2 ^ (a + 1))) continuous_of_discreteTopology z) =
    (2 : ℕ) • (unitsRepH2Equiv F).toAddMonoidHom
      (explicitCoeff2 (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ (a + 1)))
        (kummerCoeffInclHom F (2 ^ (a + 1))) continuous_of_discreteTopology z)
  exact map_nsmul (unitsRepH2Equiv F).toAddMonoidHom 2 _

section IntegralInvariant

variable [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The actual finite local invariants are compatible with the genuine coefficient and residue transitions. -/
theorem finiteInvariant_transition (a : ℕ)
    (z : H2 (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ (a + 1)))) :
    (ZMod.castHom (pow_dvd_pow 2 a.le_succ) (ZMod (2 ^ a)))
      (finiteInvariant F (2 ^ (a + 1)) (twoPower_isUnit F (a + 1)) z) =
    finiteInvariant F (2 ^ a) (twoPower_isUnit F a) (finiteMuH2Transition F a z) := by
  apply (ZMod.toRatAddCircle_injective (2 ^ a))
  rw [rationalCharacter_transition, finiteInvariant_toRat, finiteInvariant_toRat,
    kummerToBr_transition, map_nsmul]

end IntegralInvariant

/-- The specific finite cocycle obtained from actual integral trace-target reduction. -/
def muReducedZ2 (a : ℕ) (z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom) :
    Z2 (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ a)) :=
  cocyclesMap2 (AbsoluteGaloisGroup F) (FiniteTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F) a)
    (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ a)) (ContinuousMonoidHom.id _)
    (actualMuLevelEquiv F a).toAddMonoidHom continuous_of_discreteTopology (actualMuLevelEquiv_smul F a)
    ⟨fun p => cfun (reduceTwoCycle (AbsoluteGaloisGroup F) (UnitsCoeff F) a z).val ![p.1, p.2],
      mem_Z2_of_d_eq_zero _ (reduceTwoCycle (AbsoluteGaloisGroup F) (UnitsCoeff F) a z).2⟩

/-- The actual trace-target class reduction is the class of its specific finite cocycle. -/
theorem actualMuReduction_class (a : ℕ) (z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom) :
    actualMuH2Reduction F a z = H2pi (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ a))
      (muReducedZ2 F a z) := rfl

/-- The genuine integral trace-target class reductions form a compatible finite-level family. -/
theorem actualMuReduction_transition (a : ℕ)
    (z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom) :
    actualMuH2Reduction F a z = finiteMuH2Transition F a (actualMuH2Reduction F (a + 1) z) := by
  rw [actualMuReduction_class, actualMuReduction_class]
  change H2pi (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ a)) (muReducedZ2 F a z) =
    explicitCoeff2 (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ (a + 1)))
      (kummerCoeffPow F (pow_dvd_pow 2 a.le_succ)) continuous_of_discreteTopology
      (H2pi (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ (a + 1))) (muReducedZ2 F (a + 1) z))
  erw [explicitCoeff2_mk]
  apply congrArg (H2pi (AbsoluteGaloisGroup F) (KummerCoeff F (2 ^ a)))
  apply Subtype.ext
  funext p
  have h := congrArg (fun c => cfun c ![p.1, p.2])
    (reduceCochains_succ (AbsoluteGaloisGroup F) (UnitsCoeff F) a 2 z.val)
  change coefficientTransition (AbsoluteGaloisGroup F) (UnitsCoeff F) a
      (coefficientProjection (AbsoluteGaloisGroup F) (UnitsCoeff F) (a + 1) (cfun z.val ![p.1, p.2])) =
    coefficientProjection (AbsoluteGaloisGroup F) (UnitsCoeff F) a (cfun z.val ![p.1, p.2]) at h
  change actualMuLevelEquiv F a
      (coefficientProjection (AbsoluteGaloisGroup F) (UnitsCoeff F) a (cfun z.val ![p.1, p.2])) =
    kummerCoeffPow F (pow_dvd_pow 2 a.le_succ)
      (actualMuLevelEquiv F (a + 1)
        (coefficientProjection (AbsoluteGaloisGroup F) (UnitsCoeff F) (a + 1) (cfun z.val ![p.1, p.2])))
  rw [← h]
  exact actualMuLevelEquiv_transition F a _

section InvariantLift

variable [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The independently specified actual finite invariant of a genuine integral target cocycle. -/
def residueInvariant (a : ℕ) : LinearMap.ker ((actualTraceComplex F).d 2 3).hom →+ ZMod (2 ^ a) :=
  (finiteInvariant F (2 ^ a) (twoPower_isUnit F a)).toAddMonoidHom.comp (actualMuH2Reduction F a)

/-- The actual finite invariant residues of an integral target cocycle are compatible. -/
theorem residueInvariant_transition (a : ℕ)
    (z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom) :
    (ZMod.castHom (pow_dvd_pow 2 a.le_succ) (ZMod (2 ^ a))) (residueInvariant F (a + 1) z) =
      residueInvariant F a z := by
  change (ZMod.castHom (pow_dvd_pow 2 a.le_succ) (ZMod (2 ^ a)))
      (finiteInvariant F (2 ^ (a + 1)) (twoPower_isUnit F (a + 1)) (actualMuH2Reduction F (a + 1) z)) =
    finiteInvariant F (2 ^ a) (twoPower_isUnit F a) (actualMuH2Reduction F a z)
  rw [finiteInvariant_transition, ← actualMuReduction_transition]

/-- The fixed integral representatives of the actual finite invariant residues. -/
def invariantRepresentatives (z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom) (a : ℕ) : ℤ :=
  (residueInvariant F a z).val

/-- The fixed invariant representatives satisfy the actual two-adic Cauchy divisibility condition. -/
theorem invariantRepresentatives_step
    (z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom) (a : ℕ) :
    (2 : ℤ) ^ a ∣ invariantRepresentatives F z (a + 1) - invariantRepresentatives F z a := by
  have h := residueInvariant_transition F a z
  have hhigh : (((residueInvariant F (a + 1) z).val : ℕ) : ZMod (2 ^ (a + 1))) =
      residueInvariant F (a + 1) z := ZMod.natCast_zmod_val _
  rw [← hhigh, map_natCast] at h
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 ^ a)).mp
  change (((invariantRepresentatives F z (a + 1) - invariantRepresentatives F z a : ℤ) : ZMod (2 ^ a))) = 0
  rw [Int.cast_sub, sub_eq_zero]
  simpa only [invariantRepresentatives, Int.cast_natCast, ZMod.natCast_zmod_val, Nat.cast_pow,
    Nat.cast_ofNat] using h

/-- The normalized actual integral local invariant of every genuine integral target two-cocycle. -/
def traceCycleValue (z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom) : ℤ_[2] :=
  PadicInt.ofIntSeq (invariantRepresentatives F z)
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (invariantRepresentatives F z) 2
      (invariantRepresentatives_step F z))

/-- The actual integral cycle invariant reduces to the independently defined genuine finite invariant at every level. -/
theorem traceCycleValue_projection (z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom) (a : ℕ) :
    PadicInt.toZModPow a (traceCycleValue F z) = residueInvariant F a z := by
  rw [traceCycleValue, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub]
  simp only [invariantRepresentatives, Int.cast_natCast, ZMod.natCast_zmod_val]
  all_goals simpa only [Nat.cast_ofNat] using invariantRepresentatives_step F z

/-- Finite trace-target cochains see two-adic scalars through the actual finite residue. -/
theorem finiteMuCochain_smul (a n : ℕ) (r : ℤ_[2])
    (c : (finiteIntegralComplex (AbsoluteGaloisGroup F) (UnitsCoeff F) a).X n) :
    r • c = (PadicInt.toZModPow a r).val • c := by
  apply Subtype.ext
  funext p
  let t : FiniteTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F) a := cfun c p
  let v : ZMod (2 ^ a) := PadicInt.toZModPow a r
  change v • t = v.val • t
  simpa only [Nat.cast_smul_eq_nsmul] using
    congrArg (fun x : ZMod (2 ^ a) => x • t) (ZMod.natCast_zmod_val v).symm

/-- The independently specified actual finite invariant is semilinear for the genuine finite scalar reduction. -/
theorem residueInvariant_smul (a : ℕ) (r : ℤ_[2])
    (z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom) :
    residueInvariant F a (r • z) = (PadicInt.toZModPow a r).val • residueInvariant F a z := by
  have h : reduceTwoCycle (AbsoluteGaloisGroup F) (UnitsCoeff F) a (r • z) =
      (PadicInt.toZModPow a r).val • reduceTwoCycle (AbsoluteGaloisGroup F) (UnitsCoeff F) a z := by
    rw [map_smul]
    apply Subtype.ext
    exact finiteMuCochain_smul F a 2 r _
  let ψ : LinearMap.ker ((finiteIntegralComplex (AbsoluteGaloisGroup F) (UnitsCoeff F) a).d 2 3).hom →+
      ZMod (2 ^ a) :=
    (finiteInvariant F (2 ^ a) (twoPower_isUnit F a)).toAddMonoidHom.comp
      ((actualMuH2Equiv F a).toAddMonoidHom.comp
        (kerToH2 (k := ℤ_[2]) (G := AbsoluteGaloisGroup F)
          (M := FiniteTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F) a)))
  change ψ (reduceTwoCycle (AbsoluteGaloisGroup F) (UnitsCoeff F) a (r • z)) =
    (PadicInt.toZModPow a r).val • ψ (reduceTwoCycle (AbsoluteGaloisGroup F) (UnitsCoeff F) a z)
  rw [h, map_nsmul]

/-- The normalized actual integral local invariant is a genuine linear map on actual target two-cocycles. -/
def normalizedCycleTrace : LinearMap.ker ((actualTraceComplex F).d 2 3).hom →ₗ[ℤ_[2]] ℤ_[2] where
  toFun := traceCycleValue F
  map_add' z w := by
    apply PadicInt.ext_of_toZModPow.mp
    intro a
    rw [map_add, traceCycleValue_projection, traceCycleValue_projection, traceCycleValue_projection, map_add]
  map_smul' r z := by
    apply PadicInt.ext_of_toZModPow.mp
    intro a
    simp only [smul_eq_mul, map_mul, traceCycleValue_projection]
    rw [residueInvariant_smul, nsmul_eq_mul, ZMod.natCast_zmod_val]
    rfl

/-- The normalized actual integral cycle trace has its prescribed genuine finite local invariant at every level. -/
theorem normalizedCycleTrace_projection
    (z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom) (a : ℕ) :
    PadicInt.toZModPow a (normalizedCycleTrace F z) =
      finiteInvariant F (2 ^ a) (twoPower_isUnit F a) (actualMuH2Reduction F a z) :=
  traceCycleValue_projection F z a

/-- The kernel of the normalized actual integral cycle trace is exactly the actual continuous coboundaries. -/
theorem normalizedCycleTrace_eq_zero_iff_boundary
    (z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom) :
    normalizedCycleTrace F z = 0 ↔
      ∃ b : (actualTraceComplex F).X 1, ((actualTraceComplex F).d 1 2).hom b = z.val := by
  rw [← actualMuH2Reduction_all_zero_iff_boundary]
  constructor
  · intro hz a
    apply (finiteInvariant_eq_zero_iff F (2 ^ a) (twoPower_isUnit F a) _).mp
    have h := normalizedCycleTrace_projection F z a
    rw [hz, map_zero] at h
    exact h.symm
  · intro hz
    apply PadicInt.ext_of_toZModPow.mp
    intro a
    rw [normalizedCycleTrace_projection, hz a, map_zero, map_zero]

/-- The normalized actual cycle trace kills every actual continuous coboundary. -/
theorem normalizedCycleTrace_boundary
    (z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom) (b : (actualTraceComplex F).X 1)
    (hb : ((actualTraceComplex F).d 1 2).hom b = z.val) : normalizedCycleTrace F z = 0 :=
  (normalizedCycleTrace_eq_zero_iff_boundary F z).mpr ⟨b, hb⟩

end InvariantLift

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralTrace

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralCompatibility

open TauCeti TauCeti.ContCohomology
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralTrace

variable (F : Type) [Field F] [CharZero F] [DecidableEq F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]

/-- The normalized actual integral cup invariant is the genuine finite local Tate pairing of the fixed actual class reductions. -/
theorem integralCup_invariant_compatibility (a : ℕ)
    (u v : LinearMap.ker ((pointComplex F B).d 1 2).hom) :
    padicInvariant a (normalizedCycleTrace F (integralCupCycle F B u v)) =
      ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B (2 ^ a) (twoPower_isUnit F a)
        (pointH1Reduction F B a u) (pointH1Reduction F B a v) := by
  unfold padicInvariant
  change ZMod.toRatAddCircle (2 ^ a)
      (PadicInt.toZModPow a (normalizedCycleTrace F (integralCupCycle F B u v))) = _
  rw [normalizedCycleTrace_projection, integralCupCycle_reduction, finiteInvariant_toRat]
  rfl

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralCompatibility

end

/-!
# Extension of a scalar map from a saturated kernel

A kernel with torsion-free target splits inside every finitely generated
submodule over a principal ideal domain. Compactness of the scalar ring
then assembles the finite extensions into a scalar-linear map on the
entire source. No global complement of the kernel is assumed.
-/

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.TraceExtension

section FiniteExtension

variable {R N V : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [AddCommGroup N] [Module R N] [AddCommGroup V] [Module R V]
  [Module.IsTorsionFree R V]

/-- A scalar map on the genuine kernel extends over each finitely generated source submodule. -/
theorem kernel_extension_on_finite_submodule (d : N →ₗ[R] V) (f : LinearMap.ker d →ₗ[R] R)
    (U : Submodule R N) [Module.Finite R U] :
    ∃ h : U →ₗ[R] R, ∀ (u : U) (hu : d u.val = 0), h u = f ⟨u.val, hu⟩ := by
  let q : U →ₗ[R] V := d.comp U.subtype
  let q' : U →ₗ[R] LinearMap.range q := q.rangeRestrict
  have hsurj : Function.Surjective q' := by
    rintro ⟨v, u, hu⟩
    exact ⟨u, Subtype.ext hu⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q'
    (LinearMap.id : LinearMap.range q →ₗ[R] LinearMap.range q) hsurj
  let p : U →ₗ[R] LinearMap.ker d :=
    (U.subtype - U.subtype.comp (s.comp q')).codRestrict _ (by
      intro u
      change d (u.val - (s (q' u)).val) = 0
      rw [map_sub]
      have h := congrArg (fun t : LinearMap.range q => t.val) (LinearMap.congr_fun hs (q' u))
      change d (s (q' u)).val = d u.val at h
      rw [h, sub_self])
  refine ⟨f.comp p, ?_⟩
  intro u hu
  have hq : q' u = 0 := Subtype.ext hu
  change f ⟨u.val - (s (q' u)).val, _⟩ = f ⟨u.val, hu⟩
  apply congrArg f
  apply Subtype.ext
  change u.val - (s (q' u)).val = u.val
  rw [hq, map_zero, Submodule.coe_zero, sub_zero]

end FiniteExtension

section CompactExtension

variable {R N V : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]
  [AddCommGroup N] [Module R N] [AddCommGroup V] [Module R V]
  [Module.IsTorsionFree R V]

/-- The equations required of an extension: additivity, scalar linearity and agreement on the kernel. -/
abbrev Equation (d : N →ₗ[R] V) := (N × N) ⊕ ((R × N) ⊕ LinearMap.ker d)

open scoped Classical in
/-- The finite source support of one extension equation. -/
def equationSupport (d : N →ₗ[R] V) : Equation d → Finset N
  | Sum.inl (x, y) => {x, y, x + y}
  | Sum.inr (Sum.inl (r, x)) => {x, r • x}
  | Sum.inr (Sum.inr x) => {x.val}

/-- One closed condition on a prospective scalar extension. -/
def equationSet (d : N →ₗ[R] V) (f : LinearMap.ker d →ₗ[R] R) : Equation d → Set (N → R)
  | Sum.inl (x, y) => {h | h (x + y) = h x + h y}
  | Sum.inr (Sum.inl (r, x)) => {h | h (r • x) = r * h x}
  | Sum.inr (Sum.inr x) => {h | h x.val = f x}

/-- Each actual extension equation is closed in the compact product of scalar rings. -/
theorem equationSet_closed (d : N →ₗ[R] V) (f : LinearMap.ker d →ₗ[R] R) (e : Equation d) :
    IsClosed (equationSet d f e) := by
  rcases e with ⟨x, y⟩ | (⟨r, x⟩ | x)
  · exact isClosed_eq (continuous_apply (x + y)) ((continuous_apply x).add (continuous_apply y))
  · exact isClosed_eq (continuous_apply (r • x)) (continuous_const.mul (continuous_apply x))
  · exact isClosed_eq (continuous_apply x.val) continuous_const

/-- A linear map from a kernel with torsion-free target extends to the whole source over a compact scalar PID. -/
theorem kernel_extension_of_compact_scalar (d : N →ₗ[R] V) (f : LinearMap.ker d →ₗ[R] R) :
    ∃ h : N →ₗ[R] R, ∀ x : LinearMap.ker d, h x.val = f x := by
  classical
  have hfinite : ∀ s : Finset (Equation d), (⋂ e ∈ s, equationSet d f e).Nonempty := by
    intro s
    let nodes := s.biUnion (equationSupport d)
    let U : Submodule R N := Submodule.span R (nodes : Set N)
    obtain ⟨g, hg⟩ := kernel_extension_on_finite_submodule d f U
    let h : N → R := fun x => if hx : x ∈ U then g ⟨x, hx⟩ else 0
    have hvalue (x : N) (hx : x ∈ U) : h x = g ⟨x, hx⟩ := dif_pos hx
    refine ⟨h, ?_⟩
    simp only [Set.mem_iInter]
    intro e he
    have hmem (x : N) (hx : x ∈ equationSupport d e) : x ∈ U :=
      Submodule.subset_span (Finset.mem_biUnion.mpr ⟨e, he, hx⟩)
    rcases e with ⟨x, y⟩ | (⟨r, x⟩ | x)
    · have hx : x ∈ U := hmem x (by simp [equationSupport])
      have hy : y ∈ U := hmem y (by simp [equationSupport])
      change h (x + y) = h x + h y
      rw [hvalue (x + y) (U.add_mem hx hy), hvalue x hx, hvalue y hy]
      exact map_add g ⟨x, hx⟩ ⟨y, hy⟩
    · have hx : x ∈ U := hmem x (by simp [equationSupport])
      change h (r • x) = r * h x
      rw [hvalue (r • x) (U.smul_mem r hx), hvalue x hx]
      exact map_smul g r ⟨x, hx⟩
    · have hx : x.val ∈ U := hmem x.val (by simp [equationSupport])
      change h x.val = f x
      rw [hvalue x.val hx]
      exact hg ⟨x.val, hx⟩ x.2
  obtain ⟨h, hh⟩ := CompactSpace.iInter_nonempty (equationSet_closed d f) hfinite
  have hAdd (x y : N) : h (x + y) = h x + h y :=
    Set.mem_iInter.mp hh (Sum.inl (x, y))
  have hSmul (r : R) (x : N) : h (r • x) = r * h x :=
    Set.mem_iInter.mp hh (Sum.inr (Sum.inl (r, x)))
  let g : N →ₗ[R] R :=
    { toFun := h
      map_add' := hAdd
      map_smul' := fun r x => hSmul r x }
  exact ⟨g, fun x => Set.mem_iInter.mp hh (Sum.inr (Sum.inr x))⟩

end CompactExtension

section TwoAdicTate

open TauCeti

/-- The genuine two-adic Tate module is torsion-free over the actual scalar ring. -/
theorem tateModule_isTorsionFree (A : Type*) [AddCommGroup A] :
    Module.IsTorsionFree ℤ_[2] (TateModule 2 A) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r x hx
  by_cases hr : r = 0
  · exact Or.inl hr
  · right
    apply TateModule.eq_zero_of_pow_nsmul_eq_zero (k := r.valuation)
    let u : ℤ_[2]ˣ := PadicInt.unitCoeff hr
    have hru : r = (u : ℤ_[2]) * (2 : ℤ_[2]) ^ r.valuation := PadicInt.unitCoeff_spec hr
    rw [hru, mul_smul] at hx
    have h := congrArg (fun y : TateModule 2 A => (u⁻¹ : ℤ_[2]ˣ).val • y) hx
    simp only [← mul_smul, smul_zero] at h
    rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at h
    have hp : ((2 : ℤ_[2]) ^ r.valuation) • x = (2 ^ r.valuation : ℕ) • x := by
      rw [← Nat.cast_smul_eq_nsmul (R := ℤ_[2]), Nat.cast_pow, Nat.cast_ofNat]
    rwa [hp] at h

end TwoAdicTate

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.TraceExtension

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.AllCochainTrace

open TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.TraceExtension
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralTrace

variable (F : Type) [Field F]

/-- The actual integral trace-target cochains are torsion-free over the genuine scalar ring. -/
theorem traceCochains_isTorsionFree (n : ℕ) : Module.IsTorsionFree ℤ_[2] ((actualTraceComplex F).X n) := by
  haveI : Module.IsTorsionFree ℤ_[2] (IntegralTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F)) :=
    tateModule_isTorsionFree (UnitsCoeff F)
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r c hc
  by_cases hr : r = 0
  · exact Or.inl hr
  · right
    apply Subtype.ext
    funext s
    change (cfun c s : IntegralTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F)) = 0
    have h : r • (cfun c s : IntegralTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F)) = 0 :=
      congrArg (fun v => cfun v s) hc
    exact (smul_eq_zero_iff_right (M := IntegralTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F)) hr).mp h

variable [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The normalized genuine cycle invariant extends linearly to all actual degree-two cochains. -/
theorem allCochainTraceExtension_exists :
    ∃ trv : (actualTraceComplex F).X 2 →ₗ[ℤ_[2]] ℤ_[2],
      ∀ z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom,
        trv z.val = normalizedCycleTrace F z := by
  haveI := traceCochains_isTorsionFree F 3
  exact kernel_extension_of_compact_scalar ((actualTraceComplex F).d 2 3).hom (normalizedCycleTrace F)

/-- A fixed all-cochain extension of the independently normalized actual local invariant. -/
def trv : (actualTraceComplex F).X 2 →ₗ[ℤ_[2]] ℤ_[2] :=
  (allCochainTraceExtension_exists F).choose

/-- On actual cocycles the fixed all-cochain trace is the genuine normalized local invariant. -/
theorem trv_on_cycles (z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom) :
    trv F z.val = normalizedCycleTrace F z :=
  (allCochainTraceExtension_exists F).choose_spec z

/-- The actual all-cochain trace kills every genuine continuous coboundary. -/
theorem htrv (y : (actualTraceComplex F).X 1) :
    trv F (((actualTraceComplex F).d 1 2).hom y) = 0 := by
  have hz : ((actualTraceComplex F).d 2 3).hom (((actualTraceComplex F).d 1 2).hom y) = 0 := by
    have h := congrArg (fun f => f.hom y) ((actualTraceComplex F).d_comp_d 1 2 3)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h
  rw [trv_on_cycles F ⟨_, hz⟩]
  exact normalizedCycleTrace_boundary F ⟨_, hz⟩ y rfl

/-- A genuine integral target cocycle in the trace kernel is a genuine continuous coboundary. -/
theorem hker (z : (actualTraceComplex F).X 2)
    (hz : ((actualTraceComplex F).d 2 3).hom z = 0) (htrace : trv F z = 0) :
    ∃ y : (actualTraceComplex F).X 1, ((actualTraceComplex F).d 1 2).hom y = z := by
  apply (normalizedCycleTrace_eq_zero_iff_boundary F ⟨z, hz⟩).mp
  rw [← trv_on_cycles]
  exact htrace

/-- The fixed all-cochain trace has the independently specified finite local invariant on every actual cocycle. -/
theorem trv_finite_normalization
    (z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom) (a : ℕ) :
    PadicInt.toZModPow a (trv F z.val) =
      FiniteTrace.finiteInvariant F (2 ^ a) (twoPower_isUnit F a) (actualMuH2Reduction F a z) := by
  rw [trv_on_cycles, normalizedCycleTrace_projection]

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.AllCochainTrace

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralTransport

open CategoryTheory TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction

variable (F : Type) [Field F] [CharZero F] [DecidableEq F] (B : WeierstrassCurve F) [B.IsElliptic]

/-- The actual integral Tate coefficient map from the algebraic closure to the separable closure. -/
def toSepCoefficients : IntegralTateCoeff (Field.absoluteGaloisGroup F) (PtAlg F B) →ₗ[ℤ_[2]]
    IntegralTateCoeff (AbsoluteGaloisGroup F) B.PointCoeff :=
  TateModule.mapLinearMap (pointCoeffToAlg F B).symm.toAddMonoidHom

/-- The inverse integral Tate coefficient map is induced by the canonical closure inclusion. -/
def toAlgCoefficients : IntegralTateCoeff (AbsoluteGaloisGroup F) B.PointCoeff →ₗ[ℤ_[2]]
    IntegralTateCoeff (Field.absoluteGaloisGroup F) (PtAlg F B) :=
  TateModule.mapLinearMap (pointCoeffToAlg F B).toAddMonoidHom

/-- Integral coefficient transport preserves the actual inverse-limit topology. -/
theorem toSepCoefficients_continuous : Continuous (toSepCoefficients F B) := by
  apply TateModule.continuous_iff.mpr
  intro a
  exact (TateModule.isLocallyConstant_proj a).comp
    (TateModule.levelMap (pointCoeffToAlg F B).symm.toAddMonoidHom a)

/-- The inverse integral coefficient transport is continuous. -/
theorem toAlgCoefficients_continuous : Continuous (toAlgCoefficients F B) := by
  apply TateModule.continuous_iff.mpr
  intro a
  exact (TateModule.isLocallyConstant_proj a).comp
    (TateModule.levelMap (pointCoeffToAlg F B).toAddMonoidHom a)

/-- The inverse point dictionary intertwines the genuine absolute Galois actions. -/
theorem pointCoeffToSep_smul (σ : AbsoluteGaloisGroup F) (p : PtAlg F B) :
    (pointCoeffToAlg F B).symm ((absoluteGaloisGroupRestrictEquiv F).symm σ • p) =
      σ • (pointCoeffToAlg F B).symm p := by
  apply (pointCoeffToAlg F B).injective
  rw [(pointCoeffToAlg F B).apply_symm_apply]
  have h := pointCoeffToAlg_smul F B ((absoluteGaloisGroupRestrictEquiv F).symm σ)
    ((pointCoeffToAlg F B).symm p)
  rw [(absoluteGaloisGroupRestrictEquiv F).apply_symm_apply,
    (pointCoeffToAlg F B).apply_symm_apply] at h
  exact h.symm

/-- Integral coefficient transport intertwines the actual Galois action along the actual group equivalence. -/
theorem toSepCoefficients_smul (σ : AbsoluteGaloisGroup F)
    (x : IntegralTateCoeff (Field.absoluteGaloisGroup F) (PtAlg F B)) :
    toSepCoefficients F B ((absoluteGaloisGroupRestrictEquiv F).symm σ • x) =
      σ • toSepCoefficients F B x := by
  apply TateModule.ext
  intro a
  apply Subtype.ext
  exact pointCoeffToSep_smul F B σ (TateModule.proj a x).val

/-- The inverse integral coefficient map intertwines the actual group actions. -/
theorem toAlgCoefficients_smul (σ : Field.absoluteGaloisGroup F)
    (x : IntegralTateCoeff (AbsoluteGaloisGroup F) B.PointCoeff) :
    toAlgCoefficients F B (absoluteGaloisGroupRestrictEquiv F σ • x) =
      σ • toAlgCoefficients F B x := by
  apply TateModule.ext
  intro a
  apply Subtype.ext
  exact pointCoeffToAlg_smul F B σ (TateModule.proj a x).val

/-- The actual integral cochain transport to the separable-closure description used by the cup. -/
def toSepComplex : actualIntegralComplex F B ⟶ IntegralPairing.pointComplex F B :=
  contCochainsMap ⟨(absoluteGaloisGroupRestrictEquiv F).symm.toMulEquiv.toMonoidHom,
      (absoluteGaloisGroupRestrictEquiv F).symm.continuous⟩
    (toSepCoefficients F B) (toSepCoefficients_continuous F B) (toSepCoefficients_smul F B)

/-- The inverse genuine cochain transport along the canonical closure dictionary. -/
def toAlgComplex : IntegralPairing.pointComplex F B ⟶ actualIntegralComplex F B :=
  contCochainsMap ⟨(absoluteGaloisGroupRestrictEquiv F).toMulEquiv.toMonoidHom,
      (absoluteGaloisGroupRestrictEquiv F).continuous⟩
    (toAlgCoefficients F B) (toAlgCoefficients_continuous F B) (toAlgCoefficients_smul F B)

/-- The actual integral cochain transport has its prescribed coefficient-and-group formula in every degree. -/
theorem toSepComplex_apply (n : ℕ) (c : (actualIntegralComplex F B).X n)
    (s : Fin n → AbsoluteGaloisGroup F) :
    cfun (((toSepComplex F B).f n).hom c) s =
      toSepCoefficients F B (cfun c (fun i => (absoluteGaloisGroupRestrictEquiv F).symm (s i))) := rfl

/-- The genuine cochain transport restricted to actual integral one-cocycles. -/
def toSepCycle : LinearMap.ker ((actualIntegralComplex F B).d 1 2).hom →ₗ[ℤ_[2]]
    LinearMap.ker ((IntegralPairing.pointComplex F B).d 1 2).hom where
  toFun c := ⟨((toSepComplex F B).f 1).hom c.val, by
    change ((IntegralPairing.pointComplex F B).d 1 2).hom (((toSepComplex F B).f 1).hom c.val) = 0
    have h := congrArg (fun f => f.hom c.val) ((toSepComplex F B).comm 1 2)
    have hc : ((actualIntegralComplex F B).d 1 2).hom c.val = 0 := c.2
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hc, map_zero] using h⟩
  map_add' c d := Subtype.ext (map_add ((toSepComplex F B).f 1).hom c.val d.val)
  map_smul' r c := Subtype.ext (map_smul ((toSepComplex F B).f 1).hom r c.val)

/-- Actual finite cochain projection commutes with the actual integral closure transport in every degree. -/
theorem toSepComplex_reduction (a n : ℕ) (c : (actualIntegralComplex F B).X n)
    (s : Fin n → AbsoluteGaloisGroup F) :
    IntegralPairing.pointLevelEquiv F B a
      (cfun (((reduceCochains (AbsoluteGaloisGroup F) B.PointCoeff a).f n).hom
        (((toSepComplex F B).f n).hom c)) s) =
      (torsionCoeffToAlg F B (2 ^ a)).symm
        (actualLevelEquiv F B a (cfun
          (((reduceCochains (Field.absoluteGaloisGroup F) (PtAlg F B) a).f n).hom c)
            (fun i => (absoluteGaloisGroupRestrictEquiv F).symm (s i)))) := by
  apply Subtype.ext
  rfl

/-- Integral closure transport followed by its inverse is the identity on actual coefficients. -/
theorem toAlg_toSep_coefficients
    (x : IntegralTateCoeff (Field.absoluteGaloisGroup F) (PtAlg F B)) :
    toAlgCoefficients F B (toSepCoefficients F B x) = x := by
  apply TateModule.ext
  intro a
  apply Subtype.ext
  exact (pointCoeffToAlg F B).apply_symm_apply (TateModule.proj a x).val

/-- The inverse closure transport followed by the forward map is the identity on actual coefficients. -/
theorem toSep_toAlg_coefficients
    (x : IntegralTateCoeff (AbsoluteGaloisGroup F) B.PointCoeff) :
    toSepCoefficients F B (toAlgCoefficients F B x) = x := by
  apply TateModule.ext
  intro a
  apply Subtype.ext
  exact (pointCoeffToAlg F B).symm_apply_apply (TateModule.proj a x).val

/-- The actual cochain closure transports are inverse in every degree. -/
theorem toSepComplex_toAlgComplex : toSepComplex F B ≫ toAlgComplex F B = 𝟙 (actualIntegralComplex F B) := by
  ext n c
  apply Subtype.ext
  funext s
  change toAlgCoefficients F B (toSepCoefficients F B
      (cfun c (fun i => (absoluteGaloisGroupRestrictEquiv F).symm (absoluteGaloisGroupRestrictEquiv F (s i))))) =
    cfun c s
  simp only [(absoluteGaloisGroupRestrictEquiv F).symm_apply_apply, toAlg_toSep_coefficients]

/-- The inverse cochain transport has the reverse identity law. -/
theorem toAlgComplex_toSepComplex : toAlgComplex F B ≫ toSepComplex F B = 𝟙 (IntegralPairing.pointComplex F B) := by
  ext n c
  apply Subtype.ext
  funext s
  change toSepCoefficients F B (toAlgCoefficients F B
      (cfun c (fun i => absoluteGaloisGroupRestrictEquiv F ((absoluteGaloisGroupRestrictEquiv F).symm (s i))))) =
    cfun c s
  simp only [(absoluteGaloisGroupRestrictEquiv F).apply_symm_apply, toSep_toAlg_coefficients]

/-- The actual integral closure comparison is an isomorphism of the genuine cochain complexes. -/
def closureCochainIso : actualIntegralComplex F B ≅ IntegralPairing.pointComplex F B where
  hom := toSepComplex F B
  inv := toAlgComplex F B
  hom_inv_id := toSepComplex_toAlgComplex F B
  inv_hom_id := toAlgComplex_toSepComplex F B

/-- The fixed finite algebraic-closure cocycle of an actual integral one-cocycle. -/
def algReductionZ1 (a : ℕ) (c : LinearMap.ker ((actualIntegralComplex F B).d 1 2).hom) :
    Z1 (Field.absoluteGaloisGroup F) (TorsAlg F B (2 ^ a)) :=
  cocyclesMap1 (Field.absoluteGaloisGroup F) (FiniteTateCoeff (Field.absoluteGaloisGroup F) (PtAlg F B) a)
    (Field.absoluteGaloisGroup F) (TorsAlg F B (2 ^ a)) (ContinuousMonoidHom.id _)
    (actualLevelEquiv F B a).toAddMonoidHom continuous_of_discreteTopology (actualLevelEquiv_smul F B a)
    ⟨fun σ => cfun (reduceOneCycle (Field.absoluteGaloisGroup F) (PtAlg F B) a c).val (fun _ => σ),
      mem_Z1_of_d_eq_zero _ (reduceOneCycle (Field.absoluteGaloisGroup F) (PtAlg F B) a c).2⟩

/-- The genuine algebraic-closure class reduction is the class of its specific finite cocycle. -/
theorem actualH1Reduction_class (a : ℕ) (c : LinearMap.ker ((actualIntegralComplex F B).d 1 2).hom) :
    actualH1Reduction F B a c = H1pi (Field.absoluteGaloisGroup F) (TorsAlg F B (2 ^ a))
      (algReductionZ1 F B a c) := rfl

/-- The fixed finite separable-closure cocycle of an actual integral one-cocycle. -/
def sepReductionZ1 (a : ℕ) (c : LinearMap.ker ((IntegralPairing.pointComplex F B).d 1 2).hom) :
    Z1 (AbsoluteGaloisGroup F) (B.TorsionCoeff (2 ^ a)) :=
  cocyclesMap1 (AbsoluteGaloisGroup F) (FiniteTateCoeff (AbsoluteGaloisGroup F) B.PointCoeff a)
    (AbsoluteGaloisGroup F) (B.TorsionCoeff (2 ^ a)) (ContinuousMonoidHom.id _)
    (IntegralPairing.pointLevelEquiv F B a).toAddMonoidHom continuous_of_discreteTopology
    (IntegralPairing.pointLevelEquiv_smul F B a)
    ⟨fun σ => cfun (reduceOneCycle (AbsoluteGaloisGroup F) B.PointCoeff a c).val (fun _ => σ),
      mem_Z1_of_d_eq_zero _ (reduceOneCycle (AbsoluteGaloisGroup F) B.PointCoeff a c).2⟩

/-- The genuine separable-closure class reduction is the class of its specific finite cocycle. -/
theorem pointH1Reduction_class (a : ℕ)
    (c : LinearMap.ker ((IntegralPairing.pointComplex F B).d 1 2).hom) :
    IntegralPairing.pointH1Reduction F B a c = H1pi (AbsoluteGaloisGroup F) (B.TorsionCoeff (2 ^ a))
      (sepReductionZ1 F B a c) := rfl

/-- The actual finite Kummer class reductions commute with the genuine integral closure isomorphism. -/
theorem integralReduction_square (a : ℕ)
    (c : LinearMap.ker ((actualIntegralComplex F B).d 1 2).hom) :
    IntegralPairing.pointH1Reduction F B a (toSepCycle F B c) =
      (hOneToAlg F B (2 ^ a)).symm (actualH1Reduction F B a c) := by
  rw [pointH1Reduction_class, actualH1Reduction_class]
  erw [hOneToAlg, explicitMap1Equiv_symm_apply, explicitMap1_mk]

/-- Actual integral cochain closure transport commutes with every differential. -/
theorem toSepComplex_d (n : ℕ) (c : (actualIntegralComplex F B).X n) :
    ((toSepComplex F B).f (n + 1)).hom (((actualIntegralComplex F B).d n (n + 1)).hom c) =
      ((IntegralPairing.pointComplex F B).d n (n + 1)).hom (((toSepComplex F B).f n).hom c) := by
  have h := congrArg (fun f => f.hom c) ((toSepComplex F B).comm n (n + 1))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h.symm

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralTransport

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.TransportedLocal

open CategoryTheory NumberField IsDedekindDomain TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralTransport

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]

/-- The earlier actual local degree-one Kummer presentation map transported to the genuine cup coefficients. -/
def localKummerOne : (Fin (actualLocalPresentation K w B).rankZero → ℤ_[2]) →ₗ[ℤ_[2]]
    LinearMap.ker ((pointComplex (w.adicCompletion K) B).d 1 2).hom :=
  (toSepCycle (w.adicCompletion K) B).comp (actualLocalKummerOne K w B)

/-- The earlier actual local degree-zero Kummer presentation map transported by the same integral isomorphism. -/
def localKummerZero : (Fin (actualLocalPresentation K w B).rankOne → ℤ_[2]) →ₗ[ℤ_[2]]
    (pointComplex (w.adicCompletion K) B).X 0 :=
  ((toSepComplex (w.adicCompletion K) B).f 0).hom.comp (actualLocalKummerZero K w B)

/-- The fixed genuine transported local maps satisfy the differential square of the original actual presentation. -/
theorem localKummerZero_d (u : Fin (actualLocalPresentation K w B).rankOne → ℤ_[2]) :
    ((pointComplex (w.adicCompletion K) B).d 0 1).hom (localKummerZero K w B u) =
      (localKummerOne K w B ((actualLocalPresentation K w B).f u)).val := by
  change ((pointComplex (w.adicCompletion K) B).d 0 1).hom
      (((toSepComplex (w.adicCompletion K) B).f 0).hom (actualLocalKummerZero K w B u)) =
    ((toSepComplex (w.adicCompletion K) B).f 1).hom
      (actualLocalKummerOne K w B ((actualLocalPresentation K w B).f u)).val
  rw [← toSepComplex_d, actualLocalKummerZero_d]

/-- The fixed class reduction of the transported actual local presentation is exactly the previously specified genuine finite local reduction. -/
theorem localKummerOne_reduction (a : ℕ)
    (u : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2]) :
    pointH1Reduction (w.adicCompletion K) B a (localKummerOne K w B u) =
      actualLocalReduction K w B a u := by
  change pointH1Reduction (w.adicCompletion K) B a
    (toSepCycle (w.adicCompletion K) B (actualLocalKummerOne K w B u)) = _
  rw [integralReduction_square]
  rfl

/-- The specific transported integral local classes lie in the genuine Kummer image at every finite level. -/
theorem localKummerOne_mem_genuine_Kummer (a : ℕ)
    (u : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2]) :
    pointH1Reduction (w.adicCompletion K) B a (localKummerOne K w B u) ∈
      (B.kummerMap (2 ^ a) (twoPower_isUnit (w.adicCompletion K) a)).range := by
  rw [localKummerOne_reduction]
  exact actualLocalReduction_mem_genuine_Kummer K w B a u

/-- Cup–invariant compatibility on the fixed transported actual local presentation, using the all-cochain trace. -/
theorem localCup_invariant_compatibility (a : ℕ)
    (u v : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2]) :
    padicInvariant a (AllCochainTrace.trv (w.adicCompletion K)
      (integralCupOne (w.adicCompletion K) B (localKummerOne K w B u).val (localKummerOne K w B v).val)) =
      ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B (2 ^ a) (twoPower_isUnit (w.adicCompletion K) a)
        (actualLocalReduction K w B a u) (actualLocalReduction K w B a v) := by
  change padicInvariant a (AllCochainTrace.trv (w.adicCompletion K)
    (integralCupCycle (w.adicCompletion K) B (localKummerOne K w B u) (localKummerOne K w B v)).val) = _
  rw [AllCochainTrace.trv_on_cycles (w.adicCompletion K)
      (integralCupCycle (w.adicCompletion K) B (localKummerOne K w B u) (localKummerOne K w B v))]
  rw [IntegralCompatibility.integralCup_invariant_compatibility,
    localKummerOne_reduction, localKummerOne_reduction]

/-- Printed finite Kummer isotropy gives divisibility of the genuine all-cochain trace values for the fixed actual local maps. -/
theorem localCup_trace_divisible (hM : MilneLocalDualityPrint) (a : ℕ)
    (u v : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2]) :
    (2 : ℤ_[2]) ^ a ∣ AllCochainTrace.trv (w.adicCompletion K)
      (integralCupOne (w.adicCompletion K) B (localKummerOne K w B u).val (localKummerOne K w B v).val) := by
  obtain ⟨D⟩ := hM (w.adicCompletion K) B
  apply (padicInvariant_eq_zero_iff a _).mp
  rw [localCup_invariant_compatibility, actualLocalReduction_apply, actualLocalReduction_apply]
  exact kummer_finite_isotropy B D (2 ^ a) (twoPower_isUnit (w.adicCompletion K) a) _ _

/-- The all-cochain trace of the cup of two fixed actual local Kummer cochains is zero. -/
theorem localCup_trace_zero (hM : MilneLocalDualityPrint)
    (u v : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2]) :
    AllCochainTrace.trv (w.adicCompletion K)
      (integralCupOne (w.adicCompletion K) B (localKummerOne K w B u).val (localKummerOne K w B v).val) = 0 := by
  apply PadicInt.ext_of_toZModPow.mp
  intro a
  rw [map_zero]
  apply (PadicInt.toZModPow_eq_zero_iff_dvd a _).mpr
  simpa only [Nat.cast_ofNat] using localCup_trace_divisible K w B hM a u v

/-- The actual integral cup of two fixed actual local Kummer cochains is a genuine continuous coboundary. -/
theorem localCup_is_boundary (hM : MilneLocalDualityPrint)
    (u v : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2]) :
    ∃ b : (actualTraceComplex (w.adicCompletion K)).X 1,
      ((actualTraceComplex (w.adicCompletion K)).d 1 2).hom b =
        integralCupOne (w.adicCompletion K) B (localKummerOne K w B u).val (localKummerOne K w B v).val :=
  AllCochainTrace.hker (w.adicCompletion K) _
    (integralCupOne_isCycle (w.adicCompletion K) B (localKummerOne K w B u) (localKummerOne K w B v))
    (localCup_trace_zero K w B hM u v)

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.TransportedLocal

end

/-!
# A finite free local presentation and its cochain map

The two-term presentation retains the relations in degree zero and the
point generators in degree one. Its map to the actual local cochains is
determined by its degree-zero and degree-one maps and their differential
square. The trace adjoint is formed on the genuine local cup product.
-/

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.SelfDualCore

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.Duality
open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology (VanishesOutside)

variable {R : Type} [CommRing R]

/-- The terms of a fixed finite free point presentation, retaining both degrees. -/
def presentationX (r1 r0 : ℕ) (n : ℤ) : ModuleCat R :=
  if n = 0 then ModuleCat.of R (Fin r1 → R)
  else if n = 1 then ModuleCat.of R (Fin r0 → R)
  else ModuleCat.of R PUnit

/-- The actual presentation differential is the specified relation map in degree zero. -/
def presentationD (r1 r0 : ℕ) (f : (Fin r1 → R) →ₗ[R] (Fin r0 → R))
    (i j : ℤ) (h : i + 1 = j) : presentationX (R := R) r1 r0 i →ₗ[R] presentationX (R := R) r1 r0 j :=
  if hi : i = 0 then by
    subst i
    have hj : j = 1 := by omega
    subst j
    exact f
  else 0

/-- Only degree zero has a nonzero differential in the fixed point presentation. -/
theorem presentationD_of_ne (r1 r0 : ℕ) (f : (Fin r1 → R) →ₗ[R] (Fin r0 → R))
    (i j : ℤ) (h : i + 1 = j) (hi : i ≠ 0) : presentationD r1 r0 f i j h = 0 := by
  unfold presentationD
  exact dif_neg hi

/-- The genuine two-term free presentation, including its degree-zero relation module. -/
def presentationCx (r1 r0 : ℕ) (f : (Fin r1 → R) →ₗ[R] (Fin r0 → R)) : GCx R where
  X := presentationX r1 r0
  d := presentationD r1 r0 f
  d_d i j k hij hjk x := by
    by_cases hi : i = 0
    · subst i
      have hj : j = 1 := by omega
      subst j
      simp only [presentationD, zero_add, ↓reduceDIte, one_ne_zero, LinearMap.zero_apply]
    · change presentationD r1 r0 f j k hjk (presentationD r1 r0 f i j hij x) = 0
      erw [presentationD_of_ne r1 r0 f i j hij hi, map_zero]

/-- Every degree outside zero and one of the fixed presentation is zero. -/
theorem presentationCx_vanishes (r1 r0 : ℕ) (f : (Fin r1 → R) →ₗ[R] (Fin r0 → R)) :
    VanishesOutside (presentationCx r1 r0 f) (fun i => i = 0 ∨ i = 1) := by
  intro i hi
  have hi0 : i ≠ 0 := fun h => hi (Or.inl h)
  have hi1 : i ≠ 1 := fun h => hi (Or.inr h)
  change Subsingleton (presentationX (R := R) r1 r0 i)
  simp only [presentationX, if_neg hi0, if_neg hi1]
  infer_instance

/-- The actual degree maps of a point presentation, with their required cochain differential identities. -/
structure PresentationMap (L : GCx R) (r1 r0 : ℕ)
    (f : (Fin r1 → R) →ₗ[R] (Fin r0 → R)) where
  zero : (Fin r1 → R) →ₗ[R] L.X 0
  one : (Fin r0 → R) →ₗ[R] L.X 1
  differential : ∀ u, L.d 0 1 rfl (zero u) = one (f u)
  cycle : ∀ u, L.d 1 2 rfl (one u) = 0

/-- The fixed component of the genuine presentation cochain map. -/
def presentationMapComponent {L : GCx R} {r1 r0 : ℕ} {f : (Fin r1 → R) →ₗ[R] (Fin r0 → R)}
    (I : PresentationMap L r1 r0 f) (i j : ℤ) (h : i = j) :
    (presentationCx r1 r0 f).X i →ₗ[R] L.X j := by
  subst j
  exact if hi : i = 0 then by subst i; exact I.zero
    else if hi1 : i = 1 then by subst i; exact I.one
    else 0

/-- The prescribed degree maps give a genuine cochain map of the fixed free presentation. -/
def presentationMap {L : GCx R} {r1 r0 : ℕ} {f : (Fin r1 → R) →ₗ[R] (Fin r0 → R)}
    (I : PresentationMap L r1 r0 f) : GHom (presentationCx r1 r0 f) L where
  f := presentationMapComponent I
  comm i i1 j j1 hij hi hj hjj1 x := by
    subst j
    subst j1
    have hi1 : i1 = i + 1 := hi.symm
    subst i1
    by_cases hi0 : i = 0
    · subst i
      exact (I.differential x).symm
    · by_cases hione : i = 1
      · subst i
        change 0 = L.d 1 2 rfl (I.one x)
        exact (I.cycle x).symm
      · have hmap : presentationMapComponent I i i rfl = 0 := by
          simp only [presentationMapComponent, dif_neg hi0, dif_neg hione]
        change presentationMapComponent I (i + 1) (i + 1) rfl
            (presentationD r1 r0 f i (i + 1) rfl x) =
          L.d i (i + 1) rfl (presentationMapComponent I i i rfl x)
        erw [presentationD_of_ne r1 r0 f i (i + 1) rfl hi0, map_zero, hmap, map_zero]

section OrdinaryCone

variable {U L D : GCx R}

/-- The ordinary mapping-cone differential for a genuine local-condition cochain map. -/
def ordinaryConeD (ι : GHom U L) (i j : ℤ) (h : i + 1 = j) :
    (L.X i × U.X (i + 1)) →ₗ[R] (L.X j × U.X (j + 1)) :=
  ((L.d i j h).comp (LinearMap.fst R _ _) +
    (ι.f (i + 1) j h).comp (LinearMap.snd R _ _)).prod
      (-(U.d (i + 1) (j + 1) (by omega)).comp (LinearMap.snd R _ _))

/-- The actual ordinary cone of the fixed local-condition map, with no perfect-model replacement. -/
def ordinaryCone (ι : GHom U L) : GCx R where
  X n := ModuleCat.of R (L.X n × U.X (n + 1))
  d := ordinaryConeD ι
  d_d i j k hij hjk z := by
    apply Prod.ext
    · change L.d j k hjk (L.d i j hij z.1 + ι.f (i + 1) j hij z.2) +
        ι.f (j + 1) k hjk (-(U.d (i + 1) (j + 1) (by omega) z.2)) = 0
      rw [map_add, L.d_d, zero_add, map_neg]
      have h := ι.comm (i + 1) (j + 1) j k hij (by omega) hjk hjk z.2
      rw [h, add_neg_cancel]
    · change -(U.d (j + 1) (k + 1) (by omega)
        (-(U.d (i + 1) (j + 1) (by omega) z.2))) = 0
      rw [map_neg, neg_neg, U.d_d]

/-- A genuine cochain map vanishing on the local condition gives its specified comparison from the ordinary cone. -/
def coneComparison (ι : GHom U L) (g : GHom L D)
    (hzero : ∀ (i : ℤ) (u : U.X i), g.f i i rfl (ι.f i i rfl u) = 0) :
    GHom (ordinaryCone ι) D where
  f i j h := (g.f i j h).comp (LinearMap.fst R _ _)
  comm i i1 j j1 hij hi hj h1 z := by
    subst j
    subst j1
    have h : i1 = i + 1 := hi.symm
    subst i1
    change g.f (i + 1) (i + 1) rfl
      (L.d i (i + 1) rfl z.1 + ι.f (i + 1) (i + 1) rfl z.2) =
      D.d i (i + 1) rfl (g.f i i rfl z.1)
    rw [map_add, hzero, add_zero]
    exact g.comm i (i + 1) i (i + 1) rfl rfl rfl rfl z.1

end OrdinaryCone

section ActualAdjoint

variable {U L T : GCx R} (ι : GHom U L) (P : GPair L L T)
  (tr : T.X 2 →ₗ[R] R) (htr : ∀ y, tr (T.d 1 2 rfl y) = 0)

/-- The integral trace adjoint of the genuine cup paired against the specified local condition. -/
def traceAdjoint : GHom L (dualCx U 2) :=
  adjHom (pullPair P (idGHom L) ι) 2 tr htr

/-- With a two-term local condition, scalar cup isotropy in bidegree one kills the entire restricted trace adjoint. -/
theorem traceAdjoint_local_zero
    (hU : VanishesOutside U (fun i => i = 0 ∨ i = 1))
    (h11 : ∀ u v : U.X 1, tr (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι.f 1 1 rfl v)) = 0)
    (i : ℤ) (u : U.X i) :
    (traceAdjoint ι P tr htr).f i i rfl (ι.f i i rfl u) = 0 := by
  apply dualCx_ext
  intro v
  change tr (P.P i (2 - i) 2 (by omega) (ι.f i i rfl u) (ι.f (2 - i) (2 - i) rfl v)) = 0
  by_cases hi : i = 1
  · subst i
    exact h11 u v
  · by_cases hi0 : i = 0
    · subst i
      haveI := hU (2 - 0) (by omega)
      have hv : v = 0 := Subsingleton.elim _ _
      rw [hv, map_zero, map_zero, map_zero]
    · haveI := hU i (by omega)
      have hu : u = 0 := Subsingleton.elim _ _
      rw [hu, map_zero, LinearMap.map_zero₂, map_zero]

/-- The specified integral self-dual local comparison from the actual ordinary cone. -/
def selfDualConeComparison
    (hU : VanishesOutside U (fun i => i = 0 ∨ i = 1))
    (h11 : ∀ u v : U.X 1, tr (P.P 1 1 2 rfl (ι.f 1 1 rfl u) (ι.f 1 1 rfl v)) = 0) :
    GHom (ordinaryCone ι) (dualCx U 2) :=
  coneComparison ι (traceAdjoint ι P tr htr) (traceAdjoint_local_zero ι P tr htr hU h11)

end ActualAdjoint

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.SelfDualCore

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualSelfDual

open CategoryTheory NumberField IsDedekindDomain TauCeti TauCeti.ContCohomology
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.Duality ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.TransportedLocal
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.SelfDualCore
open ZInQ.Manuscript.RC.SelmerComplex

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]

/-- The fixed finite free presentation of the genuine completed local point group. -/
def localCondition : GCx ℤ_[2] :=
  presentationCx (actualLocalPresentation K w B).rankOne (actualLocalPresentation K w B).rankZero
    (actualLocalPresentation K w B).f

/-- The actual continuous local point-coefficient cochains, without a finite perfect-model substitution. -/
abbrev localCochains := natCx (pointComplex (w.adicCompletion K) B)

/-- The genuine integral local trace-target cochains. -/
abbrev localTraceTarget := natCx (actualTraceComplex (w.adicCompletion K))

/-- The fixed genuine point presentation data in the actual local cochains. -/
def localPresentationMap : PresentationMap (localCochains K w B)
    (actualLocalPresentation K w B).rankOne (actualLocalPresentation K w B).rankZero
      (actualLocalPresentation K w B).f where
  zero := localKummerZero K w B
  one := (LinearMap.ker ((pointComplex (w.adicCompletion K) B).d 1 2).hom).subtype.comp
    (localKummerOne K w B)
  differential u := localKummerZero_d K w B u
  cycle u := (localKummerOne K w B u).2

/-- The actual cochain-level Kummer inclusion is the map of the fixed genuine free presentation. -/
def localConditionMap : GHom (localCondition K w B) (localCochains K w B) :=
  presentationMap (localPresentationMap K w B)

/-- Degree zero of the genuine presentation map is the earlier actual Kummer relation primitive. -/
theorem localConditionMap_zero (u : Fin (actualLocalPresentation K w B).rankOne → ℤ_[2]) :
    (localConditionMap K w B).f 0 0 rfl u = localKummerZero K w B u := rfl

/-- Degree one of the genuine presentation map is the earlier fixed actual Kummer one-cocycle. -/
theorem localConditionMap_one (u : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2]) :
    (localConditionMap K w B).f 1 1 rfl u = (localKummerOne K w B u).val := rfl

/-- The actual integral local cup product in all relation-indexed degrees. -/
def localCup : GPair (localCochains K w B) (localCochains K w B) (localTraceTarget K w) :=
  natPair (integralCupPair (w.adicCompletion K) B)

/-- The scalar trace of the cup of the specified actual Kummer presentation maps is zero. -/
theorem localCondition_scalar_isotropy (hM : MilneLocalDualityPrint)
    (u v : (localCondition K w B).X 1) :
    AllCochainTrace.trv (w.adicCompletion K)
      ((localCup K w B).P 1 1 2 rfl ((localConditionMap K w B).f 1 1 rfl u)
        ((localConditionMap K w B).f 1 1 rfl v)) = 0 :=
  localCup_trace_zero K w B hM u v

/-- The genuine truncated isotropy interface is supplied by the actual trace, actual kernel exactness and the fixed local maps. -/
def localTruncatedIsotropy (hM : MilneLocalDualityPrint) :
    LocalTruncIsotropy (localConditionMap K w B) (localConditionMap K w B) (localCup K w B) :=
  kummerTruncIsotropy
    (presentationCx_vanishes _ _ _) (presentationCx_vanishes _ _ _)
    (AllCochainTrace.trv (w.adicCompletion K)) (AllCochainTrace.hker (w.adicCompletion K))
    (localCondition_scalar_isotropy K w B hM)

/-- The actual local quotient cone of the genuine point presentation in Galois cochains. -/
def localQuotientCone : GCx ℤ_[2] := ordinaryCone (localConditionMap K w B)

/-- The genuine derived dual of the fixed finite free Kummer presentation in complementary degree two. -/
def localDualTarget : GCx ℤ_[2] := dualCx (localCondition K w B) 2

/-- The trace adjoint on the actual local Galois cochains, before passage to the quotient cone. -/
def localTraceAdjoint : GHom (localCochains K w B) (localDualTarget K w B) :=
  traceAdjoint (localConditionMap K w B) (localCup K w B)
    (AllCochainTrace.trv (w.adicCompletion K)) (AllCochainTrace.htrv (w.adicCompletion K))

/-- The actual integral self-dual local comparison is constructed on the genuine quotient cone, not postulated. -/
def localSelfDualComparison (hM : MilneLocalDualityPrint) :
    GHom (localQuotientCone K w B) (localDualTarget K w B) :=
  selfDualConeComparison (localConditionMap K w B) (localCup K w B)
    (AllCochainTrace.trv (w.adicCompletion K)) (AllCochainTrace.htrv (w.adicCompletion K))
    (presentationCx_vanishes _ _ _) (localCondition_scalar_isotropy K w B hM)

/-- The constructed local comparison is exactly the trace-cup adjoint on its Galois-cochain component. -/
theorem localSelfDualComparison_formula (hM : MilneLocalDualityPrint) (i : ℤ)
    (z : (localQuotientCone K w B).X i) (u : (localCondition K w B).X (2 - i)) :
    asDual ((localSelfDualComparison K w B hM).f i i rfl z) u =
      AllCochainTrace.trv (w.adicCompletion K)
        ((localCup K w B).P i (2 - i) 2 (by omega) z.1
          ((localConditionMap K w B).f (2 - i) (2 - i) rfl u)) := rfl

/-- A finite based realization of the genuine local quotient cone. This is source-model data only, independent of self-duality. -/
structure IntegralConeBasedResolution (κe κo : Type) [Fintype κe] [Fintype κo]
    [DecidableEq κe] [DecidableEq κo] where
  C : BasedCx ℤ_[2] κe κo
  realization : GHom C.toGCx (localQuotientCone K w B)
  quasiIso : QuasiIso (GHom.toCC realization)

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualSelfDual

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedDual

open Matrix
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison

variable {R : Type} [CommRing R]

/-- The standard finite coordinate basis identifies vectors with their dual linear forms. -/
def vectorDual (r : ℕ) : (Fin r → R) ≃ₗ[R] Module.Dual R (Fin r → R) :=
  (Pi.basisFun R (Fin r)).toDualEquiv

/-- Evaluation of the standard coordinate dual on a basis vector. -/
theorem vectorDual_basis (r : ℕ) (v : Fin r → R) (i : Fin r) :
    vectorDual (R := R) r v (Pi.single i 1) = v i := by
  simpa [vectorDual] using (Pi.basisFun R (Fin r)).toDual_apply_left v i

/-- A coordinate basis vector in the dual reads the same coordinate. -/
theorem vectorDual_single (r : ℕ) (i : Fin r) (v : Fin r → R) :
    vectorDual (R := R) r (Pi.single i 1) v = v i := by
  simpa [vectorDual] using (Pi.basisFun R (Fin r)).toDual_apply_right i v

/-- The fixed dual relation map in the genuine standard coordinate bases. -/
def dualRelation {r1 r0 : ℕ} (f : (Fin r1 → R) →ₗ[R] (Fin r0 → R)) :
    (Fin r0 → R) →ₗ[R] (Fin r1 → R) :=
  (vectorDual r1).symm.toLinearMap.comp (f.dualMap.comp (vectorDual r0).toLinearMap)

/-- The dual relation map is exactly the dual of the actual relation map. -/
theorem dualRelation_dual {r1 r0 : ℕ} (f : (Fin r1 → R) →ₗ[R] (Fin r0 → R)) (v : Fin r0 → R) :
    vectorDual r1 (dualRelation f v) = f.dualMap (vectorDual r0 v) :=
  (vectorDual r1).apply_symm_apply _

/-- In the standard bases the actual dual relation matrix is the transpose. -/
theorem dualRelation_matrix {r1 r0 : ℕ} (f : (Fin r1 → R) →ₗ[R] (Fin r0 → R)) :
    LinearMap.toMatrix' (dualRelation f) = (LinearMap.toMatrix' f).transpose := by
  ext i j
  change dualRelation f (Pi.single j 1) i = f (Pi.single i 1) j
  rw [← vectorDual_basis r1 (dualRelation f (Pi.single j 1)) i, dualRelation_dual]
  exact vectorDual_single r0 j (f (Pi.single i 1))

/-- The based complementary-degree dual of the actual fixed free point presentation. -/
def dualPresentationCx {r1 r0 : ℕ} (f : (Fin r1 → R) →ₗ[R] (Fin r0 → R)) : BasedCx R (Fin r1) (Fin r0) where
  degE _ := 2
  degO _ := 1
  even_degE _ := ⟨1, rfl⟩
  odd_degO _ := ⟨0, rfl⟩
  dOE := 0
  dEO := LinearMap.toMatrix' (dualRelation f)
  dd_E := by simp
  dd_O := by simp
  deg_dOE _ _ h := absurd rfl h
  deg_dEO _ _ _ := rfl

/-- The differential of the based dual is the prescribed actual dual relation map. -/
theorem dualPresentationCx_d {r1 r0 : ℕ} (f : (Fin r1 → R) →ₗ[R] (Fin r0 → R)) (v : Fin r0 → R) :
    (dualPresentationCx f).dEO *ᵥ v = dualRelation f v := by
  change LinearMap.toMatrix' (dualRelation f) *ᵥ v = dualRelation f v
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

section ResidueModel

variable {F : Type} [Field F] {r1 r0 : ℕ}
  (f : (Fin r1 → F) →ₗ[F] (Fin r0 → F))

/-- The actual even residue class map of the based dual, restricting the coordinate form to the reduced relation kernel. -/
def evenClass : cyclesE (dualPresentationCx f) →ₗ[F] Module.Dual F (LinearMap.ker f) :=
  (LinearMap.ker f).dualRestrict.comp
    ((vectorDual r1).toLinearMap.comp (cyclesE (dualPresentationCx f)).subtype)

/-- The even class map of the based dual is onto. -/
theorem evenClass_surjective : Function.Surjective (evenClass f) := by
  intro ψ
  obtain ⟨φ, hφ⟩ := Subspace.dualRestrict_surjective (W := LinearMap.ker f) ψ
  let v := (vectorDual r1).symm φ
  have hv : v ∈ cyclesE (dualPresentationCx f) := by
    change (0 : Matrix (Fin r0) (Fin r1) F) *ᵥ v = 0
    exact zero_mulVec v
  refine ⟨⟨v, hv⟩, ?_⟩
  change (LinearMap.ker f).dualRestrict (vectorDual r1 ((vectorDual r1).symm φ)) = ψ
  rw [(vectorDual r1).apply_symm_apply, hφ]

/-- The even class kernel of the actual based dual is exactly its boundaries. -/
theorem evenClass_kernel (x : cyclesE (dualPresentationCx f)) :
    evenClass f x = 0 ↔ ∃ b : Fin r0 → F, (dualPresentationCx f).dEO *ᵥ b = x.val := by
  constructor
  · intro hx
    have hAnn : vectorDual r1 x.val ∈ (LinearMap.ker f).dualAnnihilator := hx
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker f] at hAnn
    obtain ⟨φ, hφ⟩ := hAnn
    refine ⟨(vectorDual r0).symm φ, ?_⟩
    rw [dualPresentationCx_d]
    apply (vectorDual r1).injective
    rw [dualRelation_dual, (vectorDual r0).apply_symm_apply, hφ]
  · rintro ⟨b, hb⟩
    change (LinearMap.ker f).dualRestrict (vectorDual r1 x.val) = 0
    rw [← hb, dualPresentationCx_d, dualRelation_dual]
    ext u
    change vectorDual r0 b (f u.val) = 0
    rw [u.2, map_zero]

/-- Odd dual cocycles are precisely the coordinate linear forms annihilating the actual reduced relation image. -/
def oddAnnihilator : cyclesO (dualPresentationCx f) →ₗ[F] (LinearMap.range f).dualAnnihilator :=
  (((vectorDual r0).toLinearMap).comp (cyclesO (dualPresentationCx f)).subtype).codRestrict _ (by
    intro x
    rw [← LinearMap.ker_dualMap_eq_dualAnnihilator_range f]
    change f.dualMap (vectorDual r0 x.val) = 0
    have hx : (dualPresentationCx f).dEO *ᵥ x.val = 0 := x.2
    rw [dualPresentationCx_d] at hx
    rw [← dualRelation_dual, hx, map_zero])

/-- The actual odd residue class of the based dual is the specified functional on the reduced point quotient. -/
def oddClass : cyclesO (dualPresentationCx f) →ₗ[F]
    Module.Dual F ((Fin r0 → F) ⧸ LinearMap.range f) :=
  (LinearMap.range f).dualQuotEquivDualAnnihilator.symm.toLinearMap.comp (oddAnnihilator f)

/-- The odd class map of the based dual is injective. -/
theorem oddClass_injective : Function.Injective (oddClass f) := by
  intro x y h
  apply Subtype.ext
  apply (vectorDual r0).injective
  have h' := (LinearMap.range f).dualQuotEquivDualAnnihilator.symm.injective h
  have hv := congrArg Subtype.val h'
  change vectorDual r0 x.val = vectorDual r0 y.val at hv
  exact hv

/-- The odd class map of the actual based dual is onto. -/
theorem oddClass_surjective : Function.Surjective (oddClass f) := by
  intro ψ
  let α := (LinearMap.range f).dualQuotEquivDualAnnihilator ψ
  let v := (vectorDual r0).symm α.val
  have hv : v ∈ cyclesO (dualPresentationCx f) := by
    change (dualPresentationCx f).dEO *ᵥ v = 0
    rw [dualPresentationCx_d]
    apply (vectorDual r1).injective
    rw [dualRelation_dual, map_zero, (vectorDual r0).apply_symm_apply]
    exact (show α.val ∈ LinearMap.ker f.dualMap from
      (LinearMap.ker_dualMap_eq_dualAnnihilator_range f).symm ▸ α.2)
  let x : cyclesO (dualPresentationCx f) := ⟨v, hv⟩
  refine ⟨x, ?_⟩
  change (LinearMap.range f).dualQuotEquivDualAnnihilator.symm (oddAnnihilator f x) = ψ
  rw [← (LinearMap.range f).dualQuotEquivDualAnnihilator.symm_apply_apply ψ]
  congr 1
  apply Subtype.ext
  exact (vectorDual r0).apply_symm_apply α.val

/-- The odd class kernel of the actual based dual is exactly its boundaries. -/
theorem oddClass_kernel (x : cyclesO (dualPresentationCx f)) :
    oddClass f x = 0 ↔ ∃ b : Fin r1 → F, (dualPresentationCx f).dOE *ᵥ b = x.val := by
  constructor
  · intro hx
    have hz : x = 0 := oddClass_injective f (hx.trans (map_zero (oddClass f)).symm)
    exact ⟨0, by rw [hz]; exact mulVec_zero _⟩
  · rintro ⟨b, hb⟩
    have hval : x.val = 0 := hb.symm.trans (zero_mulVec b)
    have hz : x = 0 := Subtype.ext hval
    rw [hz, map_zero]

/-- The full canonical residue cohomology model of the based complementary-degree dual presentation. -/
def dualPresentationModel : CohomologyModel (dualPresentationCx f)
    (Module.Dual F (LinearMap.ker f))
    (Module.Dual F ((Fin r0 → F) ⧸ LinearMap.range f)) where
  classE := evenClass f
  ontoE := evenClass_surjective f
  kernelE := evenClass_kernel f
  classO := oddClass f
  ontoO := oddClass_surjective f
  kernelO := oddClass_kernel f

end ResidueModel

section TwoTermBased

/-- A fixed finite free complex in degrees one and two, in its standard bases. -/
def twoTermBased {r1 r2 : ℕ} (d : (Fin r1 → R) →ₗ[R] (Fin r2 → R)) : BasedCx R (Fin r2) (Fin r1) where
  degE _ := 2
  degO _ := 1
  even_degE _ := ⟨1, rfl⟩
  odd_degO _ := ⟨0, rfl⟩
  dOE := 0
  dEO := LinearMap.toMatrix' d
  dd_E := by simp
  dd_O := by simp
  deg_dOE _ _ h := absurd rfl h
  deg_dEO _ _ _ := rfl

/-- The specified differential is exactly the based matrix differential. -/
theorem twoTermBased_d {r1 r2 : ℕ} (d : (Fin r1 → R) →ₗ[R] (Fin r2 → R)) (v : Fin r1 → R) :
    (twoTermBased d).dEO *ᵥ v = d v := by
  change LinearMap.toMatrix' d *ᵥ v = d v
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

/-- The dual fixed presentation has its precise finite two-term based model. -/
theorem dualPresentationCx_eq_twoTerm {r1 r0 : ℕ}
    (f : (Fin r1 → R) →ₗ[R] (Fin r0 → R)) : dualPresentationCx f = twoTermBased (dualRelation f) := rfl

/-- Canonical coefficient reduction of a finite based differential. -/
def reducedDifferential {S : Type} [CommRing S] (π : R →+* S) {r1 r2 : ℕ}
    (d : (Fin r1 → R) →ₗ[R] (Fin r2 → R)) : (Fin r1 → S) →ₗ[S] (Fin r2 → S) :=
  Matrix.toLin' ((LinearMap.toMatrix' d).map π)

/-- Coefficient reduction commutes with the specified finite two-term based model. -/
theorem twoTermBased_map {S : Type} [CommRing S] (π : R →+* S) {r1 r2 : ℕ}
    (d : (Fin r1 → R) →ₗ[R] (Fin r2 → R)) :
    (twoTermBased d).map π = twoTermBased (reducedDifferential π d) := by
  unfold twoTermBased BasedCx.map
  congr 1
  · exact Matrix.map_zero _ (map_zero π)
  · exact (LinearMap.toMatrix'_toLin' _).symm

/-- Canonical coefficient reduction commutes with the actual complementary-degree dual relation map. -/
theorem dualPresentationCx_map {S : Type} [CommRing S] (π : R →+* S) {r1 r0 : ℕ}
    (f : (Fin r1 → R) →ₗ[R] (Fin r0 → R)) :
    (dualPresentationCx f).map π = dualPresentationCx (reducedDifferential π f) := by
  unfold dualPresentationCx BasedCx.map
  congr 1
  · exact Matrix.map_zero _ (map_zero π)
  · change (LinearMap.toMatrix' (dualRelation f)).map π =
      LinearMap.toMatrix' (dualRelation (reducedDifferential π f))
    rw [dualRelation_matrix, dualRelation_matrix, reducedDifferential,
      LinearMap.toMatrix'_toLin', Matrix.transpose_map]

/-- Degree-one and degree-two maps satisfying the specified differential square give the based chain map. -/
def twoTermBasedMap {r1 r2 s1 s2 : ℕ}
    {dC : (Fin r1 → R) →ₗ[R] (Fin r2 → R)} {dD : (Fin s1 → R) →ₗ[R] (Fin s2 → R)}
    (f1 : (Fin r1 → R) →ₗ[R] (Fin s1 → R)) (f2 : (Fin r2 → R) →ₗ[R] (Fin s2 → R))
    (h : dD.comp f1 = f2.comp dC) : ChainMapR (twoTermBased dC) (twoTermBased dD) where
  fE := LinearMap.toMatrix' f2
  fO := LinearMap.toMatrix' f1
  deg_fE _ _ _ := rfl
  deg_fO _ _ _ := rfl
  commOE := by simp [twoTermBased]
  commEO := by
    change LinearMap.toMatrix' dD * LinearMap.toMatrix' f1 = LinearMap.toMatrix' f2 * LinearMap.toMatrix' dC
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp, h]

end TwoTermBased

section TwoTermCohomology

variable {F : Type} [Field F] {r1 r2 : ℕ}
  (d : (Fin r1 → F) →ₗ[F] (Fin r2 → F))

/-- The even class map of the fixed two-term source is the actual cokernel projection. -/
def twoTermEvenClass : cyclesE (twoTermBased d) →ₗ[F] ((Fin r2 → F) ⧸ LinearMap.range d) :=
  (LinearMap.range d).mkQ.comp (cyclesE (twoTermBased d)).subtype

/-- The odd class map of the fixed two-term source is the actual reduced relation kernel. -/
def twoTermOddClass : cyclesO (twoTermBased d) →ₗ[F] LinearMap.ker d :=
  (cyclesO (twoTermBased d)).subtype.codRestrict _ (fun x => by
    have hx : (twoTermBased d).dEO *ᵥ x.val = 0 := x.2
    rwa [twoTermBased_d] at hx)

/-- The full canonical residue cohomology model of the finite two-term source. -/
def twoTermModel : CohomologyModel (twoTermBased d)
    ((Fin r2 → F) ⧸ LinearMap.range d) (LinearMap.ker d) where
  classE := twoTermEvenClass d
  ontoE := by
    intro y
    obtain ⟨x, hx⟩ := (LinearMap.range d).mkQ_surjective y
    exact ⟨⟨x, zero_mulVec x⟩, hx⟩
  kernelE := by
    intro x
    change Submodule.Quotient.mk x.val = 0 ↔ ∃ b, (twoTermBased d).dEO *ᵥ b = x.val
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨b, (twoTermBased_d d b).trans hb⟩
    · rintro ⟨b, hb⟩
      exact ⟨b, (twoTermBased_d d b).symm.trans hb⟩
  classO := twoTermOddClass d
  ontoO := by
    intro x
    refine ⟨⟨x.val, ?_⟩, rfl⟩
    change (twoTermBased d).dEO *ᵥ x.val = 0
    rw [twoTermBased_d]
    exact x.2
  kernelO := by
    intro x
    constructor
    · intro hx
      have hv : x.val = 0 := congrArg Subtype.val hx
      exact ⟨0, by rw [hv]; exact mulVec_zero _⟩
    · rintro ⟨b, hb⟩
      have hv : x.val = 0 := hb.symm.trans (zero_mulVec b)
      exact Subtype.ext hv

end TwoTermCohomology

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedDual

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedBridge

open Matrix CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedDual
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.SelfDualCore

variable {R : Type} [CommRing R] {c1 c2 r1 r0 : ℕ}
  (d : (Fin c1 → R) →ₗ[R] (Fin c2 → R))
  (f : (Fin r1 → R) →ₗ[R] (Fin r0 → R))

/-- The genuine degree-one coordinate inclusion in a finite based two-term source. -/
def oddCoordinates : (Fin c1 → R) →ₗ[R] (twoTermBased d).toGCx.X 1 where
  toFun u := ⟨Sum.elim 0 u, by
    rintro (i | j) h
    · rfl
    · exact (h rfl).elim⟩
  map_add' u v := Subtype.ext (by
    change (Sum.elim (0 : Fin c2 → R) (u + v) : Fin c2 ⊕ Fin c1 → R) =
      Sum.elim (0 : Fin c2 → R) u + Sum.elim (0 : Fin c2 → R) v
    funext i
    rcases i with i | i <;> simp)
  map_smul' r u := Subtype.ext (by
    change (Sum.elim (0 : Fin c2 → R) (r • u) : Fin c2 ⊕ Fin c1 → R) =
      r • Sum.elim (0 : Fin c2 → R) u
    funext i
    rcases i with i | i <;> simp)

/-- The genuine degree-two coordinate inclusion in the same finite based source. -/
def evenCoordinates : (Fin c2 → R) →ₗ[R] (twoTermBased d).toGCx.X 2 where
  toFun u := ⟨Sum.elim u 0, by
    rintro (i | j) h
    · exact (h rfl).elim
    · rfl⟩
  map_add' u v := Subtype.ext (by
    change (Sum.elim (u + v) (0 : Fin c1 → R) : Fin c2 ⊕ Fin c1 → R) =
      Sum.elim u (0 : Fin c1 → R) + Sum.elim v (0 : Fin c1 → R)
    funext i
    rcases i with i | i <;> simp)
  map_smul' r u := Subtype.ext (by
    change (Sum.elim (r • u) (0 : Fin c1 → R) : Fin c2 ⊕ Fin c1 → R) =
      r • Sum.elim u (0 : Fin c1 → R)
    funext i
    rcases i with i | i <;> simp)

/-- The coordinate inclusions intertwine the specified genuine source differential. -/
theorem oddCoordinates_d (u : Fin c1 → R) :
    (twoTermBased d).toGCx.d 1 2 rfl (oddCoordinates d u) = evenCoordinates d (d u) := by
  apply Subtype.ext
  change (twoTermBased d).dTot *ᵥ Sum.elim 0 u = Sum.elim (d u) 0
  rw [BasedCx.dTot, fromBlocks_mulVec]
  simp only [twoTermBased, zero_mulVec, mulVec_zero, zero_add, add_zero]
  congr 1
  exact (twoTermBased_d d u)

variable (g : GHom (twoTermBased d).toGCx (dualCx (presentationCx r1 r0 f) 2))

/-- The actual degree-one component of the comparison, read as a coordinate dual form. -/
def comparisonOne : (Fin c1 → R) →ₗ[R] Module.Dual R (Fin r0 → R) :=
  (g.f 1 1 rfl).comp (oddCoordinates d)

/-- The actual degree-two component of the comparison in the complementary coordinate dual. -/
def comparisonTwo : (Fin c2 → R) →ₗ[R] Module.Dual R (Fin r1 → R) :=
  (g.f 2 2 rfl).comp (evenCoordinates d)

/-- The genuine cochain comparison gives exactly the coordinate dual differential square. -/
theorem comparison_components_commute :
    (comparisonTwo d f g).comp d = f.dualMap.comp (comparisonOne d f g) := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  have h := g.comm 1 2 1 2 rfl rfl rfl rfl (oddCoordinates d u)
  rw [oddCoordinates_d] at h
  have hv := congrArg (fun φ : (dualCx (presentationCx r1 r0 f) 2).X 2 => asDual φ v) h
  change comparisonTwo d f g (d u) v = (-(sgn (1 : ℤ))) • comparisonOne d f g u (f v) at hv
  change comparisonTwo d f g (d u) v = comparisonOne d f g u (f v)
  simpa [sgn] using hv

/-- The degree-one based matrix is obtained from the specified genuine comparison, not selected by an abstract isomorphism. -/
def comparisonOneCoordinates : (Fin c1 → R) →ₗ[R] (Fin r0 → R) :=
  (vectorDual r0).symm.toLinearMap.comp (comparisonOne d f g)

/-- The degree-two based matrix is read from the same actual trace adjoint. -/
def comparisonTwoCoordinates : (Fin c2 → R) →ₗ[R] (Fin r1 → R) :=
  (vectorDual r1).symm.toLinearMap.comp (comparisonTwo d f g)

/-- The actual coordinate comparison maps satisfy the dual-presentation square. -/
theorem coordinate_comparison_commutes :
    (dualRelation f).comp (comparisonOneCoordinates d f g) =
      (comparisonTwoCoordinates d f g).comp d := by
  apply LinearMap.ext
  intro u
  apply (vectorDual r1).injective
  rw [LinearMap.comp_apply, LinearMap.comp_apply, dualRelation_dual]
  change f.dualMap (vectorDual r0 ((vectorDual r0).symm (comparisonOne d f g u))) =
    vectorDual r1 ((vectorDual r1).symm (comparisonTwo d f g (d u)))
  rw [(vectorDual r0).apply_symm_apply, (vectorDual r1).apply_symm_apply]
  exact (LinearMap.congr_fun (comparison_components_commute d f g) u).symm

/-- The genuine cochain trace comparison in chosen source bases gives the specified integral based chain map to the dual fixed presentation. -/
def basedComparison : ChainMapR (twoTermBased d) (dualPresentationCx f) :=
  twoTermBasedMap (comparisonOneCoordinates d f g) (comparisonTwoCoordinates d f g)
    (coordinate_comparison_commutes d f g)

/-- The odd matrix of the constructed based comparison is exactly its genuine trace-adjoint coordinate map. -/
theorem basedComparison_one (u : Fin c1 → R) :
    (basedComparison d f g).fO *ᵥ u = comparisonOneCoordinates d f g u := by
  change LinearMap.toMatrix' (comparisonOneCoordinates d f g) *ᵥ u = _
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

/-- The even matrix of the constructed based comparison is exactly its genuine trace-adjoint coordinate map. -/
theorem basedComparison_two (u : Fin c2 → R) :
    (basedComparison d f g).fE *ᵥ u = comparisonTwoCoordinates d f g u := by
  change LinearMap.toMatrix' (comparisonTwoCoordinates d f g) *ᵥ u = _
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedBridge

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.ModelComparison

open Matrix
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison

variable {R : Type} [CommRing R]
  {κe κo κe' κo' : Type} [Fintype κe] [Fintype κo] [Fintype κe'] [Fintype κo']
  [DecidableEq κe] [DecidableEq κo] [DecidableEq κe'] [DecidableEq κo']
  {C : BasedCx R κe κo} {D : BasedCx R κe' κo'}
  {HE HO HE' HO' : Type} [AddCommGroup HE] [Module R HE] [AddCommGroup HO] [Module R HO]
  [AddCommGroup HE'] [Module R HE'] [AddCommGroup HO'] [Module R HO']
  (f : ChainMapR C D) (M : CohomologyModel C HE HO) (N : CohomologyModel D HE' HO')

/-- The actual target even class map composed with the specified based comparison on cycles. -/
def evenCycleClass : cyclesE C →ₗ[R] HE' := N.classE.comp (cycleMapE f)

/-- The actual target odd class map composed with the same specified chain map. -/
def oddCycleClass : cyclesO C →ₗ[R] HO' := N.classO.comp (cycleMapO f)

/-- The even comparison kills the kernel of the specified source class map because chain maps send actual boundaries to boundaries. -/
theorem evenCycleClass_kills_kernel : LinearMap.ker M.classE ≤ LinearMap.ker (evenCycleClass f N) := by
  intro x hx
  obtain ⟨b, hb⟩ := (M.kernelE x).mp hx
  apply (N.kernelE (cycleMapE f x)).mpr
  refine ⟨f.fO *ᵥ b, ?_⟩
  change D.dEO *ᵥ (f.fO *ᵥ b) = f.fE *ᵥ x.val
  rw [mulVec_mulVec, f.commEO, ← mulVec_mulVec, hb]

/-- The odd comparison kills the source class kernel for the same genuine boundary reason. -/
theorem oddCycleClass_kills_kernel : LinearMap.ker M.classO ≤ LinearMap.ker (oddCycleClass f N) := by
  intro x hx
  obtain ⟨b, hb⟩ := (M.kernelO x).mp hx
  apply (N.kernelO (cycleMapO f x)).mpr
  refine ⟨f.fE *ᵥ b, ?_⟩
  change D.dOE *ᵥ (f.fE *ᵥ b) = f.fO *ᵥ x.val
  rw [mulVec_mulVec, f.commOE, ← mulVec_mulVec, hb]

/-- The independently specified induced even comparison on the actual chosen cohomology models. -/
def alphaEven : HE →ₗ[R] HE' :=
  ((LinearMap.ker M.classE).liftQ (evenCycleClass f N) (evenCycleClass_kills_kernel f M N)).comp
    (M.classE.quotKerEquivOfSurjective M.ontoE).symm.toLinearMap

/-- The independently specified induced odd comparison on the same models. -/
def alphaOdd : HO →ₗ[R] HO' :=
  ((LinearMap.ker M.classO).liftQ (oddCycleClass f N) (oddCycleClass_kills_kernel f M N)).comp
    (M.classO.quotKerEquivOfSurjective M.ontoO).symm.toLinearMap

/-- The even commuting square is derived for these specific class maps and this specific reduced chain map. -/
theorem commE (x : cyclesE C) :
    N.classE (cycleMapE f x) = alphaEven f M N (M.classE x) := by
  let e := M.classE.quotKerEquivOfSurjective M.ontoE
  have hx : M.classE x = e (Submodule.Quotient.mk x) := rfl
  change evenCycleClass f N x =
    (LinearMap.ker M.classE).liftQ (evenCycleClass f N) (evenCycleClass_kills_kernel f M N)
      (e.symm (M.classE x))
  rw [hx, e.symm_apply_apply, Submodule.liftQ_apply]

/-- The odd commuting square is derived from the same independently specified model data. -/
theorem commO (x : cyclesO C) :
    N.classO (cycleMapO f x) = alphaOdd f M N (M.classO x) := by
  let e := M.classO.quotKerEquivOfSurjective M.ontoO
  have hx : M.classO x = e (Submodule.Quotient.mk x) := rfl
  change oddCycleClass f N x =
    (LinearMap.ker M.classO).liftQ (oddCycleClass f N) (oddCycleClass_kills_kernel f M N)
      (e.symm (M.classO x))
  rw [hx, e.symm_apply_apply, Submodule.liftQ_apply]

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.ModelComparison

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualBasedComparison

open CategoryTheory NumberField IsDedekindDomain TauCeti TauCeti.ContCohomology
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedDual
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedBridge
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualSelfDual

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]

/-- Independent finite source-model data for the genuine local quotient cone, with no self-duality assertion. -/
structure TwoTermConeBasedResolution (c1 c2 : ℕ) where
  differential : (Fin c1 → ℤ_[2]) →ₗ[ℤ_[2]] (Fin c2 → ℤ_[2])
  realization : GHom (twoTermBased differential).toGCx (localQuotientCone K w B)
  quasiIso : QuasiIso (GHom.toCC realization)

variable {c1 c2 : ℕ} (I : TwoTermConeBasedResolution K w B c1 c2)

/-- The self-dual comparison in the supplied genuine source bases, formed from the actual trace adjoint and realization. -/
def actualBasedMap (hM : MilneLocalDualityPrint) :
    ChainMapR (twoTermBased I.differential) (dualPresentationCx (actualLocalPresentation K w B).f) :=
  basedComparison I.differential (actualLocalPresentation K w B).f
    (ghomComp I.realization (localSelfDualComparison K w B hM))

/-- The fixed genuine relation differential of the point presentation reduced modulo two. -/
def pointDifferentialModTwo :
    (Fin (actualLocalPresentation K w B).rankOne → ZMod 2) →ₗ[ZMod 2]
      (Fin (actualLocalPresentation K w B).rankZero → ZMod 2) :=
  reducedDifferential (PadicInt.toZMod (p := 2)) (actualLocalPresentation K w B).f

/-- The specified source-model differential reduced in its actual bases. -/
def sourceDifferentialModTwo : (Fin c1 → ZMod 2) →ₗ[ZMod 2] (Fin c2 → ZMod 2) :=
  reducedDifferential (PadicInt.toZMod (p := 2)) I.differential

/-- The full canonical cohomology model of the reduced finite source, retaining its actual kernel and cokernel. -/
def sourceModTwoModel :
    CohomologyModel ((twoTermBased I.differential).map (PadicInt.toZMod (p := 2)))
      ((Fin c2 → ZMod 2) ⧸ LinearMap.range (sourceDifferentialModTwo K w B I))
      (LinearMap.ker (sourceDifferentialModTwo K w B I)) :=
  (twoTermBased_map (PadicInt.toZMod (p := 2)) I.differential).symm ▸
    twoTermModel (sourceDifferentialModTwo K w B I)

/-- The full canonical cohomology model of the reduced actual dual point presentation. -/
def targetModTwoModel :
    CohomologyModel ((dualPresentationCx (actualLocalPresentation K w B).f).map (PadicInt.toZMod (p := 2)))
      (Module.Dual (ZMod 2) (LinearMap.ker (pointDifferentialModTwo K w B)))
      (Module.Dual (ZMod 2)
        ((Fin (actualLocalPresentation K w B).rankZero → ZMod 2) ⧸ LinearMap.range (pointDifferentialModTwo K w B))) :=
  (dualPresentationCx_map (PadicInt.toZMod (p := 2)) (actualLocalPresentation K w B).f).symm ▸
    dualPresentationModel (pointDifferentialModTwo K w B)

/-- The specific induced even comparison for the actual trace-adjoint based map and the specified models. -/
def alphaEven (hM : MilneLocalDualityPrint) :
    ((Fin c2 → ZMod 2) ⧸ LinearMap.range (sourceDifferentialModTwo K w B I)) →ₗ[ZMod 2]
      Module.Dual (ZMod 2) (LinearMap.ker (pointDifferentialModTwo K w B)) :=
  ModelComparison.alphaEven ((actualBasedMap K w B I hM).map (PadicInt.toZMod (p := 2)))
    (sourceModTwoModel K w B I) (targetModTwoModel K w B)

/-- The specific induced odd comparison for the same genuine based map. -/
def alphaOdd (hM : MilneLocalDualityPrint) :
    LinearMap.ker (sourceDifferentialModTwo K w B I) →ₗ[ZMod 2]
      Module.Dual (ZMod 2)
        ((Fin (actualLocalPresentation K w B).rankZero → ZMod 2) ⧸ LinearMap.range (pointDifferentialModTwo K w B)) :=
  ModelComparison.alphaOdd ((actualBasedMap K w B I hM).map (PadicInt.toZMod (p := 2)))
    (sourceModTwoModel K w B I) (targetModTwoModel K w B)

/-- The even model square is derived for the actual constructed trace-adjoint chain map in the supplied source bases. -/
theorem commE (hM : MilneLocalDualityPrint)
    (x : cyclesE ((twoTermBased I.differential).map (PadicInt.toZMod (p := 2)))) :
    (targetModTwoModel K w B).classE
        (cycleMapE ((actualBasedMap K w B I hM).map (PadicInt.toZMod (p := 2))) x) =
      alphaEven K w B I hM ((sourceModTwoModel K w B I).classE x) :=
  ModelComparison.commE _ _ _ x

/-- The odd model square is derived from the same actual map and the same specified source/target models. -/
theorem commO (hM : MilneLocalDualityPrint)
    (x : cyclesO ((twoTermBased I.differential).map (PadicInt.toZMod (p := 2)))) :
    (targetModTwoModel K w B).classO
        (cycleMapO ((actualBasedMap K w B I hM).map (PadicInt.toZMod (p := 2))) x) =
      alphaOdd K w B I hM ((sourceModTwoModel K w B I).classO x) :=
  ModelComparison.commO _ _ _ x

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualBasedComparison

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteCycleLift

open TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralTrace
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.AllCochainTrace

variable (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The independent degree-three exactness statement for the actual integral local trace target. -/
def ThirdDegreeExact : Prop :=
  ∀ t : (actualTraceComplex F).X 3, ((actualTraceComplex F).d 3 4).hom t = 0 →
    ∃ y : (actualTraceComplex F).X 2, ((actualTraceComplex F).d 2 3).hom y = t

/-- Given genuine degree-three exactness, a cochain whose differential is a prescribed two-power multiple differs from an actual cocycle by that two-power multiple. -/
theorem cycleLift_of_third_exact (hexact : ThirdDegreeExact F) (a : ℕ)
    (z : (actualTraceComplex F).X 2) (t : (actualTraceComplex F).X 3)
    (ht : ((actualTraceComplex F).d 2 3).hom z = (2 : ℤ_[2]) ^ a • t) :
    ∃ w : LinearMap.ker ((actualTraceComplex F).d 2 3).hom,
      ∃ y : (actualTraceComplex F).X 2, z = w.val + (2 : ℤ_[2]) ^ a • y := by
  haveI := traceCochains_isTorsionFree F 4
  have hdt : ((actualTraceComplex F).d 3 4).hom t = 0 := by
    apply (smul_eq_zero_iff_right (R := ℤ_[2]) (M := (actualTraceComplex F).X 4)
      (pow_ne_zero a (two_ne_zero : (2 : ℤ_[2]) ≠ 0))).mp
    have h := congrArg (fun f => f.hom z) ((actualTraceComplex F).d_comp_d 2 3 4)
    have hcomp : ((actualTraceComplex F).d 3 4).hom (((actualTraceComplex F).d 2 3).hom z) = 0 := by
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h
    rwa [ht, map_smul] at hcomp
  obtain ⟨y, hy⟩ := hexact t hdt
  have hw : ((actualTraceComplex F).d 2 3).hom (z - (2 : ℤ_[2]) ^ a • y) = 0 := by
    rw [map_sub, map_smul, ht, hy, sub_self]
  exact ⟨⟨z - (2 : ℤ_[2]) ^ a • y, hw⟩, y, (sub_add_cancel _ _).symm⟩

/-- The fixed all-cochain trace has the same genuine finite invariant as an actual lifted cycle, independently of the chosen all-cochain extension. -/
theorem cycleLift_trace_normalization (a : ℕ)
    (z : (actualTraceComplex F).X 2) (w : LinearMap.ker ((actualTraceComplex F).d 2 3).hom)
    (y : (actualTraceComplex F).X 2) (h : z = w.val + (2 : ℤ_[2]) ^ a • y) :
    PadicInt.toZModPow a (AllCochainTrace.trv F z) =
      FiniteTrace.finiteInvariant F (2 ^ a) (twoPower_isUnit F a) (actualMuH2Reduction F a w) := by
  rw [h, map_add, map_smul, smul_eq_mul, map_add, map_mul, trv_finite_normalization]
  have hzero : PadicInt.toZModPow (p := 2) a ((2 : ℤ_[2]) ^ a) = 0 := by
    apply (PadicInt.toZModPow_eq_zero_iff_dvd a _).mpr
    simp only [Nat.cast_ofNat]
    exact dvd_rfl
  rw [hzero, zero_mul, add_zero]

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteCycleLift

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.RetainedTorsionNaturality

open NumberField IsDedekindDomain TauCeti
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.CloudB3RC53.Duality
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.TransportedLocal

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]

/-- An actual presentation relation divisible by two gives its specific completed rational torsion point. -/
def relationTorsion
    (x : Fin (actualLocalPresentation K w B).rankOne → ℤ_[2])
    (y : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2])
    (hxy : (actualLocalPresentation K w B).f x = (2 : ℤ_[2]) • y) :
    torsionN (2 : ℤ_[2]) (PointCompletion B.toAffine.Point) :=
  ⟨(actualLocalPresentation K w B).g y, by
    change (2 : ℤ_[2]) • (actualLocalPresentation K w B).g y = 0
    rw [← map_smul, ← hxy]
    exact LinearMap.congr_fun (actualLocalPresentation K w B).complex x⟩

/-- The exact retained-degree-zero coefficient naturality obligation for the fixed actual local presentation. This statement is recorded as an open obligation, not assumed as a printed leaf. -/
def DegreeZeroReductionNaturality : Prop :=
  ∀ (x : Fin (actualLocalPresentation K w B).rankOne → ℤ_[2])
    (y : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2])
    (hxy : (actualLocalPresentation K w B).f x = (2 : ℤ_[2]) • y),
    IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1
      (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1
        (cfun (localKummerZero K w B x) Fin.elim0)) =
    B.baseTorsionCoeff 2 (etaZero K w B (relationTorsion K w B x y hxy))

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.RetainedTorsionNaturality

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.SourceAlgebra

open CategoryTheory
open scoped Topology
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality

/-- Compatible nonempty finite-level class fibers on a compact source have a common point. -/
theorem simultaneous_class_equations {P : Type} [TopologicalSpace P] [CompactSpace P]
    (V : ℕ → Type) [∀ a, TopologicalSpace (V a)] [∀ a, T2Space (V a)]
    (t : ∀ a, V (a + 1) → V a) (g : ∀ a, P → V a) (z : ∀ a, V a)
    (hcont : ∀ a, Continuous (g a))
    (hg : ∀ a x, t a (g (a + 1) x) = g a x)
    (hz : ∀ a, t a (z (a + 1)) = z a)
    (hnonempty : ∀ a, ∃ x, g a x = z a) :
    ∃ x : P, ∀ a, g a x = z a := by
  let S : ℕ → Set P := fun a => {x | g a x = z a}
  have hclosed : ∀ a, IsClosed (S a) := fun a => isClosed_eq (hcont a) continuous_const
  have hstep : ∀ a, S (a + 1) ⊆ S a := by
    intro a x hx
    change g a x = z a
    rw [← hg a x, hx, hz]
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    S hstep hnonempty (hclosed 0).isCompact hclosed
  exact ⟨x, Set.mem_iInter.mp hx⟩

/-- Acyclicity of the genuine cone gives the actual cochain quasi-isomorphism. -/
theorem quasiIso_of_cone_acyclic {R : Type} [CommRing R] {A B : GCx R}
    (f : GHom A B) (h : GAcyclic (coneCx f)) : QuasiIso (GHom.toCC f) := by
  have h1 : QuasiIso (coneSESHom f).τ₁ := by
    change QuasiIso (GHom.toCC (idGHom (shiftDown B)))
    rw [toCC_idGHom]
    infer_instance
  have h2 : QuasiIso (coneSESHom f).τ₂ :=
    quasiIso_of_acyclic _ ((acyclic_toCC_iff _).2 h)
      ((acyclic_toCC_iff _).2 (coneCx_id_acyclic B))
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (coneSESHom f) (coneSES_shortExact f) (coneSES_shortExact _) h1 h2

/-- Reindexing a genuine cochain-map component by the identity changes only its target degree. -/
theorem component_reindex {R : Type} [CommRing R] {A B : GCx R} (f : GHom A B)
    (i j k : ℤ) (hij : i = j) (hjk : j = k) (x : A.X i) :
    (idGHom B).f j k hjk (f.f i j hij x) = f.f i k (hij.trans hjk) x := by
  subst hij
  subst hjk
  rfl

/-- The two genuine cycle/boundary conditions suffice to establish quasi-isomorphism in all degrees. -/
theorem quasiIso_of_cycle_comparisons {R : Type} [CommRing R] {A B : GCx R}
    (f : GHom A B)
    (hsurj : ∀ n (z : B.X n), B.d n (n + 1) rfl z = 0 →
      ∃ (x : A.X n) (y : B.X (n - 1)), A.d n (n + 1) rfl x = 0 ∧
        f.f n n rfl x + B.d (n - 1) n (by omega) y = z)
    (hinj : ∀ n (x : A.X n), A.d n (n + 1) rfl x = 0 →
      (∃ y : B.X (n - 1), B.d (n - 1) n (by omega) y = f.f n n rfl x) →
        ∃ y : A.X (n - 1), A.d (n - 1) n (by omega) y = x) :
    QuasiIso (GHom.toCC f) := by
  apply quasiIso_of_cone_acyclic f
  apply (acyclic_toCC_iff _).mp
  intro n
  rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro c hc
  have hc' : (coneCx f).d n (n + 1) rfl c = 0 :=
    (GCx.toCC_d_hom (coneCx f) n (n + 1) rfl c).symm.trans hc
  obtain ⟨a, b⟩ := c
  have ha : A.d n (n + 1) rfl a = 0 := congrArg Prod.fst hc'
  have hfb : f.f n n rfl a = B.d (n - 1) n (by omega) b := by
    have h0 := sub_eq_zero.mp (congrArg Prod.snd hc')
    have h1 := congrArg ((idGHom B).f (n + 1 - 1) n (by omega)) h0
    rw [component_reindex] at h1
    have h2 := (idGHom B).comm (n - 1) (n + 1 - 1) (n - 1) n
      rfl (by omega) (by omega) (by omega) b
    rw [h2, idGHom_f_self] at h1
    exact h1
  obtain ⟨x, hx⟩ := hinj n a ha ⟨b, hfb.symm⟩
  have hz : B.d (n - 1) n (by omega) (b - f.f (n - 1) (n - 1) rfl x) = 0 := by
    rw [map_sub]
    have hcomm := f.comm (n - 1) n (n - 1) n rfl (by omega) (by omega) rfl x
    rw [← hcomm, hx]
    exact sub_eq_zero.mpr hfb.symm
  have hz' : B.d (n - 1) (n - 1 + 1) rfl (b - f.f (n - 1) (n - 1) rfl x) = 0 := by
    have h := congrArg ((idGHom B).f n (n - 1 + 1) (by omega)) hz
    have hi := (idGHom B).comm (n - 1) n (n - 1) (n - 1 + 1)
      rfl (by omega) rfl (by omega) (b - f.f (n - 1) (n - 1) rfl x)
    rw [hi, idGHom_f_self, map_zero] at h
    exact h
  obtain ⟨a', y, ha', hy⟩ := hsurj (n - 1) (b - f.f (n - 1) (n - 1) rfl x) hz'
  have ha'' : A.d (n - 1) n (by omega) a' = 0 := by
    have h := congrArg ((idGHom A).f (n - 1 + 1) n (by omega)) ha'
    have hi := (idGHom A).comm (n - 1) (n - 1 + 1) (n - 1) n
      rfl rfl (by omega) (by omega) a'
    rw [hi, idGHom_f_self, map_zero] at h
    exact h
  refine ⟨(x + a', -y), ?_⟩
  apply (GCx.toCC_d_hom _ (n - 1) n (by omega) _).trans
  apply Prod.ext
  · change A.d (n - 1) n (by omega) (x + a') = a
    rw [map_add, hx, ha'', add_zero]
  · change f.f (n - 1) (n - 1) rfl (x + a') - B.d (n - 1 - 1) (n - 1) (by omega) (-y) = b
    rw [map_add, map_neg, sub_neg_eq_add, add_assoc, hy, add_sub_cancel]

/-- The actual finite residue of a two-adic integer is locally constant, hence continuous for every topology on its finite target. -/
theorem continuous_scalar_residue (a : ℕ) [TopologicalSpace (ZMod (2 ^ a))] :
    Continuous (PadicInt.toZModPow (p := 2) a) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have h : ∀ᶠ y in 𝓝 x, PadicInt.toZModPow (p := 2) a y = PadicInt.toZModPow (p := 2) a x := by
    filter_upwards [Metric.ball_mem_nhds x (zpow_pos (show (0 : ℝ) < 2 by norm_num) (-a : ℤ))] with y hy
    have hnorm : ‖y - x‖ ≤ (2 : ℝ) ^ (-a : ℤ) :=
      le_of_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hy)
    have hmem := (PadicInt.norm_le_pow_iff_mem_span_pow (y - x) a).mp hnorm
    have hdiv := Ideal.mem_span_singleton.mp hmem
    apply sub_eq_zero.mp
    rw [← map_sub]
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hmem
  exact (tendsto_const_nhds : Filter.Tendsto (fun _ : ℤ_[2] => PadicInt.toZModPow a x)
    (𝓝 x) (𝓝 (PadicInt.toZModPow a x))).congr' (h.mono fun _ hy => hy.symm)

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.SourceAlgebra

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.SourceFiniteness

variable {R U V W H : Type} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [AddCommGroup H]

/-- The actual outgoing differential descends through the actual incoming boundaries. -/
def quotientDifferential (d : U →ₗ[R] V) (b : W →ₗ[R] U) (h : d.comp b = 0) :
    (U ⧸ LinearMap.range b) →ₗ[R] V :=
  (LinearMap.range b).liftQ d (by
    rintro x ⟨y, rfl⟩
    exact LinearMap.congr_fun h y)

/-- On actual cochain representatives the quotient differential is the original differential. -/
theorem quotientDifferential_mk (d : U →ₗ[R] V) (b : W →ₗ[R] U) (h : d.comp b = 0) (u : U) :
    quotientDifferential d b h (Submodule.Quotient.mk u) = d u := rfl

/-- Finite cycle classes make the primitive classes of each actual boundary finite. -/
theorem finite_primitive_classes [Finite H]
    (d : U →ₗ[R] V) (b : W →ₗ[R] U) (h : d.comp b = 0)
    (q : LinearMap.ker d →+ H)
    (hq : ∀ x, q x = 0 ↔ ∃ y, b y = x.val)
    (z : V) (u : U) (hu : d u = z) :
    Finite {x : U ⧸ LinearMap.range b // quotientDifferential d b h x = z} := by
  classical
  let F := {x : U ⧸ LinearMap.range b // quotientDifferential d b h x = z}
  let rep (x : F) : U := ((LinearMap.range b).mkQ_surjective x.val).choose
  have hrep (x : F) : (Submodule.Quotient.mk (rep x) : U ⧸ LinearMap.range b) = x.val :=
    ((LinearMap.range b).mkQ_surjective x.val).choose_spec
  have hd (x : F) : d (rep x) = z := by
    rw [← quotientDifferential_mk d b h, hrep]
    exact x.2
  let cycle (x : F) : LinearMap.ker d := ⟨rep x - u, by
    rw [LinearMap.mem_ker, map_sub, hd, hu, sub_self]⟩
  apply Finite.of_injective (fun x : F => q (cycle x))
  intro x y hxy
  change q (cycle x) = q (cycle y) at hxy
  have hzero : q (cycle x - cycle y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨v, hv⟩ := (hq _).mp hzero
  apply Subtype.ext
  rw [← hrep x, ← hrep y]
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨v, ?_⟩
  change b v = rep x - rep y
  change b v = (rep x - u) - (rep y - u) at hv
  simpa only [sub_sub_sub_cancel_right] using hv

/-- A finite compatible segment is obtained by projecting one actual terminal value. -/
theorem compatible_segment (S : ℕ → Type) (t : ∀ n, S (n + 1) → S n)
    (default : ∀ n, S n) (N : ℕ) (v : S N) :
    ∃ x : ∀ n, S n, x N = v ∧ ∀ a < N, t a (x (a + 1)) = x a := by
  classical
  induction N with
  | zero => exact ⟨Function.update default 0 v, Function.update_self _ _ _, by omega⟩
  | succ N ih =>
    obtain ⟨x, hx, ht⟩ := ih (t N v)
    let y := Function.update x (N + 1) v
    refine ⟨y, Function.update_self _ _ _, ?_⟩
    intro a ha
    by_cases h : a = N
    · subst a
      simp only [y, Function.update_self, Function.update_of_ne (show N ≠ N + 1 by omega)]
      exact hx.symm
    · have h1 : a ≠ N + 1 := by omega
      have h2 : a + 1 ≠ N + 1 := by omega
      simp only [y, Function.update_of_ne h1, Function.update_of_ne h2]
      exact ht a (by omega)

/-- Every inverse system of nonempty finite types has an actual compatible family; surjectivity of its transition maps is not required. -/
theorem finite_system_has_section (S : ℕ → Type) [∀ n, Finite (S n)] [∀ n, Nonempty (S n)]
    (t : ∀ n, S (n + 1) → S n) :
    ∃ x : ∀ n, S n, ∀ n, t n (x (n + 1)) = x n := by
  classical
  let default : ∀ n, S n := fun n => Classical.choice (inferInstance : Nonempty (S n))
  letI : ∀ n, TopologicalSpace (S n) := fun _ => ⊥
  letI : ∀ n, DiscreteTopology (S n) := fun _ => ⟨rfl⟩
  let C : ℕ → Set (∀ n, S n) := fun N => {x | ∀ a ≤ N, t a (x (a + 1)) = x a}
  have hclosed : ∀ N, IsClosed (C N) := by
    intro N
    change IsClosed {x : ∀ n, S n | ∀ a ≤ N, t a (x (a + 1)) = x a}
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro a
    apply isClosed_iInter
    intro _
    exact isClosed_eq ((continuous_of_discreteTopology (f := t a)).comp (continuous_apply (a + 1)))
      (continuous_apply a)
  have hstep : ∀ N, C (N + 1) ⊆ C N := fun N x hx a ha => hx a (by omega)
  have hnonempty : ∀ N, (C N).Nonempty := by
    intro N
    obtain ⟨x, _, hx⟩ := compatible_segment S t default (N + 1) (default (N + 1))
    exact ⟨x, fun a ha => hx a (by omega)⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    C hstep hnonempty (hclosed 0).isCompact hclosed
  exact ⟨x, fun n => Set.mem_iInter.mp hx n n (le_refl n)⟩

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.SourceFiniteness

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.SourceKummerClasses

open ZInQ.Contrib.RC53Assist.DerivedKummer
open CategoryTheory TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer

variable (F : Type) [Field F] [CharZero F] [DecidableEq F]
  (B : WeierstrassCurve F) [B.IsElliptic]

/-- The genuine class reductions see scalar coefficients through the prescribed finite residues. -/
theorem raw_reduction_smul (a : ℕ) (r : ℤ_[2])
    (c : LinearMap.ker ((actualIntegralComplex F B).d 1 2).hom) :
    reducedOneClass (Field.absoluteGaloisGroup F) (PtAlg F B) a (r • c) =
      (PadicInt.toZModPow a r).val • reducedOneClass (Field.absoluteGaloisGroup F) (PtAlg F B) a c := by
  have h : reduceOneCycle (Field.absoluteGaloisGroup F) (PtAlg F B) a (r • c) =
      (PadicInt.toZModPow a r).val • reduceOneCycle (Field.absoluteGaloisGroup F) (PtAlg F B) a c := by
    apply Subtype.ext
    change ((reduceCochains (Field.absoluteGaloisGroup F) (PtAlg F B) a).f 1).hom (r • c.val) = _
    rw [map_smul]
    exact finiteCochain_smul_repr F B a 1 r _
  change kerToH1 (reduceOneCycle (Field.absoluteGaloisGroup F) (PtAlg F B) a (r • c)) = _
  rw [h, map_nsmul]
  rfl

/-- Genuine integral one-cocycle classes form a compatible finite family. -/
theorem raw_reduction_compatible (a : ℕ)
    (c : LinearMap.ker ((actualIntegralComplex F B).d 1 2).hom) :
    transitionH1 (Field.absoluteGaloisGroup F) (PtAlg F B) a
        (reducedOneClass (Field.absoluteGaloisGroup F) (PtAlg F B) (a + 1) c) =
      reducedOneClass (Field.absoluteGaloisGroup F) (PtAlg F B) a c := by
  change transitionH1 _ _ a (kerToH1 (reduceOneCycle _ _ (a + 1) c)) = kerToH1 (reduceOneCycle _ _ a c)
  rw [transitionH1_kerToH1]
  apply congrArg kerToH1
  apply Subtype.ext
  exact reduceCochains_succ (Field.absoluteGaloisGroup F) (PtAlg F B) a 1 c.val

variable {r : ℕ}
  (κ : (Fin r → ℤ_[2]) →ₗ[ℤ_[2]] LinearMap.ker ((actualIntegralComplex F B).d 1 2).hom)

/-- The actual finite class map of a specified based integral cycle map is computed in the specified coordinate residues. -/
theorem raw_based_reduction (a : ℕ) (u : Fin r → ℤ_[2]) :
    reducedOneClass (Field.absoluteGaloisGroup F) (PtAlg F B) a (κ u) =
      ∑ i : Fin r, (PadicInt.toZModPow a (u i)).val •
        reducedOneClass (Field.absoluteGaloisGroup F) (PtAlg F B) a (κ (Pi.single i 1)) := by
  have hu : (∑ i : Fin r, u i • (Pi.single i 1 : Fin r → ℤ_[2])) = u := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [← hu]
  simp only [map_sum, map_smul, raw_reduction_smul]

/-- Finite solvability for all prescribed actual class reductions gives one simultaneous integral based vector. -/
theorem simultaneous_based_reduction
    (c : LinearMap.ker ((actualIntegralComplex F B).d 1 2).hom)
    (hexists : ∀ a : ℕ, ∃ u : Fin r → ℤ_[2],
      reducedOneClass (Field.absoluteGaloisGroup F) (PtAlg F B) a (κ u) =
        reducedOneClass (Field.absoluteGaloisGroup F) (PtAlg F B) a c) :
    ∃ u : Fin r → ℤ_[2], ∀ a : ℕ,
      reducedOneClass (Field.absoluteGaloisGroup F) (PtAlg F B) a (κ u) =
        reducedOneClass (Field.absoluteGaloisGroup F) (PtAlg F B) a c := by
  let V (a : ℕ) := H1 (Field.absoluteGaloisGroup F) (FiniteTateCoeff (Field.absoluteGaloisGroup F) (PtAlg F B) a)
  letI : ∀ a, TopologicalSpace (V a) := fun _ => ⊥
  letI : ∀ a, DiscreteTopology (V a) := fun _ => ⟨rfl⟩
  letI : ∀ a, TopologicalSpace (ZMod (2 ^ a)) := fun _ => ⊥
  letI : ∀ a, DiscreteTopology (ZMod (2 ^ a)) := fun _ => ⟨rfl⟩
  have hcont : ∀ a, Continuous (fun u : Fin r → ℤ_[2] =>
      reducedOneClass (Field.absoluteGaloisGroup F) (PtAlg F B) a (κ u)) := by
    intro a
    have hs : Continuous (fun u : Fin r → ℤ_[2] => fun i : Fin r => PadicInt.toZModPow a (u i)) :=
      continuous_pi (fun i => (SourceAlgebra.continuous_scalar_residue a).comp (continuous_apply i))
    have ht : Continuous (fun q : Fin r → ZMod (2 ^ a) =>
        ∑ i : Fin r, (q i).val • reducedOneClass (Field.absoluteGaloisGroup F) (PtAlg F B) a (κ (Pi.single i 1))) :=
      continuous_of_discreteTopology
    convert ht.comp hs using 1
    funext u
    exact raw_based_reduction F B κ a u
  exact SourceAlgebra.simultaneous_class_equations V
    (fun a x => transitionH1 (Field.absoluteGaloisGroup F) (PtAlg F B) a x)
    (fun a u => reducedOneClass (Field.absoluteGaloisGroup F) (PtAlg F B) a (κ u))
    (fun a => reducedOneClass (Field.absoluteGaloisGroup F) (PtAlg F B) a c)
    hcont (fun a u => raw_reduction_compatible F B a (κ u))
    (fun a => raw_reduction_compatible F B a c) hexists

/-- Membership in all prescribed finite images of a fixed based cycle map implies genuine integral membership modulo actual continuous boundaries. -/
theorem integral_based_image_of_all_finite_images
    (c : LinearMap.ker ((actualIntegralComplex F B).d 1 2).hom)
    (hexists : ∀ a : ℕ, ∃ u : Fin r → ℤ_[2],
      reducedOneClass (Field.absoluteGaloisGroup F) (PtAlg F B) a (κ u) =
        reducedOneClass (Field.absoluteGaloisGroup F) (PtAlg F B) a c) :
    ∃ (u : Fin r → ℤ_[2]) (b : (actualIntegralComplex F B).X 0),
      ((actualIntegralComplex F B).d 0 1).hom b = c.val - (κ u).val := by
  obtain ⟨u, hu⟩ := simultaneous_based_reduction F B κ c hexists
  haveI := actualIntegralCoeff_compact F B
  refine ⟨u, ?_⟩
  apply integral_one_boundary_of_finite_boundaries (Field.absoluteGaloisGroup F) (PtAlg F B)
    (actualCoefficientProjection_surjective F B) (c.val - (κ u).val)
  intro a
  have hz : reducedOneClass (Field.absoluteGaloisGroup F) (PtAlg F B) a (c - κ u) = 0 := by
    rw [map_sub, hu, sub_self]
  exact (kerToH1_eq_zero_iff _).mp hz

/-- On every rational point, the completed Kummer class is exactly the genuine finite Kummer map. -/
theorem completion_class_of_point (a : ℕ) (p : B.toAffine.Point) :
    completionKummerClass F B a (completePoint B.toAffine.Point p) =
      FiniteTrace.hOneToAlg F B (2 ^ a) (B.kummerMap (2 ^ a) (twoPower_isUnit F a) p) := by
  change FiniteTrace.hOneToAlg F B (2 ^ a)
      (B.kummerClassMap (2 ^ a) _
        (completionQuotientEquiv B.toAffine.Point a (Submodule.Quotient.mk (completePoint B.toAffine.Point p)))) = _
  rw [completionQuotientEquiv_completePoint, B.kummerClassMap_mk]

/-- The independently specified finite Kummer classes separate genuine completed points at every level. -/
theorem completion_class_family_injective (x y : PointCompletion B.toAffine.Point)
    (h : ∀ a, completionKummerClass F B a x = completionKummerClass F B a y) : x = y := by
  apply Subtype.ext
  funext a
  apply (pointLevelEquiv B.toAffine.Point a).injective
  have ha := h a
  change FiniteTrace.hOneToAlg F B (2 ^ a)
      (B.kummerClassMap (2 ^ a) _ (completionQuotientEquiv B.toAffine.Point a (Submodule.Quotient.mk x))) =
    FiniteTrace.hOneToAlg F B (2 ^ a)
      (B.kummerClassMap (2 ^ a) _ (completionQuotientEquiv B.toAffine.Point a (Submodule.Quotient.mk y))) at ha
  have hq := B.kummerClassMap_injective (2 ^ a) (twoPower_isUnit F a)
    ((FiniteTrace.hOneToAlg F B (2 ^ a)).injective ha)
  simpa only [completionQuotientEquiv_mk] using hq

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.SourceKummerClasses

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.SourceDegreeZero

open NumberField IsDedekindDomain TauCeti
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction

/-- The actual Tate-module transition over several levels is the prescribed power of two. -/
theorem projection_shift (A : Type) [AddCommGroup A] (v : TateModule 2 A) (a e : ℕ) :
    (2 ^ e : ℕ) • (TateModule.proj (a + e) v).val = (TateModule.proj a v).val := by
  induction e with
  | zero => simp only [Nat.add_zero, pow_zero, one_nsmul]
  | succ e ih =>
    have h : (2 : ℕ) • (TateModule.proj (a + e + 1) v).val =
        (TateModule.proj (a + e) v).val := congrArg Subtype.val (TateModule.proj_succ v (a + e))
    rw [pow_succ', mul_nsmul]
    change (2 ^ e : ℕ) • ((2 : ℕ) • (TateModule.proj (a + e + 1) v).val) = (TateModule.proj a v).val
    rw [h]
    exact ih

/-- The genuine elliptic Tate module at an actual completion has no nonzero rational Galois invariant. -/
theorem actual_fixed_tate_eq_zero
    (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    [DecidableEq (w.adicCompletion K)]
    (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]
    (v : IntegralTateCoeff (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff)
    (hv : ∀ σ : AbsoluteGaloisGroup (w.adicCompletion K), σ • v = v) : v = 0 := by
  obtain ⟨e, he⟩ := boundedTwoPrimary_local K w B
  apply TateModule.ext
  intro a
  apply Subtype.ext
  let q : B.TorsionCoeff (2 ^ (a + e)) := TateModule.proj (a + e) v
  have hq : ∀ σ : AbsoluteGaloisGroup (w.adicCompletion K), σ • q = q := by
    intro σ
    have h := congrArg (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff (a + e)) (hv σ)
    rw [coefficientProjection_smul] at h
    exact h
  obtain ⟨t, ht⟩ := B.exists_baseTorsionCoeff_eq_of_forall_smul_eq hq
  have hqzero : (2 ^ e : ℕ) • q.val = 0 := by
    rw [← ht]
    change (2 ^ e : ℕ) • B.basePointCoeff t.val = 0
    rw [← map_nsmul, he (a + e) t.val (AddSubgroup.torsionBy.nsmul_iff.mp t.2), map_zero]
  change (TateModule.proj a v).val = 0
  rw [← projection_shift B.PointCoeff v a e]
  exact hqzero

/-- Degree zero of the genuine continuous local elliptic Tate cochains is exact. -/
theorem actual_zero_cochain_kernel
    (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    [DecidableEq (w.adicCompletion K)]
    (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]
    (b : (integralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff).X 0)
    (hb : ((integralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff).d 0 1).hom b = 0) : b = 0 := by
  let v : IntegralTateCoeff (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff :=
    ZInQ.Manuscript.RC.CoefModules.cfun b Fin.elim0
  have hv : ∀ σ : AbsoluteGaloisGroup (w.adicCompletion K), σ • v = v := by
    intro σ
    apply TateModule.ext
    intro a
    have h0 : ((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff a).d 0 1).hom
        (((reduceCochains (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff a).f 0).hom b) = 0 := by
      rw [← reduceCochains_d, hb, map_zero]
    let z : LinearMap.ker
        ((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff a).d 0 1).hom :=
      ⟨((reduceCochains (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff a).f 0).hom b, h0⟩
    have h := (FixedPoints.mem_addSubgroup _ _ _).mp
      (ZInQ.Manuscript.RC.SelmerComplex.kerToH0 z).property σ
    exact h
  have hvzero := actual_fixed_tate_eq_zero K w B v hv
  apply Subtype.ext
  funext s
  have hs : s = Fin.elim0 := Subsingleton.elim _ _
  change ZInQ.Manuscript.RC.CoefModules.cfun b s = 0
  rw [hs]
  exact hvzero

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.SourceDegreeZero

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualBockstein

open TauCeti TauCeti.ContCohomology CategoryTheory
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace

variable (F : Type) [Field F] [CharZero F] [DecidableEq F]
  (B : WeierstrassCurve F) [B.IsElliptic]

/-- Multiplication by two kills the actual first Tate level in every cochain degree. -/
theorem two_kills_first_level (k : ℕ)
    (u : (finiteIntegralComplex (AbsoluteGaloisGroup F) B.PointCoeff 1).X k) :
    (2 : ℤ_[2]) • u = 0 := by
  change ((2 : ℕ) : ℤ_[2]) • u = 0
  rw [Nat.cast_smul_eq_nsmul]
  apply contCochains_ext
  intro s
  apply Subtype.ext
  let q : FiniteTateCoeff (AbsoluteGaloisGroup F) B.PointCoeff 1 := cfun u s
  change (2 : ℕ) • (show TateModuleLevel 2 B.PointCoeff 1 from q).val = 0
  exact AddSubgroup.torsionBy.nsmul_iff.mp (show TateModuleLevel 2 B.PointCoeff 1 from q).property

/-- The actual coefficient Bockstein of a completed-point Kummer class is its specific rational two-torsion coefficient. -/
theorem completed_point_bockstein
    (b : (pointComplex F B).X 0)
    (c : LinearMap.ker ((pointComplex F B).d 1 2).hom)
    (m : PointCompletion B.toAffine.Point)
    (hb : ((pointComplex F B).d 0 1).hom b = (2 : ℤ_[2]) • c.val)
    (hc : ∀ a, pointH1Reduction F B a c =
      (hOneToAlg F B (2 ^ a)).symm (completionKummerClass F B a m)) :
    ∃ t : AddSubgroup.torsionBy B.toAffine.Point 2,
      IntegralPairing.pointLevelEquiv F B 1
          (coefficientProjection (AbsoluteGaloisGroup F) B.PointCoeff 1 (cfun b Fin.elim0)) =
        B.baseTorsionCoeff 2 t ∧ m = completePoint B.toAffine.Point t.val := by
  let v : IntegralTateCoeff (AbsoluteGaloisGroup F) B.PointCoeff := cfun b Fin.elim0
  have hd (a : ℕ) : ((finiteIntegralComplex (AbsoluteGaloisGroup F) B.PointCoeff a).d 0 1).hom
        (((reduceCochains (AbsoluteGaloisGroup F) B.PointCoeff a).f 0).hom b) =
      (2 : ℤ_[2]) • ((reduceCochains (AbsoluteGaloisGroup F) B.PointCoeff a).f 1).hom c.val := by
    rw [← reduceCochains_d, hb, map_smul]
  have hzero : ((finiteIntegralComplex (AbsoluteGaloisGroup F) B.PointCoeff 1).d 0 1).hom
      (((reduceCochains (AbsoluteGaloisGroup F) B.PointCoeff 1).f 0).hom b) = 0 :=
    (hd 1).trans (two_kills_first_level F B 1 _)
  let z : LinearMap.ker ((finiteIntegralComplex (AbsoluteGaloisGroup F) B.PointCoeff 1).d 0 1).hom :=
    ⟨((reduceCochains (AbsoluteGaloisGroup F) B.PointCoeff 1).f 0).hom b, hzero⟩
  let q : B.TorsionCoeff 2 := IntegralPairing.pointLevelEquiv F B 1
    (coefficientProjection (AbsoluteGaloisGroup F) B.PointCoeff 1 v)
  have hq : ∀ σ : AbsoluteGaloisGroup F, σ • q = q := by
    intro σ
    have h := (FixedPoints.mem_addSubgroup _ _ _).mp (kerToH0 z).property σ
    exact h
  obtain ⟨t, ht⟩ := B.exists_baseTorsionCoeff_eq_of_forall_smul_eq hq
  let Q (a : ℕ) : B.PointCoeff := (TateModule.proj (a + 1) v).val
  have hdivide (a : ℕ) : (2 ^ a : ℕ) • Q a = B.basePointCoeff t.val := by
    have h1 : (TateModule.proj 1 v).val = B.basePointCoeff t.val := congrArg Subtype.val ht.symm
    change (2 ^ a : ℕ) • (TateModule.proj (a + 1) v).val = _
    rw [Nat.add_comm a 1]
    exact (SourceDegreeZero.projection_shift B.PointCoeff v 1 a).trans h1
  have hclass (a : ℕ) : pointH1Reduction F B a c = B.kummerMap (2 ^ a) (twoPower_isUnit F a) t.val := by
    have hcycle : pointReductionZ1 F B a c =
        (⟨WeierstrassCurve.kummerCocycle (hdivide a),
          WeierstrassCurve.kummerCocycle_mem_Z1 (hdivide a)⟩ : Z1 (AbsoluteGaloisGroup F) (B.TorsionCoeff (2 ^ a))) := by
      apply Subtype.ext
      funext σ
      apply Subtype.ext
      let w : IntegralTateCoeff (AbsoluteGaloisGroup F) B.PointCoeff := cfun c.val (fun _ => σ)
      change (TateModule.proj a w).val = σ • Q a - Q a
      have h := congrArg (fun u => cfun u (fun _ => σ)) (hd (a + 1))
      simp only [contFun_d01] at h
      change σ • coefficientProjection (AbsoluteGaloisGroup F) B.PointCoeff (a + 1) v -
          coefficientProjection (AbsoluteGaloisGroup F) B.PointCoeff (a + 1) v =
        (2 : ℤ_[2]) • coefficientProjection (AbsoluteGaloisGroup F) B.PointCoeff (a + 1)
          (cfun c.val (fun _ => σ)) at h
      change _ = ((2 : ℕ) : ℤ_[2]) • _ at h
      rw [Nat.cast_smul_eq_nsmul] at h
      have hp := congrArg (fun u : FiniteTateCoeff (AbsoluteGaloisGroup F) B.PointCoeff (a + 1) =>
        (show TateModuleLevel 2 B.PointCoeff (a + 1) from u).val) h
      change σ • Q a - Q a = (2 : ℕ) • (TateModule.proj (a + 1) w).val at hp
      have hs : (2 : ℕ) • (TateModule.proj (a + 1) w).val =
          (TateModule.proj a w).val := by
        simpa only [pow_one] using SourceDegreeZero.projection_shift B.PointCoeff w a 1
      exact hs.symm.trans hp.symm
    rw [pointH1Reduction_class, hcycle]
    exact (WeierstrassCurve.kummerMap_eq_H1pi (W := B) (m := 2 ^ a)
      (twoPower_isUnit F a) (hdivide a)).symm
  have hm : m = completePoint B.toAffine.Point t.val := by
    apply SourceKummerClasses.completion_class_family_injective F B
    intro a
    have h := congrArg (hOneToAlg F B (2 ^ a)) (hc a)
    rw [(hOneToAlg F B (2 ^ a)).apply_symm_apply, hclass] at h
    rw [SourceKummerClasses.completion_class_of_point]
    exact h.symm
  exact ⟨t, ht.symm, hm⟩

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualBockstein

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralFiniteBoundary

open CategoryTheory TauCeti
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.SourceFiniteness

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Type) [AddCommGroup A] [DistribMulAction G A]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul G A]

/-- Finite genuine cycle classes make every integral cocycle detected by its actual finite reductions; no transition-surjectivity assumption on cohomology is needed. -/
theorem boundary_of_finite_boundaries (k : ℕ)
    (hcoeff : ∀ a, Function.Surjective (coefficientTransition G A a))
    (H : ℕ → Type) [∀ a, AddCommGroup (H a)] [∀ a, Finite (H a)]
    (q : ∀ a, LinearMap.ker ((finiteIntegralComplex G A a).d (k + 1) (k + 2)).hom →+ H a)
    (hq : ∀ a x, q a x = 0 ↔ ∃ y : (finiteIntegralComplex G A a).X k,
      ((finiteIntegralComplex G A a).d k (k + 1)).hom y = x.val)
    (z : (integralComplex G A).X (k + 2))
    (hz : ∀ a, ∃ u : (finiteIntegralComplex G A a).X (k + 1),
      ((finiteIntegralComplex G A a).d (k + 1) (k + 2)).hom u =
        ((reduceCochains G A a).f (k + 2)).hom z) :
    ∃ u : (integralComplex G A).X (k + 1), ((integralComplex G A).d (k + 1) (k + 2)).hom u = z := by
  classical
  choose prim hprim using hz
  let B (a : ℕ) : Submodule ℤ_[2] ((finiteIntegralComplex G A a).X (k + 1)) :=
    LinearMap.range ((finiteIntegralComplex G A a).d k (k + 1)).hom
  have dd (a : ℕ) :
      ((finiteIntegralComplex G A a).d (k + 1) (k + 2)).hom.comp
        ((finiteIntegralComplex G A a).d k (k + 1)).hom = 0 := by
    have h := congrArg ModuleCat.Hom.hom ((finiteIntegralComplex G A a).d_comp_d k (k + 1) (k + 2))
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero] using h
  let D (a : ℕ) := quotientDifferential
    ((finiteIntegralComplex G A a).d (k + 1) (k + 2)).hom
    ((finiteIntegralComplex G A a).d k (k + 1)).hom (dd a)
  let F (a : ℕ) := {x : (finiteIntegralComplex G A a).X (k + 1) ⧸ B a //
    D a x = ((reduceCochains G A a).f (k + 2)).hom z}
  letI : ∀ a, Finite (F a) := fun a => finite_primitive_classes
    ((finiteIntegralComplex G A a).d (k + 1) (k + 2)).hom
    ((finiteIntegralComplex G A a).d k (k + 1)).hom (dd a) (q a) (hq a)
    (((reduceCochains G A a).f (k + 2)).hom z) (prim a) (hprim a)
  letI : ∀ a, Nonempty (F a) := fun a => ⟨⟨(B a).mkQ (prim a), hprim a⟩⟩
  let T (a : ℕ) : ((finiteIntegralComplex G A (a + 1)).X (k + 1) ⧸ B (a + 1)) →ₗ[ℤ_[2]]
      ((finiteIntegralComplex G A a).X (k + 1) ⧸ B a) :=
    (B (a + 1)).mapQ (B a) ((transitionCochains G A a).f (k + 1)).hom (by
      rintro x ⟨y, rfl⟩
      exact ⟨((transitionCochains G A a).f k).hom y, (transitionCochains_d G A a k y).symm⟩)
  have T_mk (a : ℕ) (u : (finiteIntegralComplex G A (a + 1)).X (k + 1)) :
      T a ((B (a + 1)).mkQ u) = (B a).mkQ (((transitionCochains G A a).f (k + 1)).hom u) := rfl
  have D_T (a : ℕ) (x : (finiteIntegralComplex G A (a + 1)).X (k + 1) ⧸ B (a + 1)) :
      D a (T a x) = ((transitionCochains G A a).f (k + 2)).hom (D (a + 1) x) := by
    induction x using Submodule.Quotient.induction_on with
    | H u =>
      change ((finiteIntegralComplex G A a).d (k + 1) (k + 2)).hom
          (((transitionCochains G A a).f (k + 1)).hom u) =
        ((transitionCochains G A a).f (k + 2)).hom
          (((finiteIntegralComplex G A (a + 1)).d (k + 1) (k + 2)).hom u)
      exact (transitionCochains_d G A a (k + 1) u).symm
  let τ (a : ℕ) : F (a + 1) → F a := fun x => ⟨T a x.val, by
    rw [D_T, x.property]
    exact reduceCochains_succ G A a (k + 2) z⟩
  obtain ⟨classes, hclasses⟩ := finite_system_has_section F τ
  let rep (a : ℕ) : (finiteIntegralComplex G A a).X (k + 1) :=
    ((B a).mkQ_surjective (classes a).val).choose
  have hrep (a : ℕ) : (B a).mkQ (rep a) = (classes a).val :=
    ((B a).mkQ_surjective (classes a).val).choose_spec
  have step (a : ℕ) (u : (finiteIntegralComplex G A a).X (k + 1))
      (hu : (B a).mkQ u = (classes a).val) :
      ∃ u' : (finiteIntegralComplex G A (a + 1)).X (k + 1),
        (B (a + 1)).mkQ u' = (classes (a + 1)).val ∧
        ((transitionCochains G A a).f (k + 1)).hom u' = u := by
    have ht : T a (classes (a + 1)).val = (classes a).val := congrArg Subtype.val (hclasses a)
    have hzero : (B a).mkQ
        (((transitionCochains G A a).f (k + 1)).hom (rep (a + 1)) - u) = 0 := by
      rw [map_sub, ← T_mk, hrep, ht, hu, sub_self]
    have hmem : ((transitionCochains G A a).f (k + 1)).hom (rep (a + 1)) - u ∈ B a := by
      change Submodule.Quotient.mk _ = 0 at hzero
      rwa [Submodule.Quotient.mk_eq_zero] at hzero
    obtain ⟨v, hv⟩ := hmem
    obtain ⟨v', hv'⟩ := transitionCochains_surjective G A a k (hcoeff a) v
    refine ⟨rep (a + 1) - ((finiteIntegralComplex G A (a + 1)).d k (k + 1)).hom v', ?_, ?_⟩
    · rw [map_sub, hrep]
      have hb : (B (a + 1)).mkQ (((finiteIntegralComplex G A (a + 1)).d k (k + 1)).hom v') = 0 := by
        change Submodule.Quotient.mk _ = 0
        rw [Submodule.Quotient.mk_eq_zero]
        exact ⟨v', rfl⟩
      rw [hb, sub_zero]
    · rw [map_sub, transitionCochains_d, hv', hv, sub_sub_cancel]
  let u : ∀ a, {u : (finiteIntegralComplex G A a).X (k + 1) // (B a).mkQ u = (classes a).val} :=
    fun a => Nat.rec (motive := fun a => {u : (finiteIntegralComplex G A a).X (k + 1) //
        (B a).mkQ u = (classes a).val}) ⟨rep 0, hrep 0⟩
      (fun a u => ⟨(step a u.val u.property).choose, (step a u.val u.property).choose_spec.1⟩) a
  have hu : ∀ a, ((transitionCochains G A a).f (k + 1)).hom (u (a + 1)).val = (u a).val :=
    fun a => (step a (u a).val (u a).property).choose_spec.2
  refine ⟨liftCompatibleCochains G A (k + 1) (fun a => (u a).val) hu, ?_⟩
  apply integralCochain_ext G A (k + 2)
  intro a
  rw [reduceCochains_d, liftCompatibleCochains_projection]
  change D a ((B a).mkQ (u a).val) = _
  rw [(u a).property]
  exact (classes a).property

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralFiniteBoundary

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.RetainedTorsionNaturality

open NumberField IsDedekindDomain TauCeti
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.TransportedLocal

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]

/-- The retained-degree-zero reduction square for the fixed actual local Kummer presentation is derived from its genuine coefficient Bockstein. -/
theorem degreeZeroReductionNaturality_proof : DegreeZeroReductionNaturality K w B := by
  intro x y hxy
  obtain ⟨t, ht, hm⟩ := ActualBockstein.completed_point_bockstein (w.adicCompletion K) B
    (localKummerZero K w B x) (localKummerOne K w B y) ((actualLocalPresentation K w B).g y)
    (by
      rw [localKummerZero_d, hxy, map_smul]
      rfl)
    (by
      intro a
      rw [localKummerOne_reduction]
      change (FiniteTrace.hOneToAlg (w.adicCompletion K) B (2 ^ a)).symm
          (IntegralReduction.actualH1Reduction (w.adicCompletion K) B a
            (IntegralKummer.actualLocalKummerOne K w B y)) = _
      rw [IntegralKummer.actualLocalKummerOne, IntegralKummer.basedKummerOne_reduction])
  have hrel : relationTorsion K w B x y hxy = torsionToCompletion B.toAffine.Point 1 t :=
    Subtype.ext hm
  rw [hrel, etaZero_torsionToCompletion]
  exact ht

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.RetainedTorsionNaturality

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.SourceIntegralImage

open CategoryTheory NumberField IsDedekindDomain TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralTransport
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.TransportedLocal
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]

/-- A vector realizing an actual completed rational point reduces to exactly its genuine finite Kummer class. -/
theorem local_reduction_of_complete_point (a : ℕ)
    (u : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2]) (p : B.toAffine.Point)
    (hu : (actualLocalPresentation K w B).g u = completePoint B.toAffine.Point p) :
    pointH1Reduction (w.adicCompletion K) B a (localKummerOne K w B u) =
      B.kummerMap (2 ^ a) (twoPower_isUnit (w.adicCompletion K) a) p := by
  rw [localKummerOne_reduction]
  change (hOneToAlg (w.adicCompletion K) B (2 ^ a)).symm
    (actualH1Reduction (w.adicCompletion K) B a (actualLocalKummerOne K w B u)) = _
  rw [actualLocalKummerOne, basedKummerOne_reduction, hu,
    SourceKummerClasses.completion_class_of_point, (hOneToAlg (w.adicCompletion K) B (2 ^ a)).symm_apply_apply]

/-- Actual membership at every fixed finite Kummer reduction lifts to actual integral membership modulo continuous boundaries. -/
theorem local_integral_image_of_all_finite_images
    (c : LinearMap.ker ((pointComplex (w.adicCompletion K) B).d 1 2).hom)
    (hc : ∀ a, pointH1Reduction (w.adicCompletion K) B a c ∈
      (B.kummerMap (2 ^ a) (twoPower_isUnit (w.adicCompletion K) a)).range) :
    ∃ (u : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2])
      (b : (pointComplex (w.adicCompletion K) B).X 0),
      ((pointComplex (w.adicCompletion K) B).d 0 1).hom b = c.val - (localKummerOne K w B u).val := by
  let ca : LinearMap.ker ((actualIntegralComplex (w.adicCompletion K) B).d 1 2).hom :=
    ⟨((toAlgComplex (w.adicCompletion K) B).f 1).hom c.val, by
      change ((actualIntegralComplex (w.adicCompletion K) B).d 1 2).hom
        (((toAlgComplex (w.adicCompletion K) B).f 1).hom c.val) = 0
      have hc0 : ((pointComplex (w.adicCompletion K) B).d 1 2).hom c.val = 0 := c.2
      have h := congrArg (fun f => f.hom c.val) ((toAlgComplex (w.adicCompletion K) B).comm 1 2)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hc0, map_zero] using h⟩
  have hca : toSepCycle (w.adicCompletion K) B ca = c := by
    apply Subtype.ext
    change ((toSepComplex (w.adicCompletion K) B).f 1).hom
      (((toAlgComplex (w.adicCompletion K) B).f 1).hom c.val) = c.val
    have h := congrArg (fun f => (f.f 1).hom c.val) (toAlgComplex_toSepComplex (w.adicCompletion K) B)
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h
  have hfinite : ∀ a, ∃ u : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2],
      reducedOneClass (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B) a
          (actualLocalKummerOne K w B u) =
        reducedOneClass (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B) a ca := by
    intro a
    obtain ⟨p, hp⟩ := hc a
    obtain ⟨u, hu⟩ := (actualLocalPresentation K w B).surjective (completePoint B.toAffine.Point p)
    refine ⟨u, ?_⟩
    apply (explicitCoeff1Equiv (Field.absoluteGaloisGroup (w.adicCompletion K))
      (FiniteTateCoeff (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B) a)
      (actualLevelEquiv (w.adicCompletion K) B a) continuous_of_discreteTopology
      continuous_of_discreteTopology (actualLevelEquiv_smul (w.adicCompletion K) B a)).injective
    change actualH1Reduction (w.adicCompletion K) B a (actualLocalKummerOne K w B u) =
      actualH1Reduction (w.adicCompletion K) B a ca
    have h := (local_reduction_of_complete_point K w B a u p hu).trans hp
    change pointH1Reduction (w.adicCompletion K) B a
      (toSepCycle (w.adicCompletion K) B (actualLocalKummerOne K w B u)) =
      pointH1Reduction (w.adicCompletion K) B a c at h
    rw [← hca, integralReduction_square, integralReduction_square] at h
    exact (hOneToAlg (w.adicCompletion K) B (2 ^ a)).symm.injective h
  obtain ⟨u, b, hb⟩ := SourceKummerClasses.integral_based_image_of_all_finite_images
    (w.adicCompletion K) B (actualLocalKummerOne K w B) ca hfinite
  refine ⟨u, ((toSepComplex (w.adicCompletion K) B).f 0).hom b, ?_⟩
  rw [← toSepComplex_d, hb, map_sub]
  change (toSepCycle (w.adicCompletion K) B ca).val - (localKummerOne K w B u).val = _
  rw [hca]

/-- The printed actual finite Kummer annihilator detects the actual integral quotient class through the fixed trace and fixed reduction maps. -/
theorem local_integral_annihilator_of_print (hM : MilneLocalDualityPrint)
    (c : LinearMap.ker ((pointComplex (w.adicCompletion K) B).d 1 2).hom)
    (hc : ∀ u : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2],
      AllCochainTrace.trv (w.adicCompletion K)
        (integralCupOne (w.adicCompletion K) B (localKummerOne K w B u).val c.val) = 0) :
    ∃ (u : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2])
      (b : (pointComplex (w.adicCompletion K) B).X 0),
      ((pointComplex (w.adicCompletion K) B).d 0 1).hom b = c.val - (localKummerOne K w B u).val := by
  apply local_integral_image_of_all_finite_images K w B c
  intro a
  apply (kummer_exact_annihilator_of_print hM (w.adicCompletion K) B
    (2 ^ a) (twoPower_isUnit (w.adicCompletion K) a) _).mpr
  rintro x ⟨p, rfl⟩
  obtain ⟨u, hu⟩ := (actualLocalPresentation K w B).surjective (completePoint B.toAffine.Point p)
  have hzero := congrArg (padicInvariant a) (hc u)
  rw [map_zero] at hzero
  have hnorm : padicInvariant a (AllCochainTrace.trv (w.adicCompletion K)
        (integralCupOne (w.adicCompletion K) B (localKummerOne K w B u).val c.val)) =
      ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B (2 ^ a)
        (twoPower_isUnit (w.adicCompletion K) a)
        (pointH1Reduction (w.adicCompletion K) B a (localKummerOne K w B u))
        (pointH1Reduction (w.adicCompletion K) B a c) := by
    change padicInvariant a (AllCochainTrace.trv (w.adicCompletion K)
      (integralCupCycle (w.adicCompletion K) B (localKummerOne K w B u) c).val) = _
    rw [AllCochainTrace.trv_on_cycles, IntegralCompatibility.integralCup_invariant_compatibility]
  rw [local_reduction_of_complete_point K w B a u p hu] at hnorm
  exact hnorm.symm.trans hzero

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.SourceIntegralImage

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.SourceFirstCohomology

open CategoryTheory NumberField IsDedekindDomain TauCeti
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.TransportedLocal

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]

/-- Actual degree-one cycles in the genuine local point Tate cochains. -/
abbrev cycles : Submodule ℤ_[2] ((pointComplex (w.adicCompletion K) B).X 1) :=
  LinearMap.ker ((pointComplex (w.adicCompletion K) B).d 1 2).hom

/-- The actual incoming differential, with its genuine cycle codomain. -/
def incoming : (pointComplex (w.adicCompletion K) B).X 0 →ₗ[ℤ_[2]] cycles K w B :=
  ((pointComplex (w.adicCompletion K) B).d 0 1).hom.codRestrict _ (fun b => by
    change ((pointComplex (w.adicCompletion K) B).d 1 2).hom
      (((pointComplex (w.adicCompletion K) B).d 0 1).hom b) = 0
    have h := congrArg (fun f => f.hom b) ((pointComplex (w.adicCompletion K) B).d_comp_d 0 1 2)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h)

/-- Degree-one boundaries of the actual quotient cone include the actual local Kummer image. -/
def boundaries : Submodule ℤ_[2] (cycles K w B) :=
  LinearMap.range (incoming K w B) ⊔ LinearMap.range (localKummerOne K w B)

/-- The actual degree-one quotient by continuous boundaries and the fixed completed Kummer condition. -/
abbrev sourceOne := cycles K w B ⧸ boundaries K w B

/-- The actual trace-cup pairing on degree-one source cycles, evaluated on the fixed point generators. -/
def pairing : cycles K w B →ₗ[ℤ_[2]]
    Module.Dual ℤ_[2] (Fin (actualLocalPresentation K w B).rankZero → ℤ_[2]) where
  toFun c := ((AllCochainTrace.trv (w.adicCompletion K)).comp
    ((integralCupOne (w.adicCompletion K) B).flip c.val)).comp
      ((cycles K w B).subtype.comp (localKummerOne K w B))
  map_add' c d := by
    apply LinearMap.ext
    intro u
    change AllCochainTrace.trv (w.adicCompletion K)
        (integralCupOne (w.adicCompletion K) B (localKummerOne K w B u).val (c.val + d.val)) = _
    rw [map_add, map_add]
    rfl
  map_smul' r c := by
    apply LinearMap.ext
    intro u
    change AllCochainTrace.trv (w.adicCompletion K)
        (integralCupOne (w.adicCompletion K) B (localKummerOne K w B u).val (r • c.val)) = _
    rw [map_smul, map_smul]
    rfl

/-- The actual trace-cup pairing kills an actual continuous boundary. -/
theorem pairing_incoming (b : (pointComplex (w.adicCompletion K) B).X 0)
    (u : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2]) :
    pairing K w B (incoming K w B b) u = 0 := by
  have hk : ((pointComplex (w.adicCompletion K) B).d 1 2).hom (localKummerOne K w B u).val = 0 :=
    (localKummerOne K w B u).property
  have h := (integralCupPair (w.adicCompletion K) B).leib 1 0 1 rfl
    (localKummerOne K w B u).val b
  rw [hk, LinearMap.map_zero₂, zero_add] at h
  simp only [pow_one, neg_one_smul] at h
  change ((IntegralReduction.actualTraceComplex (w.adicCompletion K)).d 1 2).hom
      (((integralCupPair (w.adicCompletion K) B).P 1 0 1 rfl) (localKummerOne K w B u).val b) =
    -(integralCupOne (w.adicCompletion K) B (localKummerOne K w B u).val
      (((pointComplex (w.adicCompletion K) B).d 0 1).hom b)) at h
  have ht : -(AllCochainTrace.trv (w.adicCompletion K)
      (integralCupOne (w.adicCompletion K) B (localKummerOne K w B u).val
        (((pointComplex (w.adicCompletion K) B).d 0 1).hom b))) = 0 := by
    rw [← map_neg, ← h]
    exact AllCochainTrace.htrv (w.adicCompletion K) _
  change AllCochainTrace.trv (w.adicCompletion K)
    (integralCupOne (w.adicCompletion K) B (localKummerOne K w B u).val
      (((pointComplex (w.adicCompletion K) B).d 0 1).hom b)) = 0
  exact neg_eq_zero.mp ht

/-- Both actual boundary summands are killed before passing to the quotient. -/
theorem boundaries_le_kernel (hM : MilneLocalDualityPrint) :
    boundaries K w B ≤ LinearMap.ker (pairing K w B) := by
  apply sup_le
  · rintro c ⟨b, rfl⟩
    change pairing K w B (incoming K w B b) = 0
    apply LinearMap.ext
    intro u
    exact pairing_incoming K w B b u
  · rintro c ⟨u, rfl⟩
    change pairing K w B (localKummerOne K w B u) = 0
    apply LinearMap.ext
    intro v
    exact localCup_trace_zero K w B hM v u

/-- The fixed actual trace pairing descends to the actual degree-one quotient cone class module. -/
def classPairing (hM : MilneLocalDualityPrint) : sourceOne K w B →ₗ[ℤ_[2]]
    Module.Dual ℤ_[2] (Fin (actualLocalPresentation K w B).rankZero → ℤ_[2]) :=
  (boundaries K w B).liftQ (pairing K w B) (boundaries_le_kernel K w B hM)

/-- The actual integral annihilator theorem makes this particular class pairing injective. -/
theorem classPairing_injective (hM : MilneLocalDualityPrint) :
    Function.Injective (classPairing K w B hM) := by
  have hzero : ∀ z : sourceOne K w B, classPairing K w B hM z = 0 → z = 0 := by
    intro z hz
    obtain ⟨c, hc⟩ := (boundaries K w B).mkQ_surjective z
    have hp : pairing K w B c = 0 := by
      change classPairing K w B hM ((boundaries K w B).mkQ c) = 0
      rw [hc]
      exact hz
    obtain ⟨u, b, hb⟩ := SourceIntegralImage.local_integral_annihilator_of_print K w B hM c
      (fun v => LinearMap.congr_fun hp v)
    have heq : c = incoming K w B b + localKummerOne K w B u := by
      apply Subtype.ext
      change c.val = ((pointComplex (w.adicCompletion K) B).d 0 1).hom b + (localKummerOne K w B u).val
      exact sub_eq_iff_eq_add.mp hb.symm
    rw [← hc]
    change Submodule.Quotient.mk c = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_sup.mpr ⟨incoming K w B b, ⟨b, rfl⟩,
      localKummerOne K w B u, ⟨u, rfl⟩, heq.symm⟩
  intro z y h
  have hz : classPairing K w B hM (z - y) = 0 := by rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (hzero _ hz)

/-- Degree-one cohomology of the actual local quotient cone is finite over the integral coefficient ring. -/
theorem sourceOne_finite (hM : MilneLocalDualityPrint) : Module.Finite ℤ_[2] (sourceOne K w B) :=
  Module.Finite.of_injective (classPairing K w B hM) (classPairing_injective K w B hM)

/-- The actual degree-one quotient cone class module has no integral scalar torsion. -/
theorem sourceOne_torsionFree (hM : MilneLocalDualityPrint) :
    Module.IsTorsionFree ℤ_[2] (sourceOne K w B) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r x hx
  by_cases hr : r = 0
  · exact Or.inl hr
  · right
    have h : r • classPairing K w B hM x = 0 := by
      have h := congrArg (classPairing K w B hM) hx
      simpa only [map_smul, map_zero] using h
    have hz := (smul_eq_zero_iff_right (R := ℤ_[2])
      (M := Module.Dual ℤ_[2] (Fin (actualLocalPresentation K w B).rankZero → ℤ_[2])) hr).mp h
    apply classPairing_injective K w B hM
    rw [map_zero]
    exact hz

/-- Degree-one cohomology of the actual quotient condition is finite free over the two-adic coefficient ring. -/
theorem sourceOne_free (hM : MilneLocalDualityPrint) : Module.Free ℤ_[2] (sourceOne K w B) := by
  haveI := sourceOne_finite K w B hM
  haveI := sourceOne_torsionFree K w B hM
  infer_instance

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.SourceFirstCohomology

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.UniformReductions

/-- Equality at a higher compatible level implies equality at each prescribed lower level. -/
theorem equality_at_lower_level {X : Type} (V : ℕ → Type)
    (t : ∀ n, V (n + 1) → V n) (q : ∀ n, X → V n)
    (hq : ∀ n x, t n (q (n + 1) x) = q n x) (a b : ℕ) (hab : a ≤ b) :
    ∀ x y, q b x = q b y → q a x = q a y := by
  induction hab with
  | refl => intro x y h; exact h
  | @step b hab ih =>
    intro x y h
    apply ih x y
    rw [← hq b x, ← hq b y, h]

/-- A uniformly bounded compatible finite family that separates actual classes proves finiteness of those classes. -/
theorem finite_of_uniform_separating_reductions {X : Type}
    (V : ℕ → Type) [∀ n, Finite (V n)]
    (t : ∀ n, V (n + 1) → V n) (q : ∀ n, X → V n)
    (hq : ∀ n x, t n (q (n + 1) x) = q n x)
    (hsep : ∀ x y, (∀ n, q n x = q n y) → x = y)
    (B : ℕ) (hB : ∀ n, Nat.card (V n) ≤ B) : Finite X := by
  classical
  by_contra hX
  letI : Infinite X := ⟨hX⟩
  let e : Fin (B + 1) ↪ X :=
    ⟨fun i => Infinite.natEmbedding X i.val, (Infinite.natEmbedding X).injective.comp Fin.val_injective⟩
  have hd : ∀ i j : Fin (B + 1), i ≠ j → ∃ n, q n (e i) ≠ q n (e j) := by
    intro i j hij
    by_contra h
    apply hij
    apply e.injective
    apply hsep
    intro n
    by_contra hn
    exact h ⟨n, hn⟩
  let level (p : Fin (B + 1) × Fin (B + 1)) : ℕ :=
    if h : p.1 = p.2 then 0 else (hd p.1 p.2 h).choose
  let N := Finset.univ.sup level
  have hqi : Function.Injective (fun i : Fin (B + 1) => q N (e i)) := by
    intro i j hij
    by_contra hne
    have hl : level (i, j) ≤ N := Finset.le_sup (Finset.mem_univ (i, j))
    have heq := equality_at_lower_level V t q hq (level (i, j)) N hl (e i) (e j) hij
    have hneq : q (level (i, j)) (e i) ≠ q (level (i, j)) (e j) := by
      have hlv : level (i, j) = (hd i j hne).choose := by
        dsimp only [level]
        split
        · rename_i h
          exact (hne h).elim
        · rfl
      rw [hlv]
      exact (hd i j hne).choose_spec
    exact hneq heq
  letI := Fintype.ofFinite (V N)
  have hcard := Fintype.card_le_of_injective (fun i : Fin (B + 1) => q N (e i)) hqi
  have hbound := hB N
  simp only [Fintype.card_fin, Nat.card_eq_fintype_card] at hcard hbound
  omega

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.UniformReductions

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.SourceCharacterBound

open ZInQ.Contrib.RC53Assist.DerivedKummer

variable (P : Type) [AddCommGroup P] (e : ℕ)
  (he : ∀ (a : ℕ) (p : P), (2 ^ a : ℕ) • p = 0 → (2 ^ e : ℕ) • p = 0)
  [Finite (AddSubgroup.torsionBy P (2 ^ e))]

/-- Every finite primary torsion level injects into the actual fixed bounded level. -/
def torsionEmbedding (a : ℕ) : AddSubgroup.torsionBy P (2 ^ a) ↪ AddSubgroup.torsionBy P (2 ^ e) where
  toFun t := ⟨t.val, AddSubgroup.torsionBy.nsmul_iff.mpr (he a t.val (AddSubgroup.torsionBy.nsmul_iff.mp t.2))⟩
  inj' t u h := by
    have hv := congrArg (fun x : AddSubgroup.torsionBy P (2 ^ e) => x.val) h
    exact Subtype.ext hv

include he in
/-- Finite primary-torsion character groups have one uniform finite cardinality bound. -/
theorem characters_card_bound (a : ℕ) :
    Nat.card (AddSubgroup.torsionBy P (2 ^ a) →+ RationalCircle) ≤
      (2 ^ e) ^ Nat.card (AddSubgroup.torsionBy P (2 ^ e)) := by
  classical
  let T := AddSubgroup.torsionBy P (2 ^ a)
  let E := AddSubgroup.torsionBy P (2 ^ e)
  letI : Finite T := Finite.of_injective (torsionEmbedding P e he a) (torsionEmbedding P e he a).injective
  letI := Fintype.ofFinite T
  letI := Fintype.ofFinite E
  have hkill : ∀ t : T, (2 ^ e : ℕ) • t = 0 := by
    intro t
    apply Subtype.ext
    exact he a t.val (AddSubgroup.torsionBy.nsmul_iff.mp t.2)
  let c := charactersToZMod (2 ^ e) hkill
  let f : (T →+ RationalCircle) → (T → ZMod (2 ^ e)) := fun χ => c χ
  have hf : Function.Injective f := by
    intro χ ψ h
    apply c.injective
    exact AddMonoidHom.ext (congrFun h)
  letI : Finite (T →+ RationalCircle) := Finite.of_injective f hf
  letI := Fintype.ofFinite (T →+ RationalCircle)
  have hcard := Fintype.card_le_of_injective f hf
  have ht := Fintype.card_le_of_injective (torsionEmbedding P e he a)
    (torsionEmbedding P e he a).injective
  have hpow : (2 ^ e) ^ Fintype.card T ≤ (2 ^ e) ^ Fintype.card E :=
    Nat.pow_le_pow_right (by positivity) ht
  simp only [Fintype.card_fun, ZMod.card] at hcard
  simpa only [Nat.card_eq_fintype_card] using hcard.trans hpow

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.SourceCharacterBound

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.SourceSecondCohomology

open CategoryTheory NumberField IsDedekindDomain TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]

/-- The actual degree-two cycles, in the fixed algebraic-closure cochain description. -/
abbrev cycles : Submodule ℤ_[2] ((actualIntegralComplex (w.adicCompletion K) B).X 2) :=
  LinearMap.ker ((actualIntegralComplex (w.adicCompletion K) B).d 2 3).hom

/-- The genuine incoming differential into degree-two cycles. -/
def incoming : (actualIntegralComplex (w.adicCompletion K) B).X 1 →ₗ[ℤ_[2]] cycles K w B :=
  ((actualIntegralComplex (w.adicCompletion K) B).d 1 2).hom.codRestrict _ (fun b => by
    change ((actualIntegralComplex (w.adicCompletion K) B).d 2 3).hom
      (((actualIntegralComplex (w.adicCompletion K) B).d 1 2).hom b) = 0
    have h := congrArg (fun f => f.hom b) ((actualIntegralComplex (w.adicCompletion K) B).d_comp_d 1 2 3)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h)

/-- Actual integral degree-two cohomology retains the torsion boundary quotient. -/
abbrev sourceTwo := cycles K w B ⧸ LinearMap.range (incoming K w B)

/-- A fixed actual cycle representative of each actual integral degree-two class. -/
def representative (x : sourceTwo K w B) : cycles K w B :=
  ((LinearMap.range (incoming K w B)).mkQ_surjective x).choose

/-- The representative realizes its specified class in the actual boundary quotient. -/
theorem representative_class (x : sourceTwo K w B) :
    (LinearMap.range (incoming K w B)).mkQ (representative K w B x) = x :=
  ((LinearMap.range (incoming K w B)).mkQ_surjective x).choose_spec

/-- The fixed finite source coefficient projections give genuine surjective coefficient transitions. -/
theorem point_transition_surjective (a : ℕ) :
    Function.Surjective (coefficientTransition (Field.absoluteGaloisGroup (w.adicCompletion K))
      (PtAlg (w.adicCompletion K) B) a) := by
  intro t
  obtain ⟨v, hv⟩ := actualCoefficientProjection_surjective (w.adicCompletion K) B a t
  exact ⟨coefficientProjection _ _ (a + 1) v, (coefficientProjection_succ _ _ a v).trans hv⟩

/-- Finite actual first cohomology, needed for the actual primitive-class lifting argument. -/
theorem finite_first_level (hF : MilneFiniteLocalDualityPrint) (a : ℕ) :
    Finite (H1 (Field.absoluteGaloisGroup (w.adicCompletion K))
      (FiniteTateCoeff (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B) a)) := by
  haveI := (hF (w.adicCompletion K) B (2 ^ a) (twoPower_isUnit (w.adicCompletion K) a)).1
  let e := (explicitCoeff1Equiv (Field.absoluteGaloisGroup (w.adicCompletion K))
    (FiniteTateCoeff (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B) a)
    (actualLevelEquiv (w.adicCompletion K) B a) continuous_of_discreteTopology
    continuous_of_discreteTopology (actualLevelEquiv_smul (w.adicCompletion K) B a)).trans
      (hOneToAlg (w.adicCompletion K) B (2 ^ a)).symm
  exact Finite.of_equiv (H1 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff (2 ^ a))) e.symm.toEquiv

/-- Actual finite second cohomology is identified with the finite rational-torsion character group by the cited pairing, not by an arbitrary group isomorphism. -/
def finite_second_dictionary (a : ℕ) :
    H2 (Field.absoluteGaloisGroup (w.adicCompletion K))
      (FiniteTateCoeff (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B) a) ≃+
        H2 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff (2 ^ a)) :=
  (explicitCoeff2Equiv (Field.absoluteGaloisGroup (w.adicCompletion K))
    (FiniteTateCoeff (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B) a)
    (actualLevelEquiv (w.adicCompletion K) B a) continuous_of_discreteTopology
    continuous_of_discreteTopology (actualLevelEquiv_smul (w.adicCompletion K) B a)).trans
      (hTwoToAlg (w.adicCompletion K) B (2 ^ a)).symm

/-- The actual finite second class transition is the genuine multiplication transition on coefficients. -/
def transition (a : ℕ) :=
  explicitCoeff2 (Field.absoluteGaloisGroup (w.adicCompletion K))
    (FiniteTateCoeff (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B) (a + 1))
    (transitionCoefficientHom (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B) a)
    continuous_of_discreteTopology

/-- The actual integral degree-two classes reduce through their specified actual representatives. -/
def reduction (a : ℕ) (x : sourceTwo K w B) :=
  reducedTwoClass (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B) a
    (representative K w B x)

/-- The specified degree-two class reductions are compatible with the actual finite coefficient transitions. -/
theorem reduction_compatible (a : ℕ) (x : sourceTwo K w B) :
    transition K w B a (reduction K w B (a + 1) x) = reduction K w B a x := by
  change explicitCoeff2 _ _ _ _ (kerToH2 (reduceTwoCycle _ _ (a + 1) _)) = kerToH2 (reduceTwoCycle _ _ a _)
  erw [kerToH2_apply, explicitCoeff2_mk]
  apply congrArg (H2pi _ _)
  apply Subtype.ext
  funext p
  obtain ⟨σ, τ⟩ := p
  exact congrArg (fun v => cfun v ![σ, τ])
    (reduceCochains_succ (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B) a 2 _)

/-- Genuine finite class reductions separate actual integral degree-two classes, by finite first-cohomology primitive classes. -/
theorem reduction_separates (hF : MilneFiniteLocalDualityPrint) (x y : sourceTwo K w B)
    (hxy : ∀ a, reduction K w B a x = reduction K w B a y) : x = y := by
  let c := representative K w B x - representative K w B y
  let H (a : ℕ) := H1 (Field.absoluteGaloisGroup (w.adicCompletion K))
    (FiniteTateCoeff (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B) a)
  letI : ∀ a, Finite (H a) := fun a => finite_first_level K w B hF a
  obtain ⟨b, hb⟩ := IntegralFiniteBoundary.boundary_of_finite_boundaries
    (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B) 0
    (point_transition_surjective K w B) H
    (fun a => kerToH1 (k := ℤ_[2]) (G := Field.absoluteGaloisGroup (w.adicCompletion K))
      (M := FiniteTateCoeff (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B) a))
    (fun a z => kerToH1_eq_zero_iff z) c.val (by
      intro a
      have hz : reducedTwoClass (Field.absoluteGaloisGroup (w.adicCompletion K))
          (PtAlg (w.adicCompletion K) B) a c = 0 := by
        change reducedTwoClass (Field.absoluteGaloisGroup (w.adicCompletion K))
          (PtAlg (w.adicCompletion K) B) a (representative K w B x - representative K w B y) = 0
        rw [map_sub]
        exact sub_eq_zero.mpr (hxy a)
      exact (kerToH2_eq_zero_iff _).mp hz)
  rw [← representative_class K w B x, ← representative_class K w B y]
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨b, ?_⟩
  apply Subtype.ext
  exact hb

/-- Each genuine finite second class group is finite by the fixed Milne character dictionary. -/
theorem finite_second_level (hF : MilneFiniteLocalDualityPrint) (a : ℕ) :
    Finite (H2 (Field.absoluteGaloisGroup (w.adicCompletion K))
      (FiniteTateCoeff (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B) a)) := by
  classical
  let T := AddSubgroup.torsionBy B.toAffine.Point (2 ^ a)
  haveI : Finite T := WeierstrassCurve.finite_torsionBy B (by
    exact_mod_cast pow_ne_zero a (by decide : (2 : ℕ) ≠ 0))
  have hT : ∀ t : T, (2 ^ a : ℕ) • t = 0 := by
    intro t
    exact Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.mp t.2)
  let d := charactersToZMod (2 ^ a) hT
  haveI : Finite (T →+ RationalCircle) := by
    apply Finite.of_injective (fun f : T →+ RationalCircle => (d f : T → ZMod (2 ^ a)))
    intro f g h
    apply d.injective
    exact AddMonoidHom.ext (congrFun h)
  obtain ⟨_, _, _, e, _⟩ := hF (w.adicCompletion K) B (2 ^ a) (twoPower_isUnit (w.adicCompletion K) a)
  exact Finite.of_equiv (T →+ RationalCircle) ((finite_second_dictionary K w B a).trans e).symm.toEquiv

/-- Bounded genuine rational torsion bounds all actual finite second cohomology groups uniformly. -/
theorem finite_second_uniform_bound (hF : MilneFiniteLocalDualityPrint) :
    ∃ N : ℕ, ∀ a, Nat.card (H2 (Field.absoluteGaloisGroup (w.adicCompletion K))
      (FiniteTateCoeff (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B) a)) ≤ N := by
  obtain ⟨e, he⟩ := boundedTwoPrimary_local K w B
  haveI : Finite (AddSubgroup.torsionBy B.toAffine.Point (2 ^ e)) :=
    WeierstrassCurve.finite_torsionBy B (by exact_mod_cast pow_ne_zero e (by decide : (2 : ℕ) ≠ 0))
  refine ⟨(2 ^ e) ^ Nat.card (AddSubgroup.torsionBy B.toAffine.Point (2 ^ e)), ?_⟩
  intro a
  obtain ⟨_, _, _, f, _⟩ := hF (w.adicCompletion K) B (2 ^ a) (twoPower_isUnit (w.adicCompletion K) a)
  rw [Nat.card_congr ((finite_second_dictionary K w B a).trans f).toEquiv]
  exact SourceCharacterBound.characters_card_bound B.toAffine.Point e he a

/-- The actual integral degree-two quotient has finite cardinality, not merely finite rank. -/
theorem sourceTwo_finite (hF : MilneFiniteLocalDualityPrint) : Finite (sourceTwo K w B) := by
  let V (a : ℕ) := H2 (Field.absoluteGaloisGroup (w.adicCompletion K))
    (FiniteTateCoeff (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B) a)
  letI : ∀ a, Finite (V a) := fun a => finite_second_level K w B hF a
  obtain ⟨N, hN⟩ := finite_second_uniform_bound K w B hF
  exact UniformReductions.finite_of_uniform_separating_reductions V
    (fun a x => transition K w B a x) (reduction K w B)
    (fun a x => reduction_compatible K w B a x) (fun x y h => reduction_separates K w B hF x y h) N hN

/-- Actual integral degree-two cohomology is consequently a finite module over the two-adic ring. -/
theorem sourceTwo_moduleFinite (hF : MilneFiniteLocalDualityPrint) :
    Module.Finite ℤ_[2] (sourceTwo K w B) := by
  haveI := sourceTwo_finite K w B hF
  infer_instance

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.SourceSecondCohomology

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteSourceCoordinates

open Matrix CategoryTheory
open ZInQ.Contrib.CloudB3RC53.Torsion ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedDual
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedBridge

variable {R : Type} [CommRing R] {r1 r2 : ℕ}
  (d : (Fin r1 → R) →ₗ[R] (Fin r2 → R))

def oddProjection : (twoTermBased d).toGCx.X 1 →ₗ[R] (Fin r1 → R) where
  toFun x i := x.val (Sum.inr i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def evenProjection : (twoTermBased d).toGCx.X 2 →ₗ[R] (Fin r2 → R) where
  toFun x i := x.val (Sum.inl i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The prescribed odd-coordinate inclusion and projection recover each actual degree-one source vector. -/
theorem odd_reconstruct (x : (twoTermBased d).toGCx.X 1) : oddCoordinates d (oddProjection d x) = x := by
  apply Subtype.ext
  funext i
  rcases i with i | i
  · change 0 = x.val (Sum.inl i)
    exact (x.2 (Sum.inl i) (by change (2 : ℤ) ≠ 1; norm_num)).symm
  · rfl

/-- The prescribed even-coordinate inclusion and projection recover degree two. -/
theorem even_reconstruct (x : (twoTermBased d).toGCx.X 2) : evenCoordinates d (evenProjection d x) = x := by
  apply Subtype.ext
  funext i
  rcases i with i | i
  · rfl
  · change 0 = x.val (Sum.inr i)
    exact (x.2 (Sum.inr i) (by change (1 : ℤ) ≠ 2; norm_num)).symm

/-- All other source degrees are actually zero. -/
theorem source_subsingleton (n : ℤ) (h1 : n ≠ 1) (h2 : n ≠ 2) :
    Subsingleton ((twoTermBased d).toGCx.X n) := by
  refine ⟨fun x y => Subtype.ext (funext fun i => ?_)⟩
  rcases i with i | i
  · exact (x.2 (Sum.inl i) (by change (2 : ℤ) ≠ n; exact h2.symm)).trans
      (y.2 (Sum.inl i) (by change (2 : ℤ) ≠ n; exact h2.symm)).symm
  · exact (x.2 (Sum.inr i) (by change (1 : ℤ) ≠ n; exact h1.symm)).trans
      (y.2 (Sum.inr i) (by change (1 : ℤ) ≠ n; exact h1.symm)).symm

/-- The outgoing differential of an actual degree-two source vector is zero. -/
theorem even_d_zero (u : Fin r2 → R) : (twoTermBased d).toGCx.d 2 3 rfl (evenCoordinates d u) = 0 := by
  apply Subtype.ext
  change (twoTermBased d).dTot *ᵥ Sum.elim u 0 = 0
  rw [BasedCx.dTot, fromBlocks_mulVec]
  simp only [twoTermBased, zero_mulVec, mulVec_zero, zero_add]
  change Sum.elim ((LinearMap.toMatrix' d) *ᵥ (0 : Fin r1 → R)) (0 : Fin r1 → R) = 0
  rw [mulVec_zero]
  funext i
  rcases i with i | i <;> rfl

variable (C : GCx R)
  (f1 : (Fin r1 → R) →ₗ[R] C.X 1) (f2 : (Fin r2 → R) →ₗ[R] C.X 2)

def realizationComponent (n : ℤ) : (twoTermBased d).toGCx.X n →ₗ[R] C.X n :=
  if h1 : n = 1 then h1.symm ▸ f1.comp (oddProjection d)
  else if h2 : n = 2 then h2.symm ▸ f2.comp (evenProjection d)
  else 0

/-- The finite source realization is formed from the specified actual cycle and relation lifts. -/
def realization
    (hcomm : (C.d 1 2 rfl).comp f1 = f2.comp d)
    (hcycle : (C.d 2 3 rfl).comp f2 = 0) : GHom (twoTermBased d).toGCx C where
  f i j h := h ▸ realizationComponent d C f1 f2 i
  comm i i' j j' hij hsrc htgt hij' x := by
    subst hij
    subst hij'
    subst hsrc
    by_cases hi : i = 1
    · subst i
      rw [← odd_reconstruct d x]
      change f2 (evenProjection d ((twoTermBased d).toGCx.d 1 2 rfl
          (oddCoordinates d (oddProjection d x)))) = C.d 1 2 rfl (f1 (oddProjection d x))
      rw [oddCoordinates_d]
      exact (LinearMap.congr_fun hcomm _).symm
    · by_cases hi2 : i = 2
      · subst i
        rw [← even_reconstruct d x]
        change (realizationComponent d C f1 f2 3)
            ((twoTermBased d).toGCx.d 2 3 rfl (evenCoordinates d (evenProjection d x))) =
          C.d 2 3 rfl (f2 (evenProjection d x))
        rw [even_d_zero, map_zero]
        exact (LinearMap.congr_fun hcycle _).symm
      · haveI := source_subsingleton d i hi hi2
        have hx : x = 0 := Subsingleton.elim _ _
        rw [hx, map_zero, map_zero, map_zero, map_zero]

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteSourceCoordinates

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteSourceRecipe

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- A finite free presentation of a specified finite source cohomology module. -/
structure Presentation (M : Type) [AddCommGroup M] [Module R M] where
  generators : ℕ
  relations : ℕ
  differential : (Fin relations → R) →ₗ[R] (Fin generators → R)
  classes : (Fin generators → R) →ₗ[R] M
  complex : classes.comp differential = 0
  injective : Function.Injective differential
  surjective : Function.Surjective classes
  exact : ∀ x, classes x = 0 → ∃ y, differential y = x

/-- The specified cohomology module has an independent finite free presentation over the scalar PID. -/
theorem presentation_nonempty (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Nonempty (Presentation (R := R) M) := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let g : (Fin n → R) →ₗ[R] M := Fintype.linearCombination R s
  have hg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hs]
  obtain ⟨m, b⟩ := (LinearMap.ker g).basisOfPid (Pi.basisFun R (Fin n))
  let f : (Fin m → R) →ₗ[R] (Fin n → R) :=
    (LinearMap.ker g).subtype.comp b.equivFun.symm.toLinearMap
  refine ⟨⟨n, m, f, g, ?_, ?_, hg, ?_⟩⟩
  · apply LinearMap.ext
    intro x
    exact (b.equivFun.symm x).property
  · exact (LinearMap.ker g).subtype_injective.comp b.equivFun.symm.injective
  · intro x hx
    refine ⟨b.equivFun ⟨x, hx⟩, ?_⟩
    change ((b.equivFun.symm (b.equivFun ⟨x, hx⟩) : LinearMap.ker g) : Fin n → R) = x
    rw [b.equivFun.symm_apply_apply]

/-- Actual cycle-class maps and their actual boundary kernels, independent of any self-dual comparison. -/
structure CohomologyData (C : GCx R) (H1 H2 : Type)
    [AddCommGroup H1] [Module R H1] [AddCommGroup H2] [Module R H2] where
  classOne : LinearMap.ker (C.d 1 2 rfl) →ₗ[R] H1
  one_surjective : Function.Surjective classOne
  one_kernel : ∀ x, classOne x = 0 ↔ ∃ y : C.X 0, C.d 0 1 rfl y = x.val
  classTwo : LinearMap.ker (C.d 2 3 rfl) →ₗ[R] H2
  two_surjective : Function.Surjective classTwo
  two_kernel : ∀ x, classTwo x = 0 ↔ ∃ y : C.X 1, C.d 1 2 rfl y = x.val

/-- The chosen finite presentation generators lift to actual degree-two source cycles. -/
theorem lift_generators (C : GCx R) (H1 H2 : Type)
    [AddCommGroup H1] [Module R H1] [AddCommGroup H2] [Module R H2]
    (D : CohomologyData C H1 H2) (P : Presentation (R := R) H2) :
    ∃ z : (Fin P.generators → R) →ₗ[R] LinearMap.ker (C.d 2 3 rfl),
      D.classTwo.comp z = P.classes := by
  exact Module.projective_lifting_property D.classTwo P.classes D.two_surjective

/-- Each finite presentation relation admits an actual continuous degree-one primitive, chosen linearly by projectivity. -/
theorem lift_relations (C : GCx R) (H1 H2 : Type)
    [AddCommGroup H1] [Module R H1] [AddCommGroup H2] [Module R H2]
    (D : CohomologyData C H1 H2) (P : Presentation (R := R) H2)
    (z : (Fin P.generators → R) →ₗ[R] LinearMap.ker (C.d 2 3 rfl))
    (hz : D.classTwo.comp z = P.classes) :
    ∃ f : (Fin P.relations → R) →ₗ[R] C.X 1,
      (C.d 1 2 rfl).comp f = (LinearMap.ker (C.d 2 3 rfl)).subtype.comp (z.comp P.differential) := by
  classical
  let b : C.X 1 →ₗ[R] LinearMap.ker (C.d 2 3 rfl) :=
    (C.d 1 2 rfl).codRestrict _ (fun x => C.d_d 1 2 3 rfl rfl x)
  let r : (Fin P.relations → R) →ₗ[R] LinearMap.range b :=
    (z.comp P.differential).codRestrict _ (fun x => by
      have hx : D.classTwo (z (P.differential x)) = 0 := by
        have h := LinearMap.congr_fun hz (P.differential x)
        exact h.trans (LinearMap.congr_fun P.complex x)
      obtain ⟨y, hy⟩ := (D.two_kernel _).mp hx
      exact ⟨y, Subtype.ext hy⟩)
  have hb : Function.Surjective b.rangeRestrict := by
    rintro ⟨x, y, rfl⟩
    exact ⟨y, rfl⟩
  obtain ⟨f, hf⟩ := Module.projective_lifting_property b.rangeRestrict r hb
  refine ⟨f, ?_⟩
  apply LinearMap.ext
  intro x
  have h := congrArg (fun y : LinearMap.range b => y.val.val) (LinearMap.congr_fun hf x)
  exact h

/-- The finite free actual first cohomology module admits a linear cycle section, by projectivity rather than an assumed comparison inverse. -/
theorem lift_first_classes (C : GCx R) (H1 H2 : Type)
    [AddCommGroup H1] [Module R H1] [Module.Free R H1]
    [AddCommGroup H2] [Module R H2] (D : CohomologyData C H1 H2) :
    ∃ z : H1 →ₗ[R] LinearMap.ker (C.d 1 2 rfl), D.classOne.comp z = LinearMap.id := by
  exact Module.projective_lifting_property D.classOne LinearMap.id D.one_surjective

/-- Restricting a finite coordinate vector to its relation coordinates. -/
def relationCoordinates (r s : ℕ) : (Fin (r + s) → R) →ₗ[R] (Fin r → R) where
  toFun x i := x (Fin.castAdd s i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restricting the same vector to its independent first-cohomology coordinates. -/
def cohomologyCoordinates (r s : ℕ) : (Fin (r + s) → R) →ₗ[R] (Fin s → R) where
  toFun x i := x (Fin.natAdd r i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Cycle and relation lifts form a finite based realization of the specified actual cochain complex. -/
theorem finite_realization_exists (C : GCx R) (H1 H2 : Type)
    [AddCommGroup H1] [Module R H1] [Module.Free R H1] [Module.Finite R H1]
    [AddCommGroup H2] [Module R H2] [Module.Finite R H2]
    (D : CohomologyData C H1 H2) :
    ∃ (r1 r2 : ℕ) (d : (Fin r1 → R) →ₗ[R] (Fin r2 → R)),
      Nonempty (GHom (ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedDual.twoTermBased d).toGCx C) := by
  classical
  let P : Presentation (R := R) H2 := (presentation_nonempty H2).some
  obtain ⟨z2, hz2⟩ := lift_generators C H1 H2 D P
  obtain ⟨frel, hfrel⟩ := lift_relations C H1 H2 D P z2 hz2
  obtain ⟨z1, hz1⟩ := lift_first_classes C H1 H2 D
  let I := Module.Free.ChooseBasisIndex R H1
  let b := (Module.Free.chooseBasis R H1).reindex (Fintype.equivFin I)
  let s := Fintype.card I
  let first : (Fin s → R) →ₗ[R] C.X 1 :=
    (LinearMap.ker (C.d 1 2 rfl)).subtype.comp (z1.comp b.equivFun.symm.toLinearMap)
  let d : (Fin (P.relations + s) → R) →ₗ[R] (Fin P.generators → R) :=
    P.differential.comp (relationCoordinates P.relations s)
  let f1 : (Fin (P.relations + s) → R) →ₗ[R] C.X 1 :=
    frel.comp (relationCoordinates P.relations s) + first.comp (cohomologyCoordinates P.relations s)
  let f2 : (Fin P.generators → R) →ₗ[R] C.X 2 :=
    (LinearMap.ker (C.d 2 3 rfl)).subtype.comp z2
  have hcomm : (C.d 1 2 rfl).comp f1 = f2.comp d := by
    apply LinearMap.ext
    intro x
    change C.d 1 2 rfl (frel (relationCoordinates P.relations s x) +
      (z1 (b.equivFun.symm (cohomologyCoordinates P.relations s x))).val) = _
    rw [map_add, (z1 (b.equivFun.symm (cohomologyCoordinates P.relations s x))).property, add_zero]
    exact LinearMap.congr_fun hfrel _
  have hcycle : (C.d 2 3 rfl).comp f2 = 0 := by
    apply LinearMap.ext
    intro x
    exact (z2 x).property
  exact ⟨P.relations + s, P.generators, d,
    ⟨ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteSourceCoordinates.realization d C f1 f2 hcomm hcycle⟩⟩

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteSourceRecipe

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.TraceThirdDegree

open TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralFiniteBoundary
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace

variable (F : Type) [Field F] [CharZero F] [DecidableEq F]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The independent finite third-degree exactness statement for genuine roots-of-unity coefficients. -/
def FiniteThirdDegreeExact : Prop :=
  ∀ (a : ℕ) (t : (finiteIntegralComplex (AbsoluteGaloisGroup F) (UnitsCoeff F) a).X 3),
    ((finiteIntegralComplex (AbsoluteGaloisGroup F) (UnitsCoeff F) a).d 3 4).hom t = 0 →
    ∃ y : (finiteIntegralComplex (AbsoluteGaloisGroup F) (UnitsCoeff F) a).X 2,
      ((finiteIntegralComplex (AbsoluteGaloisGroup F) (UnitsCoeff F) a).d 2 3).hom y = t

/-- The genuine finite local invariant makes the second cohomology of each actual Tate level finite. -/
theorem finite_mu_second_cohomology (a : ℕ) :
    Finite (H2 (AbsoluteGaloisGroup F) (FiniteTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F) a)) :=
  Finite.of_equiv (ZMod (2 ^ a))
    (((actualMuH2Equiv F a).trans (finiteInvariant F (2 ^ a) (twoPower_isUnit F a))).symm.toEquiv)

/-- Genuine finite third-degree exactness lifts to the actual integral trace-target exactness by finite second-cohomology primitive classes. -/
theorem actual_third_exact_of_finite (hfinite : FiniteThirdDegreeExact F) :
    FiniteCycleLift.ThirdDegreeExact F := by
  intro t ht
  let H (a : ℕ) := H2 (AbsoluteGaloisGroup F) (FiniteTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F) a)
  letI : ∀ a, Finite (H a) := fun a => finite_mu_second_cohomology F a
  apply boundary_of_finite_boundaries (AbsoluteGaloisGroup F) (UnitsCoeff F) 1
    (actualMuTransition_surjective F) H
    (fun a => kerToH2 (k := ℤ_[2]) (G := AbsoluteGaloisGroup F)
      (M := FiniteTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F) a))
    (fun a z => kerToH2_eq_zero_iff z) t
  intro a
  apply hfinite a (((reduceCochains (AbsoluteGaloisGroup F) (UnitsCoeff F) a).f 3).hom t)
  rw [← reduceCochains_d, ht, map_zero]

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.TraceThirdDegree

end
