import ZInQKernel.Contrib.RC53Assist.DerivedKummer.LocalDuality
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
