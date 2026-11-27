import ZInQKernel.Contrib.OneProof.RC.KSplitSeed.Sieve

/-! The finite Frobenius match of App G, with the stationary types adjoined
to the field detecting the actual modulo-two trace value. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KSplitSeed

open AddressGenuine Wiring PrintsArith KSplit
open ZInQ.Manuscript.RC.Even

/-- Match the singleton trace at coefficient `p²` and all stationary
labels (tex 10317–10318, 10437–10441). It suffices for the indicated
coefficient of the actual trace to descend modulo the integer two on the
given field; the full trace orbit is not needed here. The good Hecke
reading has no correction at this coefficient since the new prime is
different from `p`. -/
theorem exists_fresh_trace_match {ℓ : ℕ} {W : WData ℓ} (D : LabelData W)
    (O : Subring ℂ) {p : ℕ} (hp : p.Prime) (hpM : p.Coprime D.m₂)
    (hkp : jacobiSym W.kfin p = 1) {φ : GalQ} (hφ : IsFrobAt φ p)
    (avoid : Finset ℕ) (E : IntermediateField ℚ Qbar) (hE : FiniteDimensional ℚ E)
    (tr : GalQ → ℂ) (f : ℕ → ℂ)
    (htr : ∀ g : GalQ, (∀ x ∈ E, g x = φ x) → InTwoO O (tr φ - tr g))
    (hhecke : ∀ q : ℕ, q.Prime → q.Coprime D.m₂ → q ∉ avoid → q ≠ p →
      ∀ g : GalQ, IsFrobAt g q → tr g = f (p ^ 2 * q)) :
    ∃ q : ℕ, q.Prime ∧ q.Coprime D.m₂ ∧ q ∉ avoid ∧ q ≠ p ∧
      sqClassOf D.m₂ q = sqClassOf D.m₂ p ∧ jacobiSym W.kfin q = 1 ∧
      InTwoO O (tr φ - f (p ^ 2 * q)) := by
  classical
  obtain ⟨A, hA, hfix⟩ := exists_fixingSubgroup_le_ker_typChar D.m₂
  obtain ⟨g, q, hq, hqS, hg, heq⟩ := ZInQ.Contrib.ChebFD.C10.frobDense
    ZInQ.Contrib.chebotarevExists (insert p (D.m₂.primeFactors ∪ avoid))
    (A ⊔ E) inferInstance φ
  have hqM : q.Coprime D.m₂ := hq.coprime_iff_not_dvd.mpr fun hd =>
    hqS (Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Nat.mem_primeFactors.mpr ⟨hq, hd, D.m₂_pos.ne'⟩)))
  have hqA : q ∉ avoid := fun h =>
    hqS (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
  have hqne : q ≠ p := fun h => hqS (h ▸ Finset.mem_insert_self _ _)
  have hgf : IsFrobAt g q := (isFrobAt_iff_c10 hq).2 hg
  have hinl : (A : Set Qbar) ⊆ ↑(A ⊔ E) := SetLike.coe_subset_coe.mpr le_sup_left
  have hinr : (E : Set Qbar) ⊆ ↑(A ⊔ E) := SetLike.coe_subset_coe.mpr le_sup_right
  have hφg : φ⁻¹ * g ∈ A.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [AlgEquiv.mul_apply, heq x (hinl hx), AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have htype : typChar D.m₂ g = typChar D.m₂ φ := by
    have e : φ * (φ⁻¹ * g) = g := by group
    rw [← e, map_mul, hfix _ hφg]
    exact add_zero (Multiplicative.toAdd (typChar D.m₂ φ))
  rw [typChar_of_isFrobAt D.m₂ hq hqM hgf, typChar_of_isFrobAt D.m₂ hp hpM hφ] at htype
  have hc : sqClassOf D.m₂ q = sqClassOf D.m₂ p := congrArg Multiplicative.toAdd htype
  have hkq : jacobiSym W.kfin q = 1 := by
    apply (kChar_sqClassOf_eq_zero_iff D.kdvd hq hqM).mp
    rw [hc]
    exact (kChar_sqClassOf_eq_zero_iff D.kdvd hp hpM).mpr hkp
  have hm := htr g (fun x hx => heq x (hinr hx))
  rw [hhecke q hq hqM hqA hqne g hgf] at hm
  exact ⟨q, hq, hqM, hqA, hqne, hc, hkq, hm⟩

/-- A prime pair matching the stationary type passes the transported
square-unit filter, including the dyadic condition (tex 10317–10318,
10448–10449). Each member may fail the squareclass condition on its own. -/
theorem matched_product_in_filter {ℓ : ℕ} {W : WData ℓ} (D : LabelData W)
    {S : Finset ℕ} (hS : S ⊆ D.m₂.primeFactors) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hpM : p.Coprime D.m₂) (hqM : q.Coprime D.m₂)
    (hmatch : sqClassOf D.m₂ p = sqClassOf D.m₂ q) :
    S0Filter S 1 (p * q) := by
  have hcop : (p * q).Coprime D.m₂ := hpM.mul_left hqM
  have hup := isUnit_natCast_of_coprime hpM
  have huq := isUnit_natCast_of_coprime hqM
  have hx : sqClassOf D.m₂ ((p : ℤ) * q) = 0 := by
    rw [sqClassOf_mul hup huq, hmatch, sqClass_add_self]
  have hs : IsSquare ((((p : ℤ) * q) : ℤ) : ZMod D.m₂) := by
    exact (sqClassOf_eq_zero_iff (by simpa only [Int.cast_mul] using hup.mul huq)).mp hx
  have hlocal (d : ℕ) (hd : d ∣ D.m₂) : IsSquare ((p * q : ℕ) : ZMod d) := by
    have hs' : IsSquare ((p * q : ℕ) : ZMod D.m₂) := by
      simpa only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul] using hs
    simpa only [map_natCast] using hs'.map (ZMod.castHom hd (ZMod d))
  have h8 : (p * q) % 8 = 1 := by
    have odd := Nat.odd_iff.mp
      (odd_of_coprime_of_two_dvd (dvd_trans (by decide : 2 ∣ 8) D.eight₂) hcop)
    have hv : (((p * q : ℕ) : ZMod 8).val) % 2 = 1 := by
      rw [ZMod.val_natCast]; omega
    obtain ⟨z, hz⟩ := hlocal 8 D.eight₂
    have test : ∀ z : ZMod 8, (z * z).val % 2 = 1 → z * z = 1 := by decide
    rw [hz] at hv
    have he := congrArg ZMod.val (hz.trans (test z hv))
    simpa only [ZMod.val_natCast, ZMod.val_one_eq_one_mod, show 1 % 8 = 1 by decide] using he
  refine ⟨Nat.mul_pos hp.pos hq.pos, Nat.squarefree_mul_iff.mpr
    ⟨(Nat.coprime_primes hp hq).mpr hne, hp.squarefree, hq.squarefree⟩,
    fun d hd => ?_, fun d hd => ?_⟩
  · have hd' := hS hd
    exact (Nat.prime_of_mem_primeFactors hd').coprime_iff_not_dvd.mp
      (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hd') hcop.symm)
  · simp only [mul_one]
    exact ⟨fun _ => h8, fun _ => hlocal d (Nat.dvd_of_mem_primeFactors (hS hd))⟩

end ZInQ.Manuscript.RC.KSplitSeed
