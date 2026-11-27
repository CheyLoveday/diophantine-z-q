import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceGeometricPoints
import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceTateProfile

/-! The split profile of an actual cyclic level subgroup, in the
rational frame of the reference. Tex 9136–9146. -/

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory Eichler Adelic PkgI3.AbVar
open scoped CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {A : PkgI3.AbVar k} {a b : ℚ}

omit [IsAlgClosed k] in
private theorem span_reference_primary (p : Prime) (r n : ℕ) (hr : IsUnit (r : ℤ_[p.val]))
    (C : Subgroup (A.Pt (AlgebraicClosure k))) (hC : ∀ x ∈ C, x ^ (r * p.val ^ n) = 1) :
    let D := C ⊓ (powMonoidHom (p.val ^ n)).ker
    Submodule.span ℤ_[p.val] (tateHom p.val A A '' (levelHom C C : Set A.End)) =
      Submodule.span ℤ_[p.val] (tateHom p.val A A '' (levelHom D D : Set A.End)) := by
  let D := C ⊓ (powMonoidHom (p.val ^ n)).ker
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨f, hf, rfl⟩
    refine ⟨f, fun x hx => ⟨hf x hx.1, ?_⟩, rfl⟩
    change (x ≫ f.hom) ^ (p.val ^ n) = 1
    rw [← MonObj.pow_comp, show x ^ (p.val ^ n) = 1 from hx.2, MonObj.one_comp]
  · apply Submodule.span_le.mpr
    rintro _ ⟨f, hf, rfl⟩
    have hf' : r • f ∈ levelHom C C := by
      intro x hx
      have hx' : x ^ r ∈ D :=
        ⟨C.pow_mem hx _, by change (x ^ r) ^ (p.val ^ n) = 1; rw [← pow_mul]; exact hC x hx⟩
      change x ≫ f.hom ^ r ∈ C
      rw [MonObj.comp_pow, ← MonObj.pow_comp]
      exact (hf _ hx').1
    let L := Submodule.span ℤ_[p.val] (tateHom p.val A A '' (levelHom C C : Set A.End))
    have hl : tateHom p.val A A (r • f) ∈ L := Submodule.subset_span ⟨_, hf', rfl⟩
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℤ_[p.val]] at hl
    have hi : (↑hr.unit⁻¹ : ℤ_[p.val]) * (r : ℤ_[p.val]) = 1 :=
      (congrArg ((↑hr.unit⁻¹ : ℤ_[p.val]) * ·) hr.unit_spec.symm).trans (Units.inv_mul hr.unit)
    change tateHom p.val A A f ∈ L
    simpa only [smul_smul, hi, one_smul] using L.smul_mem (↑hr.unit⁻¹ : ℤ_[p.val]) hl

private theorem cyclic_primary {G : Type*} [CommGroup G] (P : G) (r s : ℕ)
    (hr : r ≠ 0) (hs : s ≠ 0) (hP : orderOf P = r * s) :
    Subgroup.zpowers P ⊓ (powMonoidHom s).ker = Subgroup.zpowers (P ^ r) := by
  apply le_antisymm
  · intro x hx
    have ht : IsOfFinOrder P := isOfFinOrder_iff_pow_eq_one.mpr
      ⟨r * s, Nat.mul_pos (Nat.pos_of_ne_zero hr) (Nat.pos_of_ne_zero hs),
        hP ▸ pow_orderOf_eq_one P⟩
    obtain ⟨m, rfl⟩ := ht.mem_powers_iff_mem_zpowers.mpr hx.1
    have hm : r * s ∣ m * s := by
      rw [← hP]
      exact orderOf_dvd_of_pow_eq_one (by
        rw [pow_mul]
        exact hx.2)
    obtain ⟨v, rfl⟩ := (Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hs) hm)
    change P ^ (r * v) ∈ Subgroup.zpowers (P ^ r)
    rw [pow_mul]
    exact (Subgroup.zpowers (P ^ r)).pow_mem (Subgroup.mem_zpowers _) _
  · apply Subgroup.zpowers_le.mpr
    refine ⟨(Subgroup.zpowers P).pow_mem (Subgroup.mem_zpowers _) _, ?_⟩
    change (P ^ r) ^ s = 1
    rw [← pow_mul, ← hP, pow_orderOf_eq_one]

/-- The completion of the level order is in standard split coordinates
at each prime of residue characteristic different from that of the
reference. The same proof includes zero exponent and the prime two. -/
theorem splitProfile_of_cyclicReference (p : Prime) (hp : (p.val : k) ≠ 0)
    (N : ℕ) (hN : N ≠ 0) (P : A.Pt k) (hP : orderOf P = N)
    (R : Order a b) (embed : A.End →+* B a b)
    (hR : embed '' (levelEnd A (Subgroup.zpowers P) : Set A.End) = (R.ring : Set (B a b)))
    (bE : Module.Basis (Fin 4) ℤ A.End) (bT : Module.Basis (Fin 2) ℤ_[p.val] (A.T p.val)) :
    ∃ d : Bp p.val a b ≃ₐ[ℚ_[p.val]] M2 ℚ_[p.val],
      d '' (R.completion p.val : Set _) = standardLevel p.val (N.factorization p.val) := by
  let C := Subgroup.zpowers P
  let Q := levelPointsToClosure A P
  let D := Subgroup.zpowers Q
  have hCD : C.map (levelPointsToClosure A) = D := MonoidHom.map_zpowers _ _
  have hL : (levelEnd A C : Set A.End) = (levelHom D D : Set A.End) :=
    Set.ext fun f => by
      change f ∈ levelEnd A C ↔ f ∈ levelHom D D
      rw [← hCD]
      exact levelEnd_iff_levelHom_closure C f
  have hQ : orderOf Q = N :=
    (orderOf_injective (levelPointsToClosure A) (levelPointsToClosure_injective A) P).trans hP
  let n := N.factorization p.val
  let r := N / p.val ^ n
  have hn : N = r * p.val ^ n := by
    rw [mul_comm]
    exact (Nat.ordProj_mul_ordCompl_eq_self N p.val).symm
  have hnd := Nat.not_dvd_ordCompl p.property hN
  have hr : IsUnit (r : ℤ_[p.val]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr
      ((Nat.Prime.coprime_iff_not_dvd p.property).mpr hnd))
  have hr₀ : r ≠ 0 := fun h => hN (by simp [hn, h])
  have hp₀ : p.val ^ n ≠ 0 := pow_ne_zero _ p.property.ne_zero
  have hD : ∀ x ∈ D, x ^ (r * p.val ^ n) = 1 := by
    intro x hx
    have hpow : Q ^ N = 1 := hQ ▸ pow_orderOf_eq_one Q
    have hfin : IsOfFinOrder Q := isOfFinOrder_iff_pow_eq_one.mpr ⟨N, Nat.pos_of_ne_zero hN, hpow⟩
    obtain ⟨m, rfl⟩ := hfin.mem_powers_iff_mem_zpowers.mpr hx
    change (Q ^ m) ^ (r * p.val ^ n) = 1
    rw [← hn, pow_right_comm, hpow, one_pow]
  have hfull : Submodule.span ℤ_[p.val] (Set.range (tateHom p.val A A)) = ⊤ :=
    span_homT_eq_top_of_basis p.val 4 hp bE ((bT.linearMap bT).reindex finProdFinEquiv)
  obtain ⟨e, he⟩ := exists_rationalTate_coordinates_of_endOrder R embed C hR p bE bT hfull
  let U := Q ^ r
  have hU : orderOf U = p.val ^ n := by
    change orderOf (Q ^ r) = _
    rw [orderOf_pow_of_dvd hr₀ (by rw [hQ, hn]; exact dvd_mul_right _ _), hQ, hn,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hr₀)]
  have hspan :
      (Submodule.span ℤ_[p.val] (tateHom p.val A A '' (levelEnd A C : Set A.End)) :
        Set (Module.End ℤ_[p.val] (A.T p.val))) =
      {f : Module.End ℤ_[p.val] (A.T p.val) | Set.MapsTo (⇑f)
        (tateLevelPreimage A p.val n (Subgroup.zpowers U))
        (tateLevelPreimage A p.val n (Subgroup.zpowers U))} := by
    rw [hL, span_reference_primary p r n hr D hD, cyclic_primary Q r _ hr₀ hp₀ (hQ.trans hn)]
    apply span_levelHom_eq_tateLevelMaps p.val n hp _ _ _ hfull
    intro x hx
    have hpow : U ^ (p.val ^ n) = 1 := hU ▸ pow_orderOf_eq_one U
    have hfin : IsOfFinOrder U := isOfFinOrder_iff_pow_eq_one.mpr
      ⟨p.val ^ n, Nat.pos_of_ne_zero hp₀, hpow⟩
    obtain ⟨m, rfl⟩ := hfin.mem_powers_iff_mem_zpowers.mpr hx
    change (U ^ m) ^ (p.val ^ n) = 1
    rw [pow_right_comm, hpow, one_pow]
  have hchain : ∃ c : A.T p.val ≃ₗ[ℤ_[p.val]] (Fin 2 → ℤ_[p.val]),
      ∀ y, y ∈ tateLevelPreimage A p.val n (Subgroup.zpowers U) ↔
        c y ∈ splitLevelLattice p.val 0 n := by
    by_cases hn₀ : n = 0
    · refine ⟨bT.equivFun, fun y => ?_⟩
      have hy : y.1 0 = 0 := by simpa only [pow_zero, one_nsmul] using PkgI3.Tate.pow_smul_eq_zero y.2 0
      rw [hn₀]
      change Additive.toMul (y.1 0) ∈ Subgroup.zpowers U ↔ _
      rw [hy]
      simp [splitLevelLattice]
    · exact exists_tateLevelPreimage_standard p.val hp n (Nat.pos_of_ne_zero hn₀) U hU bT
  obtain ⟨c, hc⟩ := hchain
  let basis := Module.Basis.ofEquivFun c
  have hs : tateLevelPreimage A p.val n (Subgroup.zpowers U) =
      basis.equivFun ⁻¹' splitLevelLattice p.val 0 n := by
    ext y
    change _ ↔ basis.equivFun y ∈ splitLevelLattice p.val 0 n
    simpa only [basis, Module.Basis.equivFun_ofEquivFun] using hc y
  rw [hs] at hspan
  exact splitProfile_of_referenceTateChain p n R embed C hR e he basis hspan

/-- The frame of a cyclic geometric reference in the pinned detector
order. The only rank inputs are the level-one Deuring theorem and the
geometric Tate rank theorem. -/
theorem detector_referenceCoordinates_of_cyclic
    (hD : DeuringSupersingularEndOrder) (hT : PkgI3.TateModuleFree)
    (q : ℕ) [Fact q.Prime] [Fact (q % 4 = 3)] [CharP k q] (hdim : A.dim = 1)
    (hss : ∀ x : A.Pt k, x ^ q = 1 → x = 1)
    (N : ℕ) (hN : 0 < N) (hcop : N.Coprime q)
    (S : Order (-1) (-(q : ℚ))) (j : A.End ≃+* S.ring)
    (hmax : ∀ T : Order (-1) (-(q : ℚ)), S.ring ≤ T.ring → T.ring ≤ S.ring)
    (P : A.Pt k) (hP : orderOf P = N)
    (hC : ∀ x ∈ Subgroup.zpowers P, x ^ N = 1) :
    ∃ z : Adelic.FiniteUnits (levelOrder q Fact.out N hN),
      ReferenceOrderCoordinates (levelOrder q Fact.out N hN)
        (levelOrderOfEndOrder S j (Subgroup.zpowers P) N hN.ne' hC) z := by
  have hqN : IsUnit (N : ℤ_[q]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hcop.symm)
  apply detector_referenceCoordinates q N hN hcop hqN S j hmax (Subgroup.zpowers P) hC
  intro p hp
  have hp' : (p.val : k) ≠ 0 := by
    intro hz
    have hd := (CharP.cast_eq_zero_iff k q p.val).mp hz
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out p.property).mp hd).symm
  obtain ⟨bE⟩ := end_basis_of_deuring hD q hdim hss
  obtain ⟨hFree, hFinite, hRank⟩ := hT k A p.val hp'
  have hRank' : ((Module.finrank ℤ_[p.val] (A.T p.val) : ℕ∞) : WithBot ℕ∞) = 2 := by
    simpa only [hdim, mul_one] using hRank
  let bT := Module.finBasisOfFinrankEq ℤ_[p.val] (A.T p.val)
    (WithTop.coe_inj.mp (WithBot.coe_inj.mp hRank'))
  exact splitProfile_of_cyclicReference p hp' N hN.ne' P hP _ (S.ring.subtype.comp j.toRingHom) rfl bE bT

end ZInQ.Manuscript.RC.HCMV21
