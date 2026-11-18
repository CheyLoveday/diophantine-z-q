import ZInQKernel.Contrib.CloudB3RC53.Mattuck.Doubling
import ZInQKernel.Contrib.CloudB3RC53.Mattuck.IndexLemma2

/-!
# Mattuck at `p = 2`, part 3: the filtration `Ê(I^k)` and its indices

Manuscript `diophantine_zq.tex`, tex 4551–4556.

For an adic ideal `I` of a complete linearly topologised ring `O`, the parameters in `I^k` form a
subgroup `lev k` of the formal group `Ê(I)` (Tau Ceti's `formalAddEval_mem`,
`formalInverseEval_mem`). Since the group law is `t + s` to first order
(`formalAddEval_sub_add_mem`: `F(t, s) − (t + s) ∈ I^{2k}` for `t, s ∈ I^k`), for
`k ≤ k' ≤ 2k` the map `lev k → O ⧸ I^{k'}`, `P ↦ P mod I^{k'}`, is a homomorphism with kernel
`lev k'` and image the image of `I^k`; hence

* **`relIndex_lev`**: `[lev k : lev k'] = [I^k : I^{k'}]` for `1 ≤ k`, `k' ≤ 2k` (indices of
  additive subgroups of `O`);
* `finiteIndex_lev`: if every `[I^k : I^{k+1}]` is finite, every `lev n` has finite index;
* with `2I = I^{e+1}` and `4I = I^{2e+1}` (as in a discrete valuation ring with `2O = I^e`), the
  doubling results of `Doubling.lean` say that `lev (e+1)` has no `2`-torsion
  (`lev_noTwoTorsion`) and `2 · lev (e+1) = lev (2e+1)`, so
  **`card_modN_lev`**: `|lev(e+1) / 2 lev(e+1)| = [I^{e+1} : I^{2e+1}]`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Mattuck

open WeierstrassCurve

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O]
  {W : WeierstrassCurve O} {I : Ideal O} [Fact (IsAdic I)]

variable (W I) in
/-- **The level `Ê(I^k)`**: the formal-group points with parameter in `I^k`. -/
def lev (k : ℕ) : AddSubgroup (FormalGroupPoint W I) where
  carrier := {P | (P : O) ∈ I ^ k}
  zero_mem' := by simp
  add_mem' {P Q} hP hQ := by
    change W.formalAddEval P Q ∈ I ^ k
    exact W.formalAddEval_mem (Fact.out : IsAdic I) hP hQ
  neg_mem' {P} hP := by
    change W.formalInverseEval P ∈ I ^ k
    exact W.formalInverseEval_mem P.hasEval hP

theorem mem_lev {k : ℕ} {P : FormalGroupPoint W I} : P ∈ lev W I k ↔ (P : O) ∈ I ^ k :=
  Iff.rfl

theorem lev_one : lev W I 1 = ⊤ := by
  ext P
  simp [mem_lev, P.property]

theorem lev_anti {k k' : ℕ} (h : k ≤ k') : lev W I k' ≤ lev W I k :=
  fun _ hP => Ideal.pow_le_pow_right h hP

/-- The reduction map `lev k → O ⧸ I^{k'}` (`k' ≤ 2k`), a homomorphism. -/
def levRed {k k' : ℕ} (h2 : k' ≤ 2 * k) : lev W I k →+ O ⧸ I ^ k' where
  toFun P := Ideal.Quotient.mk _ (P.1 : O)
  map_zero' := by simp
  map_add' P Q := by
    rw [← map_add, Ideal.Quotient.eq]
    change W.formalAddEval P.1 Q.1 - ((P.1 : O) + Q.1) ∈ I ^ k'
    exact Ideal.pow_le_pow_right h2 (W.formalAddEval_sub_add_mem (Fact.out : IsAdic I) P.2 Q.2)

theorem levRed_ker {k k' : ℕ} (h2 : k' ≤ 2 * k) :
    (levRed (W := W) (I := I) h2).ker = (lev W I k').addSubgroupOf (lev W I k) := by
  ext P
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, mem_lev]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The reduction map `I^k → O ⧸ I^{k'}` on `O`. -/
def idealRed (k k' : ℕ) : (I ^ k).toAddSubgroup →+ O ⧸ I ^ k' :=
  (Ideal.Quotient.mk (I ^ k')).toAddMonoidHom.comp (I ^ k).toAddSubgroup.subtype

theorem levRed_range {k k' : ℕ} (h0 : 1 ≤ k) (h2 : k' ≤ 2 * k) :
    (levRed (W := W) (I := I) h2).range = (idealRed (I := I) k k').range := by
  ext x
  simp only [AddMonoidHom.mem_range]
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨⟨P.1, P.2⟩, rfl⟩
  · rintro ⟨t, rfl⟩
    have htI : (t : O) ∈ I := Ideal.pow_le_self (by omega) t.2
    exact ⟨⟨⟨t, htI⟩, t.2⟩, rfl⟩

omit [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] [Fact (IsAdic I)] in
theorem idealRed_ker (k k' : ℕ) :
    (idealRed (I := I) k k').ker =
      (I ^ k').toAddSubgroup.addSubgroupOf (I ^ k).toAddSubgroup := by
  ext t
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- **`[Ê(I^k) : Ê(I^{k'})] = [I^k : I^{k'}]`** for `1 ≤ k ≤ k' ≤ 2k`. PROVED. -/
theorem relIndex_lev {k k' : ℕ} (h0 : 1 ≤ k) (h2 : k' ≤ 2 * k) :
    (lev W I k').relIndex (lev W I k) =
      (I ^ k').toAddSubgroup.relIndex (I ^ k).toAddSubgroup := by
  rw [AddSubgroup.relIndex, AddSubgroup.relIndex, ← levRed_ker h2, ← idealRed_ker,
    AddSubgroup.index_ker, AddSubgroup.index_ker, levRed_range h0 h2]

/-- `[Ê(I) : Ê(I^n)] = ∏ [I^k : I^{k+1}]`, hence finite when every step is. PROVED. -/
theorem finiteIndex_lev
    (hfin : ∀ k, 1 ≤ k → (I ^ (k + 1)).toAddSubgroup.relIndex (I ^ k).toAddSubgroup ≠ 0)
    (n : ℕ) : (lev W I n).FiniteIndex := by
  induction n with
  | zero =>
    rw [show lev W I 0 = ⊤ from eq_top_iff.mpr (fun P _ => by simp [mem_lev])]
    infer_instance
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [zero_add, lev_one]; infer_instance
    · constructor
      rw [← AddSubgroup.relIndex_mul_index (lev_anti (W := W) (I := I) (Nat.le_succ n)),
        relIndex_lev hn (by omega)]
      exact mul_ne_zero (hfin n hn) ih.index_ne_zero

/-! ### Doubling on the level `2I = I^{e+1}` -/

/-- **`Ê(I^{e+1})` has no `2`-torsion** when `I^{e+1} = 2I` (`O` a domain, `2 ≠ 0`). PROVED. -/
theorem lev_noTwoTorsion [IsDomain O] (h2 : (2 : O) ≠ 0) {e : ℕ}
    (he : ∀ x : O, x ∈ I ^ (e + 1) ↔ ∃ t ∈ I, x = 2 * t) :
    ∀ P ∈ lev W I (e + 1), 2 • P = 0 → P = 0 := by
  intro P hP h
  obtain ⟨t, ht, hPt⟩ := (he P).mp hP
  exact eq_zero_of_two_nsmul_eq_zero_of_eq_two_mul h2 P ht hPt h

/-- **`2 · Ê(I^{e+1}) = Ê(I^{2e+1})`**, as subgroups of `Ê(I^{e+1})`, when `I^{e+1} = 2I` and
`I^{2e+1} = 4I`. -/
theorem range_dbl_lev {e : ℕ} (he : ∀ x : O, x ∈ I ^ (e + 1) ↔ ∃ t ∈ I, x = 2 * t)
    (he' : ∀ x : O, x ∈ I ^ (2 * e + 1) ↔ ∃ σ ∈ I, x = 4 * σ) :
    (dbl (lev W I (e + 1))).range = (lev W I (2 * e + 1)).addSubgroupOf (lev W I (e + 1)) := by
  ext x
  rw [mem_range_dbl, AddSubgroup.mem_addSubgroupOf, mem_lev]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨t, ht, hyt⟩ := (he y.1).mp y.2
    rw [he']
    refine ⟨_, aeval_mem_of_constantCoeff_eq_zero (constantCoeff_dblSeries W) ht, ?_⟩
    change ((2 • y.1 : FormalGroupPoint W I) : O) = _
    exact two_nsmul_coe_of_eq_two_mul y.1 ht hyt
  · intro hx
    obtain ⟨σ, hσ, hxσ⟩ := (he' _).mp hx
    obtain ⟨P, t, ht, hPt, h2P⟩ := exists_two_nsmul_eq_of_eq_four_mul x.1 hσ hxσ
    exact ⟨⟨P, (he P).mpr ⟨t, ht, hPt⟩⟩, Subtype.ext h2P⟩

/-- **`|Ê(I^{e+1}) / 2 Ê(I^{e+1})| = [I^{e+1} : I^{2e+1}]`** (an index of additive subgroups of
`O`) when `I^{e+1} = 2I` and `I^{2e+1} = 4I`. PROVED. -/
theorem card_modN_lev {e : ℕ} (he : ∀ x : O, x ∈ I ^ (e + 1) ↔ ∃ t ∈ I, x = 2 * t)
    (he' : ∀ x : O, x ∈ I ^ (2 * e + 1) ↔ ∃ σ ∈ I, x = 4 * σ) :
    Nat.card (ModN (lev W I (e + 1)) 2) =
      (I ^ (2 * e + 1)).toAddSubgroup.relIndex (I ^ (e + 1)).toAddSubgroup := by
  rw [natCard_modN_two, range_dbl_lev he he', ← AddSubgroup.relIndex,
    relIndex_lev (by omega) (by omega)]

end ZInQ.Contrib.CloudB3RC53.Mattuck
