import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Restricted

/-! Faithfulness of evaluation on the algebraic finite restricted tensor
(tex 8996–9004). The finite elimination argument is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Metaplectic Filter
open scoped Classical BigOperators

private theorem spherical_zero_value (p : Place) : (spherical p).1 0 = 1 := by
  rw [spherical_apply, ite_eq_left (by simp [localLattice])]

private theorem replace_self (f : Elementary) (p : Place) : replace f p (f p) = f := by
  apply RestrictedProduct.ext
  intro q
  change Function.update (⇑f) p (f p) q = f q
  by_cases h : q = p
  · subst q; exact Function.update_self _ _ _
  · exact Function.update_of_ne h _ _

private def insertLocal (f : Elementary) (p : Place) : SchwartzBruhat p →ₗ[ℂ] RestrictedTensor where
  toFun v := pure (replace f p v)
  map_add' := pure_add f p
  map_smul' := pure_smul f p

private def atLocal (p : Place) (x : LocalVectors p) : SchwartzBruhat p →ₗ[ℂ] ℂ where
  toFun f := f.1 x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def onlyAt (p : Place) (T : Module.End ℂ (SchwartzBruhat p)) : RestrictedOperators :=
  ⟨Function.update (fun q => (1 : Module.End ℂ (SchwartzBruhat q))) p T, by
    filter_upwards [(Set.finite_singleton p).compl_mem_cofinite] with q hq
    rw [Function.update_of_ne (show q ≠ p from hq)]
    exact (stabilizes q).one_mem⟩

private theorem onlyAt_pure (p : Place) (T : Module.End ℂ (SchwartzBruhat p)) (f : Elementary) :
    restrictedAction (onlyAt p T) (pure f) = insertLocal f p (T (f p)) := by
  change act (onlyAt p T) (pure f) = _
  rw [act_pure]
  congr 1
  apply RestrictedProduct.ext
  intro q
  change Function.update (fun q => (1 : Module.End ℂ (SchwartzBruhat q))) p T q (f q) =
    Function.update (⇑f) p (T (f p)) q
  by_cases h : q = p
  · subst q; simp
  · simp [Function.update_of_ne h]

/-- If every scalar slice vanishes, reinserting the variable factor also
gives zero. Remove one summand by subtracting its multiple from the
other factors, using a point where the pivot factor is nonzero. -/
private theorem insert_sum_zero {I : Type*} (p : Place) (s : Finset I)
    (g : I → Elementary) (hg : ∀ i, g i p = spherical p) (v : I → SchwartzBruhat p)
    (h : ∀ x : LocalVectors p, ∑ i ∈ s, (v i).1 x • pure (g i) = 0) :
    ∑ i ∈ s, insertLocal (g i) p (v i) = 0 := by
  induction s using Finset.induction_on generalizing v with
  | empty => simp
  | insert j s hj ih =>
    by_cases hv : v j = 0
    · rw [Finset.sum_insert hj, hv, map_zero, zero_add]
      apply ih v
      intro x
      simpa [Finset.sum_insert hj, hv] using h x
    · obtain ⟨x, hx⟩ : ∃ x : LocalVectors p, (v j).1 x ≠ 0 := by
        by_contra! h
        exact hv (Subtype.ext (funext h))
      let w : I → SchwartzBruhat p := fun i =>
        v i - ((v i).1 x / (v j).1 x) • v j
      have hwj : w j = 0 := by simp [w, hx]
      have hw (y : LocalVectors p) :
          ∑ i ∈ insert j s, (w i).1 y • pure (g i) = 0 := by
        calc
          _ = (∑ i ∈ insert j s, (v i).1 y • pure (g i)) -
              ((v j).1 y / (v j).1 x) • ∑ i ∈ insert j s, (v i).1 x • pure (g i) := by
            rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i _
            change ((v i).1 y - ((v i).1 x / (v j).1 x) * (v j).1 y) • pure (g i) = _
            rw [sub_smul, smul_smul]
            congr 2
            ring
          _ = 0 := by rw [h y, h x, smul_zero, sub_zero]
      have htail : ∑ i ∈ s, insertLocal (g i) p (w i) = 0 :=
        ih w (fun y => by simpa [Finset.sum_insert hj, hwj] using hw y)
      let T : Module.End ℂ (SchwartzBruhat p) :=
        (atLocal p 0).smulRight (((v j).1 x)⁻¹ • v j)
      have hT (i : I) : T (g i p) = ((v j).1 x)⁻¹ • v j := by
        rw [hg i]
        change (spherical p).1 0 • (((v j).1 x)⁻¹ • v j) = (((v j).1 x)⁻¹ • v j)
        rw [spherical_zero_value, one_smul]
      have hhead : ∑ i ∈ insert j s, insertLocal (g i) p
          (((v i).1 x / (v j).1 x) • v j) = 0 := by
        have he := congrArg (restrictedAction (onlyAt p T)) (h x)
        rw [map_sum, map_zero] at he
        refine (Finset.sum_congr rfl fun i _ => ?_).trans he
        rw [map_smul (restrictedAction (onlyAt p T)), onlyAt_pure, hT,
          map_smul (insertLocal (g i) p), map_smul (insertLocal (g i) p), smul_smul, div_eq_mul_inv]
      calc
        _ = (∑ i ∈ insert j s, insertLocal (g i) p (w i)) +
            ∑ i ∈ insert j s, insertLocal (g i) p (((v i).1 x / (v j).1 x) • v j) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [← map_add, show w i + ((v i).1 x / (v j).1 x) • v j = v i from sub_add_cancel _ _]
        _ = 0 := by rw [Finset.sum_insert hj, hwj, map_zero, zero_add, htail, hhead, add_zero]

private def replaceVector (y : FiniteVectors) (p : Place) (x : LocalVectors p) : FiniteVectors :=
  fun i => ⟨Function.update (⇑(y i)) p (x i), by
    filter_upwards [(y i).2, (Set.finite_singleton p).compl_mem_cofinite] with q hq hne
    rwa [Function.update_of_ne (show q ≠ p from hne)]⟩

private theorem evaluation_support (f : Elementary) (y : FiniteVectors) :
    (fun q => (f q).1 (atPlace q y)).HasFiniteMulSupport := by
  apply eventually_cofinite.mp
  have hy : ∀ᶠ q in cofinite, atPlace q y ∈ localLattice q :=
    (Filter.eventually_all.mpr fun i : Fin 3 => (y i).2).mono fun _ h i _ => h i
  filter_upwards [hy, f.2] with q hq hf
  change f q = spherical q at hf
  rw [hf, spherical_apply, ite_eq_left hq]

private theorem slice_formula (f : Elementary) (p : Place) (x : LocalVectors p) (y : FiniteVectors) :
    (f p).1 x * evaluate (pure (replace f p (spherical p))) y =
      (spherical p).1 (atPlace p y) * evaluate (pure f) (replaceVector y p x) := by
  simp only [evaluate_pure]
  rw [← mul_finprod_cond_ne p (evaluation_support (replace f p (spherical p)) y),
    ← mul_finprod_cond_ne p (evaluation_support f (replaceVector y p x))]
  have r : atPlace p (replaceVector y p x) = x := by
    funext i
    exact Function.update_self _ _ _
  rw [r]
  change (f p).1 x * ((Function.update (⇑f) p (spherical p) p).1 (atPlace p y) * _) = _
  rw [Function.update_self, mul_left_comm]
  congr 2
  apply finprod_mem_congr rfl
  intro q hq
  change q ≠ p at hq
  have e : atPlace q (replaceVector y p x) = atPlace q y := by
    funext i
    exact Function.update_of_ne hq _ _
  change (Function.update (⇑f) p (spherical p) q).1 (atPlace q y) = _
  rw [Function.update_of_ne hq, e]

private theorem sum_zero_of_eval {I : Type*} (S : Finset Place) (s : Finset I)
    (f : I → Elementary) (c : I → ℂ) (hf : ∀ i ∈ s, ∀ p ∉ S, f i p = spherical p)
    (h : evaluate (∑ i ∈ s, c i • pure (f i)) = 0) :
    ∑ i ∈ s, c i • pure (f i) = 0 := by
  induction S using Finset.induction_on generalizing f c with
  | empty =>
    let e : Elementary := ⟨spherical, .of_forall (fun _ => Set.mem_singleton _)⟩
    have he (i : I) (hi : i ∈ s) : f i = e := by
      apply RestrictedProduct.ext
      intro p
      exact hf i hi p (Finset.notMem_empty _)
    have H : ∑ i ∈ s, c i • pure (f i) = (∑ i ∈ s, c i) • pure e := by
      rw [Finset.sum_smul]
      exact Finset.sum_congr rfl fun i hi => by rw [he i hi]
    have heval : evaluate (pure e) 0 = 1 := by
      rw [evaluate_pure]
      exact finprod_eq_one_of_forall_eq_one (fun p => spherical_zero_value p)
    rw [H, map_smul] at h
    have h' := congrFun h 0
    change (∑ i ∈ s, c i) * evaluate (pure e) 0 = 0 at h'
    rw [heval, mul_one] at h'
    rw [H, h', zero_smul]
  | insert p S hp ih =>
    let g (i : I) := replace (f i) p (spherical p)
    have hg (i : I) : g i p = spherical p := Function.update_self _ _ _
    have htail (i : I) (hi : i ∈ s) (q : Place) (hq : q ∉ S) : g i q = spherical q := by
      by_cases e : q = p
      · subst q; exact hg i
      · change Function.update (⇑(f i)) p (spherical p) q = _
        rw [Function.update_of_ne e]
        exact hf i hi q (by simp [e, hq])
    have hslice (x : LocalVectors p) : ∑ i ∈ s, (c i * (f i p).1 x) • pure (g i) = 0 := by
      apply ih g _ htail
      funext y
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      calc
        _ = (spherical p).1 (atPlace p y) *
            ∑ i ∈ s, c i * evaluate (pure (f i)) (replaceVector y p x) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          change c i * (f i p).1 x * evaluate (pure (replace (f i) p (spherical p))) y = _
          rw [mul_assoc, slice_formula, mul_left_comm]
        _ = 0 := by
          have e := congrFun h (replaceVector y p x)
          simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e
          rw [e, mul_zero]
    have H := insert_sum_zero p s g hg (fun i => c i • f i p) hslice
    refine (Finset.sum_congr rfl fun i _ => ?_).trans H
    rw [map_smul]
    congr 2
    apply RestrictedProduct.ext
    intro q
    change f i q = Function.update (⇑(g i)) p (f i p) q
    by_cases e : q = p
    · subst q; simp
    · rw [Function.update_of_ne e]
      change f i q = Function.update (⇑(f i)) p (spherical p) q
      rw [Function.update_of_ne e]

/-- Evaluation distinguishes arbitrary algebraic restricted tensors. -/
theorem evaluate_injective : Function.Injective evaluate := by
  apply (LinearMap.ker_eq_bot).1
  rw [Submodule.eq_bot_iff]
  intro v hv
  let S := Submodule.span ℂ (Set.range pure)
  have hS : S.mkQ = 0 := by
    apply tensor_ext
    intro f
    exact (Submodule.Quotient.mk_eq_zero (p := S)).2 (Submodule.subset_span ⟨f, rfl⟩)
  have hm : v ∈ S := (Submodule.Quotient.mk_eq_zero (p := S)).1 (by
    change S.mkQ v = 0
    rw [hS, LinearMap.zero_apply])
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hm
  change (∑ f ∈ c.support, c f • pure f) = v at hc
  rw [← hc] at hv ⊢
  let F (f : Elementary) : Finset Place := (eventually_cofinite.mp f.2).toFinset
  apply sum_zero_of_eval (c.support.biUnion F) c.support id c _ hv
  intro f hf p hp
  by_contra h
  exact hp (Finset.mem_biUnion.mpr ⟨f, hf, (Set.Finite.mem_toFinset _).mpr h⟩)

#print axioms spherical_zero_value
#print axioms replace_self
#print axioms onlyAt_pure
#print axioms insert_sum_zero
#print axioms evaluation_support
#print axioms slice_formula
#print axioms sum_zero_of_eval
#print axioms evaluate_injective

end ZInQ.Manuscript.RC.Metaplectic2
