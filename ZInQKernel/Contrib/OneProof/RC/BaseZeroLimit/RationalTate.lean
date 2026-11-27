import ZInQKernel.Contrib.OneProof.SelmerTwoPower

/-!
Lane RC30: the rational Tate module of a cofinitely generated `ℤ₂`-module

This is the textbook fact used by lane RC30 for the central dimension count of Lemma
`ex:arith-base-zero` (manuscript `diophantine_zq.tex`, tex 4350–4352: "Full Selmer corank one gives
central dimensions (1,1) ... This uses the full Selmer group, including a possible divisible part
of Ш"; and tex 5303–5311, universal coefficients with `ℚ₂/ℤ₂`): the rational Tate module of a
cofinitely generated `ℤ₂`-module of corank `r` has `ℚ₂`-dimension `r`.

Kind: GLUE (textbook), made PROVED.

Contents.
* `ratTateSubgroup M`, `RatTate M`: the rational Tate module `V₂M`, the additive maps `ℚ₂ → M`
  killing `2^N ℤ₂` for some `N` (the additive maps that are continuous when `M` is discrete,
  `mem_ratTateSubgroup_iff_continuous`), with
  the `ℚ₂`-module structure `(c • f) x = f (c * x)` written by hand.
* `RatTate.map`, `RatTate.congr`, `RatTate.prodEquiv`, `RatTate.piEquiv`: functoriality and
  compatibility with finite products.
* `RatTate.subsingleton_of_finite`: `V₂F = 0` for a finite group `F`.
* `ratTateQ2Z2Equiv`: `V₂(ℚ₂/ℤ₂) ≃ ℚ₂`, whose inverse sends `a` to `x ↦ [a x]`; surjectivity is
  `End(ℚ₂/ℤ₂) = ℤ₂`, proved with the compactness of `ℤ₂`.
* `finiteDimensional_ratTate_of_Z2Corank`, `finrank_ratTate_of_Z2Corank`: if `Z2Corank M r` then
  `dim_{ℚ₂} V₂M = r`; `finrank_ratTate_prod_of_Z2Corank` for a product of two such groups.
* Non-vacuity: `finrank_ratTate_Q2Z2`, `z2Corank_Q2Z2_one`, `z2Corank_punit_zero`.

Every theorem below is PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.BaseZeroLimit

open ZInQ.Manuscript.SelmerTwoPower

/-! Section: Elementary facts about `ℚ₂`. -/

/-- The `2`-adic norm of `2` is `1/2`. PROVED. -/
theorem norm_two_padic : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by
  simpa using (Padic.norm_p (p := 2))

/-- Every `2`-adic number becomes a `2`-adic integer after multiplication by a large enough power
of two. PROVED. -/
theorem exists_two_pow_mul_norm_le_one (c : ℚ_[2]) : ∃ k : ℕ, ‖(2 : ℚ_[2]) ^ k * c‖ ≤ 1 := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact ⟨0, by simp⟩
  · have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hpos) (by norm_num : (2⁻¹ : ℝ) < 1)
    refine ⟨k, ?_⟩
    rw [norm_mul, norm_pow, norm_two_padic]
    have h := mul_lt_mul_of_pos_right hk hpos
    rw [inv_mul_cancel₀ hpos.ne'] at h
    exact h.le

/-- The norm of a power of two is at most one. PROVED. -/
theorem norm_two_pow_le_one (k : ℕ) : ‖(2 : ℚ_[2]) ^ k‖ ≤ 1 := by
  rw [norm_pow, norm_two_padic]
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- A product of two elements of norm at most one has norm at most one. PROVED. -/
theorem norm_mul_le_one {a b : ℚ_[2]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  calc ‖a‖ * ‖b‖ ≤ 1 * 1 := mul_le_mul ha hb (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-! Section: The rational Tate module. -/

/-- **The rational Tate module `V₂M`** of an additive commutative group `M`, as a subgroup of
`ℚ₂ →+ M`: the additive maps `f` with `f (2^N x) = 0` for every `x ∈ ℤ₂`, for some `N`. These are
exactly the additive maps `ℚ₂ → M` that are continuous for the discrete topology on `M`
(`mem_ratTateSubgroup_iff_continuous`), i.e. `V₂M = Hom_cont(ℚ₂, M)`. -/
def ratTateSubgroup (M : Type*) [AddCommGroup M] : AddSubgroup (ℚ_[2] →+ M) where
  carrier := {f | ∃ N : ℕ, ∀ x : ℤ_[2], f ((2 : ℚ_[2]) ^ N * (x : ℚ_[2])) = 0}
  zero_mem' := ⟨0, fun _ => rfl⟩
  add_mem' := by
    rintro f g ⟨N, hN⟩ ⟨K, hK⟩
    refine ⟨N + K, fun x => ?_⟩
    have h1 := hN (Padic.lift ((2 : ℚ_[2]) ^ K * x) (norm_mul_le_one (norm_two_pow_le_one K) x.2))
    have h2 := hK (Padic.lift ((2 : ℚ_[2]) ^ N * x) (norm_mul_le_one (norm_two_pow_le_one N) x.2))
    rw [PadicInt.coe_lift] at h1 h2
    rw [AddMonoidHom.add_apply, pow_add]
    rw [← mul_assoc] at h1 h2
    rw [← pow_add] at h1 h2 ⊢
    rw [add_comm K N] at h2
    rw [h1, h2, add_zero]
  neg_mem' := by
    rintro f ⟨N, hN⟩
    exact ⟨N, fun x => by simp [hN x]⟩

variable {M M' : Type*} [AddCommGroup M] [AddCommGroup M']

/-- Membership in `ratTateSubgroup M`, unfolded. PROVED. -/
theorem mem_ratTateSubgroup {f : ℚ_[2] →+ M} :
    f ∈ ratTateSubgroup M ↔ ∃ N : ℕ, ∀ x : ℤ_[2], f ((2 : ℚ_[2]) ^ N * (x : ℚ_[2])) = 0 :=
  Iff.rfl

/-- **The defining condition is continuity**: for `M` discrete, an additive map `ℚ₂ → M` lies in
`ratTateSubgroup M` iff it is continuous; so `V₂M = Hom_cont(ℚ₂, M)`. PROVED. -/
theorem mem_ratTateSubgroup_iff_continuous [TopologicalSpace M] [DiscreteTopology M]
    (f : ℚ_[2] →+ M) : f ∈ ratTateSubgroup M ↔ Continuous f := by
  constructor
  · rintro ⟨N, hN⟩
    rw [continuous_discrete_rng]
    intro m
    rw [Metric.isOpen_iff]
    intro x hx
    refine ⟨(2⁻¹ : ℝ) ^ N, by positivity, fun y hy => ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have hz : ‖((2 : ℚ_[2]) ^ N)⁻¹ * (y - x)‖ ≤ 1 := by
      rw [norm_mul, norm_inv, norm_pow, norm_two_padic]
      have hp : (0 : ℝ) < (2⁻¹ : ℝ) ^ N := by positivity
      rw [inv_mul_le_iff₀ hp, mul_one]
      exact hy.le
    have h := hN (Padic.lift _ hz)
    rw [PadicInt.coe_lift, mul_inv_cancel_left₀ (pow_ne_zero N two_ne_zero)] at h
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
    have e : y = x + (y - x) := by ring
    rw [e, map_add, h, hx, add_zero]
  · intro hf
    have h0 : f ⁻¹' {0} ∈ nhds (0 : ℚ_[2]) := by
      apply hf.continuousAt.preimage_mem_nhds
      rw [map_zero]
      exact (isOpen_discrete _).mem_nhds rfl
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h0
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2⁻¹ : ℝ) < 1)
    refine ⟨N, fun x => ?_⟩
    have hx : (2 : ℚ_[2]) ^ N * (x : ℚ_[2]) ∈ Metric.ball (0 : ℚ_[2]) ε := by
      rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_pow, norm_two_padic]
      calc (2⁻¹ : ℝ) ^ N * ‖(x : ℚ_[2])‖ ≤ (2⁻¹ : ℝ) ^ N * 1 :=
            mul_le_mul_of_nonneg_left x.2 (by positivity)
        _ < ε := by rw [mul_one]; exact hN
    exact hball hx

/-- If an additive map kills `2^N ℤ₂`, it kills `2^(N + k) ℤ₂`. PROVED. -/
theorem map_two_pow_add_mul_eq_zero {f : ℚ_[2] →+ M} {N : ℕ}
    (hf : ∀ x : ℤ_[2], f ((2 : ℚ_[2]) ^ N * (x : ℚ_[2])) = 0) (k : ℕ) (x : ℤ_[2]) :
    f ((2 : ℚ_[2]) ^ (N + k) * (x : ℚ_[2])) = 0 := by
  have h := hf (Padic.lift ((2 : ℚ_[2]) ^ k * x) (norm_mul_le_one (norm_two_pow_le_one k) x.2))
  rw [PadicInt.coe_lift, ← mul_assoc, ← pow_add] at h
  exact h

/-- **`V₂M`**: the rational Tate module of `M`, the elements of `ratTateSubgroup M`. -/
abbrev RatTate (M : Type*) [AddCommGroup M] : Type _ := ↥(ratTateSubgroup M)

/-- Precomposition with multiplication by `c ∈ ℚ₂` preserves `ratTateSubgroup M`: if `f` kills
`2^N ℤ₂` and `2^k c ∈ ℤ₂`, then `x ↦ f (c x)` kills `2^(N + k) ℤ₂`. PROVED. -/
theorem comp_mulLeft_mem (c : ℚ_[2]) {f : ℚ_[2] →+ M} (hf : f ∈ ratTateSubgroup M) :
    f.comp (AddMonoidHom.mulLeft c) ∈ ratTateSubgroup M := by
  obtain ⟨N, hN⟩ := hf
  obtain ⟨k, hk⟩ := exists_two_pow_mul_norm_le_one c
  refine ⟨N + k, fun x => ?_⟩
  have h := hN (Padic.lift ((2 : ℚ_[2]) ^ k * c * x) (norm_mul_le_one hk x.2))
  rw [PadicInt.coe_lift] at h
  rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft]
  rw [← h]
  congr 1
  ring

/-- The scalar action of `ℚ₂` on `V₂M` by precomposition with multiplication:
`(c • f) x = f (c * x)`. -/
instance instSMulRatTate : SMul ℚ_[2] (RatTate M) where
  smul c f := ⟨(f : ℚ_[2] →+ M).comp (AddMonoidHom.mulLeft c), comp_mulLeft_mem c f.2⟩

/-- The scalar action on `V₂M` evaluated: `(c • f) x = f (c * x)`. PROVED. -/
@[simp]
theorem RatTate.smul_apply (c : ℚ_[2]) (f : RatTate M) (x : ℚ_[2]) :
    ((c • f : RatTate M) : ℚ_[2] →+ M) x = (f : ℚ_[2] →+ M) (c * x) :=
  rfl

/-- **The `ℚ₂`-vector space structure on `V₂M`**, by precomposition with multiplication. It is
written by hand (it is not the postcomposition structure on `ℚ₂ →+ M`). -/
instance instModuleRatTate : Module ℚ_[2] (RatTate M) where
  one_smul f := Subtype.ext <| AddMonoidHom.ext fun x => by simp
  mul_smul c d f := Subtype.ext <| AddMonoidHom.ext fun x => by
    simp only [RatTate.smul_apply]
    congr 1
    ring
  smul_zero c := Subtype.ext <| AddMonoidHom.ext fun x => by simp
  smul_add c f g := Subtype.ext <| AddMonoidHom.ext fun x => by simp
  add_smul c d f := Subtype.ext <| AddMonoidHom.ext fun x => by simp [add_mul]
  zero_smul f := Subtype.ext <| AddMonoidHom.ext fun x => by simp

/-! Section: Functoriality and products. -/

/-- Postcomposition with an additive map preserves the rational Tate subgroup. PROVED. -/
theorem comp_mem_ratTateSubgroup (φ : M →+ M') {f : ℚ_[2] →+ M} (hf : f ∈ ratTateSubgroup M) :
    φ.comp f ∈ ratTateSubgroup M' := by
  obtain ⟨N, hN⟩ := hf
  exact ⟨N, fun x => by simp [hN x]⟩

/-- **Functoriality** `V₂(φ) : V₂M → V₂M'`, postcomposition with `φ : M →+ M'`; it is
`ℚ₂`-linear. -/
def RatTate.map (φ : M →+ M') : RatTate M →ₗ[ℚ_[2]] RatTate M' where
  toFun f := ⟨φ.comp (f : ℚ_[2] →+ M), comp_mem_ratTateSubgroup φ f.2⟩
  map_add' f g := Subtype.ext <| AddMonoidHom.ext fun x => by simp
  map_smul' c f := Subtype.ext <| AddMonoidHom.ext fun x => rfl

/-- `V₂(φ)` evaluated. PROVED. -/
@[simp]
theorem RatTate.map_apply (φ : M →+ M') (f : RatTate M) (x : ℚ_[2]) :
    ((RatTate.map φ f : RatTate M') : ℚ_[2] →+ M') x = φ ((f : ℚ_[2] →+ M) x) :=
  rfl

/-- **`V₂` of an isomorphism**: `M ≃+ M'` induces `V₂M ≃ V₂M'` (postcomposition with `e`). -/
def RatTate.congr (e : M ≃+ M') : RatTate M ≃ₗ[ℚ_[2]] RatTate M' :=
  LinearEquiv.ofLinearMap (RatTate.map (e : M →+ M')) (RatTate.map (e.symm : M' →+ M))
    (LinearMap.ext fun f => Subtype.ext <| AddMonoidHom.ext fun x => by simp)
    (LinearMap.ext fun f => Subtype.ext <| AddMonoidHom.ext fun x => by simp)

/-- The pairing `x ↦ (f x, g x)` of two elements of the rational Tate subgroups lies in the
rational Tate subgroup of the product. PROVED. -/
theorem prod_mem_ratTateSubgroup (f : RatTate M) (g : RatTate M') :
    (f : ℚ_[2] →+ M).prod (g : ℚ_[2] →+ M') ∈ ratTateSubgroup (M × M') := by
  obtain ⟨N, hN⟩ := f.2
  obtain ⟨K, hK⟩ := g.2
  refine ⟨N + K, fun x => ?_⟩
  rw [AddMonoidHom.prod_apply]
  have h2 := map_two_pow_add_mul_eq_zero hK N x
  rw [add_comm K N] at h2
  rw [map_two_pow_add_mul_eq_zero hN K x, h2]
  rfl

/-- **`V₂` of a product**: `V₂(M × M') ≃ V₂M × V₂M'`. -/
def RatTate.prodEquiv : RatTate (M × M') ≃ₗ[ℚ_[2]] RatTate M × RatTate M' where
  toFun f := (RatTate.map (AddMonoidHom.fst M M') f, RatTate.map (AddMonoidHom.snd M M') f)
  invFun g := ⟨(g.1 : ℚ_[2] →+ M).prod (g.2 : ℚ_[2] →+ M'), prod_mem_ratTateSubgroup g.1 g.2⟩
  map_add' f g := Prod.ext (map_add _ f g) (map_add _ f g)
  map_smul' c f := Prod.ext (map_smul _ c f) (map_smul _ c f)
  left_inv _ := Subtype.ext <| AddMonoidHom.ext fun _ => rfl
  right_inv _ := Prod.ext (Subtype.ext <| AddMonoidHom.ext fun _ => rfl)
    (Subtype.ext <| AddMonoidHom.ext fun _ => rfl)

/-- The tuple `x ↦ (f i x)_i` of finitely many elements of the rational Tate subgroup lies in the
rational Tate subgroup of the power. PROVED. -/
theorem pi_mem_ratTateSubgroup {r : ℕ} (f : Fin r → RatTate M) :
    AddMonoidHom.pi (fun i => (f i : ℚ_[2] →+ M)) ∈ ratTateSubgroup (Fin r → M) := by
  have hf : ∀ i, ∃ N : ℕ, ∀ x : ℤ_[2], (f i : ℚ_[2] →+ M) ((2 : ℚ_[2]) ^ N * (x : ℚ_[2])) = 0 :=
    fun i => (f i).2
  choose N hN using hf
  refine ⟨∑ i, N i, fun x => funext fun i => ?_⟩
  have hle : N i ≤ ∑ j, N j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [AddMonoidHom.pi_apply, hk, Pi.zero_apply]
  exact map_two_pow_add_mul_eq_zero (hN i) k x

/-- **`V₂` of a finite power**: `V₂(M^r) ≃ (V₂M)^r`. -/
def RatTate.piEquiv (r : ℕ) : RatTate (Fin r → M) ≃ₗ[ℚ_[2]] (Fin r → RatTate M) where
  toFun f i := RatTate.map (Pi.evalAddMonoidHom (fun _ : Fin r => M) i) f
  invFun g := ⟨AddMonoidHom.pi (fun i => (g i : ℚ_[2] →+ M)), pi_mem_ratTateSubgroup g⟩
  map_add' f g := funext fun _ => map_add _ f g
  map_smul' c f := funext fun _ => map_smul _ c f
  left_inv _ := Subtype.ext <| AddMonoidHom.ext fun _ => rfl
  right_inv _ := funext fun _ => Subtype.ext <| AddMonoidHom.ext fun _ => rfl

/-! Section: Finite groups. -/

/-- **`V₂F = 0` for a finite group `F`**: an additive map from the divisible group `ℚ₂` to a finite
group is zero, since `f x = f (n • (x / n)) = n • f (x / n) = 0` with `n = Nat.card F`. PROVED. -/
theorem RatTate.subsingleton_of_finite (F : Type*) [AddCommGroup F] [Finite F] :
    Subsingleton (RatTate F) := by
  have key : ∀ h : ℚ_[2] →+ F, h = 0 := by
    intro h
    refine AddMonoidHom.ext fun x => ?_
    have hn : (Nat.card F : ℚ_[2]) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hx : x = Nat.card F • (x / (Nat.card F : ℚ_[2])) := by
      rw [nsmul_eq_mul, mul_div_cancel₀ _ hn]
    rw [AddMonoidHom.zero_apply, hx, map_nsmul, card_nsmul_eq_zero']
  exact ⟨fun f g => Subtype.ext ((key f).trans (key g).symm)⟩

/-! Section: The key computation `V₂(ℚ₂/ℤ₂) ≃ ℚ₂`. -/

/-- A class in `ℚ₂/ℤ₂` vanishes iff a representative is a `2`-adic integer. PROVED. -/
theorem mk_eq_zero_iff (y : ℚ_[2]) : ((y : ℚ_[2]) : Q2Z2) = 0 ↔ ‖y‖ ≤ 1 := by
  rw [QuotientAddGroup.eq_zero_iff]
  exact Iff.rfl

/-- Two classes in `ℚ₂/ℤ₂` agree iff the representatives differ by a `2`-adic integer.
PROVED. -/
theorem mk_eq_mk_iff (y z : ℚ_[2]) : ((y : ℚ_[2]) : Q2Z2) = (z : Q2Z2) ↔ ‖z - y‖ ≤ 1 := by
  rw [QuotientAddGroup.eq, neg_add_eq_sub]
  exact Iff.rfl

/-- The additive map `x ↦ [a x]` from `ℚ₂` to `ℚ₂/ℤ₂`. -/
def q2z2Hom (a : ℚ_[2]) : ℚ_[2] →+ Q2Z2 :=
  (QuotientAddGroup.mk' (PadicInt.subring 2).toAddSubgroup).comp (AddMonoidHom.mulLeft a)

/-- `q2z2Hom a` evaluated: `x ↦ [a x]`. PROVED. -/
@[simp]
theorem q2z2Hom_apply (a x : ℚ_[2]) : q2z2Hom a x = ((a * x : ℚ_[2]) : Q2Z2) :=
  rfl

/-- `x ↦ [a x]` kills `2^k ℤ₂` as soon as `2^k a ∈ ℤ₂`; so it lies in the rational Tate
subgroup. PROVED. -/
theorem q2z2Hom_mem (a : ℚ_[2]) : q2z2Hom a ∈ ratTateSubgroup Q2Z2 := by
  obtain ⟨k, hk⟩ := exists_two_pow_mul_norm_le_one a
  refine ⟨k, fun x => ?_⟩
  rw [q2z2Hom_apply, mk_eq_zero_iff]
  have h : a * ((2 : ℚ_[2]) ^ k * (x : ℚ_[2])) = (2 : ℚ_[2]) ^ k * a * x := by ring
  rw [h]
  exact norm_mul_le_one hk x.2

/-- The `ℚ₂`-linear map `ℚ₂ → V₂(ℚ₂/ℤ₂)`, `a ↦ (x ↦ [a x])`. -/
def ratTateOfQ2 : ℚ_[2] →ₗ[ℚ_[2]] RatTate Q2Z2 where
  toFun a := ⟨q2z2Hom a, q2z2Hom_mem a⟩
  map_add' a b := Subtype.ext <| AddMonoidHom.ext fun x => by
    simp [add_mul]
  map_smul' c a := Subtype.ext <| AddMonoidHom.ext fun x => by
    simp only [RingHom.id_apply, RatTate.smul_apply, q2z2Hom_apply, smul_eq_mul]
    congr 1
    ring

/-- `ratTateOfQ2 a` evaluated: `x ↦ [a x]`. PROVED. -/
@[simp]
theorem ratTateOfQ2_apply (a x : ℚ_[2]) :
    ((ratTateOfQ2 a : RatTate Q2Z2) : ℚ_[2] →+ Q2Z2) x = ((a * x : ℚ_[2]) : Q2Z2) :=
  rfl

/-- Injectivity of `a ↦ (x ↦ [a x])`: for `a ≠ 0`, `x = (2a)⁻¹` gives `[1/2] ≠ 0`. PROVED. -/
theorem ratTateOfQ2_injective : Function.Injective ratTateOfQ2 := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  by_contra hne
  have h : ((ratTateOfQ2 a : RatTate Q2Z2) : ℚ_[2] →+ Q2Z2) ((2 * a)⁻¹) = 0 := by
    rw [ha]
    rfl
  rw [ratTateOfQ2_apply, mk_eq_zero_iff] at h
  have e : a * (2 * a)⁻¹ = 2⁻¹ := by field_simp
  rw [e, norm_inv, norm_two_padic] at h
  norm_num at h

/-- **`End(ℚ₂/ℤ₂) = ℤ₂`, in the form needed here**: an additive map `g : ℚ₂ → ℚ₂/ℤ₂` killing `ℤ₂`
is `x ↦ [b x]` for some `b`. The sets `S n = {b ∈ ℤ₂ : g (2^{-n}) = [b 2^{-n}]}` are nonempty
(as `2^n • g (2^{-n}) = g 1 = 0`), closed and decreasing, so by compactness of `ℤ₂` they have a
common point `b`; writing `x = k 2^{-n} + z` with `k ∈ ℕ`, `z ∈ ℤ₂` gives `g x = [b x]`.
PROVED. -/
theorem exists_eq_q2z2Hom_of_map_eq_zero (g : ℚ_[2] →+ Q2Z2) (hg : ∀ x : ℤ_[2], g x = 0) :
    ∃ b : ℚ_[2], g = q2z2Hom b := by
  have h2 : ∀ n : ℕ, (2 : ℚ_[2]) ^ n ≠ 0 := fun n => pow_ne_zero n two_ne_zero
  let S : ℕ → Set ℤ_[2] := fun n =>
    {b | g ((2 : ℚ_[2]) ^ n)⁻¹ = (((b : ℚ_[2]) * ((2 : ℚ_[2]) ^ n)⁻¹ : ℚ_[2]) : Q2Z2)}
  have hS : ∀ n (b : ℤ_[2]), b ∈ S n ↔
      g ((2 : ℚ_[2]) ^ n)⁻¹ = (((b : ℚ_[2]) * ((2 : ℚ_[2]) ^ n)⁻¹ : ℚ_[2]) : Q2Z2) :=
    fun _ _ => Iff.rfl
  have hsub : ∀ n, S (n + 1) ⊆ S n := by
    intro n b hb
    rw [hS] at hb ⊢
    have e1 : ((2 : ℚ_[2]) ^ n)⁻¹ = 2 • ((2 : ℚ_[2]) ^ (n + 1))⁻¹ := by
      rw [nsmul_eq_mul, pow_succ]
      field_simp
      norm_num
    have e2 : (b : ℚ_[2]) * ((2 : ℚ_[2]) ^ n)⁻¹ =
        2 • ((b : ℚ_[2]) * ((2 : ℚ_[2]) ^ (n + 1))⁻¹) := by
      rw [e1, nsmul_eq_mul, nsmul_eq_mul]
      ring
    rw [e2, QuotientAddGroup.mk_nsmul, ← hb, ← map_nsmul, ← e1]
  have hne : ∀ n, (S n).Nonempty := by
    intro n
    obtain ⟨y, hy⟩ := QuotientAddGroup.mk_surjective (s := (PadicInt.subring 2).toAddSubgroup)
      (g ((2 : ℚ_[2]) ^ n)⁻¹)
    have h1 : (((2 : ℚ_[2]) ^ n * y : ℚ_[2]) : Q2Z2) = 0 := by
      have e1 : (2 : ℚ_[2]) ^ n * y = (2 ^ n : ℕ) • y := by
        rw [nsmul_eq_mul]
        push_cast
        ring
      have e2 : ((1 : ℤ_[2]) : ℚ_[2]) = (2 ^ n : ℕ) • ((2 : ℚ_[2]) ^ n)⁻¹ := by
        rw [nsmul_eq_mul, PadicInt.coe_one]
        push_cast
        exact (mul_inv_cancel₀ (h2 n)).symm
      rw [e1, QuotientAddGroup.mk_nsmul]
      change (2 ^ n : ℕ) • (QuotientAddGroup.mk y : Q2Z2) = 0
      rw [hy, ← map_nsmul, ← e2]
      exact hg 1
    rw [mk_eq_zero_iff] at h1
    refine ⟨Padic.lift ((2 : ℚ_[2]) ^ n * y) h1, ?_⟩
    rw [hS, PadicInt.coe_lift, ← hy]
    congr 1
    field_simp
  have hcl : ∀ n, IsClosed (S n) := by
    intro n
    obtain ⟨y, hy⟩ := QuotientAddGroup.mk_surjective (s := (PadicInt.subring 2).toAddSubgroup)
      (g ((2 : ℚ_[2]) ^ n)⁻¹)
    have e : S n = {b : ℤ_[2] | ‖(b : ℚ_[2]) * ((2 : ℚ_[2]) ^ n)⁻¹ - y‖ ≤ 1} := by
      ext b
      rw [hS, Set.mem_ofPred_eq, ← hy]
      exact mk_eq_mk_iff _ _
    rw [e]
    have hc : Continuous (fun b : ℤ_[2] => (b : ℚ_[2])) := continuous_subtype_val
    exact isClosed_le (by fun_prop) continuous_const
  obtain ⟨b, hb⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hsub hne
    (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hb
  refine ⟨b, AddMonoidHom.ext fun x => ?_⟩
  obtain ⟨n, hn⟩ := exists_two_pow_mul_norm_le_one x
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp
    (PadicInt.appr_spec n (Padic.lift ((2 : ℚ_[2]) ^ n * x) hn))
  set k : ℕ := PadicInt.appr (Padic.lift ((2 : ℚ_[2]) ^ n * x) hn) n with hk
  have hz' := congrArg (fun w : ℤ_[2] => (w : ℚ_[2])) hz
  simp only [PadicInt.coe_mul, PadicInt.coe_sub, PadicInt.coe_pow, PadicInt.coe_natCast,
    PadicInt.coe_lift] at hz'
  have hx : x = (k : ℚ_[2]) * ((2 : ℚ_[2]) ^ n)⁻¹ + (z : ℚ_[2]) := by
    have e3 : ((2 : ℕ) : ℚ_[2]) = 2 := by norm_num
    rw [e3] at hz'
    field_simp
    linear_combination -hz'
  have hbn : g ((2 : ℚ_[2]) ^ n)⁻¹ = (((b : ℚ_[2]) * ((2 : ℚ_[2]) ^ n)⁻¹ : ℚ_[2]) : Q2Z2) :=
    (hS n b).mp (hb n)
  have hbz : (((b : ℚ_[2]) * (z : ℚ_[2]) : ℚ_[2]) : Q2Z2) = 0 :=
    (mk_eq_zero_iff _).mpr (norm_mul_le_one b.2 z.2)
  rw [q2z2Hom_apply]
  calc g x = g ((k : ℚ_[2]) * ((2 : ℚ_[2]) ^ n)⁻¹ + (z : ℚ_[2])) := congrArg g hx
    _ = k • g ((2 : ℚ_[2]) ^ n)⁻¹ := by rw [map_add, hg z, add_zero, ← nsmul_eq_mul, map_nsmul]
    _ = k • (((b : ℚ_[2]) * ((2 : ℚ_[2]) ^ n)⁻¹ : ℚ_[2]) : Q2Z2) := by rw [hbn]
    _ = (((k : ℚ_[2]) * ((b : ℚ_[2]) * ((2 : ℚ_[2]) ^ n)⁻¹) : ℚ_[2]) : Q2Z2) := by
      rw [← QuotientAddGroup.mk_nsmul, nsmul_eq_mul]
    _ = (((k : ℚ_[2]) * ((b : ℚ_[2]) * ((2 : ℚ_[2]) ^ n)⁻¹) + (b : ℚ_[2]) * (z : ℚ_[2]) :
          ℚ_[2]) : Q2Z2) := by
      rw [QuotientAddGroup.mk_add, hbz, add_zero]
    _ = (((b : ℚ_[2]) * x : ℚ_[2]) : Q2Z2) := by
      rw [hx]
      congr 1
      ring

/-- Surjectivity of `a ↦ (x ↦ [a x])` onto `V₂(ℚ₂/ℤ₂)`: if `f` kills `2^N ℤ₂`, then
`g x = f (2^N x)` kills `ℤ₂`, so `g = (x ↦ [b x])` and `f = (x ↦ [b 2^{-N} x])`. PROVED. -/
theorem ratTateOfQ2_surjective : Function.Surjective ratTateOfQ2 := by
  rintro ⟨f, N, hN⟩
  obtain ⟨b, hb⟩ := exists_eq_q2z2Hom_of_map_eq_zero
    (f.comp (AddMonoidHom.mulLeft ((2 : ℚ_[2]) ^ N))) (fun x => hN x)
  have h2 : (2 : ℚ_[2]) ^ N ≠ 0 := pow_ne_zero N two_ne_zero
  refine ⟨b * ((2 : ℚ_[2]) ^ N)⁻¹, Subtype.ext (AddMonoidHom.ext fun x => ?_)⟩
  have h := congrArg (fun φ : ℚ_[2] →+ Q2Z2 => φ (((2 : ℚ_[2]) ^ N)⁻¹ * x)) hb
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, q2z2Hom_apply,
    mul_inv_cancel_left₀ h2] at h
  rw [ratTateOfQ2_apply, h, mul_assoc]

/-- **`V₂(ℚ₂/ℤ₂) ≃ ℚ₂`** as `ℚ₂`-vector spaces; the inverse sends `a` to `x ↦ [a x]`
(`ratTateQ2Z2Equiv_symm_apply`). -/
def ratTateQ2Z2Equiv : RatTate Q2Z2 ≃ₗ[ℚ_[2]] ℚ_[2] :=
  (LinearEquiv.ofBijective ratTateOfQ2 ⟨ratTateOfQ2_injective, ratTateOfQ2_surjective⟩).symm

/-- The inverse of `ratTateQ2Z2Equiv` sends `a` to `x ↦ [a x]`. PROVED. -/
@[simp]
theorem ratTateQ2Z2Equiv_symm_apply (a x : ℚ_[2]) :
    ((ratTateQ2Z2Equiv.symm a : RatTate Q2Z2) : ℚ_[2] →+ Q2Z2) x = ((a * x : ℚ_[2]) : Q2Z2) :=
  rfl

/-! Section: The dimension count. -/

/-- For `M ≃+ (ℚ₂/ℤ₂)^r × F`: `V₂M ≃ ℚ₂^r × V₂F`. -/
def RatTate.equivOfAddEquiv {F : Type*} [AddCommGroup F] {r : ℕ}
    (e : M ≃+ (Fin r → Q2Z2) × F) : RatTate M ≃ₗ[ℚ_[2]] (Fin r → ℚ_[2]) × RatTate F :=
  (RatTate.congr e).trans <| RatTate.prodEquiv.trans <|
    LinearEquiv.prodCongr
      ((RatTate.piEquiv r).trans (LinearEquiv.piCongrRight fun _ => ratTateQ2Z2Equiv))
      (LinearEquiv.refl ℚ_[2] (RatTate F))

/-- **The rational Tate module of a cofinitely generated `ℤ₂`-module is finite dimensional.**
PROVED. -/
theorem finiteDimensional_ratTate_of_Z2Corank {M : Type*} [AddCommGroup M] {r : ℕ}
    (h : Z2Corank M r) : FiniteDimensional ℚ_[2] (RatTate M) := by
  obtain ⟨F, _, _, ⟨e⟩⟩ := h
  have := RatTate.subsingleton_of_finite F
  exact (RatTate.equivOfAddEquiv e).symm.finiteDimensional

/-- **`dim_{ℚ₂} V₂M = corank_{ℤ₂} M`**: if `M ≅ (ℚ₂/ℤ₂)^r × F` with `F` finite, then the rational
Tate module of `M` has `ℚ₂`-dimension `r`. PROVED. -/
theorem finrank_ratTate_of_Z2Corank {M : Type*} [AddCommGroup M] {r : ℕ}
    (h : Z2Corank M r) : Module.finrank ℚ_[2] (RatTate M) = r := by
  obtain ⟨F, _, _, ⟨e⟩⟩ := h
  have := RatTate.subsingleton_of_finite F
  rw [(RatTate.equivOfAddEquiv e).finrank_eq, Module.finrank_prod, Module.finrank_fin_fun,
    Module.finrank_zero_of_subsingleton, add_zero]

/-- The product of the rational Tate modules of two cofinitely generated `ℤ₂`-modules is finite
dimensional. PROVED. -/
theorem finiteDimensional_ratTate_prod_of_Z2Corank {M₁ M₂ : Type*} [AddCommGroup M₁]
    [AddCommGroup M₂] {r₁ r₂ : ℕ} (h₁ : Z2Corank M₁ r₁) (h₂ : Z2Corank M₂ r₂) :
    FiniteDimensional ℚ_[2] (RatTate M₁ × RatTate M₂) := by
  have := finiteDimensional_ratTate_of_Z2Corank h₁
  have := finiteDimensional_ratTate_of_Z2Corank h₂
  infer_instance

/-- **Dimensions add**: for coranks `r₁, r₂`, `dim_{ℚ₂} (V₂M₁ × V₂M₂) = r₁ + r₂`. PROVED. -/
theorem finrank_ratTate_prod_of_Z2Corank {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂]
    {r₁ r₂ : ℕ} (h₁ : Z2Corank M₁ r₁) (h₂ : Z2Corank M₂ r₂) :
    Module.finrank ℚ_[2] (RatTate M₁ × RatTate M₂) = r₁ + r₂ := by
  have := finiteDimensional_ratTate_of_Z2Corank h₁
  have := finiteDimensional_ratTate_of_Z2Corank h₂
  rw [Module.finrank_prod, finrank_ratTate_of_Z2Corank h₁, finrank_ratTate_of_Z2Corank h₂]

/-! Section: Non-vacuity. -/

/-- Non-vacuity: `V₂(ℚ₂/ℤ₂)` is one dimensional. PROVED. -/
theorem finrank_ratTate_Q2Z2 : Module.finrank ℚ_[2] (RatTate Q2Z2) = 1 := by
  rw [ratTateQ2Z2Equiv.finrank_eq, Module.finrank_self]

/-- Non-vacuity: `ℚ₂/ℤ₂` has corank one (`ℚ₂/ℤ₂ ≃ (ℚ₂/ℤ₂)^1 × 0`). PROVED. -/
theorem z2Corank_Q2Z2_one : Z2Corank Q2Z2 1 :=
  ⟨PUnit, inferInstance, inferInstance,
    ⟨(AddEquiv.funUnique (Fin 1) Q2Z2).symm.trans AddEquiv.prodUnique.symm⟩⟩

/-- Non-vacuity: the zero group has corank zero. PROVED. -/
theorem z2Corank_punit_zero : Z2Corank PUnit 0 :=
  ⟨PUnit, inferInstance, inferInstance,
    ⟨(AddEquiv.ofUnique : PUnit ≃+ (Fin 0 → Q2Z2)).trans AddEquiv.prodUnique.symm⟩⟩

/-- Non-vacuity of the product statement: `dim_{ℚ₂} (V₂(ℚ₂/ℤ₂) × V₂(ℚ₂/ℤ₂)) = 2`. PROVED. -/
theorem finrank_ratTate_Q2Z2_prod :
    Module.finrank ℚ_[2] (RatTate Q2Z2 × RatTate Q2Z2) = 2 :=
  finrank_ratTate_prod_of_Z2Corank z2Corank_Q2Z2_one z2Corank_Q2Z2_one

end ZInQ.Manuscript.RC.BaseZeroLimit
