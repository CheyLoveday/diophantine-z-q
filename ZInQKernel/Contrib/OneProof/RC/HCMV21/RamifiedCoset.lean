import ZInQKernel.Contrib.OneProof.RC.LocalDivision.Quadratic

/-! Division-order calculations at the detector (tex 9146–9148, 9249–9255).
The residue factorization is an algebraic consequence of the order
identification. It does not require a choice of geometric Dieudonné module. -/

noncomputable section

namespace ZInQ.Manuscript.RC.HCMV21

open LocalDivision

variable {q : ℕ} [Fact q.Prime] [Fact (q % 4 = 3)]

omit [Fact (q % 4 = 3)] in
private theorem integralJ_sq :
    orderEquiv (p := q) integralJ * orderEquiv integralJ =
      algebraMap ℤ_[q] (order q) (-(q : ℤ_[q])) := by
  rw [← map_mul, ← (orderEquiv (p := q)).commutes]
  congr 1
  change (⟨0, 0, 1, 0⟩ : IntegralD q) * ⟨0, 0, 1, 0⟩ = _
  rw [QuaternionAlgebra.mk_mul_mk]
  apply QuaternionAlgebra.ext <;> simp [QuaternionAlgebra.algebraMap_eq]

/-- Any unital scalar action of the completed division order in
characteristic `q` is its canonical residue action followed by a field
embedding. In particular this applies to a tangent scalar action once the
geometric endomorphism order has been identified. -/
theorem division_scalar_factors {k : Type*} [Field k] [CharP k q]
    (d : order q →+* k) :
    ∃! e : GaloisField q 2 →+* k, e.comp (red (p := q)) = d := by
  have hJ : d (orderEquiv (p := q) integralJ) = 0 := by
    have h := congrArg d (integralJ_sq (q := q))
    simpa only [map_mul, map_neg, map_natCast, CharP.cast_eq_zero, neg_zero, mul_eq_zero,
      or_self] using h
  have hker : RingHom.ker (red (p := q)) ≤ RingHom.ker d := by
    intro a ha
    obtain ⟨y, hy⟩ := (red_ker_j _).mp (RingHom.mem_ker.mp ha)
    exact RingHom.mem_ker.mpr (by rw [hy, map_mul, hJ, zero_mul])
  let e := (red (p := q)).liftOfSurjective red_surj ⟨d, hker⟩
  have he : e.comp (red (p := q)) = d :=
    (red (p := q)).liftOfSurjective_comp red_surj ⟨d, hker⟩
  refine ⟨e, he, ?_⟩
  intro z hz
  ext t
  obtain ⟨a, rfl⟩ := red_surj t
  exact DFunLike.congr_fun (hz.trans he.symm) a

/-- The explicit division algebra is the direct sum of its unramified
quadratic field and that field times the division uniformizer. -/
theorem division_existsUnique_quadraticPair (x : D q) :
    ∃! yz : QuadraticD q × QuadraticD q,
      x = quadraticInclusion yz.1 + quadraticInclusion yz.2 * j := by
  have hcoords (a b : QuadraticD q) :
      quadraticInclusion a + quadraticInclusion b * j = (⟨a.re, a.im, b.re, b.im⟩ : D q) := by
    rw [quadraticInclusion_apply, quadraticInclusion_apply]
    change (⟨a.re, a.im, 0, 0⟩ : D q) + ⟨b.re, b.im, 0, 0⟩ * ⟨0,0,1,0⟩ = _
    rw [QuaternionAlgebra.mk_mul_mk]
    apply QuaternionAlgebra.ext <;> simp
  refine ⟨(⟨x.re, x.imI⟩, ⟨x.imJ, x.imK⟩), ?_, ?_⟩
  · change x = quadraticInclusion ⟨x.re, x.imI⟩ + quadraticInclusion ⟨x.imJ, x.imK⟩ * j
    rw [hcoords]
  · rintro ⟨a, b⟩ h
    change x = quadraticInclusion a + quadraticInclusion b * j at h
    rw [hcoords] at h
    exact Prod.ext
      (QuadraticAlgebra.ext (congrArg QuaternionAlgebra.re h).symm
        (congrArg QuaternionAlgebra.imI h).symm)
      (QuadraticAlgebra.ext (congrArg QuaternionAlgebra.imJ h).symm
        (congrArg QuaternionAlgebra.imK h).symm)

/-- The reduced-norm valuation is a homomorphism on division units. -/
def divisionVal (q : ℕ) [Fact q.Prime] [Fact (q % 4 = 3)] :
    (D q)ˣ →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd (nrd (g : D q)).valuation
  map_one' := by simp
  map_mul' g h := nrd_valuation_mul _ _ g.ne_zero h.ne_zero

/-- The inclusion of integral order units. -/
def divisionOrderUnits (q : ℕ) [Fact q.Prime] [Fact (q % 4 = 3)] :
    (order q)ˣ →* (D q)ˣ := Units.map (order q).val.toMonoidHom

theorem divisionVal_eq_one_iff (g : (D q)ˣ) :
    divisionVal q g = 1 ↔ g ∈ (divisionOrderUnits q).range := by
  constructor
  · intro h
    change (nrd (g : D q)).valuation = 0 at h
    let x : order q := ⟨g, (mem_order_iff_valuation _).2 h.ge⟩
    have hx : IsUnit x := (orderUnit_iff_norm _).2 (by
      change ‖nrd (g : D q)‖ = 1
      rw [Padic.norm_eq_zpow_neg_valuation (mt (nrd_eq_zero _).1 g.ne_zero), h]
      simp)
    exact ⟨hx.unit, Units.ext (congrArg Subtype.val hx.unit_spec)⟩
  · rintro ⟨u, rfl⟩
    have h₁ := (mem_order_iff_valuation ((u : order q) : D q)).1 (u : order q).property
    have h₂ := (mem_order_iff_valuation ((↑u⁻¹ : order q) : D q)).1
      (↑u⁻¹ : order q).property
    change 0 ≤ (divisionVal q (divisionOrderUnits q u)).toAdd at h₁
    change 0 ≤ (divisionVal q (divisionOrderUnits q u⁻¹)).toAdd at h₂
    rw [map_inv, map_inv] at h₂
    change 0 ≤ -(divisionVal q (divisionOrderUnits q u)).toAdd at h₂
    apply Multiplicative.toAdd.injective
    change (divisionVal q (divisionOrderUnits q u)).toAdd = 0
    omega

theorem divisionVal_uniformizer :
    divisionVal q (uniformizer (p := q)) = Multiplicative.ofAdd 1 :=
  congrArg Multiplicative.ofAdd (uniformizer_norm (p := q))

theorem division_uniformizer_decomposition (g : (D q)ˣ) :
    ∃ u : (order q)ˣ,
      g = uniformizer ^ (divisionVal q g).toAdd * divisionOrderUnits q u := by
  let n := (divisionVal q g).toAdd
  have h : divisionVal q (uniformizer ^ (-n) * g) = 1 := by
    rw [map_mul, map_zpow, divisionVal_uniformizer]
    change -n * 1 + n = 0
    omega
  obtain ⟨u, hu⟩ := (divisionVal_eq_one_iff _).1 h
  refine ⟨u, ?_⟩
  rw [hu, ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]

/-- Inclusion of the explicit unramified quadratic field on units. -/
def divisionTorus (q : ℕ) [Fact q.Prime] [Fact (q % 4 = 3)] :
    (QuadraticD q)ˣ →* (D q)ˣ := Units.map (quadraticInclusion (p := q)).toMonoidHom

theorem divisionVal_torus_even (a : (QuadraticD q)ˣ) :
    ∃ k : ℤ, (divisionVal q (divisionTorus q a)).toAdd = 2 * k := by
  change ∃ k : ℤ, (nrd (quadraticInclusion (a : QuadraticD q))).valuation = 2 * k
  rw [quadraticInclusion_apply, nrd_formula]
  simpa using valuation_pair_even (Fact.out : q % 4 = 3) a.val.re a.val.im

private theorem uniformizer_sq_value :
    (↑(uniformizer (p := q) ^ (2 : ℤ)) : D q) = algebraMap ℚ_[q] (D q) (-(q : ℚ_[q])) := by
  rw [zpow_two]
  change (⟨0, 0, 1, 0⟩ : D q) * ⟨0, 0, 1, 0⟩ = _
  rw [QuaternionAlgebra.mk_mul_mk]
  apply QuaternionAlgebra.ext <;> simp [QuaternionAlgebra.algebraMap_eq]

private theorem uniformizer_sq_torus :
    ∃ a : (QuadraticD q)ˣ, uniformizer (p := q) ^ (2 : ℤ) = divisionTorus q a := by
  have hq : (q : ℚ_[q]) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  let a : ℚ_[q]ˣ := Units.mk0 (-(q : ℚ_[q])) (neg_ne_zero.mpr hq)
  refine ⟨Units.map (algebraMap ℚ_[q] (QuadraticD q)) a, ?_⟩
  apply Units.ext
  rw [uniformizer_sq_value]
  change _ = quadraticInclusion (algebraMap ℚ_[q] (QuadraticD q) (-(q : ℚ_[q])))
  rw [AlgHom.commutes]

/-- The coset of a power of the division uniformizer is measured exactly
by its reduced-norm valuation modulo two. This gives the two cosets
represented by `1` and `Π` in the explicit local model. -/
theorem division_doubleCoset_iff (g : (D q)ˣ) (r : ℤ) :
    (∃ (a : (QuadraticD q)ˣ) (u : (order q)ˣ),
        g = divisionTorus q a * uniformizer ^ r * divisionOrderUnits q u) ↔
      (divisionVal q g).toAdd % 2 = r % 2 := by
  have hv (n : ℤ) : (divisionVal q (uniformizer ^ n)).toAdd = n := by
    rw [map_zpow, divisionVal_uniformizer]
    change n * 1 = n
    exact mul_one n
  constructor
  · rintro ⟨a, u, rfl⟩
    obtain ⟨k, hk⟩ := divisionVal_torus_even a
    have hu : divisionVal q (divisionOrderUnits q u) = 1 :=
      (divisionVal_eq_one_iff _).2 ⟨u, rfl⟩
    rw [map_mul (divisionVal q), hu, mul_one, map_mul (divisionVal q)]
    change ((divisionVal q (divisionTorus q a)).toAdd +
      (divisionVal q (uniformizer ^ r)).toAdd) % 2 = r % 2
    rw [hk, hv]
    omega
  · intro h
    obtain ⟨u, hu⟩ := division_uniformizer_decomposition g
    obtain ⟨c, hc⟩ := uniformizer_sq_torus (q := q)
    let k := ((divisionVal q g).toAdd - r) / 2
    have he : (divisionVal q g).toAdd = 2 * k + r := by dsimp [k]; omega
    refine ⟨c ^ k, u, ?_⟩
    rw [hu, he, zpow_add, zpow_mul, hc, map_zpow]

/-- Conjugation by an order unit induces the identity on its commutative
residue field. -/
theorem division_red_unit_conj (u : (order q)ˣ) (x : order q) :
    red ((↑u⁻¹ : order q) * x * (u : order q)) = red x := by
  rw [map_mul, map_mul, mul_comm _ (red (u : order q)), ← mul_assoc, ← map_mul, Units.mul_inv,
    map_one, one_mul]

/-- Frobenius is genuinely nontrivial on the chosen generators of the
residue field, hence insertion of one division uniformizer switches the
two characters for a surjective residual quadratic action. -/
theorem division_uniformizer_switches {S k : Type*} [Ring S] [Field k]
    (i : S →+* order q) (hi : Function.Surjective ((red (p := q)).comp i))
    (e : GaloisField q 2 →+* k) :
    e.comp ((red (p := q)).comp (uniformizerOrder.toRingHom.comp i)) ≠ e.comp (red.comp i) := by
  intro h
  obtain ⟨s, hs⟩ := hi (beta (p := q))
  change red (i s) = beta at hs
  have ht := e.injective (DFunLike.congr_fun h s)
  change red (uniformizerOrder (i s)) = red (i s) at ht
  rw [uniformizer_frobenius, hs, beta_frobenius] at ht
  have hc : (2 : GaloisField q 2) ≠ 0 := by
    intro hz
    have hd : q ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField q 2) q 2).mp (by exact_mod_cast hz)
    have hmod : q % 4 = 3 := Fact.out
    have hq := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  exact beta_ne_zero (by
    apply (mul_eq_zero.mp (show (2 : GaloisField q 2) * beta = 0 by linear_combination -ht)).resolve_left hc)

private theorem central_uniformizer_even (k : ℤ) (x : D q) :
    (↑((uniformizer ^ (2 * k : ℤ))⁻¹ : (D q)ˣ) : D q) * x *
      (↑(uniformizer ^ (2 * k : ℤ) : (D q)ˣ) : D q) = x := by
  let t : (D q)ˣ := uniformizer ^ (2 * k : ℤ)
  have ht : Commute (t : D q) x := by
    dsimp only [t]
    rw [zpow_mul]
    apply Commute.units_zpow_left
    rw [uniformizer_sq_value]
    exact Algebra.commute_algebraMap_left _ _
  change (↑t⁻¹ : D q) * x * (t : D q) = x
  rw [mul_assoc, ← ht.eq, ← mul_assoc, Units.inv_mul, one_mul]

private theorem inverseConj_mul {B : Type*} [Ring B] (a b : Bˣ) (x : B) :
    (↑(a * b)⁻¹ : B) * x * (↑(a * b) : B) =
      (↑b⁻¹ : B) * ((↑a⁻¹ : B) * x * (a : B)) * (b : B) := by
  simp only [mul_inv_rev, Units.val_mul, mul_assoc]

/-- Relative orientation for two labelled embeddings related by
conjugation: the same residue action occurs exactly at even reduced-norm
valuation. This holds for any integral label whose residue map is
surjective, without identifying that label with the coordinates `1,i`. -/
theorem division_same_orientation_iff_even {S k : Type*} [Ring S] [Field k]
    (i₀ i₁ : S →+* order q) (e : GaloisField q 2 →+* k)
    (hi : Function.Surjective ((red (p := q)).comp i₀)) (g : (D q)ˣ)
    (h : ∀ x : S, (i₁ x).val = (↑g⁻¹ : D q) * (i₀ x).val * (g : D q)) :
    e.comp (red.comp i₁) = e.comp (red.comp i₀) ↔ (divisionVal q g).toAdd % 2 = 0 := by
  let n := (divisionVal q g).toAdd
  let m := n / 2
  obtain ⟨u, hu⟩ := division_uniformizer_decomposition g
  let v := divisionOrderUnits q u
  by_cases hn : n % 2 = 0
  · have hn' : n = 2 * m := by dsimp [m]; omega
    have hg : g = uniformizer ^ (2 * m : ℤ) * v := by rwa [← hn']
    have hx (x : S) : i₁ x = (↑u⁻¹ : order q) * i₀ x * (u : order q) := by
      apply Subtype.ext
      rw [h, hg, inverseConj_mul, central_uniformizer_even]
      rfl
    refine ⟨fun _ => hn, fun _ => ?_⟩
    ext x
    change e (red (i₁ x)) = e (red (i₀ x))
    rw [hx, division_red_unit_conj]
  · have hn' : n = 2 * m + 1 := by dsimp [m]; omega
    have hg : g = uniformizer ^ (2 * m : ℤ) * uniformizer * v := by
      rw [hu, show (divisionVal q g).toAdd = 2 * m + 1 from hn', zpow_add, zpow_one]
    have hx (x : S) : i₁ x =
        (↑u⁻¹ : order q) * uniformizerOrder (i₀ x) * (u : order q) := by
      apply Subtype.ext
      rw [h, hg, inverseConj_mul, inverseConj_mul, central_uniformizer_even]
      rfl
    refine ⟨fun he => ?_, fun he => (hn he).elim⟩
    exfalso
    apply division_uniformizer_switches i₀ hi e
    rw [← he]
    ext x
    change e (red (uniformizerOrder (i₀ x))) = e (red (i₁ x))
    rw [hx, division_red_unit_conj]

end ZInQ.Manuscript.RC.HCMV21
