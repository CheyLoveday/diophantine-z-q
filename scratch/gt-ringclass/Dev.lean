import ZInQKernel.Contrib.TYZGenus.ShimuraModFn
import ZInQKernel.Contrib.TYZGenus.ShimuraMain

/-! Development copy: the T5Glue declarations `RingClassLattice` depends on (verbatim from
`scratch/t5-glue/T5Glue.lean`, origin/wip/t5-glue 39bb3cd2). -/

noncomputable section

set_option maxRecDepth 20000

namespace T5Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise

/-- The finite adeles `𝔸_{K,f}` of `K = ℚ(√−m)`. -/
abbrev AfK (m : ℕ) [NeZero m] := FiniteAdeleRing (𝓞 (QNeg m)) (QNeg m)

/-- `𝔞̂ ⊂ 𝔸_{K,f}`: the closure of (the image of) a subset `𝔞 ⊂ K`; for a lattice `𝔞`,
`𝔞̂ = 𝔞 ⊗ ℤ̂`. -/
def latHat (m : ℕ) [NeZero m] (𝔞 : Set (QNeg m)) : Set (AfK m) :=
  closure (algebraMap (QNeg m) (AfK m) '' 𝔞)

/-- The finite component `s_f ∈ 𝔸_{K,f}` of an idele `s` of `K`. -/
def finPart {m : ℕ} [NeZero m] (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) : AfK m :=
  (s : AdeleRing (𝓞 (QNeg m)) (QNeg m)).2

/-- The idele class of an idele. -/
def icl {m : ℕ} [NeZero m] (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) :
    IdeleClassGroup (𝓞 (QNeg m)) (QNeg m) :=
  QuotientGroup.mk s

section Copies

variable {m : ℕ} [NeZero m]

/-- The order `O = ℤ + f𝓞_K`, as a `ℤ`-submodule of `K`. -/
def Osub (m f : ℕ) [NeZero m] [NeZero f] : Submodule ℤ (QNeg m) :=
  ((conductorOrder (QNeg m) f).toSubalgebra.toSubmodule).restrictScalars ℤ

theorem mem_Osub {f : ℕ} [NeZero f] {x : QNeg m} :
    x ∈ Osub m f ↔ x ∈ (conductorOrder (QNeg m) f).toSubalgebra := Iff.rfl

/-- **`𝔍_s = K ∩ s_f·Ô_O`**: the `O`-lattice of the idele `s` (`Ô_O` the closure of `O`). -/
def idealOf (m f : ℕ) [NeZero m] [NeZero f] (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) :
    Set (QNeg m) :=
  {j | finPart s⁻¹ * algebraMap (QNeg m) (AfK m) j ∈ latHat m (Osub m f : Set (QNeg m))}

theorem finPart_inv_mul (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) : finPart s⁻¹ * finPart s = 1 := by
  simp only [finPart]
  rw [← Prod.snd_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Prod.snd_one]

theorem finPart_mul_inv (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) : finPart s * finPart s⁻¹ = 1 := by
  simp only [finPart]
  rw [← Prod.snd_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Prod.snd_one]

theorem latHat_eq_closure (M : Submodule ℤ (QNeg m)) :
    latHat m (M : Set (QNeg m)) =
      ((M.toAddSubgroup.map (algebraMap (QNeg m) (AfK m)).toAddMonoidHom).topologicalClosure :
        Set (AfK m)) := by
  rw [AddSubgroup.topologicalClosure_coe, latHat]
  rfl

theorem latHat_add_mem (M : Submodule ℤ (QNeg m)) {x y : AfK m}
    (hx : x ∈ latHat m (M : Set (QNeg m))) (hy : y ∈ latHat m (M : Set (QNeg m))) :
    x + y ∈ latHat m (M : Set (QNeg m)) := by
  rw [latHat_eq_closure] at hx hy ⊢
  exact AddSubgroup.add_mem _ hx hy

theorem mem_latHat_of_mem {𝔞 : Set (QNeg m)} {x : QNeg m} (hx : x ∈ 𝔞) :
    algebraMap (QNeg m) (AfK m) x ∈ latHat m 𝔞 :=
  subset_closure ⟨x, hx, rfl⟩

/-- `f·𝒪̂ ⊆ Ô_O`. -/
theorem fIntAd_sub_latHatO {f : ℕ} [NeZero f] {z : AfK m}
    (hz : algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * z ∈
      FiniteAdeleRing.integralAdeles (𝓞 (QNeg m)) (QNeg m)) :
    z ∈ latHat m (Osub m f : Set (QNeg m)) := by
  have hf0 : (f : QNeg m) ≠ 0 := by exact_mod_cast NeZero.ne f
  have hcl := FiniteAdeleRing.closure_range_algebraMap (𝓞 (QNeg m)) (QNeg m)
  have hz' := (Set.ext_iff.1 hcl (algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * z)).2 hz
  have hcont : Continuous fun w : AfK m => algebraMap (QNeg m) (AfK m) (f : QNeg m) * w :=
    continuous_const.mul continuous_id
  have h1 := image_closure_subset_closure_image hcont ⟨_, hz', rfl⟩
  have hzeq : algebraMap (QNeg m) (AfK m) (f : QNeg m) *
      (algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * z) = z := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hf0, map_one, one_mul]
  beta_reduce at h1
  rw [hzeq] at h1
  refine closure_mono ?_ h1
  rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
  refine ⟨(f : QNeg m) * (r : QNeg m), ?_, ?_⟩
  · show (f : QNeg m) * (r : QNeg m) ∈ (conductorOrder (QNeg m) f).toSubalgebra
    rw [conductorOrder_toSubalgebra, mem_conductorOrderSubalgebra]
    exact ⟨0, r, by simp⟩
  · rw [map_mul] <;> rfl

/-- **GLUE RING-CLASS-LATTICE (the idelic and the congruence descriptions of `Pic O` agree).** If
the ring class of the idele `s` (Tau Ceti's `ringClassIdeleQuotient`, defined through ray classes
modulo the conductor) is the class of `J ∩ O`, then the `O`-lattice `𝔍_s = K ∩ s_f·Ô_O` of `s` is
`k·(J ∩ O)` for some `k ∈ Kˣ`. (Standard: `Pic O ≅ 𝔸_K^×/Kˣ Ô_O^× K_∞^×`, `s ↦ [K ∩ s_f Ô_O]`;
Neukirch I §12 and VI §1, Cox §7 and §9; UNVERIFIED numbers. Proof: move `s` by a principal idele
into the congruence subgroup of the conductor `𝔣` (Tau Ceti
`exists_unitEmbedding_mul_mem_ideleCongrOneSubgroup`); then `rayClassQuotient` is the ray class of
the ideal `I` of `s_f` (`rayClassQuotient_mk_of_mem`), `I = J·(βγ)` with `β ∈ O`, `γ ≡ 1 mod* 𝔣`
(`mem_ker_rayClassToPic`), and locally `s_f Ô_O = I_p` at `p ∤ f`, `= O_p` at `p ∣ f`, so
`𝔍_s = I ∩ O = βγ·(J ∩ O)`.) -/
def RingClassLattice : Prop :=
  ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
  ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus)
    (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)),
    ringClassIdeleQuotient (conductorOrder (QNeg m) f) (icl s) =
      (conductorOrder (QNeg m) f).picClass J →
    ∃ k : QNeg m, k ≠ 0 ∧ idealOf m f s = (fun x => k * x) '' idealMeetOrder m f J

end Copies

/-! ## gt-ringclass: proof of `RingClassLattice` -/

section RCL

variable {m : ℕ} [NeZero m]

local notation "𝒪̂" => FiniteAdeleRing.integralAdeles (𝓞 (QNeg m)) (QNeg m)

/-- The valuation of the `v`-component of a principal finite adele. -/
theorem val_algebraMap_apply (v : HeightOneSpectrum (𝓞 (QNeg m))) (x : QNeg m) :
    Valued.v ((algebraMap (QNeg m) (AfK m) x) v) = v.valuation (QNeg m) x := by
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

theorem mem_intAdeles_iff (z : AfK m) :
    z ∈ 𝒪̂ ↔ ∀ v : HeightOneSpectrum (𝓞 (QNeg m)), Valued.v (z v) ≤ 1 := by
  rw [FiniteAdeleRing.mem_integralAdeles]
  rfl

theorem valuation_le_exp_of_mem_pow (v : HeightOneSpectrum (𝓞 (QNeg m))) {r : 𝓞 (QNeg m)} {n : ℕ}
    (hr : r ∈ v.asIdeal ^ n) : v.valuation (QNeg m) (r : QNeg m) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (v.intValuation_le_pow_iff_mem r n).2 hr

theorem valuation_int_le_one (v : HeightOneSpectrum (𝓞 (QNeg m))) (r : 𝓞 (QNeg m)) :
    v.valuation (QNeg m) (r : QNeg m) ≤ 1 :=
  v.valuation_le_one r

theorem exp_neg_nat_le_one (n : ℕ) : WithZero.exp (-(n : ℤ)) ≤ 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem af_add_apply (z w : AfK m) (v : HeightOneSpectrum (𝓞 (QNeg m))) :
    (z + w) v = z v + w v := rfl

theorem af_sub_apply (z w : AfK m) (v : HeightOneSpectrum (𝓞 (QNeg m))) :
    (z - w) v = z v - w v := rfl

theorem af_mul_apply (z w : AfK m) (v : HeightOneSpectrum (𝓞 (QNeg m))) :
    (z * w) v = z v * w v := rfl

theorem af_neg_apply (z : AfK m) (v : HeightOneSpectrum (𝓞 (QNeg m))) :
    (-z) v = -z v := rfl

theorem af_zero_apply (v : HeightOneSpectrum (𝓞 (QNeg m))) :
    (0 : AfK m) v = 0 := rfl

/-- The local bound `exp(-e_v)`, `e_v` the exponent of `v` in the conductor of `O = ℤ + f𝓞_K`. -/
abbrev cBound (m f : ℕ) [NeZero m] [NeZero f] (v : HeightOneSpectrum (𝓞 (QNeg m))) : WithZero (Multiplicative ℤ) :=
  WithZero.exp (-((conductorOrder (QNeg m) f).conductorModulus.exponent v : ℤ))

/-- `𝔣̂`: the finite adeles whose `v`-component lies in `𝔭_v^{e_v}` at every finite place
(`e_v = 0` off the conductor, so these adeles are integral). -/
def fHat (m f : ℕ) [NeZero m] [NeZero f] : AddSubgroup (AfK m) where
  carrier := {z | ∀ v : HeightOneSpectrum (𝓞 (QNeg m)), Valued.v (z v) ≤ cBound m f v}
  zero_mem' := fun v => by
    show Valued.v ((0 : AfK m) v) ≤ _
    rw [af_zero_apply, map_zero]
    exact zero_le
  add_mem' := by
    intro z w hz hw v
    show Valued.v ((z + w) v) ≤ _
    rw [af_add_apply]
    exact Valuation.map_add_le _ (hz v) (hw v)
  neg_mem' := by
    intro z hz v
    show Valued.v ((-z) v) ≤ _
    rw [af_neg_apply, Valuation.map_neg]
    exact hz v

theorem mem_fHat {f : ℕ} [NeZero f] {z : AfK m} :
    z ∈ fHat m f ↔ ∀ v : HeightOneSpectrum (𝓞 (QNeg m)), Valued.v (z v) ≤ cBound m f v :=
  Iff.rfl

theorem conductor_le_pow_exponent {f : ℕ} [NeZero f] (v : HeightOneSpectrum (𝓞 (QNeg m))) :
    (conductorOrder (QNeg m) f).conductor ≤
      v.asIdeal ^ (conductorOrder (QNeg m) f).conductorModulus.exponent v := by
  have h := (conductorOrder (QNeg m) f).conductorModulus.pow_exponent_dvd_finitePart v
  rw [NumberFieldOrder.conductorModulus_finitePart] at h
  exact Ideal.le_of_dvd h

theorem valuation_le_cBound_of_mem_conductor {f : ℕ} [NeZero f]
    (v : HeightOneSpectrum (𝓞 (QNeg m))) {r : 𝓞 (QNeg m)}
    (hr : r ∈ (conductorOrder (QNeg m) f).conductor) :
    v.valuation (QNeg m) (r : QNeg m) ≤ cBound m f v :=
  valuation_le_exp_of_mem_pow v (conductor_le_pow_exponent v hr)

theorem algebraMap_mem_fHat_of_mem_conductor {f : ℕ} [NeZero f] {r : 𝓞 (QNeg m)}
    (hr : r ∈ (conductorOrder (QNeg m) f).conductor) :
    algebraMap (QNeg m) (AfK m) (r : QNeg m) ∈ fHat m f := fun v => by
  rw [val_algebraMap_apply]
  exact valuation_le_cBound_of_mem_conductor v hr

theorem exists_mem_conductor_of_algebraMap_mem_fHat {f : ℕ} [NeZero f] {x : QNeg m}
    (hx : algebraMap (QNeg m) (AfK m) x ∈ fHat m f) :
    ∃ r ∈ (conductorOrder (QNeg m) f).conductor, (r : QNeg m) = x := by
  have hx' : ∀ v : HeightOneSpectrum (𝓞 (QNeg m)), v.valuation (QNeg m) x ≤ cBound m f v :=
    fun v => by rw [← val_algebraMap_apply]; exact hx v
  obtain ⟨r, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (QNeg m) x
    (fun v => (hx' v).trans (exp_neg_nat_le_one _))
  refine ⟨r, ?_, rfl⟩
  rw [← NumberFieldOrder.conductorModulus_finitePart]
  refine (conductorOrder (QNeg m) f).conductorModulus.mem_finitePart_of_forall_mem_pow_exponent
    (fun v _ => ?_)
  rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem,
    ← HeightOneSpectrum.valuation_of_algebraMap (K := QNeg m)]
  exact hx' v

theorem natCast_mem_conductor (f : ℕ) [NeZero f] :
    (f : 𝓞 (QNeg m)) ∈ (conductorOrder (QNeg m) f).conductor := by
  simpa using natCast_mul_mem_conductor (QNeg m) f 1

/-- `f·𝒪̂ ⊆ 𝔣̂`. -/
theorem mem_fHat_of_fIntAd {f : ℕ} [NeZero f] {z : AfK m}
    (hz : algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * z ∈ 𝒪̂) : z ∈ fHat m f := by
  have hf0 : (f : QNeg m) ≠ 0 := by exact_mod_cast NeZero.ne f
  have hzeq : z = algebraMap (QNeg m) (AfK m) (f : QNeg m) *
      (algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * z) := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hf0, map_one, one_mul]
  intro v
  rw [hzeq, af_mul_apply, map_mul, val_algebraMap_apply]
  have h1 : v.valuation (QNeg m) (f : QNeg m) ≤ cBound m f v := by
    have := valuation_le_cBound_of_mem_conductor v (natCast_mem_conductor (m := m) f)
    simpa using this
  have h2 := (mem_intAdeles_iff _).1 hz v
  calc v.valuation (QNeg m) (f : QNeg m) *
        Valued.v ((algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * z) v)
      ≤ cBound m f v * 1 := mul_le_mul' h1 h2
    _ = cBound m f v := mul_one _

theorem isOpen_fIntAd (f : ℕ) :
    IsOpen {z : AfK m | algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * z ∈ 𝒪̂} :=
  (FiniteAdeleRing.isOpen_integralAdeles (𝓞 (QNeg m)) (QNeg m)).preimage
    (continuous_const.mul continuous_id)

theorem fHat_mem_nhds_zero (f : ℕ) [NeZero f] : (fHat m f : Set (AfK m)) ∈ nhds 0 := by
  refine Filter.mem_of_superset ((isOpen_fIntAd (m := m) f).mem_nhds ?_)
    (fun z hz => mem_fHat_of_fIntAd hz)
  show algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * 0 ∈ 𝒪̂
  rw [mul_zero]
  exact Subalgebra.zero_mem _

/-- `ℤ + 𝔣̂`. -/
def oHat (m f : ℕ) [NeZero m] [NeZero f] : AddSubgroup (AfK m) where
  carrier := {z | ∃ a : ℤ, z - algebraMap (QNeg m) (AfK m) (a : QNeg m) ∈ fHat m f}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro z w ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    have e : z + w - algebraMap (QNeg m) (AfK m) ((a + b : ℤ) : QNeg m) =
        (z - algebraMap (QNeg m) (AfK m) (a : QNeg m)) +
          (w - algebraMap (QNeg m) (AfK m) (b : QNeg m)) := by
      rw [Int.cast_add, map_add]; abel
    rw [e]
    exact (fHat m f).add_mem ha hb
  neg_mem' := by
    rintro z ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    have e : -z - algebraMap (QNeg m) (AfK m) ((-a : ℤ) : QNeg m) =
        -(z - algebraMap (QNeg m) (AfK m) (a : QNeg m)) := by
      rw [Int.cast_neg, map_neg]; abel
    rw [e]
    exact (fHat m f).neg_mem ha

theorem isClosed_oHat (f : ℕ) [NeZero f] : IsClosed (oHat m f : Set (AfK m)) := by
  refine AddSubgroup.isClosed_of_isOpen _ (AddSubgroup.isOpen_of_mem_nhds _ (g := 0) ?_)
  refine Filter.mem_of_superset (fHat_mem_nhds_zero (m := m) f) (fun z hz => ⟨0, ?_⟩)
  simpa using hz

/-- **`Ô_O = ℤ + 𝔣̂`** (`O = ℤ + 𝔣` for `O = ℤ + f𝓞_K` with conductor `𝔣`). -/
theorem mem_latHat_O_iff {f : ℕ} [NeZero f] (z : AfK m) :
    z ∈ latHat m (Osub m f : Set (QNeg m)) ↔
      ∃ a : ℤ, z - algebraMap (QNeg m) (AfK m) (a : QNeg m) ∈ fHat m f := by
  constructor
  · intro hz
    refine closure_minimal ?_ (isClosed_oHat (m := m) f) hz
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, y, rfl⟩ := (mem_conductorOrderSubalgebra (QNeg m)).1 hx
    refine ⟨a, ?_⟩
    have e : algebraMap (QNeg m) (AfK m) ((a : QNeg m) + (f : QNeg m) * (y : QNeg m)) -
        algebraMap (QNeg m) (AfK m) (a : QNeg m) =
        algebraMap (QNeg m) (AfK m) (((f : 𝓞 (QNeg m)) * y : 𝓞 (QNeg m)) : QNeg m) := by
      have e2 : (((f : 𝓞 (QNeg m)) * y : 𝓞 (QNeg m)) : QNeg m) = (f : QNeg m) * (y : QNeg m) := by
        simp
      rw [e2, ← map_sub, add_sub_cancel_left]
    rw [e]
    exact algebraMap_mem_fHat_of_mem_conductor (natCast_mul_mem_conductor (QNeg m) f y)
  · rintro ⟨a, ha⟩
    set w := z - algebraMap (QNeg m) (AfK m) (a : QNeg m)
    have hU : IsOpen {u : AfK m | algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * (w - u) ∈ 𝒪̂} :=
      (FiniteAdeleRing.isOpen_integralAdeles (𝓞 (QNeg m)) (QNeg m)).preimage
        (continuous_const.mul (continuous_const.sub continuous_id))
    have hwU : w ∈ {u : AfK m | algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * (w - u) ∈ 𝒪̂} := by
      show algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * (w - w) ∈ 𝒪̂
      rw [sub_self, mul_zero]; exact Subalgebra.zero_mem _
    obtain ⟨x, hx⟩ :=
      (FiniteAdeleRing.denseRange_algebraMap (𝓞 (QNeg m)) (QNeg m)).exists_mem_open hU ⟨w, hwU⟩
    change algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) *
      (w - algebraMap (QNeg m) (AfK m) x) ∈ 𝒪̂ at hx
    have hxF : algebraMap (QNeg m) (AfK m) x ∈ fHat m f := by
      have := (fHat m f).sub_mem ha (mem_fHat_of_fIntAd hx)
      simpa using this
    obtain ⟨r, hr, rfl⟩ := exists_mem_conductor_of_algebraMap_mem_fHat hxF
    have hrO : ((a : QNeg m) + (r : QNeg m)) ∈ (conductorOrder (QNeg m) f).toSubalgebra :=
      Subalgebra.add_mem _ (Subalgebra.intCast_mem _ a)
        ((conductorOrder (QNeg m) f).mem_toRingOfIntegers.1
          ((conductorOrder (QNeg m) f).conductor_le_toRingOfIntegers hr))
    have e : z = algebraMap (QNeg m) (AfK m) ((a : QNeg m) + (r : QNeg m)) +
        (w - algebraMap (QNeg m) (AfK m) (r : QNeg m)) := by
      rw [map_add]; simp only [w]; ring
    rw [e]
    exact latHat_add_mem _ (mem_latHat_of_mem hrO) (fIntAd_sub_latHatO hx)

end RCL

end T5Glue
