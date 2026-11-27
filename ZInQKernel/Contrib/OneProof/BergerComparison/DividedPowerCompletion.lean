import ZInQKernel.Contrib.OneProof.BergerComparison.RestrictedEvaluation

/-! Integral restricted divided-power series, before evaluation. The
principal p-adic filtration is exactly the filtration on their integral
divided-power coefficients, and this ring is complete for it. -/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4 BergerBst FontaineSt PowerSeries Ideal
open PanBergerSplit (Ainf AinfP)
open ZInQ.Contrib.G9.BdrKer.Cp

variable (p : ℕ) [hp : Fact p.Prime]

set_option maxHeartbeats 350000

private abbrev pI (S : Type*) [CommRing S] : Ideal S := Ideal.span {(p : S)}

private theorem loc_injective :
    Function.Injective (algebraMap (Ainf p) (AinfP p)) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors (witt_p_ne_zero p))

private theorem dpSeries_injective : Function.Injective (dpSeries p) := by
  intro f g h
  apply PowerSeries.ext
  intro n
  have he := congrArg (coeff n) h
  simp only [dpSeries, PowerSeries.coeff_mk] at he
  apply loc_injective p
  have hu : IsUnit (qpToLoc p ((n.factorial : ℚ_[p])⁻¹)) :=
    (isUnit_iff_ne_zero.mpr (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)))).map _
  obtain ⟨u, hu⟩ := hu
  rw [← hu] at he
  simpa only [mul_assoc, Units.mul_inv, mul_one] using
    congrArg (fun x : AinfP p => x * ↑u⁻¹) he

private theorem dpSeries_zero : dpSeries p 0 = 0 := by
  apply PowerSeries.ext
  intro n
  simp [dpSeries]

private theorem dpSeries_neg (a : (Ainf p)⟦X⟧) : dpSeries p (-a) = -dpSeries p a := by
  apply eq_neg_of_add_eq_zero_left
  rw [← dpSeries_add, neg_add_cancel, dpSeries_zero]

/-- The ring of restricted divided-power series in a formal variable,
prior to the evaluation at a generator of the Fontaine kernel. -/
def dividedPowerRestricted : Subring (AinfP p)⟦X⟧ where
  carrier := {s | ∃ f ∈ restricted p, dpSeries p f = s}
  zero_mem' := ⟨0, (restricted p).zero_mem, dpSeries_zero p⟩
  one_mem' := ⟨C 1, C_mem_restricted _ _, by rw [dpSeries_C, map_one, map_one]⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, (restricted p).add_mem hf hg, dpSeries_add p f g⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, (restricted p).neg_mem hf, dpSeries_neg p f⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨dpMul p f g, dpMul_mem p hf hg, (dpSeries_mul p f g).symm⟩

/-- Taking the divided-power series from its sequence of coefficients is
an additive equivalence. Its source uses the ordinary series product. -/
def dividedPowerCoeffs : restricted p ≃+ dividedPowerRestricted p := by
  let F : restricted p →+ dividedPowerRestricted p :=
    { toFun := fun f => ⟨dpSeries p f, f, f.property, rfl⟩
      map_zero' := Subtype.ext (dpSeries_zero p)
      map_add' := fun f g => Subtype.ext (dpSeries_add p f g) }
  refine AddEquiv.ofBijective F ⟨?_, ?_⟩
  · intro f g h
    exact Subtype.ext (dpSeries_injective p (congrArg Subtype.val h))
  · rintro ⟨_, f, hf, h⟩
    exact ⟨⟨f, hf⟩, Subtype.ext h⟩

theorem pDvd_iff_coeff (f : restricted p) (k : ℕ) :
    (p : restricted p)^k ∣ f ↔ ∀ n, (p : Ainf p)^k ∣ coeff n f.val := by
  constructor
  · rintro ⟨g, rfl⟩ n
    change (p : Ainf p)^k ∣ coeff n (((p : (Ainf p)⟦X⟧)^k) * g.val)
    rw [← map_natCast (PowerSeries.C (R := Ainf p)), ← map_pow, coeff_C_mul]
    exact dvd_mul_right _ _
  · intro h
    let g := PowerSeries.mk fun n => Classical.choose (h n)
    have hg (n : ℕ) : coeff n f.val = (p : Ainf p)^k * coeff n g := by
      rw [PowerSeries.coeff_mk]
      exact Classical.choose_spec (h n)
    have hgr : g ∈ restricted p := fun l => by
      obtain ⟨N, hN⟩ := f.property (k + l)
      refine ⟨N, fun n hn => ?_⟩
      have hd := hN n hn
      change (p : Ainf p)^(k+l) ∣ coeff n f.val at hd
      rw [pow_add, hg] at hd
      exact (mul_dvd_mul_iff_left (pow_ne_zero _ (witt_p_ne_zero p))).mp hd
    refine ⟨⟨g, hgr⟩, Subtype.ext ?_⟩
    change f.val = (p : (Ainf p)⟦X⟧)^k * g
    apply PowerSeries.ext
    intro n
    rw [← map_natCast (PowerSeries.C (R := Ainf p)), ← map_pow, coeff_C_mul, hg]

omit hp in
private theorem smod_iff_dvd {S : Type*} [CommRing S] (k : ℕ) (a b : S) :
    (a ≡ b [SMOD (pI p S ^ k • ⊤ : Submodule S S)]) ↔ (p : S)^k ∣ a - b := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem exists_restricted_limit (F : ℕ → restricted p)
    (hF : ∀ m n, m ≤ n → (p : restricted p)^m ∣ F m - F n) :
    ∃ L : restricted p, ∀ k, (p : restricted p)^k ∣ F k - L := by
  have hex (j : ℕ) : ∃ a : Ainf p, ∀ k, (p : Ainf p)^k ∣ coeff j (F k).val - a := by
    obtain ⟨a, ha⟩ := IsPrecomplete.prec (I := pI p (Ainf p)) inferInstance
      (f := fun m => coeff j (F m).val) (by
        intro m n hmn
        apply (smod_iff_dvd p _ _ _).mpr
        have hd := (pDvd_iff_coeff p _ _).mp (hF m n hmn) j
        change (p : Ainf p)^m ∣ coeff j ((F m).val - (F n).val) at hd
        simpa only [map_sub] using hd)
    exact ⟨a, fun k => (smod_iff_dvd p _ _ _).mp (ha k)⟩
  let L := PowerSeries.mk fun j => Classical.choose (hex j)
  have hL (k j : ℕ) : (p : Ainf p)^k ∣ coeff j (F k).val - coeff j L := by
    rw [PowerSeries.coeff_mk]
    exact Classical.choose_spec (hex j) k
  have hLr : L ∈ restricted p := fun k => by
    obtain ⟨N, hN⟩ := (F k).property k
    refine ⟨N, fun j hj => ?_⟩
    simpa only [sub_sub_cancel] using dvd_sub (hN j hj) (hL k j)
  exact ⟨⟨L, hLr⟩, fun k => (pDvd_iff_coeff p _ _).mpr
    (fun j => by
      change (p : Ainf p)^k ∣ coeff j ((F k).val - L)
      rw [map_sub]
      exact hL k j)⟩

private theorem restricted_eq_zero (f : restricted p)
    (hf : ∀ k, (p : restricted p)^k ∣ f) : f = 0 := by
  apply Subtype.ext
  apply PowerSeries.ext
  intro j
  change coeff j f.val = coeff j 0
  rw [map_zero]
  apply IsHausdorff.haus (I := pI p (Ainf p)) inferInstance
  intro k
  have h := (pDvd_iff_coeff p _ _).mp (hf k) j
  exact (smod_iff_dvd p _ _ _).mpr (by simpa only [sub_zero] using h)

instance restricted_isAdicComplete : IsAdicComplete (pI p (restricted p)) (restricted p) where
  haus' f h := restricted_eq_zero p f (fun k => by
    simpa only [sub_zero] using (smod_iff_dvd p _ _ _).mp (h k))
  prec' F h := by
    obtain ⟨L, hL⟩ := exists_restricted_limit p F
      (fun _ _ hmn => (smod_iff_dvd p _ _ _).mp (h hmn))
    exact ⟨L, fun k => (smod_iff_dvd p _ _ _).mpr (hL k)⟩

omit hp in
private theorem addEquiv_pDvd {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+ T)
    (k : ℕ) (a : S) : (p : T)^k ∣ e a ↔ (p : S)^k ∣ a := by
  have hm (x : S) : e ((p : S)^k * x) = (p : T)^k * e x := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, ← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨e.symm b, e.injective ?_⟩
    rw [hm, AddEquiv.apply_symm_apply, hb]
  · rintro ⟨b, rfl⟩
    exact ⟨e b, hm b⟩

instance dividedPowerRestricted_isAdicComplete :
    IsAdicComplete (pI p (dividedPowerRestricted p)) (dividedPowerRestricted p) where
  haus' f h := by
    let e := dividedPowerCoeffs p
    apply e.symm.injective
    rw [map_zero]
    apply restricted_eq_zero p
    intro k
    apply (addEquiv_pDvd p e k _).mp
    rw [AddEquiv.apply_symm_apply]
    simpa only [sub_zero] using (smod_iff_dvd p _ _ _).mp (h k)
  prec' F h := by
    let e := dividedPowerCoeffs p
    obtain ⟨L, hL⟩ := exists_restricted_limit p (fun k => e.symm (F k)) (by
      intro m n hmn
      apply (addEquiv_pDvd p e m _).mp
      rw [map_sub, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
      exact (smod_iff_dvd p _ _ _).mp (h hmn))
    refine ⟨e L, fun k => (smod_iff_dvd p _ _ _).mpr ?_⟩
    simpa only [map_sub, AddEquiv.apply_symm_apply] using (addEquiv_pDvd p e k _).mpr (hL k)

end ZInQ.Manuscript.BergerComparison
