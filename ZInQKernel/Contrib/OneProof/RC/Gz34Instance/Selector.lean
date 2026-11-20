import ZInQKernel.Contrib.OneProof.RC.Gz34Instance.Forms
import ZInQKernel.Contrib.OneProof.RC.Gz34Instance.Primitive
import ZInQKernel.Contrib.OneProof.RC.StageSelector.Selector

/-! Selections for the two actual points in tex 2411–2416. The ring-class
realization hypothesis is the analogue of `StageSelector.PreparedParamValue`.
The total option functions and their coverage proofs are on-the-spot (c). -/

noncomputable section

open NumberField WeierstrassCurve ZInQ.Progressions TauCeti.ClassFieldTheory
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.Gz34Instance

section Datum

variable {E : WeierstrassCurve ℚ}
  {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ} {s h k : ℤ}

private theorem companion_nonsquare (hk : Companion E Lat s h k) : ¬ IsSquare (k : ℚ) :=
  Qsqrt.not_isSquare_of_squarefree hk.2.2.1 (ne_of_lt (hk.1.trans zero_lt_one))

private theorem conductor_ne_zero (hp : Prepared E s h) : NeZero h.natAbs :=
  ⟨Int.natAbs_ne_zero.mpr hp.1.ne'⟩

/-- The chosen primitive form for the companion, at the same leading
coefficient as the genus form. -/
def companionForm (hN : 0 < newformLevel E)
    (hp : Prepared E s h) (hk : Companion E Lat s h k) :
    {bc : ℤ × ℤ // IsHeegnerForm (newformLevel E) (k * h.natAbs ^ 2)
      (newformLevel E) bc.1 bc.2} :=
  let hex := exists_companion_form hN hp hk
  ⟨(hex.choose, hex.choose_spec.choose), hex.choose_spec.choose_spec⟩

open Classical in
/-- For the chosen companion form, only the algebraic realization of the
analytic parametrization value over its ring class field is required.
The field, form and primitive character are constructed independently. -/
def RingParamValue (E : WeierstrassCurve ℚ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (Lat : PeriodPair) (κ : ℂ) {s h k : ℤ} (hN : 0 < newformLevel E)
    (hp : Prepared E s h) (hk : Companion E Lat s h k) : Prop :=
  letI : Fact (¬ IsSquare (k : ℚ)) := ⟨companion_nonsquare hk⟩
  letI : NeZero h.natAbs := conductor_ne_zero hp
  let H := ringClassField (conductorOrder (Qsqrt k) h.natAbs)
  ∃ (ι : H →ₐ[ℚ] ℂ) (y : (E.baseChange H).toAffine.Point),
    Affine.Point.map (W' := E.toAffine) ι y =
      phiAn E f Lat κ (cmPoint (newformLevel E) (companionForm hN hp hk).val.1 (k * h.natAbs ^ 2))

private theorem conductor_coprime_disc (hk : Companion E Lat s h k) : IsCoprime h k := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  change (h.natAbs.gcd k.natAbs) = 1
  apply Nat.coprime_of_dvd
  intro p hpp hph hpk
  have hph' := Int.natCast_dvd.mpr hph
  exact (hk.2.2.2.1 p hpp (dvd_mul_of_dvd_right hph' _)).1 (Int.natCast_dvd.mpr hpk)

set_option maxRecDepth 1024 in
/-- The companion point uses its own field and conductor, and the same
form, lattice and scale as the genus point. -/
def datumOfCompanion (hN : 0 < newformLevel E)
    (hp : Prepared E s h) (hk : Companion E Lat s h k)
    (halg : RingParamValue E f Lat κ hN hp hk) : HeegnerDatum E f Lat κ k h.natAbs h := by
  classical
  letI : Fact (¬ IsSquare (k : ℚ)) := ⟨companion_nonsquare hk⟩
  letI : NeZero h.natAbs := conductor_ne_zero hp
  let K := Qsqrt k
  have hKC : IsTotallyComplex K := Qsqrt.isTotallyComplex hk.1
  have hD : discr K = k := StageSelector.qsqrt_discr hk.1 hk.2.2.1 hk.2.1
  have h4 := (hp.2.2.1 2 Nat.prime_two (dvd_mul_right 2 _)).mod_four
  let hχ := exists_ringCharacter (c := h.natAbs) (K := K) Qsqrt.finrank hKC (d := h) rfl
  unfold RingParamValue at halg
  exact
    { K := K
      finrank_two := Qsqrt.finrank
      totallyComplex := hKC
      disc := hD
      χ := hχ.choose
      quad := hχ.choose_spec
      prim := ringCharacter_primitive hp.2.1 h4 (by rw [hD]; exact conductor_coprime_disc hk) hχ.choose_spec
      A := newformLevel E
      B := (companionForm hN hp hk).val.1
      C := (companionForm hN hp hk).val.2
      form := (companionForm hN hp hk).property
      ι := halg.choose
      y := halg.choose_spec.choose
      hy := halg.choose_spec.choose_spec }

end Datum

section Select

variable {E : WeierstrassCurve ℚ}
  {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ} {s : ℤ} (hN : 0 < newformLevel E)

open Classical in
/-- Choose the genus datum on the entire prepared filter. -/
def selectGenus (hgp : GenusPartner E s)
    (halg : ∀ h (hp : Prepared E s h), StageSelector.PreparedParamValue E f Lat κ hN hgp hp)
    (h : ℤ) : Option (HeegnerDatum E f Lat κ (h * s) 1 s) :=
  if hp : Prepared E s h then some (StageSelector.datumOfPrepared hN hgp hp (halg h hp))
  else none

open Classical in
/-- Choose the ring-class datum for every companion of a prepared parameter. -/
def selectRing
    (halg : ∀ h k (hp : Prepared E s h) (hk : Companion E Lat s h k),
      RingParamValue E f Lat κ hN hp hk)
    (h k : ℤ) : Option (HeegnerDatum E f Lat κ k h.natAbs h) :=
  if hp : Prepared E s h then
    if hk : Companion E Lat s h k then some (datumOfCompanion hN hp hk (halg h k hp hk))
    else none
  else none

/-- Coverage for `GenusOddInstance.hselG` holds without a rank condition. -/
theorem selectGenus_isSome (hgp : GenusPartner E s)
    (halg : ∀ h (hp : Prepared E s h), StageSelector.PreparedParamValue E f Lat κ hN hgp hp)
    {h : ℤ} (hp : Prepared E s h) :
    (selectGenus hN hgp halg h).isSome := by
  simp [selectGenus, hp]

/-- Coverage for `GenusOddInstance.hselR` holds without a rank condition. -/
theorem selectRing_isSome
    (halg : ∀ h k (hp : Prepared E s h) (hk : Companion E Lat s h k),
      RingParamValue E f Lat κ hN hp hk)
    {h k : ℤ} (hp : Prepared E s h) (hk : Companion E Lat s h k) :
    (selectRing hN halg h k).isSome := by
  simp [selectRing, hp, hk]

end Select

#print axioms companion_nonsquare
#print axioms conductor_ne_zero
#print axioms conductor_coprime_disc
#print axioms datumOfCompanion
#print axioms selectGenus
#print axioms selectRing
#print axioms selectGenus_isSome
#print axioms selectRing_isSome

end ZInQ.Manuscript.RC.Gz34Instance
