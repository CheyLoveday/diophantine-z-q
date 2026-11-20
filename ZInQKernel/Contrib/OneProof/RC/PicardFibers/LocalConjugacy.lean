import ZInQKernel.Contrib.OneProof.RC.O7Orbits.Admissible
import ZInQKernel.Contrib.OneProof.RC.PicardFibers.AdelicFactor
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Conjugacy

/-! Read equality in the actual orientation cube as equality of all local
integral conjugacy classes (tex 9136–9148, on-the-spot (c)). -/

noncomputable section

namespace ZInQ.Manuscript.RC.PicardFibers

open Eichler O7Actual O7Orbits Visibility

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m : ℤ}

/-- The full odd filter for this step, with the detecting prime supplied by
the actual stage. Here the fixed partner is `-s.weights.m`. -/
structure AdmissibleD (s : StageAt O N M hN m) (D : ℤ) : Prop where
  positive : 0 < D
  squarefree : Squarefree D
  coprime_partner : IsCoprime D (-(s.weights.m : ℤ))
  detecting : legendreSym s.ell D = 1
  odd_discriminant : Odd (disc s D)
  fundamental_discriminant : Nonvanishing.IsFundamentalDiscriminant (disc s D)
  split : ∀ p : ℕ, p.Prime → p ∣ 2 * N → Nonvanishing.SplitsIn (disc s D) p

theorem AdmissibleD.mod_eight {s : StageAt O N M hN m} {D : ℤ}
    (A : AdmissibleD s D) : disc s D % 8 = 1 :=
  (A.split 2 Nat.prime_two (dvd_mul_right 2 N)).two

theorem AdmissibleD.disc_squarefree {s : StageAt O N M hN m} {D : ℤ}
    (A : AdmissibleD s D) : Squarefree (disc s D) :=
  (A.fundamental_discriminant.squarefree_of_odd A.odd_discriminant).1

private theorem unitConj_map {A C : Type*} [Ring A] [Ring C] (f : A →+* C)
    {x y : A} (h : UnitConj x y) : UnitConj (f x) (f y) := by
  obtain ⟨u, hu⟩ := h
  refine ⟨Units.map f.toMonoidHom u, ?_⟩
  change f (u : A) * f x = f y * f (u : A)
  simpa only [map_mul] using congrArg f hu

private theorem unitConj_symm {A : Type*} [Ring A] {x y : A}
    (h : UnitConj x y) : UnitConj y x := by
  obtain ⟨u, hu⟩ := h
  refine ⟨u⁻¹, ?_⟩
  calc
    (↑u⁻¹ : A) * y = (↑u⁻¹ : A) * (y * (u : A)) * (↑u⁻¹ : A) := by
      rw [mul_assoc, Units.mul_inv_cancel_right]
    _ = x * (↑u⁻¹ : A) := by rw [← hu, Units.inv_mul_cancel_left]

private theorem unitConj_trans {A : Type*} [Ring A] {x y z : A}
    (hxy : UnitConj x y) (hyz : UnitConj y z) : UnitConj x z := by
  obtain ⟨u, hu⟩ := hxy
  obtain ⟨v, hv⟩ := hyz
  exact ⟨v * u, by rw [Units.val_mul, mul_assoc, hu, ← mul_assoc, hv, mul_assoc]⟩

private theorem unitConj_iff_map {A C : Type*} [Ring A] [Ring C] (f : A ≃+* C) (x y : A) :
    UnitConj (f x) (f y) ↔ UnitConj x y :=
  ⟨fun h => by simpa using unitConj_map f.symm.toRingHom h, unitConj_map f.toRingHom⟩

private theorem unitConj_affine (s : StageAt O N M hN m) (p : Adelic.Prime)
    (X Y : (ActualOrder s).completion p.val) :
    UnitConj (2 * X - 1) (2 * Y - 1) ↔ UnitConj X Y := by
  let A := (ActualOrder s).completion p.val
  have htwo : IsUnit (2 : Bp p.val (-1) (-(s.ell : ℚ))) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ_[p.val]) ≠ 0)).map
        (algebraMap ℚ_[p.val] (Bp p.val (-1) (-(s.ell : ℚ))))
  have hc (x y : A) (h : 2 * x = 2 * y) : x = y :=
    Subtype.ext (htwo.mul_left_cancel (congrArg Subtype.val h))
  constructor <;> rintro ⟨u, hu⟩ <;> refine ⟨u, ?_⟩
  · apply hc
    have h' : 2 * ((u : A) * X) - (u : A) = 2 * (Y * (u : A)) - (u : A) := by
      simpa only [mul_sub, sub_mul, mul_one, one_mul, two_mul, mul_add, add_mul] using hu
    exact sub_left_inj.mp h'
  · simp only [mul_sub, sub_mul, mul_one, one_mul, two_mul, mul_add, add_mul, hu]

private theorem exists_levelPrime {p : Adelic.Prime} {N : ℕ} (hN : N ≠ 0) (hp : p.val ∣ N) :
    ∃ j : Fin N.primeFactors.card, levelPrime N j = p := by
  let q : ↑N.primeFactors := ⟨p.val, Nat.mem_primeFactors.mpr ⟨p.prop, hp, hN⟩⟩
  let e := N.primeFactors.orderIsoOfFin rfl
  refine ⟨e.symm q, Subtype.ext ?_⟩
  exact congrArg (fun j : ↑N.primeFactors => j.val) (e.apply_symm_apply q)

/-- The bits of two actual support generators agree exactly when the
integral affine generators are conjugate by order units at every prime. -/
theorem actual_local_conj_iff (s : StageAt O N M hN m) {D : ℤ}
    (A : AdmissibleD s D) (H : SupportBridge s D)
    (hh : legendreSym s.ell (-(s.weights.m : ℤ)) = -1)
    (z w : ClassSet (ActualOrder s)) (x : ActualSupport s D z) (y : ActualSupport s D w) :
    generatorOrientation s H z x = generatorOrientation s H w y ↔
      ∀ p : Adelic.Prime, UnitConj (localGenerator s H z x p) (localGenerator s H w y p) := by
  let p₀ : Adelic.Prime := ⟨s.ell, Fact.out⟩
  have h8 := A.mod_eight
  have hsf := A.disc_squarefree
  have hd := hsf.ne_zero
  have hlevel (j : Fin N.primeFactors.card) :
      UnitConj (localGenerator s H z x (levelPrime N j))
        (localGenerator s H w y (levelPrime N j)) ↔
        generatorOrientation s H z x j.castSucc = generatorOrientation s H w y j.castSucc := by
    let p := levelPrime N j
    have hs := A.split p.val p.prop (dvd_mul_of_dvd_right
      (Nat.dvd_of_mem_primeFactors ((N.primeFactors.orderIsoOfFin rfl) j).prop) 2)
    exact (unitConj_iff_map (splitOrderChart s p (levelPrime_ne_detecting s j)) _ _).symm.trans
      (level_bit_of_filter s H h8 (lt_of_le_of_ne
        (show disc s D ≤ 0 from mul_nonpos_of_nonneg_of_nonpos A.positive.le
          (neg_nonpos.mpr (Int.natCast_nonneg _))) hd) j hs z w x y)
  have hlast :
      UnitConj (localGenerator s H z x p₀) (localGenerator s H w y p₀) ↔
        generatorOrientation s H z x (Fin.last _) = generatorOrientation s H w y (Fin.last _) :=
    (unitConj_affine s p₀ _ _).symm.trans
      ((unitConj_iff_map (divisionOrderChart s) _ _).symm.trans
        (division_bit_of_filter s H A.detecting hh z w x y))
  constructor
  · intro h p
    by_cases hp : p.val = s.ell
    · have he : p = p₀ := Subtype.ext hp
      subst p
      exact hlast.mpr (congrFun h _)
    by_cases hN' : p.val ∣ N
    · obtain ⟨j, rfl⟩ := exists_levelPrime hN.ne' hN'
      exact (hlevel j).mpr (congrFun h _)
    let c := (1 - disc s D) / 4
    have hc : disc s D = 1 - 4 * c := by dsimp [c]; omega
    obtain ⟨C, hC, hx⟩ := actual_maximal_split_normalForm s H hc hsf p hp hN' z x
    obtain ⟨C', hC', hy⟩ := actual_maximal_split_normalForm s H hc hsf p hp hN' w y
    have he : C = C' := Subtype.ext (hC.trans hC'.symm)
    exact (unitConj_iff_map (splitOrderChart s p hp) _ _).mp
      (unitConj_trans (unitConj_symm hx) (he ▸ hy))
  · intro h
    funext i
    exact Fin.lastCases (hlast.mp (h p₀)) (fun j => (hlevel j).mp (h (levelPrime N j))) i


/-- Replace the chosen class representative by an adelic representative on
which the fixed rational embedding gives the chosen support generator. -/
def reframe (s : StageAt O N M hN m) (z : ClassSet (ActualOrder s))
    (u : (B (-1) (-(s.ell : ℚ)))ˣ) : Adelic.FiniteUnits (ActualOrder s) :=
  Adelic.diagonal (ActualOrder s) u⁻¹ * Adelic.classRepresentative z

private theorem reframe_root (s : StageAt O N M hN m) {D : ℤ}
    (H : SupportBridge s D) (x₀ : (B (-1) (-(s.ell : ℚ)))ˣ)
    (z : ClassSet (ActualOrder s)) (x : ActualSupport s D z)
    (u : (B (-1) (-(s.ell : ℚ)))ˣ) (hu : unitConjRing u x₀.val = x.val)
    (p : Adelic.Prime) :
    (transportedUnit (Adelic.diagonal (ActualOrder s) x₀).val (reframe s z u) p).val =
      2 * (localGenerator s H z x p).val - 1 := by
  rw [localGenerator_spec, ← hu, unitConjRing_map, unitConjRing_mul]
  let v := (Adelic.classRepresentative z).val p
  let k := Units.map (toLocal p.val).toMonoidHom u
  let X := Units.map (toLocal p.val).toMonoidHom x₀
  change ((↑((k⁻¹ * v)⁻¹ * X * (k⁻¹ * v)) : Bp p.val (-1) (-(s.ell : ℚ)))) =
    unitConjRing (v⁻¹ * k) (X : Bp p.val (-1) (-(s.ell : ℚ)))
  have he : (k⁻¹ * v)⁻¹ = v⁻¹ * k := by group
  rw [he, unitConjRing_apply]
  simp only [Units.val_mul, mul_inv_rev, inv_inv]

private theorem unitConj_iff_intertwines (s : StageAt O N M hN m) (p : Adelic.Prime)
    (X Y : (ActualOrder s).completion p.val) :
    UnitConj X Y ↔ ∃ r : Adelic.localUnits (ActualOrder s) p,
      X.val * (r.val : Bp p.val (-1) (-(s.ell : ℚ))) =
        (r.val : Bp p.val (-1) (-(s.ell : ℚ))) * Y.val := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := unitConj_symm h
    let r' := Units.map ((ActualOrder s).completion p.val).val.toMonoidHom r
    exact ⟨⟨r', ⟨r.val.prop, r.inv.prop⟩⟩, (congrArg Subtype.val hr).symm⟩
  · rintro ⟨r, hr⟩
    let rr : ((ActualOrder s).completion p.val)ˣ :=
      ⟨⟨r.val.val, r.prop.1⟩, ⟨r.val.inv, r.prop.2⟩,
        Subtype.ext r.val.val_inv, Subtype.ext r.val.inv_val⟩
    exact unitConj_symm ⟨rr, Subtype.ext hr.symm⟩

/-- After rational conjugation to one fixed embedding, equality of actual
orientation tuples is exactly the factorization by a centralizing finite
adele on the left and an everywhere integral unit on the right. -/
theorem actual_orientation_factor_iff (s : StageAt O N M hN m) {D : ℤ}
    (A : AdmissibleD s D) (H : SupportBridge s D)
    (hh : legendreSym s.ell (-(s.weights.m : ℤ)) = -1)
    (x₀ : (B (-1) (-(s.ell : ℚ)))ˣ)
    (z w : ClassSet (ActualOrder s)) (x : ActualSupport s D z) (y : ActualSupport s D w)
    (u v : (B (-1) (-(s.ell : ℚ)))ˣ)
    (hu : unitConjRing u x₀.val = x.val) (hv : unitConjRing v x₀.val = y.val) :
    generatorOrientation s H z x = generatorOrientation s H w y ↔
      ∃ g : adelicCentralizer (ActualOrder s) (Adelic.diagonal (ActualOrder s) x₀).val,
        ∃ r : Adelic.integralUnits (ActualOrder s), reframe s w v = g.val * reframe s z u * r.val := by
  rw [actual_local_conj_iff s A H hh z w x y, ← adelic_factor_iff]
  apply forall_congr'
  intro p
  rw [← unitConj_affine s p, unitConj_iff_intertwines s p]
  apply exists_congr
  intro r
  rw [Units.ext_iff, Units.val_mul, Units.val_mul, reframe_root s H x₀ z x u hu,
    reframe_root s H x₀ w y v hv]
  rfl

end ZInQ.Manuscript.RC.PicardFibers
