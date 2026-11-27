import ZInQKernel.Contrib.OneProof.RC.O7Orbits.Local
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Family

/-! The local residue tests on the actual support of the visibility stage. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O7Orbits

open Eichler Visibility O7Actual

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m : ℤ}

abbrev ActualOrder (s : StageAt O N M hN m) :=
  Adelic.levelOrder s.ell s.mod_four N hN

abbrev index (s : StageAt O N M hN m) (D : ℤ) : ℚ :=
  (((s.weights.m : ℤ) * D : ℤ) : ℚ)

abbrev disc (s : StageAt O N M hN m) (D : ℤ) : ℤ :=
  D * -(s.weights.m : ℤ)

abbrev ActualSupport (s : StageAt O N M hN m) (D : ℤ) (z : ClassSet (ActualOrder s)) :=
  s.visibility.supp z (index s D)

/-- Exactly the support bridge on the trace-zero norm sphere. -/
def SupportBridge (s : StageAt O N M hN m) (D : ℤ) : Prop :=
  ∀ (z : ClassSet (ActualOrder s)) (x : B (-1) (-(s.ell : ℚ))),
    x.re = 0 → nrd x = index s D →
      (s.visibility.f z x ≠ 0 ↔ HalfIntegral (classOrder s.weights.ha s.weights.hb z) x)

theorem SupportBridge.half {s : StageAt O N M hN m} {D : ℤ}
    (H : SupportBridge s D) (z : ClassSet (ActualOrder s)) (x : ActualSupport s D z) :
    HalfIntegral (classOrder s.weights.ha s.weights.hb z) x :=
  (H z x x.prop.1 x.prop.2.1).mp x.prop.2.2

/-- Supply the integral support data of the chosen quadratic field. -/
def integralSupport (s : StageAt O N M hN m) {D : ℤ} (H : SupportBridge s D)
    (F : Type) [Field F] [NumberField F] (Q : QuadraticBasis F (disc s D))
    (hd : disc s D < 0) (h8 : disc s D % 8 = 1) : IntegralSupport s D where
  Fq := F
  basis := Q
  disc_neg := hd
  disc_mod_eight := h8
  half := H.half

/-- The exact bridge gives both directions of the optimal-embedding test on
the actual norm sphere. -/
theorem actualSupport_iff_optimal (s : StageAt O N M hN m) {D : ℤ}
    (H : SupportBridge s D) (F : Type) [Field F] [NumberField F] (Q : QuadraticBasis F (disc s D))
    (z : ClassSet (ActualOrder s)) {x : B (-1) (-(s.ell : ℚ))}
    (hx : x.re = 0) (hn : nrd x = index s D) :
    x ∈ s.visibility.supp z (index s D) ↔
      OptimalAt (classOrder s.weights.ha s.weights.hb z) Q x :=
  supp_iff_optimal_on_sphere s.visibility z Q rfl hx hn (H z x hx hn)

/-- Tex 9140–9146: the actual completion at a split place in integral
matrix coordinates, using the chart in the construction of the level order. -/
def splitOrderChart (s : StageAt O N M hN m) (p : Adelic.Prime) (hp : p.val ≠ s.ell) :
    (ActualOrder s).completion p.val ≃+* LocalWeights.eichler p.val (N.factorization p.val) := by
  let f := Adelic.splitChart s.ell s.mod_four p hp
  let E := LocalWeights.eichler p.val (N.factorization p.val)
  let g : E →+* Bp p.val (-1) (-(s.ell : ℚ)) :=
    f.symm.toRingHom.comp ((matrixCast p.val).comp E.val.toRingHom)
  have hm (x : E) : g x ∈ (ActualOrder s).completion p.val := by
    rw [Adelic.levelOrder_completion, Adelic.levelLocal_mem_split _ _ _ _ hp]
    exact ⟨x.val, x.prop, (f.apply_symm_apply (matrixCast p.val x.val)).symm⟩
  let G := g.codRestrict ((ActualOrder s).completion p.val).toSubring hm
  refine (RingEquiv.ofBijective G ⟨?_, ?_⟩).symm
  · intro x y h
    have hi : Function.Injective (matrixCast p.val) :=
      Matrix.map_injective (show Function.Injective (algebraMap ℤ_[p.val] ℚ_[p.val]) from
        Subtype.val_injective)
    exact Subtype.ext (hi (f.symm.injective (congrArg Subtype.val h)))
  · intro y
    have hmiff (x : Bp p.val (-1) (-(s.ell : ℚ))) :
        x ∈ (ActualOrder s).completion p.val ↔ f x ∈
          Adelic.standardOrder p (N.factorization p.val) := by
      rw [Adelic.levelOrder_completion, Adelic.levelLocal_mem_split _ _ _ _ hp]
    have hy := (hmiff y.val).mp y.prop
    obtain ⟨x, hx, he⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext (f.symm_apply_eq.mpr he)⟩

/-- Tex 9146–9148: the actual completion at the detecting prime in the
integral division model. -/
def divisionOrderChart (s : StageAt O N M hN m) :
    (ActualOrder s).completion s.ell ≃+* LocalDivision.order s.ell := by
  let p : Adelic.Prime := ⟨s.ell, Fact.out⟩
  have h : (ActualOrder s).completion s.ell = DivisionJoin.completedOrder s.ell s.mod_four := by
    change (ActualOrder s).completion p.val = _
    rw [Adelic.levelOrder_completion, Adelic.levelLocal, dite_eq_right (not_not.mpr rfl)]
  exact (Subalgebra.equivOfEq _ _ h).toRingEquiv.trans
    (DivisionJoin.orderEquiv s.ell s.mod_four).toRingEquiv

/-- Conjugation by a unit, as a ring homomorphism. -/
def unitConjRing {A : Type*} [Ring A] (u : Aˣ) : A →+* A where
  toFun x := (u : A) * x * ↑u⁻¹
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by simp [mul_add, add_mul]
  map_mul' x y := by
    simp only [mul_assoc, Units.inv_mul_cancel_left]

theorem unitConjRing_apply {A : Type*} [Ring A] (u : Aˣ) (x : A) :
    unitConjRing u x = (u : A) * x * ↑u⁻¹ := rfl

theorem unitConjRing_map {A C : Type*} [Ring A] [Ring C] (f : A →+* C) (u : Aˣ) (x : A) :
    f (unitConjRing u x) = unitConjRing (Units.map f.toMonoidHom u) (f x) := by
  rw [unitConjRing_apply, unitConjRing_apply]
  change f ((u : A) * x * ↑u⁻¹) = f (u : A) * f x * f (↑u⁻¹ : A)
  rw [map_mul, map_mul]

theorem unitConjRing_mul {A : Type*} [Ring A] (v u : Aˣ) (x : A) :
    unitConjRing v (unitConjRing u x) = unitConjRing (v * u) x := by
  simp only [unitConjRing_apply, mul_inv_rev, Units.val_mul, mul_assoc]

/-- The local image of the integral affine generator, on the actual
chosen adelic representative of the ideal class. -/
def localGenerator (s : StageAt O N M hN m) {D : ℤ} (H : SupportBridge s D)
    (z : ClassSet (ActualOrder s)) (x : ActualSupport s D z) (p : Adelic.Prime) :
    (ActualOrder s).completion p.val :=
  let t := (H.half z x).choose
  let v := (Adelic.classRepresentative z).val p
  ⟨unitConjRing v⁻¹ (toLocal p.val t.val),
    (classOrder_mem_adelic s.weights.ha s.weights.hb z t.val).mp t.prop p⟩

theorem localGenerator_spec (s : StageAt O N M hN m) {D : ℤ} (H : SupportBridge s D)
    (z : ClassSet (ActualOrder s)) (x : ActualSupport s D z) (p : Adelic.Prime) :
    2 * (localGenerator s H z x p).val - 1 =
      unitConjRing ((Adelic.classRepresentative z).val p)⁻¹ (toLocal p.val x.val) := by
  let t := (H.half z x).choose
  let f := (unitConjRing ((Adelic.classRepresentative z).val p)⁻¹).comp (toLocal p.val)
  change 2 * f t.val - 1 = f x.val
  rw [← (H.half z x).choose_spec, map_sub, map_mul, map_ofNat, map_one]

/-- A rational unit of the left order becomes an integral local unit after
conjugation by the chosen representative. -/
theorem localClassUnit_mem (s : StageAt O N M hN m) (z : ClassSet (ActualOrder s))
    (p : Adelic.Prime) (u : classG s.weights.ha s.weights.hb z) :
    let v := (Adelic.classRepresentative z).val p
    let k := Units.map (toLocal p.val).toMonoidHom (u : (B (-1) (-(s.ell : ℚ)))ˣ)
    v⁻¹ * k * v ∈ Adelic.localUnits (ActualOrder s) p := by
  let v := (Adelic.classRepresentative z).val p
  let k := Units.map (toLocal p.val).toMonoidHom (u : (B (-1) (-(s.ell : ℚ)))ˣ)
  have h (w : classG s.weights.ha s.weights.hb z) :
      (↑(w.val) : B (-1) (-(s.ell : ℚ))) ∈ (classOrder s.weights.ha s.weights.hb z).ring := by
    obtain ⟨t, ht⟩ := w.prop
    rw [← ht]
    exact t.val.prop
  refine ⟨?_, ?_⟩
  · exact (classOrder_mem_adelic s.weights.ha s.weights.hb z _).mp (h u) p
  · change (↑((v⁻¹ * k * v)⁻¹) : Bp p.val (-1) (-(s.ell : ℚ))) ∈ _
    rw [show (v⁻¹ * k * v)⁻¹ = v⁻¹ * k⁻¹ * v by group]
    exact (classOrder_mem_adelic s.weights.ha s.weights.hb z _).mp (h u⁻¹) p

/-- Conjugation on the indexed actual support. -/
abbrev conjugateSupport {s : StageAt O N M hN m} {D : ℤ}
    {z : ClassSet (ActualOrder s)} (u : s.visibility.G z) (x : ActualSupport s D z) :
    ActualSupport s D z :=
  @SMul.smul _ _ (ThetaStage.conjAction s.visibility z (index s D)).toSMul u x

set_option maxHeartbeats 500000 in
/-- Passing to an orbit in the actual visibility stage changes the
local affine generator by an integral order unit. -/
theorem localGenerator_conj (s : StageAt O N M hN m) {D : ℤ} (H : SupportBridge s D)
    (z : ClassSet (ActualOrder s)) (p : Adelic.Prime) (x : ActualSupport s D z)
    (u : s.visibility.G z) :
    UnitConj (localGenerator s H z x p) (localGenerator s H z (conjugateSupport u x) p) := by
  let v := (Adelic.classRepresentative z).val p
  let k := Units.map (toLocal p.val).toMonoidHom
    (u.val : (B (-1) (-(s.ell : ℚ)))ˣ)
  let w := v⁻¹ * k * v
  obtain ⟨w', hw'⟩ := by
    have hm : w ∈ Adelic.localUnits (ActualOrder s) p := localClassUnit_mem s z p u
    rw [Adelic.localUnits_eq_range] at hm
    exact hm
  let X := localGenerator s H z x p
  let Y := localGenerator s H z (conjugateSupport u x) p
  have h : unitConjRing w (2 * X.val - 1) = 2 * Y.val - 1 := by
    rw [localGenerator_spec s H z x p, localGenerator_spec s H z (conjugateSupport u x) p]
    change unitConjRing w (unitConjRing v⁻¹ (toLocal p.val x.val)) =
      unitConjRing v⁻¹ (toLocal p.val (unitConjRing u.val x.val))
    rw [unitConjRing_map (toLocal p.val), unitConjRing_mul, unitConjRing_mul]
    change unitConjRing (w * v⁻¹) _ = unitConjRing (v⁻¹ * k) _
    rw [show w * v⁻¹ = v⁻¹ * k by dsimp only [w]; group]
  have htwo : IsUnit (2 : Bp p.val (-1) (-(s.ell : ℚ))) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ_[p.val]) ≠ 0)).map
        (algebraMap ℚ_[p.val] (Bp p.val (-1) (-(s.ell : ℚ))))
  have hxy : unitConjRing w X.val = Y.val := by
    rw [map_sub, map_mul, map_ofNat, map_one] at h
    exact htwo.mul_left_cancel (sub_left_inj.mp h)
  refine ⟨w', Subtype.ext ?_⟩
  change ((Units.map ((ActualOrder s).completion p.val).val.toMonoidHom w' :
    (Bp p.val (-1) (-(s.ell : ℚ)))ˣ) : Bp p.val (-1) (-(s.ell : ℚ))) * X.val =
    Y.val * ↑(Units.map ((ActualOrder s).completion p.val).val.toMonoidHom w')
  rw [hw', ← hxy]
  change (w : Bp p.val (-1) (-(s.ell : ℚ))) * X.val =
    ((w : Bp p.val (-1) (-(s.ell : ℚ))) * X.val * ↑w⁻¹) * ↑w
  rw [Units.inv_mul_cancel_right]

/-- Any commutative residue homomorphism is constant under integral unit
conjugation. -/
theorem residue_eq_of_unitConj {A C : Type*} [Ring A] [CommRing C] (f : A →+* C)
    {x y : A} (h : UnitConj x y) : f x = f y := by
  obtain ⟨u, hu⟩ := h
  apply (u.isUnit.map f).mul_left_cancel
  simpa only [map_mul, mul_comm (f y)] using congrArg f hu

/-- Label the two possible residues by choosing the smaller of the two
in a finite enumeration. The local classification is independent of the
choice of enumeration. -/
def residueBit {C : Type*} [Finite C] (x y : C) : Bool :=
  letI := Fintype.ofFinite C
  decide (Fintype.equivFin C x < Fintype.equivFin C y)

/-- The primes in the level, indexed in the order of the finite set. -/
def levelPrime (N : ℕ) (i : Fin N.primeFactors.card) : Adelic.Prime :=
  let j := (N.primeFactors.orderIsoOfFin rfl) i
  ⟨j.val, Nat.prime_of_mem_primeFactors j.prop⟩

theorem levelPrime_ne_detecting (s : StageAt O N M hN m) (i : Fin N.primeFactors.card) :
    (levelPrime N i).val ≠ s.ell := by
  intro h
  have hp : (levelPrime N i).val ∣ N :=
    Nat.dvd_of_mem_primeFactors ((N.primeFactors.orderIsoOfFin rfl) i).prop
  rw [h] at hp
  exact (Fact.out : s.ell.Prime).not_dvd_one
    (s.G.eichler.prime_to_level.gcd_eq_one ▸ Nat.dvd_gcd hp (dvd_refl _))

/-- On each positive level quotient compare the selected affine root with
its complement. At the detecting prime compare the reduced root of the
discriminant with its negative. -/
def generatorOrientation (s : StageAt O N M hN m) {D : ℤ} (H : SupportBridge s D)
    (z : ClassSet (ActualOrder s)) (x : ActualSupport s D z) :
    Orientations N.primeFactors.card :=
  Fin.lastCases
    (let p : Adelic.Prime := ⟨s.ell, Fact.out⟩
     letI : Fact (s.ell % 4 = 3) := ⟨s.mod_four⟩
     let r := LocalDivision.red
       (divisionOrderChart s (2 * localGenerator s H z x p - 1))
     residueBit r (-r))
    (fun i =>
      let p := levelPrime N i
      let r := LocalWeights.level p.val (N.factorization p.val)
        (splitOrderChart s p (levelPrime_ne_detecting s i) (localGenerator s H z x p))
      residueBit r (1 - r))

/-- Tex 9136–9148: the product of the actual local labels descends to
the weighted support orbit set. -/
def orientation (s : StageAt O N M hN m) {D : ℤ} (H : SupportBridge s D) :
    OrbitSet s.visibility (index s D) → Orientations N.primeFactors.card :=
  fun P => Quotient.lift (generatorOrientation s H P.1) (by
    intro x y hy
    obtain ⟨u, hu⟩ := hy
    subst x
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · let p : Adelic.Prime := ⟨s.ell, Fact.out⟩
      let _ : Fact (s.ell % 4 = 3) := ⟨s.mod_four⟩
      let f := (LocalDivision.red (p := s.ell)).comp (divisionOrderChart s).toRingHom
      let X := localGenerator s H P.1 (conjugateSupport u y) p
      let Y := localGenerator s H P.1 y p
      have h : f Y = f X := residue_eq_of_unitConj f (localGenerator_conj s H P.1 p y u)
      have hr : f (2 * Y - 1) = f (2 * X - 1) := by
        simpa only [map_sub, map_mul, map_ofNat, map_one] using congrArg (2 * · - 1) h
      simp only [generatorOrientation, Fin.lastCases_last]
      change residueBit (f (2 * X - 1)) (-f (2 * X - 1)) =
        residueBit (f (2 * Y - 1)) (-f (2 * Y - 1))
      rw [hr]
    · let p := levelPrime N j
      let f := (LocalWeights.level p.val (N.factorization p.val)).comp
        (splitOrderChart s p (levelPrime_ne_detecting s j)).toRingHom
      let X := localGenerator s H P.1 (conjugateSupport u y) p
      let Y := localGenerator s H P.1 y p
      have h : f Y = f X := residue_eq_of_unitConj f (localGenerator_conj s H P.1 p y u)
      simp only [generatorOrientation, Fin.lastCases_castSucc]
      change residueBit (f X) (1 - f X) = residueBit (f Y) (1 - f Y)
      rw [h]) P.2

/-- The scoped global obligation, tex 9149–9170. Each actual local
orientation fiber must be identified with the class group of the supplied
maximal quadratic order. This states only the fiber equivalences. -/
abbrev PicardFibers (s : StageAt O N M hN m) {D : ℤ} (H : SupportBridge s D)
    (Cl : Type) :=
  ∀ t : Orientations N.primeFactors.card,
    Cl ≃ {P : OrbitSet s.visibility (index s D) // orientation s H P = t}

/-- The host's orbit input from the actual orientation and the remaining
global Picard fiber equivalences. -/
def orbitFibers (s : StageAt O N M hN m) {D : ℤ} (H : SupportBridge s D)
    (F : Type) [Field F] [NumberField F] (Q : QuadraticBasis F (disc s D))
    (hd : disc s D < 0) (h8 : disc s D % 8 = 1)
    (J : PicardFibers s H (integralSupport s H F Q hd h8).classGroup) :
    OrbitFibers s.visibility (index s D) N.primeFactors.card
      (integralSupport s H F Q hd h8).classGroup :=
  ⟨orientation s H, J⟩

end ZInQ.Manuscript.RC.O7Orbits
