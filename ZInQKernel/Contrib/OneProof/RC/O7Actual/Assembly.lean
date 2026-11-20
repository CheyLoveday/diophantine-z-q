import ZInQKernel.Contrib.OneProof.RC.O7Actual.Embeddings
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Orbits
import ZInQKernel.Contrib.OneProof.RC.O12StageVal.PM

/-! Build the comparison on the class set, supports and point lifts of the
supplied `PMLocal`. The unresolved geometric and arithmetic data are at the
level of individual embeddings and points. -/

noncomputable section

open scoped Quaternion NumberField

namespace ZInQ.Manuscript.RC.O7Actual

open Eichler Visibility Visibility.ThetaStage O12StageVal

section Inputs

variable {O : Type} [CommRing O] {a b : ℚ} {R : Order a b} {ell N M : ℕ}
  [Fact ell.Prime] {K : Type*} [Field K] [Algebra (ZMod ell) K] [DecidableEq K] [IsSepClosed K]
  {Ebar : WeierstrassCurve (ZMod ell)} [Ebar.IsElliptic] {ap : ℕ → ℤ}

/-- The visibility model uses precisely the same ideal classes and integer
lift of `P_M` as the actual theta stage (tex 8476–8493). -/
abbrev actualVisibility (G : PM.Geometry K R N Ebar ap) (d : PM.Evaluation K Ebar M)
    (L : ℕ) (F : PMLocal O R M N ell) (u : ClassSet R → ℤ) (hu : PM.IsLift G d L u) :
    ThetaStage O a b := (pmLift G d L F u hu).geom

/-- The stabilizer uses the defining conjugation action of the stage. -/
abbrev stageStabilizer (S : ThetaStage O a b) (z : S.X) {n : ℚ} (x : S.supp z n) :
    Subgroup (S.G z) :=
  @MulAction.stabilizer (S.G z) (S.supp z n) _ (ThetaStage.conjAction S z n) x

/-- Tex 9308–9311: optimality identifies the stabilizer calculation
inside the actual class order; the two signs are both in this order. -/
theorem actual_stabilizer (G : PM.Geometry K R N Ebar ap) (d : PM.Evaluation K Ebar M)
    (L : ℕ) (F : PMLocal O R M N ell) (u : ClassSet R → ℤ) (hu : PM.IsLift G d L u)
    {Fq : Type*} [Field Fq] [NumberField Fq] {D disc k : ℤ}
    (Q : QuadraticBasis Fq disc) (hdisc : disc = -(F.m : ℤ) * D)
    (hk : disc = 4 * k + 1) (hd : disc < 0) (h8 : disc % 8 = 1)
    (z : ClassSet R) (x : (actualVisibility G d L F u hu).supp z (((F.m : ℤ) * D : ℤ) : ℚ))
    (hopt : OptimalAt (classOrder F.ha F.hb z) Q x) :
    Nat.card (stageStabilizer (actualVisibility G d L F u hu) z x) = 2 := by
  let S := actualVisibility G d L F u hu
  let z' : S.X := z
  let n : ℚ := (((F.m : ℤ) * D : ℤ) : ℚ)
  let x' : S.supp z' n := x
  let : MulAction (S.G z') (S.supp z' n) := ThetaStage.conjAction S z' n
  let H := stageStabilizer S z' x'
  let neg : S.G z' := ⟨-1, ⟨-1, by apply Units.ext; simp [Order.unitsHom, z']⟩⟩
  let v : H := ⟨neg, by
    change neg • x' = x'
    apply Subtype.ext
    change ((neg : (B a b)ˣ) : B a b) * (x' : B a b) *
      (↑((neg : (B a b)ˣ)⁻¹) : B a b) = (x' : B a b)
    simp [neg]⟩
  let e : Bool → H := fun j => if j then 1 else v
  have hne : (1 : H) ≠ v := by
    intro he
    have he' := congrArg (fun q : H => (((q.val : S.G z') : (B a b)ˣ) : B a b)) he
    change (1 : B a b) = -1 at he'
    have h := congrArg (fun q : B a b => q.re) he'
    norm_num at h
  have he₁ : Function.Injective e := by
    intro j j'
    cases j <;> cases j' <;> simp [e, hne, Ne.symm hne]
  have he₂ : Function.Surjective e := by
    intro w
    let w' : (B a b)ˣ := w.val
    have hw : (w.val : S.G z') • x' = x' := w.prop
    have hact := congrArg (fun y : S.supp z' n => (y : B a b)) hw
    change (w' : B a b) * (x : B a b) * (↑w'⁻¹ : B a b) = (x : B a b) at hact
    have hcomm : Commute (w' : B a b) (x : B a b) := by
      change (w' : B a b) * (x : B a b) = (x : B a b) * (w' : B a b)
      have h := congrArg (· * (w' : B a b)) hact
      simpa only [mul_assoc, Units.inv_mul, mul_one] using h
    have hnorm : nrd (x : B a b) = -(disc : ℚ) := by
      rw [hdisc]
      push_cast
      simpa only [neg_mul, neg_neg, Int.cast_mul, Int.cast_natCast] using x.prop.2.1
    rcases optimal_commuting_unit_sign (classOrder F.ha F.hb z) F.ha F.hb Q hk hd h8
        x.prop.1 hnorm hopt w' w.val.prop hcomm with h | h
    · refine ⟨true, ?_⟩
      change (1 : H) = w
      exact Subtype.ext (Subtype.ext (Units.ext h.symm))
    · refine ⟨false, ?_⟩
      change v = w
      exact Subtype.ext (Subtype.ext (Units.ext h.symm))
  change Nat.card H = _
  rw [← Nat.card_congr (Equiv.ofBijective e ⟨he₁, he₂⟩)]
  simp [Nat.card_eq_fintype_card]

/-- Data attached to the actual orbits at one discriminant. The two
transport equations record the separate norm and Schwartz factors before
they are multiplied. -/
structure TorusWeights (S : ThetaStage O a b) {n : ℚ} {ω : ℕ} {Cl : Type}
    (A : OrbitFibers S n ω Cl) where
  normBase : Orientations ω → O
  schwartzBase : Orientations ω → O
  character : Cl → O
  transport : Orientations ω → Cl → Oˣ
  norm_transport : ∀ t c,
    S.χN (zc A.param (t, c)) = normBase t * character c * (transport t c : O)
  schwartz_transport : ∀ t c,
    S.f (zc A.param (t, c)) (rep A.param (t, c)) =
      schwartzBase t * (↑(transport t c)⁻¹ : O)
  norm_order : ∀ t, ∃ j : ℕ, normBase t ^ (2 ^ j : ℕ) = 1
  schwartz_order : ∀ t, ∃ j : ℕ, schwartzBase t ^ (2 ^ j : ℕ) = 1

variable {G : PM.Geometry K R N Ebar ap} {d : PM.Evaluation K Ebar M} {L : ℕ}
  {F : PMLocal O R M N ell} {u : ClassSet R → ℤ} {hu : PM.IsLift G d L u}
  {n : ℚ} {ω : ℕ} {Cl : Type} {S : ThetaStage O a b} {A : OrbitFibers S n ω Cl}

/-- The phase is the product of the two base weights (tex 9321–9327). -/
def TorusWeights.phase (W : TorusWeights S A) (t : Orientations ω) : O :=
  W.normBase t * W.schwartzBase t

theorem TorusWeights.weight (W : TorusWeights S A) (t : Orientations ω) (c : Cl) :
    S.χN (zc A.param (t, c)) * S.f (zc A.param (t, c)) (rep A.param (t, c)) =
      W.phase t * W.character c :=
  torsor_weight _ _ _ _ _ _ (W.norm_transport t c) (W.schwartz_transport t c)

theorem TorusWeights.phase_unit (W : TorusWeights S A) (t : Orientations ω) : IsUnit (W.phase t) :=
  unit_of_twoPower (twoPower_mul (W.norm_order t) (W.schwartz_order t))

/-- Weight of an embedding orbit, before multiplying by its point value. -/
def orbitWeight (S : ThetaStage O a b) {Cl : Type} {n : ℚ} {ω : ℕ}
    (A : OrbitFibers S n ω Cl) (t : Orientations ω) (c : Cl) : O :=
  S.χN (zc A.param (t, c)) * S.f (zc A.param (t, c)) (rep A.param (t, c))

/-- Pointwise normalizer data for the actual stage. The weight identities
are on the product of the two local factors, so integral changes of
adelic representative cancel. They contain no Kummer value or congruence. -/
structure Normalizers (G : PM.Geometry K R N Ebar ap) (d : PM.Evaluation K Ebar M)
    (L : ℕ) (F : PMLocal O R M N ell) (u : ClassSet R → ℤ) (hu : PM.IsLift G d L u)
    {n : ℚ} {ω : ℕ} {Cl : Type} (A : OrbitFibers (actualVisibility G d L F u hu) n ω Cl) where
  perm : Fin (ω + 1) → Orientations ω → Cl ≃ Cl
  p : Fin ω → ℕ
  prime : ∀ i, (p i).Prime
  exponent : ∀ i, 0 < N.factorization (p i)
  cusp : ∀ i, L • G.cusp (p i) = 0
  atkin_class : ∀ i : Fin ω, ∀ t c,
    zc A.param (flip i.castSucc t, perm i.castSucc t c) =
      G.atkin (p i) (prime i) (exponent i) (zc A.param (t, c))
  atkin_weight : ∀ i : Fin ω, ∀ t c,
    orbitWeight _ A (flip i.castSucc t) (perm i.castSucc t c) =
      (G.atkinSign (p i) : O) * orbitWeight _ A t c
  uniformizer_class : ∀ t c,
    zc A.param (flip (Fin.last ω) t, perm (Fin.last ω) t c) =
      G.uniformizer (zc A.param (t, c))
  uniformizer_weight : ∀ t c,
    orbitWeight _ A (flip (Fin.last ω) t) (perm (Fin.last ω) t c) = orbitWeight _ A t c

variable {A₀ : OrbitFibers (actualVisibility G d L F u hu) n ω Cl}

/-- Tex 9329–9367: sum the pointwise identities, at the original precision. -/
theorem Normalizers.orientation [Fintype Cl] (J : Normalizers G d L F u hu A₀)
    (W : TorusWeights _ A₀) (t₀ t : Orientations ω) :
    (2 : O) ^ M ∣
      W.phase t * (∑ c, W.character c * (u (zc A₀.param (t, c)) : O)) -
      W.phase t₀ * (∑ c, W.character c * (u (zc A₀.param (t₀, c)) : O)) := by
  let v : Orientations ω → Cl → O :=
    fun s c => orbitWeight _ A₀ s c * (u (zc A₀.param (s, c)) : O)
  have hed (i : Fin (ω + 1)) (s : Orientations ω) (c : Cl) :
      (2 : O) ^ M ∣ v (flip i s) (J.perm i s c) - v s c := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · dsimp [v]
      rw [J.uniformizer_weight, J.uniformizer_class]
      rw [← mul_sub]
      apply Dvd.dvd.mul_left
      simpa only [map_sub, map_pow, map_ofNat, eq_intCast] using
        map_dvd (Int.castRingHom O) (PM.lift_uniformizer_dvd G d L hu (zc A₀.param (s, c)))
    · dsimp [v]
      rw [J.atkin_class j]
      have hs : (G.atkinSign (J.p j) : O) * (G.atkinSign (J.p j) : O) = 1 := by
        rcases G.atkinSign_eq (J.p j) (J.prime j) (J.exponent j) with h | h <;> simp [h]
      apply cancel_edge_sign hs (J.atkin_weight j s c)
      simpa only [map_sub, map_pow, map_ofNat, map_mul, eq_intCast] using
        map_dvd (Int.castRingHom O)
          (PM.lift_atkin_dvd G d L hu (J.p j) (J.prime j) (J.exponent j) (J.cusp j)
            (zc A₀.param (s, c)))
  have hsum (s : Orientations ω) :
      (∑ c, v s c) = W.phase s * ∑ c, W.character c * (u (zc A₀.param (s, c)) : O) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    change orbitWeight _ A₀ s c * _ = _
    unfold orbitWeight
    rw [W.weight]
    ring
  simpa only [hsum] using orientation_sum ((2 : O) ^ M) v J.perm hed t₀ t

end Inputs

section Comparison

variable {O : Type} [CommRing O] {a b : ℚ} {R : Order a b} {ell N M : ℕ}
  [Fact ell.Prime] {K : Type*} [Field K] [Algebra (ZMod ell) K] [DecidableEq K] [IsSepClosed K]
  {Ebar : WeierstrassCurve (ZMod ell)} [Ebar.IsElliptic] {ap : ℕ → ℤ}
  {G : PM.Geometry K R N Ebar ap} {d : PM.Evaluation K Ebar M} {L : ℕ}
  (F : PMLocal O R M N ell) {u : ClassSet R → ℤ} (hu : PM.IsLift G d L u)
  {D lam : ℤ} {ω : ℕ} {Cl : Type} [Fintype Cl]
  (A : OrbitFibers (actualVisibility G d L F u hu) (((F.m : ℤ) * D : ℤ) : ℚ) ω Cl)
  (W : TorusWeights _ A) (J : Normalizers G d L F u hu A) (t₀ : Orientations ω)

-- The integer representative is produced after the raw (O.7) congruence.
-- This equality alone is a choice of coefficient representative.
variable (red : (2 : O) ^ M ∣ ∑ c, W.character c * (u (zc A.param (t₀, c)) : O) - (lam : O))
  (stab : ∀ z (x : (actualVisibility G d L F u hu).supp z (((F.m : ℤ) * D : ℤ) : ℚ)),
    Nat.card (stageStabilizer (actualVisibility G d L F u hu) z x) = 2)
  (contract : ∀ z : ℤ, (2 : O) ^ M ∣ (z : O) → (2 : ℤ) ^ M ∣ z)

/-- Use any independently specified integer representative of the phase
removed coefficient. The representative equality refers only to the actual
coefficient and the phase, and is independent of the reduction side. -/
def comparisonInputs (aθ : ℤ)
    (haθ : (2 : O) ^ M ∣ W.phase t₀ * (aθ : O) -
      thetaCoeff (actualVisibility G d L F u hu) (((F.m : ℤ) * D : ℤ) : ℚ)) :
    ComparisonInputs (actualVisibility G d L F u hu) M F.m D ω lam aθ where
  Tup := Orientations ω
  Cl := Cl
  card_Tup := card_orientations ω
  param := A.param
  ζ₀ := W.phase
  χF := W.character
  weight := W.weight
  t₀ := t₀
  reduction := red
  orientation := J.orientation W t₀
  stab := stab
  phase_unit := W.phase_unit t₀
  representative := haθ
  ring_two := contract

include J red stab in
/-- Once the separate local and reference inputs are provided, the raw
coefficient congruence supplies the representative itself. -/
theorem actual_representative :
    (2 : O) ^ M ∣ W.phase t₀ * (((Odd.c0 : ℤ) * 2 ^ ω * lam : ℤ) : O) -
      thetaCoeff (actualVisibility G d L F u hu) (((F.m : ℤ) * D : ℤ) : ℚ) := by
  have h := O7_of_inputs (actualVisibility G d L F u hu) M F.m D ω
    (card_orientations ω) A.param W.phase W.character W.weight t₀ lam red
      (J.orientation W t₀) stab
  convert dvd_neg.mpr h using 1
  push_cast
  ring

end Comparison

end ZInQ.Manuscript.RC.O7Actual
