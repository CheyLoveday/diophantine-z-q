import ZInQKernel.Contrib.OneProof.DeligneSerreFiniteLift.DS966SquareZero
import Mathlib.RingTheory.AdicCompletion.Algebra

/-! Iterating square-zero lifting in the adic completion. -/

set_option autoImplicit false

namespace DS966Lifting

open Ideal Matrix AdicCompletion
open scoped Matrix

/-- A coherent sequence of residue classes gives an element of the adic completion. -/
private theorem exists_eval_of_succ {R : Type*} [CommRing R] (I : Ideal R)
    (v : (m : ℕ) → R ⧸ I ^ m)
    (hv : ∀ m, Ideal.Quotient.factorPowSucc I m (v (m + 1)) = v m) :
    ∃ a : AdicCompletion I R, ∀ m, AdicCompletion.evalₐ I m a = v m := by
  classical
  choose x hx using fun m => Ideal.Quotient.mk_surjective (v m)
  have hcoh {m n : ℕ} (hmn : m ≤ n) :
      Ideal.Quotient.factorPow I hmn (v n) = v m :=
    (Ideal.Quotient.eq_factor_of_eq_factor_succ (fun _ _ hab => Ideal.pow_le_pow_right hab)
      v (fun t => (hv t).symm) hmn).symm
  let t : AdicCauchySequence I R := ⟨x, by
    intro m n hmn
    rw [SModEq.sub_mem]
    change x m - x n ∈ (I ^ m) * ⊤
    rw [Ideal.mul_top, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero,
      hx m, ← Ideal.Quotient.factor_mk (Ideal.pow_le_pow_right (I := I) hmn), hx n, hcoh hmn]⟩
  exact ⟨AdicCompletion.mk I R t, fun m => by rw [AdicCompletion.evalₐ_mk]; exact hx m⟩

/-- The projection from level `m+1` to level `m` has square-zero kernel for positive `m`. -/
private theorem factor_succ_square_zero {R : Type*} [CommRing R] (I : Ideal R)
    {m : ℕ} (hm : 1 ≤ m) (a b : R ⧸ I ^ (m + 1))
    (ha : Ideal.Quotient.factorPowSucc I m a = 0)
    (hb : Ideal.Quotient.factorPowSucc I m b = 0) : a * b = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at ha hb
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  apply Ideal.pow_le_pow_right (show m + 1 ≤ m + m by omega)
  rw [pow_add]
  exact Ideal.mul_mem_mul ha hb

/-- A finite-group representation over `R/I` lifts to the `I`-adic completion whenever the
order of the same group is invertible in `R/I`. No characteristic-zero realization is assumed. -/
theorem lift_matrix_adic {R n H : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    [Group H] [Fintype H] (I : Ideal R) (hn : IsUnit (Fintype.card H : R ⧸ I))
    (ρ : H →* GL n (R ⧸ I)) :
    ∃ L : H →* GL n (AdicCompletion I R),
      (Matrix.GeneralLinearGroup.map (AdicCompletion.evalOneₐ I).toRingHom).comp L = ρ := by
  classical
  let ι : (R ⧸ I) →+* (R ⧸ I ^ 1) := Ideal.Quotient.factor (by rw [pow_one])
  have hunit (m : ℕ) : IsUnit (Fintype.card H : R ⧸ I ^ (m + 1)) := by
    induction m with
    | zero => simpa using hn.map ι
    | succ m ih =>
        apply factorPowSucc.isUnit_of_isUnit_image (I := I) (n := m + 1) (by omega)
        simpa using ih
  have step (m : ℕ) (r : H →* GL n (R ⧸ I ^ (m + 1))) :
      ∃ r' : H →* GL n (R ⧸ I ^ (m + 1 + 1)),
        (Matrix.GeneralLinearGroup.map (Ideal.Quotient.factorPowSucc I (m + 1))).comp r' = r := by
    obtain ⟨u, hu⟩ := hunit m.succ
    apply lift_matrix_square_zero _ (Ideal.Quotient.factor_surjective _)
      (factor_succ_square_zero I (show 1 ≤ m + 1 by omega)) (↑(u⁻¹)) _ r
    rw [← hu]
    exact Units.inv_mul u
  let U : (m : ℕ) → H →* GL n (R ⧸ I ^ (m + 1)) :=
    fun m => Nat.rec (motive := fun m => H →* GL n (R ⧸ I ^ (m + 1)))
      ((Matrix.GeneralLinearGroup.map ι).comp ρ) (fun k r => (step k r).choose) m
  have hU (m : ℕ) : (Matrix.GeneralLinearGroup.map (Ideal.Quotient.factorPowSucc I (m + 1))).comp
      (U (m + 1)) = U m := (step m (U m)).choose_spec
  let V (g : H) (i j : n) : (m : ℕ) → R ⧸ I ^ m
    | 0 => 0
    | m + 1 => (U m g : Matrix n n (R ⧸ I ^ (m + 1))) i j
  have hV (g : H) (i j : n) (m : ℕ) : Ideal.Quotient.factorPowSucc I m (V g i j (m + 1)) =
      V g i j m := by
    cases m with
    | zero =>
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (V g i j 1)
      change Ideal.Quotient.factorPowSucc I 0 (V g i j 1) = 0
      rw [← hx]
      change Ideal.Quotient.mk (I ^ 0) x = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    | succ m =>
      exact congrArg (fun S : H →* GL n (R ⧸ I ^ (m + 1)) =>
        (S g : Matrix n n (R ⧸ I ^ (m + 1))) i j) (hU m)
  choose a ha using fun (g : H) (i j : n) => exists_eval_of_succ I (V g i j) (hV g i j)
  let M (g : H) : Matrix n n (AdicCompletion I R) := Matrix.of (a g)
  let ev (m : ℕ) : Matrix n n (AdicCompletion I R) →+* Matrix n n (R ⧸ I ^ m) :=
    (AdicCompletion.evalₐ I m).toRingHom.mapMatrix
  have hev (g : H) (m : ℕ) : ev (m + 1) (M g) = (U m g : Matrix n n (R ⧸ I ^ (m + 1))) :=
    Matrix.ext (fun i j => ha g i j (m + 1))
  have hdetermine {B D : Matrix n n (AdicCompletion I R)}
      (h : ∀ m, ev m B = ev m D) : B = D := by
    apply Matrix.ext
    intro i j
    exact AdicCompletion.ext_evalₐ (fun m => congrArg
      (fun T : Matrix n n (R ⧸ I ^ m) => T i j) (h m))
  have eval_zero (B D : Matrix n n (AdicCompletion I R)) : ev 0 B = ev 0 D := by
    have : Subsingleton (R ⧸ I ^ 0) := by rw [pow_zero, Ideal.one_eq_top]; infer_instance
    exact Subsingleton.elim _ _
  let φ : H →* Matrix n n (AdicCompletion I R) :=
    { toFun := M
      map_one' := hdetermine (fun m => by
        cases m with
        | zero => exact eval_zero _ _
        | succ m => rw [hev, map_one, map_one]; rfl)
      map_mul' := fun g h => hdetermine (fun m => by
        cases m with
        | zero => exact eval_zero _ _
        | succ m => rw [(ev (m + 1)).map_mul, hev, hev, hev, map_mul]; rfl) }
  refine ⟨φ.toHomUnits, MonoidHom.ext (fun g => Units.ext (Matrix.ext (fun i j => ?_)))⟩
  change AdicCompletion.evalOneₐ I (a g i j) = (ρ g : Matrix n n (R ⧸ I)) i j
  rw [← AdicCompletion.factorₐ_evalₐ_one, ha]
  change Ideal.Quotient.factor (show I ^ 1 ≤ I by simp) (ι ((ρ g : Matrix n n (R ⧸ I)) i j)) = _
  rw [show ι = Ideal.Quotient.factor (show I ≤ I ^ 1 by simp) from rfl,
    Ideal.Quotient.factor_comp_apply]
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective ((ρ g : Matrix n n (R ⧸ I)) i j)
  rw [← hx, Ideal.Quotient.factor_mk]

/-- For an adically complete ring, the lift can be taken over the ring itself. -/
theorem lift_matrix_complete {A n H : Type*} [CommRing A] [Fintype n] [DecidableEq n]
    [Group H] [Fintype H] (I : Ideal A) [IsAdicComplete I A]
    (hn : IsUnit (Fintype.card H : A ⧸ I)) (ρ : H →* GL n (A ⧸ I)) :
    ∃ L : H →* GL n A, (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp L = ρ := by
  obtain ⟨L, hL⟩ := lift_matrix_adic I hn ρ
  let e := (AdicCompletion.ofAlgEquiv I).symm.toRingEquiv
  refine ⟨(Matrix.GeneralLinearGroup.map e.toRingHom).comp L, ?_⟩
  refine MonoidHom.ext (fun g => Units.ext (Matrix.ext (fun i j => ?_)))
  exact (AdicCompletion.mk_ofAlgEquiv_symm_eq_evalOneₐ I ((L g : Matrix n n _) i j)).trans
    (congrArg (fun S : H →* GL n (A ⧸ I) => (↑(S g) : Matrix n n (A ⧸ I)) i j) hL)

/-- The complete lifting theorem, expressed using a specified surjective residue map. -/
theorem lift_matrix_residue {A k n H : Type*} [CommRing A] [CommRing k]
    [Fintype n] [DecidableEq n] [Group H] [Fintype H]
    (res : A →+* k) (hres : Function.Surjective res) [IsAdicComplete (RingHom.ker res) A]
    (hn : IsUnit (Fintype.card H : k)) (ρ : H →* GL n k) :
    ∃ L : H →* GL n A, (Matrix.GeneralLinearGroup.map res).comp L = ρ := by
  let e := res.quotientKerEquivOfSurjective hres
  let r := (Matrix.GeneralLinearGroup.map e.symm.toRingHom).comp ρ
  have h : IsUnit (Fintype.card H : A ⧸ RingHom.ker res) := by
    simpa using hn.map e.symm.toRingHom
  obtain ⟨L, hL⟩ := lift_matrix_complete (RingHom.ker res) h r
  refine ⟨L, MonoidHom.ext (fun g => Units.ext (Matrix.ext (fun i j => ?_)))⟩
  change res ((L g : Matrix n n A) i j) = (ρ g : Matrix n n k) i j
  rw [← RingHom.quotientKerEquivOfSurjective_apply_mk hres]
  have hentry := congrArg (fun S : H →* GL n (A ⧸ RingHom.ker res) =>
    (↑(S g) : Matrix n n (A ⧸ RingHom.ker res)) i j) hL
  change Ideal.Quotient.mk (RingHom.ker res) ((L g : Matrix n n A) i j) =
    e.symm ((ρ g : Matrix n n k) i j) at hentry
  rw [hentry]
  exact e.apply_symm_apply _

end DS966Lifting
