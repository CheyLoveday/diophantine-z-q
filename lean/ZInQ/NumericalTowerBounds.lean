module

public import Mathlib.Data.Nat.Hyperoperation
public import Mathlib.Order.Monotone.Basic

/-!
Elementary numerical bounds for the specified polynomial's size estimates.
All large-power arguments are proved for symbolic natural parameters before
specialization. No bound on the actual candidate's size parameter is asserted.
-/

public section

namespace ZInQ.NumericalTowerBounds

/-- Three powers of two, associated to the right. -/
@[expose] def triplePower (a : Nat) : Nat :=
  2 ^ (2 ^ (2 ^ a))

/-- Four powers of two, associated to the right. -/
@[expose] def quadruplePower (a : Nat) : Nat :=
  2 ^ (2 ^ (2 ^ (2 ^ a)))

theorem triplePower_strictMono : StrictMono triplePower := by
  intro a b h
  exact Nat.pow_lt_pow_right (by decide)
    (Nat.pow_lt_pow_right (by decide) (Nat.pow_lt_pow_right (by decide) h))

theorem quadruplePower_strictMono : StrictMono quadruplePower := by
  intro a b h
  exact Nat.pow_lt_pow_right (by decide)
    (Nat.pow_lt_pow_right (by decide)
      (Nat.pow_lt_pow_right (by decide) (Nat.pow_lt_pow_right (by decide) h)))

/-- The tower of zero twos is one. -/
theorem tower_zero : hyperoperation 4 2 0 = 1 :=
  hyperoperation_ge_three_eq_one 1 2

/-- One more level exponentiates two by the preceding tower. -/
theorem tower_succ (n : Nat) :
    hyperoperation 4 2 (n + 1) = 2 ^ hyperoperation 4 2 n := by
  rw [hyperoperation_recursion, hyperoperation_three]

/-- This is the only nontrivial closed tower evaluated in the proof. -/
theorem tower_four : hyperoperation 4 2 4 = 65536 := by
  calc
    hyperoperation 4 2 4 = 2 ^ (2 ^ (2 ^ (2 ^ (1 : Nat)))) := by
      rw [tower_succ 3, tower_succ 2, tower_succ 1, tower_succ 0, tower_zero]
    _ = 65536 := by decide

theorem tower_add_three (n : Nat) :
    hyperoperation 4 2 (n + 3) = triplePower (hyperoperation 4 2 n) := by
  calc
    hyperoperation 4 2 (n + 3) = 2 ^ hyperoperation 4 2 (n + 2) :=
      tower_succ (n + 2)
    _ = 2 ^ (2 ^ hyperoperation 4 2 (n + 1)) :=
      congrArg (fun t : Nat => 2 ^ t) (tower_succ (n + 1))
    _ = 2 ^ (2 ^ (2 ^ hyperoperation 4 2 n)) :=
      congrArg (fun t : Nat => 2 ^ (2 ^ t)) (tower_succ n)
    _ = triplePower (hyperoperation 4 2 n) := rfl

theorem tower_add_four (n : Nat) :
    hyperoperation 4 2 (n + 4) = quadruplePower (hyperoperation 4 2 n) := by
  calc
    hyperoperation 4 2 (n + 4) = 2 ^ hyperoperation 4 2 (n + 3) :=
      tower_succ (n + 3)
    _ = 2 ^ triplePower (hyperoperation 4 2 n) :=
      congrArg (fun t : Nat => 2 ^ t) (tower_add_three n)
    _ = quadruplePower (hyperoperation 4 2 n) := rfl

/-- The degree bound fits below the tower of seven twos. -/
theorem triplePower_9014_lt_tower_seven :
    triplePower 9014 < hyperoperation 4 2 7 := by
  have h : triplePower 9014 < triplePower 65536 :=
    triplePower_strictMono (by decide : 9014 < 65536)
  have e : hyperoperation 4 2 7 = triplePower 65536 :=
    (congrArg (fun n : Nat => hyperoperation 4 2 n)
      (by decide : 7 = 4 + 3)).trans
      ((tower_add_three 4).trans (congrArg triplePower tower_four))
  exact h.trans_eq e.symm

/-- The coefficient bound fits below the tower of eight twos. -/
theorem quadruplePower_9014_lt_tower_eight :
    quadruplePower 9014 < hyperoperation 4 2 8 := by
  have h : quadruplePower 9014 < quadruplePower 65536 :=
    quadruplePower_strictMono (by decide : 9014 < 65536)
  have e : hyperoperation 4 2 8 = quadruplePower 65536 :=
    (congrArg (fun n : Nat => hyperoperation 4 2 n)
      (by decide : 8 = 4 + 4)).trans
      ((tower_add_four 4).trans (congrArg quadruplePower tower_four))
  exact h.trans_eq e.symm

theorem triplePower_pow (a k : Nat) :
    triplePower a ^ k = 2 ^ ((2 ^ (2 ^ a)) * k) :=
  (Nat.pow_mul 2 (2 ^ (2 ^ a)) k).symm

/-- Multiplication of the inner exponent by 2048 adds eleven one level lower. -/
theorem triplePower_pow_2048 (a : Nat) :
    triplePower a ^ 2048 = 2 ^ (2 ^ (2 ^ a + 11)) := by
  calc
    triplePower a ^ 2048 = 2 ^ ((2 ^ (2 ^ a)) * 2048) :=
      triplePower_pow a 2048
    _ = 2 ^ ((2 ^ (2 ^ a)) * 2 ^ 11) :=
      congrArg (fun t : Nat => 2 ^ ((2 ^ (2 ^ a)) * t))
        (by decide : (2048 : Nat) = 2 ^ 11)
    _ = 2 ^ (2 ^ (2 ^ a + 11)) :=
      congrArg (fun t : Nat => 2 ^ t) (Nat.pow_add 2 (2 ^ a) 11).symm

theorem eleven_lt_two_pow (a : Nat) (ha : 11 < a) : 11 < 2 ^ a :=
  lt_trans ha Nat.lt_two_pow_self

theorem inner_exponent_lt_succ (a : Nat) (ha : 11 < 2 ^ a) :
    2 ^ a + 11 < 2 ^ (a + 1) := by
  calc
    2 ^ a + 11 < 2 ^ a + 2 ^ a := Nat.add_lt_add_left ha _
    _ = 2 ^ a * 2 := (Nat.mul_two _).symm
    _ = 2 ^ (a + 1) := (Nat.pow_succ 2 a).symm

theorem triplePower_pow_2048_lt_succ (a : Nat) (ha : 11 < 2 ^ a) :
    triplePower a ^ 2048 < triplePower (a + 1) := by
  have h : 2 ^ (2 ^ (2 ^ a + 11)) < triplePower (a + 1) :=
    Nat.pow_lt_pow_right (by decide)
      (Nat.pow_lt_pow_right (by decide) (inner_exponent_lt_succ a ha))
  exact (triplePower_pow_2048 a).trans_lt h

theorem succ_pow_le_of_lt (T U k : Nat) (h : T < U) :
    (T + 1) ^ k ≤ U ^ k :=
  Nat.pow_le_pow_left (Nat.succ_le_of_lt h) k

theorem degree_bound_of_parameter_cutoff (a T : Nat)
    (ha : 11 < 2 ^ a) (hT : T < triplePower a) :
    (T + 1) ^ 2048 < triplePower (a + 1) :=
  (succ_pow_le_of_lt T (triplePower a) 2048 hT).trans_lt
    (triplePower_pow_2048_lt_succ a ha)

/-- A strict cutoff at triplePower 9013 suffices for the degree estimate. -/
theorem degree_bound_of_cutoff_bound (T : Nat) (hT : T < triplePower 9013) :
    (T + 1) ^ 2048 < triplePower 9014 := by
  have h := degree_bound_of_parameter_cutoff 9013 T
    (eleven_lt_two_pow 9013 (by decide)) hT
  exact h.trans_eq (congrArg triplePower (by decide : 9013 + 1 = 9014))

theorem two_pow_lt_quadruplePower (a n : Nat) (hn : n < triplePower a) :
    2 ^ n < quadruplePower a :=
  Nat.pow_lt_pow_right (by decide) hn

/-- The same cutoff gives the coefficient estimate after one more power. -/
theorem coefficient_bound_of_cutoff_bound (T : Nat) (hT : T < triplePower 9013) :
    2 ^ ((T + 1) ^ 2048) < quadruplePower 9014 :=
  two_pow_lt_quadruplePower 9014 ((T + 1) ^ 2048) (degree_bound_of_cutoff_bound T hT)

end ZInQ.NumericalTowerBounds

