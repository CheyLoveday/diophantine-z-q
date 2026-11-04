/- Natural-number semantic bodies of the compiler's bitwise macros. -/
module

public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Data.Nat.Bitwise
import Lean.Elab.Tactic.Omega

/-!
These are the literal existential macro bodies at the mathematical semantic
layer identifying the binomial value with `Nat.choose`. The compiler bridge
for that identification is a separate task, not a Lean result claimed here.
The fresh binomial and odd-half witnesses are retained. No theorem or
correctness assumption is an argument to any definition.
-/

@[expose] public section

namespace ZInQ.NaturalBitwiseMacros

/-- Builder.odd: a fresh natural half witnesses x = 2*half+1. -/
def odd_witness (x : Nat) : Prop := ∃ half : Nat, x = 2 * half + 1

/-- Builder.mask(a,b): its binomial witness is choose(b,a). -/
def mask (a b : Nat) : Prop :=
  ∃ c : Nat, c = Nat.choose b a ∧ odd_witness c

/-- Builder.orthogonal(a,b): its binomial witness is choose(a+b,a). -/
def orthogonal (a b : Nat) : Prop :=
  ∃ c : Nat, c = Nat.choose (a + b) a ∧ odd_witness c

/-- Builder.bitAnd(z,x,y), with its exact two fresh natural remainders. -/
def bit_and (z x y : Nat) : Prop :=
  ∃ a b : Nat,
    x = z + a ∧ y = z + b ∧
    orthogonal z a ∧ orthogonal z b ∧ orthogonal a b

end ZInQ.NaturalBitwiseMacros

end

/-! Exact natural-number semantics of the bitwise macros, including zero inputs. -/

public section

namespace ZInQ.NaturalBitwiseMacros

theorem odd_witness_iff_odd (x : Nat) : odd_witness x ↔ Odd x := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩

private theorem nat_eq_iff_halves (a b : Nat) :
    a = b ↔ a % 2 = b % 2 ∧ a / 2 = b / 2 := by
  omega

private theorem and_eq_recur (a b : Nat) :
    a &&& b = a ↔ a % 2 ≤ b % 2 ∧ (a / 2 &&& b / 2) = a / 2 := by
  rw [nat_eq_iff_halves (a &&& b) a, Nat.and_div_two]
  have h := Nat.and_mod_two_eq_one (a := a) (b := b)
  omega

private theorem and_zero_recur (a b : Nat) :
    a &&& b = 0 ↔ (a % 2 = 0 ∨ b % 2 = 0) ∧ (a / 2 &&& b / 2) = 0 := by
  rw [nat_eq_iff_halves (a &&& b) 0, Nat.and_div_two]
  have h := Nat.and_mod_two_eq_one (a := a) (b := b)
  omega

private theorem choose_odd_recur (a b : Nat) :
    Odd (Nat.choose b a) ↔ a % 2 ≤ b % 2 ∧ Odd (Nat.choose (b / 2) (a / 2)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2) (n := b) (k := a)
  change (Nat.choose b a) % 2 =
    (Nat.choose (b % 2) (a % 2) * Nat.choose (b / 2) (a / 2)) % 2 at h
  rw [Nat.odd_iff, h, ← Nat.odd_iff, Nat.odd_mul]
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

theorem choose_odd_iff_land_eq (a b : Nat) :
    Odd (Nat.choose b a) ↔ Nat.land a b = a := by
  change Odd (Nat.choose b a) ↔ a &&& b = a
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha : a = 0
    · subst a
      simp
    · have hsmall : a / 2 < a := Nat.div_lt_self (by omega) (by decide)
      rw [choose_odd_recur, and_eq_recur, ih (a / 2) hsmall]

private theorem subset_add_iff_and_zero (a b : Nat) :
    a &&& (a + b) = a ↔ a &&& b = 0 := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha : a = 0
    · subst a
      simp
    · have hsmall : a / 2 < a := Nat.div_lt_self (by omega) (by decide)
      rw [and_eq_recur, and_zero_recur]
      by_cases hoverlap : a % 2 = 1 ∧ b % 2 = 1
      · have hlow : ¬ a % 2 ≤ (a + b) % 2 := by omega
        have hz : ¬ (a % 2 = 0 ∨ b % 2 = 0) := by omega
        simp only [hlow, hz, false_and]
      · have hlow : a % 2 ≤ (a + b) % 2 := by omega
        have hz : a % 2 = 0 ∨ b % 2 = 0 := by omega
        have hdiv : (a + b) / 2 = a / 2 + b / 2 := by omega
        rw [hdiv]
        simp only [hlow, hz, true_and]
        exact ih (a / 2) hsmall (b / 2)

theorem choose_add_odd_iff_land_eq_zero (a b : Nat) :
    Odd (Nat.choose (a + b) a) ↔ Nat.land a b = 0 := by
  rw [choose_odd_iff_land_eq]
  exact subset_add_iff_and_zero a b

theorem mask_iff_land_eq (a b : Nat) :
    mask a b ↔ Nat.land a b = a := by
  simp only [mask, exists_eq_left, odd_witness_iff_odd, choose_odd_iff_land_eq]

theorem orthogonal_iff_land_eq_zero (a b : Nat) :
    orthogonal a b ↔ Nat.land a b = 0 := by
  simp only [orthogonal, exists_eq_left, odd_witness_iff_odd,
    choose_add_odd_iff_land_eq_zero]

private theorem add_eq_or_add_and (a b : Nat) :
    a + b = (a ||| b) + (a &&& b) := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha : a = 0
    · subst a
      simp
    · have hsmall : a / 2 < a := Nat.div_lt_self (by omega) (by decide)
      have h := ih (a / 2) hsmall (b / 2)
      have hand := Nat.and_div_two (a := a) (b := b)
      have hor := Nat.or_div_two (a := a) (b := b)
      have handmod := Nat.and_mod_two_eq_one (a := a) (b := b)
      have hormod := Nat.or_mod_two_eq_one (a := a) (b := b)
      omega

private theorem add_eq_or_of_and_zero (a b : Nat) (h : a &&& b = 0) :
    a + b = a ||| b := by
  simpa only [h, Nat.add_zero] using add_eq_or_add_and a b

private theorem disjoint_union_and (z a b : Nat)
    (ha : z &&& a = 0) (hb : z &&& b = 0) (hab : a &&& b = 0) :
    (z ||| a) &&& (z ||| b) = z := by
  apply Nat.eq_of_testBit_eq
  intro i
  have ha' := congrArg (fun n : Nat => n.testBit i) ha
  have hb' := congrArg (fun n : Nat => n.testBit i) hb
  have hab' := congrArg (fun n : Nat => n.testBit i) hab
  simp only [Nat.testBit_and, Nat.zero_testBit] at ha' hb' hab'
  simp only [Nat.testBit_and, Nat.testBit_or]
  cases hz : z.testBit i <;> cases ha : a.testBit i <;> cases hb : b.testBit i <;>
    simp_all

private theorem and_ldiff_left (x y : Nat) : (x &&& y) &&& Nat.ldiff x y = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_ldiff, Nat.zero_testBit]
  cases x.testBit i <;> cases y.testBit i <;> rfl

private theorem and_ldiff_right (x y : Nat) : (x &&& y) &&& Nat.ldiff y x = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_ldiff, Nat.zero_testBit]
  cases x.testBit i <;> cases y.testBit i <;> rfl

private theorem ldiff_and_ldiff (x y : Nat) : Nat.ldiff x y &&& Nat.ldiff y x = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_ldiff, Nat.zero_testBit]
  cases x.testBit i <;> cases y.testBit i <;> rfl

private theorem or_ldiff_left (x y : Nat) : (x &&& y) ||| Nat.ldiff x y = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_ldiff]
  cases x.testBit i <;> cases y.testBit i <;> rfl

private theorem or_ldiff_right (x y : Nat) : (x &&& y) ||| Nat.ldiff y x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_ldiff]
  cases x.testBit i <;> cases y.testBit i <;> rfl

theorem bit_and_iff_land_eq (z x y : Nat) :
    bit_and z x y ↔ z = Nat.land x y := by
  constructor
  · rintro ⟨a, b, hx, hy, ha, hb, hab⟩
    have ha' := (orthogonal_iff_land_eq_zero z a).mp ha
    have hb' := (orthogonal_iff_land_eq_zero z b).mp hb
    have hab' := (orthogonal_iff_land_eq_zero a b).mp hab
    rw [hx, hy, add_eq_or_of_and_zero z a ha', add_eq_or_of_and_zero z b hb']
    exact (disjoint_union_and z a b ha' hb' hab').symm
  · rintro rfl
    refine ⟨Nat.ldiff x y, Nat.ldiff y x, ?_, ?_, ?_, ?_, ?_⟩
    · exact ((add_eq_or_of_and_zero (x &&& y) (Nat.ldiff x y) (and_ldiff_left x y)).trans
        (or_ldiff_left x y)).symm
    · exact ((add_eq_or_of_and_zero (x &&& y) (Nat.ldiff y x) (and_ldiff_right x y)).trans
        (or_ldiff_right x y)).symm
    · exact (orthogonal_iff_land_eq_zero _ _).mpr (and_ldiff_left x y)
    · exact (orthogonal_iff_land_eq_zero _ _).mpr (and_ldiff_right x y)
    · exact (orthogonal_iff_land_eq_zero _ _).mpr (ldiff_and_ldiff x y)

end ZInQ.NaturalBitwiseMacros

