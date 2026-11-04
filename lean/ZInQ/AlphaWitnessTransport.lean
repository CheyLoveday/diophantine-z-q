module

public import ZInQ.AlphaCore
public import ZInQ.AlphaAddition
public import ZInQ.AlphaParameterCongruence

/-!
# Coprimality of the square witness and parameter-pair residue transport

Two internal helpers for the necessity direction of the alpha characterization
(pinned AFP `Exponentiation.thy`, lines 1421-1436 and 1464-1520):

* `coprime_of_square_witness`: from `u` odd, `u^2 ∣ s`, the quadratic
  `s^2 + r^2 = 1 + b*s*r` and `v + 2*r = b*s`, the numbers `u` and `v` are coprime.
* `exists_parameter_pair_residues`: for `2 < w`, the values `alphaZ w c` and
  `alphaZ w (c+1)` are natural numbers satisfying the quadratic at parameter `w`,
  and the residue congruences modulo `v` and `u` are transported from
  `w ≡ b (mod v)` and `w ≡ 2 (mod u)`.

These results do not establish the complete alpha or exponentiation encoding.
-/

public section

namespace ZInQ.AlphaPower

theorem coprime_of_square_witness (b u r s v : Nat)
    (hu : Odd u) (hus : u^2 ∣ s) (hquad : s^2+r^2 = 1+b*s*r)
    (hv : v+2*r = b*s) : Nat.Coprime u v := by
  obtain ⟨k, hk⟩ := hu
  -- `d := gcd u v` divides `u` and `v`.
  have hdu : Nat.gcd u v ∣ u := Nat.gcd_dvd_left u v
  have hdv : Nat.gcd u v ∣ v := Nat.gcd_dvd_right u v
  -- `d ∣ u ∣ u^2 ∣ s`.
  have hds : Nat.gcd u v ∣ s :=
    Nat.dvd_trans hdu (Nat.dvd_trans (⟨u, by ring⟩ : u ∣ u ^ 2) hus)
  -- `d ∣ b*s = v + 2*r` and `d ∣ v`, hence `d ∣ 2*r`.
  have hd2r : Nat.gcd u v ∣ 2 * r := by
    have h1 : Nat.gcd u v ∣ v + 2 * r := by
      rw [hv]
      exact Nat.dvd_mul_left_of_dvd hds b
    exact (Nat.dvd_add_right hdv).mp h1
  -- `u = 2*k+1`, so `u*r = k*(2*r) + r`; with `d ∣ u*r` and `d ∣ k*(2*r)` we get `d ∣ r`.
  have hdr : Nat.gcd u v ∣ r := by
    have h1 : Nat.gcd u v ∣ k * (2 * r) + r := by
      have h2 : k * (2 * r) + r = u * r := by
        rw [hk]
        ring
      rw [h2]
      exact Nat.dvd_mul_right_of_dvd hdu r
    exact (Nat.dvd_add_right (Nat.dvd_mul_left_of_dvd hd2r k)).mp h1
  -- `d ∣ s^2 + r^2 = 1 + b*s*r` and `d ∣ b*s*r`, hence `d ∣ 1`.
  have hd1 : Nat.gcd u v ∣ 1 := by
    have hs2 : Nat.gcd u v ∣ s ^ 2 :=
      Nat.dvd_trans hds (⟨s, by ring⟩ : s ∣ s ^ 2)
    have hr2 : Nat.gcd u v ∣ r ^ 2 :=
      Nat.dvd_trans hdr (⟨r, by ring⟩ : r ∣ r ^ 2)
    have h1 : Nat.gcd u v ∣ s ^ 2 + r ^ 2 := Nat.dvd_add hs2 hr2
    have h2 : Nat.gcd u v ∣ b * s * r + 1 := by
      rw [hquad, Nat.add_comm] at h1
      exact h1
    exact (Nat.dvd_add_right (Nat.dvd_mul_left_of_dvd hdr (b * s))).mp h2
  exact Nat.eq_one_of_dvd_one hd1

theorem exists_parameter_pair_residues (b a c u v w : Nat)
    (hw : 2 < w) (ha : (a : Int) = alphaZ b c)
    (hwu : w % u = 2 % u) (hwv : w % v = b % v) :
    ∃ x y : Nat, (x : Int) = alphaZ w c ∧ (y : Int) = alphaZ w (c+1) ∧
      x^2+y^2 = 1+w*x*y ∧ a % v = x % v ∧ c % u = x % u := by
  -- Nonnegativity of the two consecutive values at parameter `w ≥ 2`.
  have hw2 : 2 ≤ w := Nat.le_of_lt hw
  have hx0 : 0 ≤ alphaZ w c := (alphaZ_step w hw2 c).1
  have hy0 : 0 ≤ alphaZ w (c + 1) := (alphaZ_step w hw2 (c + 1)).1
  -- Only now choose the natural witnesses.
  obtain ⟨x, hx⟩ := Int.eq_ofNat_of_zero_le hx0
  obtain ⟨y, hy⟩ := Int.eq_ofNat_of_zero_le hy0
  refine ⟨x, y, hx.symm, hy.symm, ?_, ?_, ?_⟩
  · -- Quadratic clause from the Cassini identity at parameter `w`.
    have hcas := alphaZ_cassini w c
    rw [hx, hy] at hcas
    have hZ : (x : Int) ^ 2 + (y : Int) ^ 2 = 1 + (w : Int) * (x : Int) * (y : Int) := by
      linear_combination hcas
    exact_mod_cast hZ
  · -- Residue modulo `v`: `w ≡ b (mod v)` transports `alphaZ w c ≡ alphaZ b c = a`.
    have hcong := alphaZ_emod_eq_of_mod_eq v w b c hwv
    rw [hx, ← ha] at hcong
    have hZ : ((a % v : Nat) : Int) = ((x % v : Nat) : Int) := by
      rw [Int.natCast_emod, Int.natCast_emod]
      exact hcong.symm
    exact_mod_cast hZ
  · -- Residue modulo `u`: `w ≡ 2 (mod u)` transports `alphaZ w c ≡ alphaZ 2 c = c`.
    have hcong := alphaZ_emod_eq_of_mod_eq u w 2 c hwu
    rw [hx, alphaZ_two_left] at hcong
    have hZ : ((c % u : Nat) : Int) = ((x % u : Nat) : Int) := by
      rw [Int.natCast_emod, Int.natCast_emod]
      exact hcong.symm
    exact_mod_cast hZ

end ZInQ.AlphaPower
