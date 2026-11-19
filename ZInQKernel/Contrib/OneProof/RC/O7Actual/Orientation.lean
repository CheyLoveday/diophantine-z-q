import ZInQKernel.Contrib.OneProof.RC.PM.Theta

/-! Along a single orientation change both signs are the same; the weighted
contribution is therefore fixed. The local moves connect the whole binary cube. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O7Actual

open Eichler

/-- A bit at each level prime and one at the ramified prime (tex 9136–9148).
Identifying the local orbit sets with these bits is a separate local calculation. -/
abbrev Orientations (ω : ℕ) := Fin (ω + 1) → Bool

theorem card_orientations (ω : ℕ) : Fintype.card (Orientations ω) = 2 ^ (ω + 1) := by
  simp [Orientations]

/-- Flip the bit at one prime, keeping all other bits fixed. -/
def flip {I : Type*} [DecidableEq I] (i : I) (t : I → Bool) : I → Bool :=
  Function.update t i (!t i)

/-- On-the-spot (c), tex 9366–9367: the cube is connected by the single
coordinate flips. State this as an invariant argument to keep the intermediate
congruences at their original precision. -/
theorem bit_induction {I : Type*} [Fintype I] [DecidableEq I] (P : (I → Bool) → Prop)
    (t₀ : I → Bool) (h₀ : P t₀) (hflip : ∀ i t, P t → P (flip i t)) (t : I → Bool) :
    P t := by
  have hs (s : Finset I) : P (fun i => if i ∈ s then t i else t₀ i) := by
    induction s using Finset.induction_on with
    | empty => simpa using h₀
    | @insert i s hi ih =>
      by_cases h : t i = t₀ i
      · convert ih using 1
        funext j
        by_cases hj : j = i
        · subst j
          simp [hi, h]
        · simp [Finset.mem_insert, hj]
      · convert hflip i _ ih using 1
        funext j
        by_cases hj : j = i
        · subst j
          have ht : t i = !t₀ i := by
            cases hL : t i <;> cases hR : t₀ i <;> simp_all
          simpa [flip, hi] using ht
        · simp [flip, Finset.mem_insert, hj]
  simpa using hs Finset.univ

/-- Tex 9331–9358: equal signs on the Schwartz factor and on the norm times
the lifted point value cancel at a single pair of matched orbits. -/
theorem cancel_edge_sign {O : Type*} [CommRing O] {q s f f' v v' : O}
    (hs : s * s = 1) (hf : f' = s * f) (hv : q ∣ v' - s * v) :
    q ∣ f' * v' - f * v := by
  have h := Dvd.dvd.mul_left hv f'
  convert h using 1
  rw [hf]
  linear_combination (f * v) * hs

/-- Tex 9329–9367: the pointwise congruences give the congruence for every
orientation. An edge may reindex the class group by an arbitrary permutation. -/
theorem orientation_sum {I Cl O : Type*} [Fintype I] [DecidableEq I] [Fintype Cl]
    [CommRing O] (q : O) (v : (I → Bool) → Cl → O)
    (e : I → (I → Bool) → Cl ≃ Cl)
    (hedge : ∀ i t c, q ∣ v (flip i t) (e i t c) - v t c)
    (t₀ t : I → Bool) :
    q ∣ (∑ c, v t c) - ∑ c, v t₀ c := by
  apply bit_induction (fun t => q ∣ (∑ c, v t c) - ∑ c, v t₀ c) t₀
  · simp
  · intro i t ht
    have he : q ∣ (∑ c, v (flip i t) c) - ∑ c, v t c := by
      rw [← Equiv.sum_comp (e i t) (v (flip i t)), ← Finset.sum_sub_distrib]
      exact Finset.dvd_sum fun c _ => hedge i t c
    simpa only [sub_add_sub_cancel] using dvd_add he ht

section PM

variable {a b : ℚ} {R : Order a b} {ell N : ℕ} [Fact ell.Prime]
  {K : Type*} [Field K] [Algebra (ZMod ell) K] [DecidableEq K] [IsSepClosed K]
  {Ebar : WeierstrassCurve (ZMod ell)} [Ebar.IsElliptic] {ap : ℕ → ℤ} {M : ℕ}
  (G : PM.Geometry K R N Ebar ap) (d : PM.Evaluation K Ebar M) (L : ℕ)
  {u : ClassSet R → ℤ} (hu : PM.IsLift G d L u)
  {O : Type*} [CommRing O] (χN : ClassSet R → O)
include d L hu

/-- Tex 9329–9339: the actual Atkin–Lehner operation preserves a single
weighted orbit contribution at precision `M`. -/
theorem atkin_edge (p : ℕ) (hp : p.Prime) (he : 0 < N.factorization p)
    (hL : L • G.cusp p = 0) (z : ClassSet R) (χp f f' : O)
    (hχ : χN (G.atkin p hp he z) = χp ^ N.factorization p * χN z)
    (hs : let s := (G.atkinSign p : O) * χp ^ N.factorization p; s * s = 1)
    (hf : f' = ((G.atkinSign p : O) * χp ^ N.factorization p) * f) :
    (2 : O) ^ M ∣
      f' * (χN (G.atkin p hp he z) * (u (G.atkin p hp he z) : O)) -
      f * (χN z * (u z : O)) :=
  cancel_edge_sign hs hf (PM.normWeighted_atkin_dvd G d L hu p hp he hL z χN χp hχ)

/-- Tex 9341–9358: the uniformizer exchanges the residue embeddings;
the two negative signs cancel while the actual detector has Frobenius sign one. -/
theorem uniformizer_edge (z : ClassSet R) (f f' : O)
    (hχ : χN (G.uniformizer z) = -χN z) (hf : f' = -f) :
    (2 : O) ^ M ∣
      f' * (χN (G.uniformizer z) * (u (G.uniformizer z) : O)) -
      f * (χN z * (u z : O)) := by
  apply cancel_edge_sign (s := (-1 : O)) (by simp) (by simpa using hf)
  simpa using PM.normWeighted_uniformizer_dvd G d L hu z χN hχ

end PM

end ZInQ.Manuscript.RC.O7Actual
