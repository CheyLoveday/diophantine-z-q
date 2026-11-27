import ZInQKernel.Contrib.OneProof.RC.O12Local.Whittaker

/-! Assemble the Whittaker evaluations of the individual dilation columns.
The action at one follows from a comparison with the classical coefficient shift
(tex 9841–9856). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open Matrix O12Local

variable {I K : Type} [Fintype I] [Field K] {p : ℕ} (hp : p ≠ 0)
variable (a : I → O12.PosIndex → K)

/-- The finite evaluations of the adelized dilation columns needed at one
prime. These data concern the input forms and involve no Hecke operator. -/
structure WhittakerColumnValues where
  Away : Type
  [awayGroup : Group Away]
  away : O12.PosIndex → Away
  away_one : away ⟨1, one_ne_zero⟩ = 1
  W : I → Matrix (Fin 2) (Fin 2) K → Away → K
  fourier : ∀ i (n : O12.PosIndex),
    W i !![(n.val : K), 0; 0, 1] (away n) = a i n / (n.val : K)
  integral_translation : ∀ i (b : Fin p),
    W i (!![1, (b.val : K); 0, 1] * !![(p : K), 0; 0, 1]) 1 =
      W i !![(p : K), 0; 0, 1] 1
  right_away : ∀ i g z, W i g (z * away ⟨p, hp⟩) = W i g z

attribute [instance] WhittakerColumnValues.awayGroup

variable {hp a} (D : WhittakerColumnValues hp a)

private def sumWhittaker (v : I → K) (g : Matrix (Fin 2) (Fin 2) K) (z : D.Away) : K :=
  ∑ i, v i * D.W i g z

private theorem sumWhittaker_fourier (v : I → K) (n : O12.PosIndex) :
    sumWhittaker D v !![(n.val : K), 0; 0, 1] (D.away n) =
      (∑ i, v i * a i n) / (n.val : K) := by
  simp [sumWhittaker, D.fourier, Finset.sum_div, mul_div_assoc]

/-- Compare a coordinate endomorphism with right translation at the
identity. Only the classical coefficient-one identity is needed for the
action field. The Whittaker values themselves come from the columns. -/
def WhittakerColumnValues.comparison [CharZero K] {H : (I → K) →ₗ[K] (I → K)}
    (hH : ∀ v, ∑ i, H v i * a i ⟨1, one_ne_zero⟩ = ∑ i, v i * a i ⟨p, hp⟩) :
    WhittakerComparison p hp Set.univ H (fun n v => ∑ i, v i * a i n) where
  Away := D.Away
  away := D.away
  away_one := D.away_one
  W := sumWhittaker D
  fourier v _ n := sumWhittaker_fourier D v n
  integral_translation v _ b := by
    unfold sumWhittaker
    exact Finset.sum_congr rfl fun i _ =>
      congrArg (v i * ·) (D.integral_translation i b)
  right_away v _ g z := by simp [sumWhittaker, D.right_away]
  action_at_one v _ := by
    have h1 (w : I → K) : sumWhittaker D w !![1, 0; 0, 1] 1 =
        ∑ i, w i * a i ⟨1, one_ne_zero⟩ := by
      simpa only [Nat.cast_one, D.away_one, div_one] using
        sumWhittaker_fourier D w ⟨1, one_ne_zero⟩
    have hpW : sumWhittaker D v !![(p : K), 0; 0, 1] 1 =
        (∑ i, v i * a i ⟨p, hp⟩) / (p : K) := by
      rw [← sumWhittaker_fourier D v ⟨p, hp⟩]
      apply Finset.sum_congr rfl
      intro i _
      have h := D.right_away i !![(p : K), 0; 0, 1] 1
      rw [one_mul] at h
      rw [h]
    have hsum := O12.whittaker_sum (fun m => sumWhittaker D v m 1) p 1 (by
      intro b
      simp only [one_mul, sumWhittaker]
      exact Finset.sum_congr rfl fun i _ =>
        congrArg (v i * ·) (D.integral_translation i b))
    simp only [one_mul] at hsum
    rw [h1, hH, hsum, hpW]
    field_simp [Nat.cast_ne_zero.mpr hp]

end ZInQ.Manuscript.RC.EvenJoin
