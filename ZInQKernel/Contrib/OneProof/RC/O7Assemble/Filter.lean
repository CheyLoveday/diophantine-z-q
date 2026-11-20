import ZInQKernel.Contrib.OneProof.RC.PicardFibers.LocalConjugacy
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Support
import ZInQKernel.Contrib.OneProof.RC.TorusWeights.Norm

/-! The level and support tests in the full odd admissibility filter. -/

namespace ZInQ.Manuscript.RC.O7Assemble

open O7Actual O7Orbits PicardFibers ThetaJoin

section Filter

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m : ℤ}
  {s : StageAt O N M hN m} {D : ℤ}

/-- Convert the full odd filter into the arithmetic read by torus weights. -/
theorem oddFilter (A : AdmissibleD s D) : TorusWeights.OddFilter N s.ell D (-(s.weights.m : ℤ)) :=
  ⟨A.positive, A.squarefree, by
    have h := A.coprime_partner
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs] at h
    exact h, A.detecting, A.fundamental_discriminant, A.odd_discriminant, A.split⟩

/-- The support and normalizer lanes use the same positive integer and
dyadic conditions, expressed there with a natural index. -/
theorem requestedIndices {n : ℕ} (A : AdmissibleD s (n : ℤ)) :
    RequestedIndices (ell := s.ell) (m := s.weights.m) n ((disc s n - 1) / 4) := by
  have h8 := A.mod_eight
  refine ⟨by exact_mod_cast A.positive, Int.squarefree_natCast.mp A.squarefree, ?_, ?_, ?_, h8⟩
  · simpa only [Int.natAbs_natCast, Int.natAbs_neg] using (oddFilter A).coprime
  · rw [← jacobiSym.legendreSym.to_jacobiSym]
    exact A.detecting
  · change disc s (n : ℤ) = _
    omega

/-- Level coprimality and all odd level symbols follow from splitting of
the same discriminant at every prime dividing twice the level. -/
theorem levelFilter {n : ℕ} (A : AdmissibleD s (n : ℤ)) :
    LevelFilter (N := N) (m := s.weights.m) n := by
  have hs (p : ℕ) (hp : p.Prime) (hL : p ∣ N) :=
    A.split p hp (dvd_mul_of_dvd_right hL 2)
  refine ⟨Nat.coprime_of_dvd ?_, ?_⟩
  · intro p hp hpn hL
    exact (hs p hp hL).not_dvd hp
      (dvd_mul_of_dvd_left (Int.natCast_dvd.mpr hpn) _)
  · intro p hp h₂ hL
    letI : Fact p.Prime := ⟨hp⟩
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    exact (legendreSym.eq_one_iff p (fun hz => (hs p hp hL).not_dvd hp
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz))).mpr ((hs p hp hL).2 h₂).2

end Filter

end ZInQ.Manuscript.RC.O7Assemble
