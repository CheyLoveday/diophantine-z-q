# rc-model-generic5 results log

## Setup
- merged main 61e00d45 into wip/rc-model-generic5 (no conflicts), merge commit 4f0328005.

## Item 1: StagePrimes.lean (builds; axioms propext, Classical.choice, Quot.sound)
- EcurveZ_disc : (EcurveZ l).Δ = 2304 * l^6.
- stagePrime_not_dvd_disc (s : Setup I L) i : ¬ (p_i : ℤ) ∣ Δ(EcurveZ ℓ)   [StageKummer.stageGood]
- stagePrime_five_le s i : 5 ≤ p_i   (h₅)   [p ≡ 3 mod 4 (stage_mod_four), 3 ∣ 2304]
- stagePrime_not_dvd_tame s (hN : 0 < N) (hB : (N*φ(N)).primeFactors ⊆ s.B) i : ¬ p_i ∣ N*φ(N)  (htame)
- subset_stageExclusions, not_dvd_tame_of_not_mem_stageExclusions (exists_detector_stages sequences are over stageExclusions ℓ Dw hstar B ⊇ B)
- two_le_newformLevel (hN : 0 < CST.newformLevel E) : 2 ≤ CST.newformLevel E  [S₂(SL₂ℤ)=0 via Mathlib CuspForm.rank_eq_zero_of_weight_lt_twelve; a₁(E)=1 via lFunction_one]
- two_le_level (hN : 0 < StageKummer.level ℓ) : 2 ≤ StageKummer.level ℓ  (h₂ from the hN hypothesis of oddStagedOfGoodRows)
