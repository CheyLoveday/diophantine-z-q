# unipotent-b results log

## Setup
- lean/.lake was missing in the worktree ("unknown module prefix 'ZInQ'"); reflink-copied from ../genus-fold/lean/.lake (identical lean/ZInQ, checked by diff -rq).

## UnipotentB.lean (imports ZInQKernel.OneProof.H.TailZ14 only)
- §0 verbatim copies of ReductSplit.SemistableUnipotent, ReductGlue.SemistableUnipotentSH, ReductGlue.StrictHenselizationInside, each `= original := rfl`. VERIFIED (compiled).
- §1 specialFibre (𝒩 ×_O k(s)), IsSemistableRes, HasSemistableReductionRes; resBarEquiv : k(s) ≃+* κ̄ for alg. closed k(s); isSemistableRes_iff, hasSemistableReductionRes_iff (k(s) vs κ̄ semistability agree when k(s) alg. closed). VERIFIED (compiled).
- §2 LEAF SemistableUnipotentPrinted (SGA 7 IX 3.5 printed form, UNVERIFIED wording: SH trait, [CharZero K], [PerfectField k(s)], Ω [IsSepClosure K Ω], semistable over k(s); iff I unipotent; echelon (σ-1)(τ-1)=0). SemistableUnipotentPrintedEchelon (used direction) with echelon_of_printed. SemistableUnipotentSH0 (= SemistableUnipotentSH + [CharZero K] [PerfectField k(s)]); semistableUnipotentSH0_of : PrintedEchelon → SH0. VERIFIED (compiled).
- §3 SemistableUnipotent0 (= SemistableUnipotent + [CharZero K] [PerfectField k(s)]); semistableUnipotent0_of : StrictHenselizationInside → SH0 → SemistableUnipotent0; semistableUnipotent0_of_printed; semistableUnipotent0_of_old. VERIFIED (compiled, no errors/warnings).
