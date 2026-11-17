# pc-s12: round 2 of fork issue #83 (Theorem 5.2 from Theorem 5.3), with Elliot's supplement S12

Task pc-s12, 2026-11-17, worktree `wip/pc-from-rc` (round 1: `docs/research/pc-from-rc.md`).
Sources: `diophantine_zq.tex` Section 5 (tex L1019–1121), and Elliot's supplement **S12**
(`research/version14/retained-sources/parity-frozen-4eaee875.tex` at upstream main 970ec6bf3, md5
5b8d6f645f240603135c536001dd4756; local untracked copy, not committed). Every use of S12 is labelled
ELLIOT (supplement) with its line numbers.

## Main result

(In progress; see the status table at the end.)

## Manuscript check

One row per step of tex L1019–1121 that this route formalizes or relies on. Verdicts:
**OK** (the text is right as written), **gap filled** (the text is right but omits an argument,
which S12 or this task supplies), **error**, **unverified** (not checked against its source).

| # | tex lines (S12 lines) | step | verdict | reason |
| --- | --- | --- | --- | --- |
| 1 | L1020–1024 | divisors of 2730 realize all real/2-adic/3-adic signatures; `5,7,13` give a basis | OK | proved in Lean (`bookkeeping`, round 1) |
| 2 | L1024–1032 | `β ≡ 17`, `θ ≡ 1 (mod 24)`, disjoint supports, mutual local squares | OK | proved in Lean (`bookkeeping`); matches S12 par:cross-squares (S12 L172–178) |
| 3 | L1033–1035 | simultaneous construction "in S11–S12" | gap filled | S11 is not available under that name; S12's par:descent (S12 L300–454) and par:simultaneous-matrices (S12 L543–683) together give the whole construction, so S11 is not needed |
| 4 | L1036–1040 (S12 L267–279) | `s_i`, `λ_i`, `K`, target `ker K = ⟨1, 1_β⟩`, `λ ∉ im K` | OK | identical to S12 (par:matrices, par:matrix-target) |
| 5 | L1041–1043 (S12 L567–571) | `d−1` slots of type `(0,0)`, one `q₀` of type `(1,1)`; types by `1`, `7 (mod 12)` | OK | checked: `q ≡ 7 (mod 12)` gives `s = λ = 1`, `q ≡ 1` gives `s = λ = 0` (reciprocity) |
| 6 | L1044 (S12 L606–610) | cross-block columns `e_i + e_d` | OK | a basis of the even-sum hyperplane of `𝔽₂^B`, which is what S12 requires |
| 7 | L1045–1048 (S12 L581–601) | rank-one correction `K♯ = K + λaᵗ` | gap filled | tex leaves `a` undefined; S12 L581–583: `a = e_{q₀} + e_{b*}`, so `aᵗ1 = 0`, `aᵗ1_B = 1`; the factorization `K = K♯T`, `T = Id − 1_B aᵗ` (S12 L599–601) gives both targets from `ker K♯ = ⟨1⟩` |
| 8 | L1046–1052 (S12 L631–652) | deleting `q₀` leaves `[[A, C],[Cᵗ, 0]]`, `1ᵗA1 = 1`, nonsingular | OK | the nonsingularity argument is complete; tex's `D₁` is not diagonal (S12 L641: "no symmetry of A is required") |
| 9 | L1052–1053 (S12 L654–658) | adding the support of `θ` preserves the block | gap filled | needs the cross row sums `Σ_J [q_j/q_i] = 0` (mutual local squares, S12 L561–565) and the `I–J` symbols set to `0` |
| 10 | L1053–1056 (S12 L658–666) | free `q₀`-symbols toggle the new diagonal; determinant's full-product coefficient is one; one assignment serves both supports | gap filled | correct because only one determinant varies: the `q₀–J` bits do not enter the smaller matrix (S12 L666; correction (d)). Over `𝔽₂`, "leading coefficient one" alone would not give a common point for two varying determinants |
| 11 | L1057–1058 (S12 L668–679) | reciprocity, CRT, Dirichlet realize the symbols by distinct primes | OK | S12 spells out the successive choice; checked |
| 12 | L1061–1062 (S12 L381–394) | shape `(3^δ ∏ q_i^{u_i}, ∏ q_i^{v_i})` of a positive-second-coordinate class | gap filled | round-1 finding: asserted in tex. S12 derives it from the real place (`a > 0`), even valuations at `2` (necessity only), good primes and the image at `3` |
| 13 | L1063–1066 (S12 L396–407) | local equations `Ku + D_λ v = δλ`, `(K + D_s)v = 0`, `(λ+s)ᵗv = 0` | OK | rechecked bit by bit (the unit quotient against `τ₁^{u_i} τ₂^{v_i}`) |
| 14 | L1068 (S12 L409–433) | "the matrix properties force `v = 0`, `δ = 0`, `u ∈ ker K`" | gap filled | round-1 finding: needs `K + Kᵗ = ssᵗ + D_s`, `sᵗ1 = 1`, `λᵗ1 = 0`, duality `im K = (ker Kᵗ)^⊥`; S12 gives exactly this (`ker N = ker Kᵗ ∩ s^⊥`). Proved in Lean (round 1, `kmat_forces`) |
| 15 | L1069–1073 (S12 L436–454) | `(β, 1)` local everywhere, independent of the torsion classes | gap filled | tex asserts; S12 checks each place: trivial at `2`, `ℝ`; `= τ₁` at `3`; `= τ₁^{1_B}` at `q ∣ ℓ` by `K1_B = 0`; unramified at good primes (uses that the image there is all unramified classes) |
| 16 | (S12 L337–345) | `#E(ℚ_q)/2E(ℚ_q) = 4` for odd `q` | OK | standard (formal group); this task's Lean route at good primes instead reduces to `𝔽_p` (see §3) |
| 17 | (S12 L364–379) | 2-adic necessity: both coordinates have even valuation | OK | rechecked the `mod 8` step: for `x` odd, `x − ℓ = 2u`, `u(ℓ+2u)(u+2ℓ) ≡ ℓ (mod 8)` |
| 18 | L1076–1093 | lem:corank: full 2-torsion and `dim Sel₂ = 3` give corank 1 | OK (cited) | `r + dim Ш[2] = 1`, `dim F[2]` even by Cassels–Tate (Poonen–Stoll), so `F = 0`, `r + t = 1`. A cited leaf here (provenance (b)); not formalized |
| 19 | L1095–1106 | lem:forward-rank (BCDT Thm A + Kolyvagin Thm 1) | unverified | round-1 finding: Kolyvagin is cited as the MPIM preprint MPI/90-69, not a refereed print; not read. Kato (L1103–1106) is used only for `r = 0` and is not needed here |
| 20 | L1107–1109 | "rank one and finite Ш, hence Ш[2] = 0" | OK | finiteness is not needed: `r = 1` and `r + dim Ш[2] = 1` give `Ш[2] = 0` (ON THE SPOT re-derivation, correction (c)); in Lean the Kummer map is onto by counting (`descentGlueM`) |
| 21 | L1110–1112 | the class is a rational point; abscissa class `β` | OK | proved in Lean (`point_of_locM`, round 1) |
| 22 | L1112–1121 | rescaling to `E_{nH}`, the eleven witnesses, `w = (eHz)⁻¹`; `θ = 1` reuse | OK | proved in Lean (`witnesses_of_points`, round 1) |

(Rows are updated as the formalization proceeds; final status in §1.)
