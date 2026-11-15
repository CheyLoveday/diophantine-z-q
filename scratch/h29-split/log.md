# h29-split results log

## Setup (2026-11-15 02:17 PST)
- Base 6edf020d (wip/h29-split). Build: `cp -r ~/dzq-check2/.lake/build` and `lean/.lake/build`
  (dzq-check2 at the same commit 6edf020d).
- **TYZ source absent**: `~/tyz-src/Period7.tex` does not exist; `find / -xdev` and `find ~ /tmp /data /var/tmp
  -maxdepth 6` for `*period7*`, `*1411.4728*` found nothing (VERIFIED). No network allowed. So every TYZ line
  number and statement below is quoted from earlier notes that read the source: `docs/research/nt-tyz.md` §1.2
  (states "VERIFIED against the source"), `rv-nt-tyz.md` (I2 row, B1), `rv-tyz-inputs.md` §1.2 and
  `scratch/rv-tyz-inputs/log.md` Step 1 (read L496–1162). Marked QUOTED below, not re-read.

## Target
- `ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2` (ZInQKernel/Contrib/TYZDecomp/Leaves.lean:273):
  `∀ ℓ, (∀ m sqfree, m%8∈{1,3} → (ℓ m:ℂ)² = lcalSq m) → PropN.LemmaTwoEight ℓ`.

## Statements QUOTED (not re-read; source absent)
- Lemma 2.9 (L1062–1066), from nt-tyz §1.2: `Σ_{n=d₁d₂} ε(d₁,d₂)𝓛(d₁)𝓛(d₂) = Q(n)`, `ε = ±1`, non-ordered
  decompositions, `d₁, d₂ > 0`, `d₂ ≡ 1 (mod 8)`; setting of §2: `n ≡ 1, 2, 3 (mod 8)` positive squarefree (L499).
- Proposition 2.3 (L580–586), from nt-tyz §1.2: `f_n((B̂^×)²) ⊂ 1 + 2ℤ`; therefore `Q(n) ≡ g(n) (mod 2)`.
- `Q(n)`: genus period `Σ_{t∈2Cl_n} f_n(t)`, `f_n` TYZ's test vector (§2.2, Thms 2.4/2.6), left `K^×`-, right
  `Ô_K^×`-invariant on `K̂^×` (scratch/rv-tyz-inputs/log.md Step 1, Prop 2.3 proof L1134–1160 as read there;
  character formula `Σ' P(d₁,d₂) = 2^{h₂}Q(n)`, L1001).
- B1 (rv-nt-tyz, confirmed by rv-tyz-inputs §1.2): TYZ's proof gives `w_K Σ ε𝓛𝓛 = Q(n)`; `w_K = 3` at `n = 3`,
  `1` for other odd `n > 1`. Undecided whether Lemma 2.9 or Thm 2.1 is misprinted.

## Checks of the target against the quoted print (each VERIFIED by reading the Lean and the quotations)
- C1 classes: target covers squarefree `m ≡ 1, 3 (mod 8)`; §2 covers `n ≡ 1, 2, 3` positive squarefree. Subset. OK.
- C2 `m = 1` excluded in clause 1 (`1 < m`); `m ≡ 3` implies `m ≥ 3`. Lemma at `n = 1` not used. OK (weaker).
- C3 index, `m ≡ 3`: non-ordered `{d₁, d₂}` with `d₂ ≡ 1` ↔ divisors `d ≡ 1` (the other factor is `≡ 3`, so each
  pair once). Lean: `m.divisors.filter (· % 8 = 1)`, term `L(m/d)·L(d)`. OK.
- C4 index, `m ≡ 1`: both factors `≡ 1`, `d ≠ m/d` (squarefree, `m > 1`), each pair once through `d² < m`. Lean:
  filter `d % 8 = 1 ∧ d*d < m`, term `L(d)·L(m/d)`. OK. Non-ordered is forced by TYZ's halving by the
  symmetry Lemma 2.8 (L1068–1077, quoted rv-nt-tyz I2).
- C5 signs: `ε = ±1` vanish mod 2. OK. Sign choice of `𝓛`: universal `ℓ` with `ℓ² = lcalSq`; a sign change of
  `ℓ(d)` flips the term, absorbed by `ε`. OK.
- C6 `w_K`: odd (1 or 3), vanishes mod 2. OK under either resolution of B1.
- C7 `g(m) = #2Cl(ℚ(√−m))` (TYZ L363, quoted nt-tyz); Lean `gNat m = gCl m = Nat.card (range (powMonoidHom 2))`
  on `ClassGroup (𝓞 (QNeg m))`. OK.
- C8 normalization of `𝓛`: inherited pin `lcalSq` (TYZDecomp §2, L338–353 as transcribed by earlier tasks); not
  re-checked here (source absent). UNCHECKED here.

## Lean: scratch/h29-split/H29Split.lean (compiled 02:45, 0 errors, no sorry; output H29Split.out)
- §1 printed forms with the genus period as parameter: `Lemma29Printed Q` (w ∈ {1, 3 at m=3}),
  `Prop23Cong Q`, `ClFun`, `sqClasses`, `genusPeriod f`, `Prop23Odd f`.
- §2 glue: `card_sqClasses : (sqClasses n).card = gCl n`; `genusPeriod_mod_two` (the "therefore" of Prop 2.3);
  `tyzLemma29Mod2_of_printed : Lemma29Printed Q → Prop23Cong Q → TYZLemma29Mod2`;
  `tyzLemma29Mod2_of_printedF : Lemma29Printed (genusPeriod f) → Prop23Odd f → TYZLemma29Mod2`.
- §3 inertness: `exists_printedQ_iff : (∃ Q, Lemma29Printed Q ∧ Prop23Cong Q) ↔ TYZLemma29Mod2`;
  `exists_printedF_iff : (∃ f, Lemma29Printed (genusPeriod f) ∧ Prop23Odd f) ↔ TYZLemma29Mod2`.
- §4 `thm11Mod2_iff (h11 : TYZThm11Integral) : TYZThm11Mod2 ↔ TYZLemma29Mod2`.
- Axioms of all five: [propext, Classical.choice, Quot.sound] (VERIFIED).
