# rc-goodrow-wire results log

- Merges: 98a68f7e0 (wip/rc-model-target 621cccc1d), 45957b1d0 (main 8e5d680c1). Clean.
- Item 1 docs: 67896e640.
- Finding: `ModelGeneric5.eq_Wint_of_extendsAtkin` needs neither `q.Prime` nor `q ∣ N`; the
  agreement `(ext q hq he).choose = Wint` needs no factorization conversion.
- Fact instance for stage primes: `O7Assemble.stagePrime` (RC/O7Assemble/ActualFamily.lean:19), global.
- SamePlace.lean builds (258s); point_W_choose axioms: propext, Classical.choice, Quot.sound
