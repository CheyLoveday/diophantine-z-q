# Results

- Base: `40d619ca811e6d8e760c49ac7e273cf5be8b2272`.
- Common-level `Blocks` and `Basis` do not retain lower levels; `Attachment` and cuspidal `GoodRec` only quantify over `Test T avoid`.
- `seed_level_dvd`: on a nonzero coordinate of `F_U`, its level divides `N₀ · ∏ U`; unary block levels divide `N₀ · J`.
- `seed_level_coprime`: good `q ∉ U` is prime to that level and hence to its degeneracy label.
- Same-lattice diamond witness at an odd good prime: `q⁻¹ • d(Fr_q) F_U`; no extra lattice-stability hypothesis.
- `Levels.lean`: passed `lake env lean`; both axiom audits printed only `propext`, `Classical.choice`, `Quot.sound`.
- `EisensteinCharacters.frob_values`, `inertia_values`: at an odd prime coprime to the occurrence level, the two Frobenius values are `α(q)` and `qβ(q)`, and both inertia values are one.
- `good_values`, `seed_good_polynomial`: trace `a_i(q)`, determinant `qχ_i(q)`, and polynomial `X² − a_i(q)X + qχ_i(q)` on each active good coordinate.
- `seed_unramified` (**hseed**): inertia fixes each nonzero coordinate of each subset seed.
- `seed_good_recursion`, `seed_fourier_over_field`: apply the good recursion to each dilation, then sum it over the nonzero coordinates; the second term uses the determinant translate.
- `odd_unit`, `seed_fourier` (**hexcl**): (q) is a coefficient unit; the diamond translate has coordinate `χ_i(q) F_U(i)` in the original lattice and gives the integral all-index formula.
- `windowModelOfLevels`, `window_good_hecke` (**good_hecke**): the existing window constructor with `hseed`, and the existing ambient/excluded split with `hexcl`.
- Remaining: `BlockLevels` and `AtLevel` data. The finite window does not realize sets outside its pool.
- Final compile: `Levels.lean`, `Eisenstein.lean`, `Attachment.lean`, `Fourier.lean`, `Window.lean` passed sequential `lake env lean -j1`, with no warnings. All 16 theorem audits and one constructor audit printed exactly `propext`, `Classical.choice`, `Quot.sound`.
