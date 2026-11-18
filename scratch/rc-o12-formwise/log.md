# Results

- Base: `40d619ca811e6d8e760c49ac7e273cf5be8b2272`.
- Common-level `Blocks` and `Basis` do not retain lower levels; `Attachment` and cuspidal `GoodRec` only quantify over `Test T avoid`.
- `seed_level_dvd`: on a nonzero coordinate of `F_U`, its level divides `N₀ · ∏ U`; unary block levels divide `N₀ · J`.
- `seed_level_coprime`: good `q ∉ U` is prime to that level and hence to its degeneracy label.
- Same-lattice diamond witness at an odd good prime: `q⁻¹ • d(Fr_q) F_U`; no extra lattice-stability hypothesis.
- `Levels.lean`: passed `lake env lean`; both axiom audits printed only `propext`, `Classical.choice`, `Quot.sound`.
