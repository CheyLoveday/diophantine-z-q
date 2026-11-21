# Results

- `BaseChange` passed targeted Lake build. The affine comparison sends the adjoined roots to the corresponding roots, the divisor restrictions commute with scalar extension, and `exactOrderBaseChange` applies the existing clopen comparison over every coefficient-ring map. All new proofs printed only `propext`, `Classical.choice` and `Quot.sound` or a subset.
- The first prerequisite check allowed Lake to launch several uncached modules concurrently. Subsequent Lake builds used a per-worktree compiler lock inside the required systemd CPU and memory scope.
