# carayol-herbrand log

- 2026-11-17 00:10 start; merged origin/main (c40109f3) into wip/carayol-herbrand (bae8f7dc), no conflicts.
- VERIFIED (read): `Swan.swanIntegral_proved : LadicCond.SwanIntegral`, `Swan.swanIndependent_proved`,
  `Swan.adaptedExists_proved` are theorems in ZInQKernel/OneProof/H/TailB.lean (namespace HDec, l. 6990-7004),
  from `PkgI6.herbrandQuotient` (Herbrand's theorem, proved in Contrib/Different/Local.lean).
  `Swan.swanAtIntegral` (finite-level change of variables), `Swan.upperAbsWild`, `Swan.upperAbsSurj_of_herbrand`
  hold for every coefficient field k; `AdaptedExists` is stated only for coefficients `PadicAlgCl ℓ`.
- Mathlib has `instNormedFieldValuedAdicCompletion` (FinitePlace.lean:162, uniform structure = Valued's) and
  `FinitePlace.norm_lt_one_iff_mem`.
- Plan: (1) generalize `adaptedExists` to ultrametric normed coefficient fields with ‖ℓ‖ < 1 (K_λ);
  (2) prove condExp = codim V^I + ∫₀^∞ codim V^{G^u} du for continuous ρ : G_{Q_p} → GL_n(K_λ), p ≠ ℓ;
  (3) DDT-form leaf CarayolThmAIrrDDT ↔ CarayolThmAIrr; discharge r17.
