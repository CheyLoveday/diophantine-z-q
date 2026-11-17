# r3prime-etale results log

## 2026-11-17 06:36 start
- Base: wip/r3prime-etale at 115cb119b (origin/wip/jp-an-retype already merged; step (1) done). VERIFIED (git log).
- sga1-etale, sga1-fix, gaga-serre are NOT ancestors of HEAD (VERIFIED, git merge-base); their CPt/AnFunAt world
  (analyticTopology, AffineChart, SerreHolAt) is on `X : Over (Spec ℂ)` and CPt X, not on the consumers'
  `𝒢.Pts τ` with `anTop`. No homeomorphism `𝒢.Pts τ ≃ₜ CPt(𝒢 ×_τ ℂ)` exists in the tree (survey fact iii).

## Plan (decided)
- Define on the consumers' carrier `𝒢.Pts τ` (anTop) Serre's structure sheaf directly: `AnHolAt h q` =
  near q, h = H(s_1,…,s_m) with s_j regular functions of 𝒢 at q and H holomorphic near (s_j(q))
  (GAGA §2 / SGA 1 XII 1.1 reduced structure sheaf; same generators as `anTop`). Not built from étale coordinates.
- `IsSerreChart φ`: φ is an isomorphism of ringed spaces onto an open of ℂ^g (stalkwise:
  AnHolAt h q ↔ h ∘ φ⁻¹ holomorphic near φ q).
- Target: `IsHolChart φ ↔ IsSerreChart φ` (with T35, as all consumers already use).
- Core glue identified: left translation by a complex point is holomorphic for Serre's sheaf (TranslationAnHol);
  IsHolChart's translated coordinates F(q⁻¹·) need it in both directions.
