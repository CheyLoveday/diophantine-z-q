# coeff-ext results log

Base origin/main 2880fef1. Build copied from ~/dzq-check2 (same commit) 2026-11-16 06:40.

## Targets (copied verbatim)
- `DS965Weak.DSThm965Weak` (ZInQKernel/Contrib/OneProof/DSThm965Weak.lean l.56), bundle field
  `HDec.HSyn.OpenResearchLeaves26.dsThm965Weak` (TailZ41.lean l.67).
- `ZInQ.Contrib.HodgeSplit.DSThm966` (TailS.lean l.1128), field `OpenResearchLeaves26.dsThm966` (TailZ41 l.22).

## Plan (leaves)
- L1 DS 9.6.5 over K_{f,λ} = `λ.adicCompletion (coeffField f)`, DS-form eigenform (Tau Ceti `HeckeRing.GL2.Eigenform`,
  DS Def 5.8.1), hypothesis `NumberField (coeffField f)`.
- L2 `K_f` is a number field (needed: L1's statement presupposes it; DSThm965Weak quantifies over all g).
- L3 DSThm966 with DS-form eigenform, locator Deligne-Serre 1974 Thm 4.1.
- Glue: coefficient form -> DS form (U_p part for p | N); K_f -> ℚ̄_ℓ via ιL∘ιC⁻¹, λ from the norm, continuous
  extension to K_{f,λ} (completion), charpoly_map.

## Findings / compile outcomes
