# h33-d1 log

- 11-17 01:10 start; merged 92fd272e (hgz-steps) cleanly into wip/h33-d1 (943889a87).
- Plan (design decision): new leaf `ZInQ.H33D1.TYZThm33Curve` over integral proper `X/ℚ` with
  `ι : K(X) ≃ X0Field 32` and an ISOMORPHISM of schemes `i₀ : X ⟶ ESch curveA` over ℚ with `i₀(∞) ∉ D₊(Z)`,
  CM points as ℂ-points `IsPointAt 32 ι τ_n`, values `GZSch.ptOf curveA (x ≫ i₀)`. Normality/dim of X omitted:
  `X ≅ A` forces X to be the smooth projective curve with function field ℚ(X₀(32)), i.e. the canonical model
  (reading, Hartshorne I.6.12, UNVERIFIED number).
- Bridge strategy: X := ESch curveA, i₀ := 𝟙, ι := φ ∘ ffEquiv. Avoids valuative extension and normality of
  ESch (the valuative-extension route needs ESch curveA normal over ℚ to invert π; Dedekind property of
  ℚ[x,y]/(W) is vendored only over algebraically closed fields). Needs: ESch integral, K(ESch) ≅ ℚ(E) via
  chart D₊(Z), values at ℂ-points via charts D₊(Z), D₊(Y) (Z/Y = 1/y vanishes at O).
