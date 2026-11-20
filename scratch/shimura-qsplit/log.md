# Results

- Base: `eb89a3638bf12b15ecc0f0de35262fc9d7a523dd`; merged `2106f37c5707a8a2fa53c01ecf93c997b40014aa` at `50254e3b058ef8c8ed97c36a99f62f1c173a55e9`.
- Requested print: `ShimuraThm1AsPrinted` minus the `PrintQuotient` conjunct. No declaration.
- Requested construction: same binders through `XiAction`; `PrintedClauses ξ f ν θ → PrintQuotient ξ f ν` for every triple. Rejected.
- Evidence: `XiAction` and `PrintedClauses` ignore `ξ 0`; `printRing` includes it. With `ξ 0 = 1`, `ak f 0 = 0` gives `(1, 0)` in the ring. `PrintQuotient` forces `ν = 0`, contrary to surjectivity onto the printed positive-dimensional `A`.
- Existing `ShimuraThm1AsPrinted`: same unrestricted index; reconstruction has the same obstruction.
- Verdict commit: `0c22a1eb0f229ae8dd10f4ee90a1d3cacd9393bd`.
- New definitions, theorems, imports: none (stop rule).
- Lake build, axiom scan, focused `#discharges`: not run; no split module to check.
