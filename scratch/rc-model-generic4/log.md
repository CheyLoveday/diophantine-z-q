# rc-model-generic4 results log

Base: wip/rc-model-neron 64a338f4 merged with main 29bfbc3f (merge commit 5e02195ad).

## Route for (b1)
- Vendor odd-step function-field hom with place seam:
  `WeierstrassCurve.exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed`.
- Vendor lift to ℂ: `PeriodPair.exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint`.
- No vendored function-field hom for the order-two Vélu step (`veluQuotient2`): only the point map
  `exists_addMonoidHom_coe_eq_veluPointMap2`.
