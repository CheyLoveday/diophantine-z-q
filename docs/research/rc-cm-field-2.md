# CM field descent on the normalized modular curve

**Scope correction (verified against the manuscript).** The Lean target quantifies over all imaginary quadratic orders and eligible forms, with a complex embedding chosen per form. Tex 2839–2844 and 2915–2916 concern a field split at (2N), exclude the two fields with extra units, and choose compatible lattices and fixed orientations. The Lean target's discriminant is (f^2D_K); the subscript in the manuscript denotes the conductor. The broader Lean scope is not supported by that passage alone. No counterexample to the Lean target is known here.

**Correction to the proposed branch argument.** The nonvanishing denominator in `X0Branch.exists_analyticJN_ratio` expresses the second plane coordinate in terms of sections on the normalization. Going from the plane pair to the normalization needs expressions in the opposite direction, or a different descent argument.

The pre-build sizing is recorded in [the results log](../../scratch/rc-cm-field-2/log.md).
