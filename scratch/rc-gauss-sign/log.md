# Results

- Base: `2fa2bb6fa4378ac1c5312fd87550d6e820601336`.
- The inherited `quadraticSum_eq_gaussSum`, `oddGauss_sq`, and `oddGauss_twist` supply the bridge, square, and unit twist.
- Route (iii), cyclotomic congruence (c): compare the first relevant coefficients after shifting the variable by one and reducing modulo the odd prime.
- `Congruence.lean`: the translated degree-m coefficients agree after scaling by m! (both −1), and a polynomial vanishing at the primitive root has zero coefficient there modulo p. Therefore equality of squares implies equality of evaluations.
- `Congruence.lean`: passed `lake env lean`; 9 theorem audits, only `propext`, `Classical.choice`, `Quot.sound`.
