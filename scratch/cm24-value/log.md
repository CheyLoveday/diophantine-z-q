# cm24-value results log

Target: `IgusaCMValue24` (field `igusaCMValue24`), equivalently (qm-glue `thetaQuotientValue24_iff`,
`igusa_of_thetaQuotientValue24`) `ThetaValueAtOmega24`: `jDen Ω₂₄ ≠ 0 ∧ jNum Ω₂₄ / jDen Ω₂₄ = −16/27`.

## Numerics / exact algebra (py/, venv /tmp/cm24venv with mpmath, sympy, cypari2)

* `py/endo.py` (VERIFIED, computed): End(A_{Ω₂₄}) has rank 8; Sp₄(ℤ)-stabilizer elements with entries
  in the search box: ±1 and ±R, R = [[1,0,0,-1],[0,-1,1,0],[0,0,1,0],[0,0,0,-1]] (an extra involution).
  R is block lower triangular in the standard action, so its fixed locus becomes the Humbert-H₄ normal
  form after the inversion Ω ↦ −Ω⁻¹.
* `py/w.py` (VERIFIED, exact sympy): W := −Ω₂₄⁻¹ = [[1 + i√6/2, 1/2], [1/2, 1/2 + i√6/4]].
  So 2W = diag(i√6, i√6/2) + [[2,1],[1,1]].
* `py/split.py`, `py/check2.py` (VERIFIED, 50 digits): F(Ω₂₄) = F(W) = −16/27;
  (1) θ_{(a,b)}(W)² = det(−iΩ₂₄)·θ_{(b,a)}(Ω₂₄)² for all ten even (a,b);
  (2) with genus-1 constants a_j at i√6, b_j at i√6/2 (θ00, θ01, θ10) and
      x = a0²b1², y = −a2²b0², z = i a1²b2², T00 = a0b1, T10 = i a2b0, T01 = e^{πi/4} a1b2:
      θ²[0;00]=x+y+z, θ²[0;10]=x−y+z, θ²[0;01]=x+y−z, θ²[0;11]=x−y−z,
      θ²[10;00]=θ²[10;01]=2T00T10, θ²[01;00]=θ²[01;10]=2T00T01, θ²[11;00]=2T01T10=−θ²[11;11].
  (3) k(i√6) = (2−√3)(√3−√2) (= k₆), k'(i√6/2) = (1−k₆)/(1+k₆) to 30 digits.
* `py/exact2.py` (VERIFIED, exact in ℚ(√2,√3)): with Y = λ(i√6)/λ'(i√6/2),
  Z = −λ'(i√6)λ(i√6/2)/λ'(i√6/2), λ(i√6) = k₆², λ'(i√6/2) = ((1−k₆)/(1+k₆))², λ = 1−λ':
  3779136·4·Y²Z²((Y+Z−1)²−4YZ)² = −(16/27)(Y²+14YZ+14Y+Z²+14Z+1)⁵ exactly.
  So F(Ω₂₄) = −16/27 is an exact consequence of (1), (2) and the disc −24 singular moduli.
