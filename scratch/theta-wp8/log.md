# theta-wp8 results log

## 2026-11-15 setup
- Merged origin/wip/jacobi-lambda (b6fc38e9) and origin/wip/gz-heegner (58a780e4) into wip/theta-wp8: clean.
- Target: `X0EtaRoute.ThetaWeierstrass8` (ZInQKernel/Contrib/OneProof/X0ModuliUsed/EtaRoute.lean:919).

## Proof plan (VERIFIED numerically, scratch/theta-wp8/num/check.py, 4 random w, err < 1e-38)
Notation: ϑ(z) = jacobiTheta₂ z w, s(z) = ϑ(z + (1+w)/2) (zeros exactly Λ = ⟨1,w⟩), c = 1/2 + w/8.
- (P1, Liouville) h(u) = (℘(u) − ℘(c))·s(u)²/(s(u−c)s(u+c)) is exactly 1- and w-periodic, meromorphic
  with order ≥ 0 everywhere, order 0 at u = 0; so h ≡ K ≠ 0 off its singular set.
- Hence wpRatio(1/2, 3w/8, c) = R := s(a−c)s(a+c)s(b)²/(s(a)²s(b−c)s(b+c))
  = ϑ(1/2+3w/8)ϑ(1/2+5w/8)ϑ(1/2+7w/8)²/(ϑ(w/2)²ϑ(3w/4)ϑ(w)).
- (P3, series split) θ₃(w) − θ₂(w) = θ₄(w/4), i.e. ϑ(0) − e^{πiw/4}ϑ(w/2) = jacobiTheta₂ (1/2) (w/4).
- (P2+P4, triple product, Q = e^{πiw/8}) θ₃/θ₂ = 1 − 2R reduces to products ∏(1 ± Q^{16n+k}) and
  the even/odd product split.
