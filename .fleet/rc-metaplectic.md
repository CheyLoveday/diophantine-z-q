# rc-metaplectic

Implementation and report SHA: `edbe87b16f5aefba74aee00f03dc8642886e555d`.
The final SHA is the commit adding this handoff; read it with
`git log -1 --format=%H -- .fleet/rc-metaplectic.md`.

At every finite place, including two, the upper unipotent and Weyl
operators are complex-linear endomorphisms of the Schwartz–Bruhat space
for the nondegenerate rectangular ternary form. They use the inherited
local character, determinant-scaled Haar measure, and actual ternary
index from `gaussGamma`. The elementary coset equations supply exactly
the two local evaluations in `GeneratorTensorAction`. The Weyl square is
`γ_p(Q)² * f(−x)` on the full local space. The proof uses reciprocal Haar
masses of polar dual rectangles and the span of their translated indicators.

All three files in `ZInQKernel/Contrib/OneProof/RC/Metaplectic/` compile.
The 33 theorem audits use only `propext`, `Classical.choice`, and
`Quot.sound`. No printed input was added.

The remaining inputs are the local operator relations and common
double cover, the restricted tensor action with good-prime spherical
vectors, and the common inverse lifts on the two rectangular spaces.
The scalar product formula is already available for `gaussGamma`.
The exact stop and manuscript check are in
`docs/research/rc-metaplectic.md`; verification outcomes are in
`scratch/rc-metaplectic/log.md`.
