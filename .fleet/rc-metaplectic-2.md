# rc-metaplectic-2

Implementation, report, and results SHA: `35db42a7df9f96b145d2e3a28403797f2118d169`.
The final handoff SHA is the commit adding this file; resolve it with
`git log -1 --format=%H -- .fleet/rc-metaplectic-2.md`.

The rectangular local development defines the normalized diagonal operators
and gives the Fourier sandwich and projective SL₂ action at every finite
prime. The Weyl–upper cube has the same sign for every form: `-1` at two,
`1` elsewhere. At a good odd prime the standard lattice vector is spherical
for the integral group. The two inverse generators are evaluated on the
finite restricted tensor as products of their actual local actions; both
`GeneratorTensorAction` cylinder tests are present for each form on its
separate operator group.

The new pullback construction realizes the common cover and computes its
two-element central kernel once the actual scalar defects lie in the
diagonal sign subgroup. The remaining work is to prove those three signed
scalar identities, use the good-prime sections to assemble and quotient
the finite restricted product, and restrict the common lifts to the two
rectangular images. The global index product formula is already available.
No new printed input.

`Matrices`, `NormalForm`, `Presentation`, and `CentralCover` passed
`lake env lean`, with 17 axiom audits in the allowed set. The other 11
checks stopped at missing dependency objects. The initial verification
briefly overlapped two Lean processes, violating the run limit; the
passing checks were repeated serially. See
`docs/research/rc-metaplectic-2.md` for the exact stop and manuscript
check and `scratch/rc-metaplectic-2/log.md` for the file outcomes.
