# Strict determinant bridge research packet

The ordinary proof in [DERIVATION.md](DERIVATION.md) identifies the actual
class-functional determinant coordinate with the frozen matrix coordinate
times the reciprocal of the **same possibly nonunit strict determinant
factor**. Its hypotheses refer to the actual two integral triangles, boundary
maps, classes and quotient functionals. It gives a source-to-coordinate bridge;
the arithmetic boundary–cup and orthogonal-localization premises remain the
parallel packets' work.

This packet is separate from the frozen 39-target Lean packet. It adds no
new Lean determinant-functor formalization. The underlying cofactor/frame
algebra is already proved in the frozen source and is reused with its exact
convention. [APPLICATION.md](APPLICATION.md) records scope and outstanding
arithmetic interfaces; [SOURCES.json](SOURCES.json) binds the sources read.

Run focused exact checks:

```sh
python3 -B research/strict-determinant-bridge/check_bridge.py
```

The saved [computational result](evidence/checks.json) records positive checks,
explicit failing controls and hashes. Finite algebra checks do not prove a
Selmer/Poitou–Tate application. Independent review status is recorded by the
parent integration packet; the author does not self-approve this proof.
