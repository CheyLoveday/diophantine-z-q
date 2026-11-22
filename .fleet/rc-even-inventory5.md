# Even inventory finite Whittaker evaluations and ramified stop

`PlacedCuspLists.dilationWhittakerAt_of_forms` supplies the finite
Whittaker values for every retained cuspidal column at a tested prime.
It computes the normalized horizontal Fourier integral of the actual
classical slash and transports the value $a_n/n$ through the row
embedding. The local matrix calculation checks the level corrections
at the tested and away primes. The report gives the fundamental-domain
argument identifying the horizontal formula with the adelic integral.

The remaining per-set GLUE is `PlacedCuspLists.RamifiedLocalModelAt`.
It asks for the local factor on the exact attached matrices of each
intrinsically ramified source and the individual translated Whittaker
values when its undilated column is retained. Conditional on that data,
Lean computes the line scalar as the placed coefficient at the tested
prime. It also proves that both endpoint coefficients vanish at the
other retained degrees. The unitary square roots can be adjoined in one
receiving field for the tested set over the fixed place.

Three new modules compile and the audit covers 37 declarations with
only `propext`, `Classical.choice` and `Quot.sound`. The printed leaf
and provider counts are unchanged. The inherited error at tex
8162–8167 is the missing base factor. The proofs use tex 8168–8182.
[Research report](../docs/research/rc-even-inventory5.md) ·
[Axioms output](../scratch/rc-even-inventory5/axioms.txt)
