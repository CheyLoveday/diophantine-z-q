**Manuscript support slip (tex 10393–10404).** The zero branch of (G.4b)
uses the full stationary support of the transported source (before adding
the tested prime), including new sieve primes. The shell argument cannot
use only the support of the source before transport. The seed proof uses
the determinant identity at tex 10375–10386 instead.

**Scoped stop.** `kSplitSeed_of_singleton_trace` produces the App G seed
implication for the same `RevGen S G.r`. The attained value at index 1
gives the empty reading. To get a nonempty reading, the proof reduces the
no-seed case to the mod-eight contradiction using the actual singleton
coefficients. The fresh-prime lemma proves the required match once the
scalar at `p²` is known to descend modulo integer two and satisfy the good
Hecke formula. The even and odd density conversions use a finite field
for each tested prime set; the odd construction works eventually on the
original ultrafilter, separately for each cutoff.

**Remaining.** The old unit comparison is an ELLIOT/companion input. The
even budget lane owns the same-source divisions. The weight-two realization
still needs the bad-prime trace and determinant identities on that
singleton and the actual constituent packets with their finite fields for
both parities. The address and budget integrators coordinate the even
modulus with the full stationary support. See
`docs/research/rc-ksplit-seed.md` for the exact hypotheses and tex lines.

**Verified.** All five Lean modules compile serially. The 23 declarations
use only `propext`, `Classical.choice`, and `Quot.sound`. No prints added.

**Final proof and report SHA:** `8a182ead4dd3f4be278670bef38cc4b70addc4a6`.
The final branch SHA is the commit that adds this handoff
(`git log -1 --format=%H -- .fleet/rc-ksplit-seed.md`).
