# A trace-one cycle at a place above two

At a chosen finite place above 2, Lean proves that the project's oriented integral trace induces an isomorphism from degree-two cohomology of the restricted line to the 2-adic integers. The theorem retains the number-field, elliptic-curve, full two-power torsion and completion assumptions in Jack's statement. It removes the need for `MilneFiniteDegreeBoundPrint` in this degree-two argument. [Jack's requested statement](https://github.com/Deicyde/diophantine-z-q/issues/83#issuecomment-7015529366) · [Lean theorem](https://github.com/CheyLoveday/diophantine-z-q/blob/f580c857e04e395d950654585d2e53d8b39453eb/ZInQKernel/Contrib/RC53Assist/PlaceAboveTwo/TraceOne.lean#L187-L193) · [Exact type checked by Lean](ProofCheck.lean)

## Proof and scope

The project already proves that a closed degree-two cochain has trace zero exactly when it is a boundary. For surjectivity, the new proof chooses the Brauer class of invariant 1 at every finite level. It corrects successive cochain representatives by coboundaries so that they reduce to each other exactly. They give an integral closed cochain whose trace reduces to 1 at every level. Its integral trace is therefore 1. Transport along the project's oriented coefficient isomorphism gives a witness for its existing `orientedLocalTrace`. Scalar multiples then realize every 2-adic integer. [Construction](https://github.com/CheyLoveday/diophantine-z-q/blob/f580c857e04e395d950654585d2e53d8b39453eb/ZInQKernel/Contrib/RC53Assist/PlaceAboveTwo/TraceOne.lean) · [Project's kernel theorem](https://github.com/Deicyde/diophantine-z-q/blob/e2cf301cfde710497612c10e13837851838d4454/ZInQKernel/Contrib/RC53Assist/DKLocalAdapter/Adapter.lean#L1045-L1075)

The companion file ports the mod-two sign-line invariant, cochain trace and degree-zero/degree-two pairing from Chey Loveday's draft #4. It identifies the sign class with its finite Kummer image. The first reduction of the new trace-one cycle agrees with this normalized sign class. These two source files are the entire proof diff against Jack's stack. [Sign-line comparison](https://github.com/CheyLoveday/diophantine-z-q/blob/f580c857e04e395d950654585d2e53d8b39453eb/ZInQKernel/Contrib/RC53Assist/PlaceAboveTwo/SignLine.lean) · [Source draft #4](https://github.com/CheyLoveday/diophantine-z-q/pull/4) · [Jack's invitation and requested location](https://github.com/Deicyde/diophantine-z-q/issues/83#issuecomment-7015365311)

## Hosted results on 19–20 November 2026

odProof ran the project's pinned Lean on Modal, on x86-64 Linux. The checks bound the two proof files and the scratch inputs to their hashes. The original and refreshed #144 commits have different coverage. [Machine-readable results and commands](result.json)

| Source | Checks that passed |
| --- | --- |
| [Proof `f580c857`](https://github.com/CheyLoveday/diophantine-z-q/commit/f580c857e04e395d950654585d2e53d8b39453eb) on [#144 base `e2cf301c`](https://github.com/Deicyde/diophantine-z-q/commit/e2cf301cfde710497612c10e13837851838d4454) | Lake built the named trace module, `OneProof.Main` and `OneProof.Discharges`. The final build reported 16,975 jobs, including reused results. The original scratch file passed the literal theorem, all ten named axiom queries and the project reporter. Both full commands exited 0. |
| [Integration `1742527c`](https://github.com/CheyLoveday/diophantine-z-q/commit/1742527c7d4e0217f8fd278588f334787ff59efc) on [refreshed #144 base `ddf572d4`](https://github.com/Deicyde/diophantine-z-q/commit/ddf572d40d932c66b98e296454d6268e9caed383) | All 1,982 project modules in the trace target's source import graph and the dependency pins were identical. Lake confirmed the cache was current and the ordinary trace-target build passed using those outputs. Lean freshly checked the focused literal example and ten axiom queries. The axiom output was byte-identical. The full board build and reporter were run on the first row only. |

All ten declarations depend on exactly `propext`, `Classical.choice` and `Quot.sound`. The new modules emitted six warnings about three imports, two local-instance declarations and one unused `simp` argument. The project reporter checked 22,767 theorems against 33 open hypotheses and listed 345 matching theorems. It selects imported candidates under `ZInQKernel.Contrib.OneProof`. Our two files are under `RC53Assist.PlaceAboveTwo`. Their evidence is the explicit build, typed example and by-name axiom audit. Project board matches credited to these files were zero. [Exact axiom output](axioms.txt) · [Complete board output](discharges.txt) · [Reporter implementation](https://github.com/Deicyde/diophantine-z-q/blob/e2cf301cfde710497612c10e13837851838d4454/ZInQKernel/OneProof/Discharges.lean#L79-L88)

Independent mathematical review, a protected statement comparator and the odProof six-checker replay remain open on these heads. The hosted checks here use the project's native Lean compiler and kernel. Earlier replay evidence for Chey's #4 concerns different source.

Chey Loveday contributed the source. OpenAI Codex drafted the port and tower proof, reviewed the source, and used the odProof chat for the proof repair and hosted checks. This verification record lives on a separate branch of Chey's fork. Reviewers can compare the two Lean files directly against Jack's refreshed stack. [Two-file review diff](https://github.com/CheyLoveday/diophantine-z-q/compare/ddf572d40d932c66b98e296454d6268e9caed383...1742527c7d4e0217f8fd278588f334787ff59efc)

## Reproduction and evidence

Use the project root at `f580c857e04e395d950654585d2e53d8b39453eb` in a hosted checkout with the pinned dependencies. Place the exact `ProofCheck.lean` beside the root Lake file. Lean was 4.35.0 at `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Lake was `5.0.0-src+eb6cafb`, and Mathlib was `56a005855ea17e0b0958f73ec801ae140b0a1679`. [Full scratch](ProofCheck.lean) · [Focused scratch](TraceOneProofCheck.lean) · [Compressed full build output](build.log.gz) · [Compressed focused build output](focused-build.log.gz)

```sh
/opt/lean/bin/lake --offline --no-cache --fail-fast build \
  +ZInQKernel.Contrib.RC53Assist.PlaceAboveTwo.TraceOne \
  +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
/opt/lean/bin/lake --offline --no-cache env lean ProofCheck.lean
```

| Input or output | SHA-256 of the original bytes |
| --- | --- |
| `SignLine.lean` | `792037d616e007ebbf5d8f4e4d8417d5d71d58836c1178d15afe405423bce4be` |
| `TraceOne.lean` | `47392d13ea94dcc96f6b769df27f155833917eb9e35a04c92cd531673581da0b` |
| `ProofCheck.lean` | `75d9d1eca3a0ab12bba24643edc0f67aa56a715f6eb15315dc2e9eb9d19d9270` |
| `TraceOneProofCheck.lean` | `a38b62ad449102e4931d305c01f69a8613587e5e904f766f402812b05f9996d4` |
| Full build standard output, after decompression | `3fd896c9d84f9f08efe21f7335ba2288894f418b24c5761f54b8ab9e424c8d83` |
| Full scratch and board output | `9d420af0e475b79f30379222013ec5884d570e4b14ad93e8b09e6b19616ad437` |
| Focused build standard output, after decompression | `98286528eb468fb95a72c9833dd5c38c0525e4ce6bf02e8bb10b4a6bb54dcb5d` |
| Focused scratch and axiom output on both heads | `3f0929e75b52a4932863a868a59f5e03fc4d5b5421f632ca69bd5d9974f41812` |

The initial proof and first rewrite reached Lean's default heartbeat limit in a private finite-class transition. The passing proof separates compatibility with transition from the normalization calculation. The public statements and default heartbeat limit were preserved. [Passing proof repair](https://github.com/CheyLoveday/diophantine-z-q/commit/f580c857e04e395d950654585d2e53d8b39453eb)

The wider project's `OneProof.H.TailX` import also exposed a Linux mapping limit. The continuation worker raised its guest `vm.max_map_count` from 65,530 to 1,048,576. The same target passed with 67,338 mappings observed. The final full build then passed. A 2,541-module checkpoint stayed on the hosted service. Both Modal workers have stopped. [Pinned Lean module loader](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/library/module.cpp#L533-L563) · [Related FLT build report](https://github.com/anthropics/fermats-last-theorem/issues/10)

## Next mathematical step

The integral result supplies the degree-two input to `canonicalLocalTrace_top` at the selected place. In the same file, degree-three exactness still has its own Milne hypothesis. Jack's updated stack changes `OneProof.Main`, and #150 advances the common-coordinate calculation on the genuine Selmer complexes. Jack's issue update also withdraws a paired-side inverse at finite stages. Our result concerns the coefficient trace. Global calibration, the integral determinant bases and assembly of `RestrictedConverseGenuine` remain separate project work. [Integral uses in Jack's source](https://github.com/Deicyde/diophantine-z-q/blob/e2cf301cfde710497612c10e13837851838d4454/ZInQKernel/Contrib/RC53Assist/DKLocalAdapter/LocalTraceTransport.lean#L297-L320) · [Jack's stack update](https://github.com/Deicyde/diophantine-z-q/issues/83#issuecomment-7025162233) · [Common-coordinate PR](https://github.com/Deicyde/diophantine-z-q/pull/150)

The next local proof target is precision one at a place above 2. Here `Acoef 1 = (ℤ/2)[X]/(X)` is isomorphic to `ℤ/2`. The missing comparison must identify the Galois action and differential on the actual `localCx` used by `centralLocalPerf`, then transport the sign-line trace to that complex. A completed application would supply the trace `trv`, its vanishing on boundaries `htrv`, and `InducesIsoH2 trv` as `htrv2`, while retaining the consumer's other hypotheses. Higher precisions include nonconstant polynomial coefficients and require further work. [Finite-stage consumer and its arguments](https://github.com/Deicyde/diophantine-z-q/blob/e2cf301cfde710497612c10e13837851838d4454/ZInQKernel/Contrib/RC53Assist/IntegralDuality/CentralLocalFit.lean#L158-L175)
