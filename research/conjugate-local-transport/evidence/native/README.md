# Native verification scope

`RESULT.json` records a fresh build of the two new modules on macOS with
Lean 4.35.0, `-j1 -Ddebug.skipKernelTC=false`, followed by transitive axiom
auditing of every theorem declared in those modules. All 27 roots passed;
only `propext`, `Quot.sound` and `Classical.choice` were permitted.

The exact commands, stdout, stderr, audit source, dependency revisions and
before/after input hashes are retained here. The printed definitions and
statements make the actual representation and H¹ carriers inspectable.
Compiled `.olean` hashes are recorded; those development artifacts remain
in the local output directory and are not published by this packet.

The imports use pinned official Mathlib master-cache artifacts. A successful
native check is not an independent import rebuild or protected comparator
run. No paranoid run, proof export or external-kernel result is claimed for
these new modules. The separately recorded Open Math run covers the unchanged
39-target foundation only.

Four math-delimiter errors in the prose derivation were corrected after this
run. The run's exact input bytes are retained as `DERIVATION.input.txt`;
`../EDITORIAL_BINDING.json` binds the correction and unchanged proof sources.
The native result is preserved verbatim. The final source review covers the
corrected prose; no new Lean run is claimed for that editorial change.
