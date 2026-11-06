# Version 6 research handoffs

The Version 6 handoff contains the 962-coordinate quartic, its source and certificates, the optimization history, lower-bound audit, analytic proof work, and independent reviews. Earlier quartics and the original construction remain at their existing repository paths.

The release tag is `quartic-962-version-6`.

| Archive | Contents |
| --- | --- |
| `z-in-q-version6-current-handoff.zip` | Complete recorded public Git snapshot and current orientation notes |
| `z-in-q-version6-full-handoff.zip` | The same collection plus the unchanged Version 5 full archive |

The source inventory and final independent reviews are bound to the manuscript and authored register. Archive builds require a `READY` descriptor and a complete immutable Git commit. The release checksums and build receipt identify the resulting archives; this guide alone does not identify archive bytes.

Compare the archive checksum with the release checksum, then run:

```sh
python -E -B handoff/verify_handoff.py ARCHIVE.zip --expected-archive-sha256 ARCHIVE_SHA --expected-plan-sha256 PLAN_SHA
```

Add `--extract NEW_DIRECTORY` to extract only after verification. The verifier checks every archive member, exact planned file coverage, the complete frozen package and research inventory, reproduction receipt, and historical preservation pins.

The snapshot is under `current/`. Start with `current/quartic_962.pdf`, `current/docs/quartic-962/README.md`, and the frozen package. The portable replay entrypoint is `current/scripts/check_quartic962.py`. [replay_extracted_current.py](replay_extracted_current.py) authenticates a current-only archive and runs its checks with outputs outside the snapshot.

The unchanged Version 5 full archive has 382,435,413 bytes and SHA-256 `8bca6f77f4721140c3d9db0d518595472a463a58f04f3efcf14173a9cf0ff236`. Its own nested revision-2 archive, source inventory and verification tools remain intact. Each historical `current/` directory describes its own release date. Previous handoff tools and notes remain under [releases/version5](releases/version5/), with earlier records at their existing paths.

Contributors: Stefan Baranczuk, Jose Brox, Gabe Conant, Sohail Farhangi, James Freitag, Elliot Glazer, Jennifer Park, and Caroline Terry.

Archive integrity, finite computational checks and mathematical source review have separate scopes. The main Lean theorem remains unproved. See [BUILDING.md](BUILDING.md) for the build sequence and [SCOPE.md](SCOPE.md) for the selection policy.
