# Build the Version 6 handoff

Use Python 3.10 or newer, Node.js 18 or newer, and Git. The commands below run from the repository root. All output paths must be new and outside the repository.

Complete the source inventory and independent reviews, copy the successful fourteen-stage reproduction receipt to `handoff/releases/version6/REPRODUCTION.json`, and finalize `handoff/release.json`. The descriptor must be `READY` and bind the complete research selection, manuscript, PDF, package, wrapper, reviews and preserved files. Commit that exact tree before preparing the plan.

Run the packaging tests:

```sh
python -E -B handoff/test_handoff.py
```

Freeze the plan using the full immutable commit ID:

```sh
python -E -B handoff/prepare_handoff.py --repo . --commit FINAL_COMMIT --verification-receipt handoff/releases/version6/REPRODUCTION.json --output ../version6-handoff-plan.json
```

Supply the unchanged Version 5 full archive, with SHA-256 `8bca6f77f4721140c3d9db0d518595472a463a58f04f3efcf14173a9cf0ff236`:

```sh
python -E -B handoff/build_handoff.py --repo . --plan ../version6-handoff-plan.json --baseline ../z-in-q-version5-full-handoff.zip --output ../version6-handoff-output
```

The builder verifies every member of both resulting archives and writes `BUILD_RECEIPT.json` and `SHA256SUMS`. Use their actual plan and current-archive hashes in the authenticated extraction command:

```sh
python -E -B handoff/replay_extracted_current.py ../version6-handoff-output/z-in-q-version6-current-handoff.zip --expected-plan-sha256 PLAN_SHA --expected-archive-sha256 CURRENT_ZIP_SHA --extract ../version6-extracted --replay-output ../version6-replay --report ../version6-handoff-output/EXTRACTED_REPLAY.json
```

Run the source-inventory validator and its adversarial tests from the extracted `current/` tree using the exact commands and source-input hash recorded in `docs/quartic-962/README.md`. Final publication requires all checks to pass. Publishing is a separate action and does not belong to these scripts.

The complete archive hash and final build receipt cannot be committed inside the archive they identify. Record them in the release or a subsequent metadata commit. Never overwrite an earlier version's asset.
