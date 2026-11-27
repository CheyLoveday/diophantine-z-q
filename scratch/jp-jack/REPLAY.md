From the repository root, with the imported modules built at the report's base:

```sh
python3 scratch/jp-jack/gen_bypass.py > scratch/jp-jack/DryRun.lean
python3 scratch/jp-jack/gen_bypass.py --counts
lake env lean scratch/jp-jack/CheckJacK.lean
lake env lean scratch/jp-jack/CheckReader.lean
lake env lean scratch/jp-jack/CheckJacKEx.lean
lake env lean scratch/jp-jack/DryRun.lean
```

Check host load and available memory before each Lean command and run them
one at a time. The generator appends the closure check to the dry run so it
can inspect the old and proposed tops in the same environment. It writes no
production file. The count command checks the current research and added
fields against the board before simulating the one-row swap.
