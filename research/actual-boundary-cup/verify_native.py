#!/usr/bin/env python3
"""Native Lean4.35 check of the new cochain-correction module only."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
PROJECT=ROOT/"lean"
PACKET=Path(__file__).resolve().parent
TARGETS=["closed_cup_differential","pure_boundary_correction","traced_pure_boundary","traced_left_boundary","traced_right_boundary","traced_change_left","traced_change_right"]
NS="Research.DerivativeSwitch.ActualBoundaryCup."
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    if len(sys.argv)!=2:raise SystemExit("usage: verify_native.py NEW_OUTPUT_DIRECTORY")
    out=Path(sys.argv[1]).resolve();out.mkdir(parents=True,exist_ok=False)
    lib=out/"lib";dest=lib/"Research/DerivativeSwitch";dest.mkdir(parents=True)
    src=PROJECT/"Research/DerivativeSwitch/ActualBoundaryCup.lean"
    inputs=[src,Path(__file__),PACKET/"DERIVATION.md",PACKET/"SOURCES.json",PACKET/"check_cochains.py",PROJECT/"lean-toolchain",PROJECT/"lakefile.toml",PROJECT/"lake-manifest.json"]
    before={str(p.relative_to(ROOT)):sha(p) for p in inputs}
    commands=[]
    def run(label,args,env=None):
        r=subprocess.run(args,cwd=PROJECT,env=env,capture_output=True)
        (out/(label+".stdout.txt")).write_bytes(r.stdout);(out/(label+".stderr.txt")).write_bytes(r.stderr)
        commands.append({"label":label,"command":args,"cwd":str(PROJECT),"exit_code":r.returncode})
        (out/"commands.json").write_text(json.dumps(commands,indent=2)+"\n")
        if r.returncode:raise RuntimeError(label+" failed")
        return r.stdout.decode()
    version=run("lean-version",["lean","--version"])
    if "version 4.35.0," not in version or "eb6cafb" not in version:raise RuntimeError("Lean version mismatch")
    deps=[];libraries=[]
    for package in json.loads((PROJECT/"lake-manifest.json").read_text())["packages"]:
        path=PROJECT/".lake/packages"/package["name"]
        rev=subprocess.check_output(["git","-C",str(path),"rev-parse","HEAD"],text=True).strip()
        if rev!=package["rev"]:raise RuntimeError("Dependency mismatch")
        subprocess.run(["git","-C",str(path),"diff","--quiet","HEAD","--"],check=True)
        deps.append({"name":package["name"],"revision":rev})
        folder=path/".lake/build/lib/lean"
        if folder.exists():libraries.append(folder)
    env=os.environ.copy();env.pop("LEAN_SRC_PATH",None);env["LEAN_PATH"]=os.pathsep.join(map(str,[lib,*libraries]))
    base=["lean","-j1","-Ddebug.skipKernelTC=false"]
    run("ActualBoundaryCup",base+["-o",str(dest/"ActualBoundaryCup.olean"),str(src.relative_to(PROJECT))],env)
    audit=out/"Audit.lean"
    audit.write_text("\n".join(["import Research.DerivativeSwitch.ActualBoundaryCup","import Lean.Util.CollectAxioms","set_option pp.explicit true", "#print "+NS+"LocalCupData", *["#print "+NS+n for n in TARGETS],"open Lean Elab Command in","run_cmd do","  let names : Array Name := #["+", ".join("`"+NS+n for n in TARGETS)+"]","  for name in names do","    let axioms ← collectAxioms name","    for ax in axioms do","      unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do",'        throwError "Unexpected axiom {ax} in {name}"','    logInfo m!"AXIOM_CHECK {name}: {axioms.toList}"', '  logInfo "AXIOM_AUDIT_PASS declarations=7"',""]))
    printed=run("axioms-and-statements",base+[str(audit)],env)
    if "AXIOM_AUDIT_PASS declarations=7" not in printed:raise RuntimeError("Audit marker absent")
    after={str(p.relative_to(ROOT)):sha(p) for p in inputs}
    if before!=after:raise RuntimeError("Input drift")
    result={"status":"PASS","scope":"native new module only; no paranoid or external replay","input_hashes":before,"input_hashes_unchanged":True,"lean_version":version.strip(),"dependencies":deps,"theorem_roots":[NS+n for n in TARGETS],"allowed_axioms":["propext","Quot.sound","Classical.choice"],"artifact_sha256":sha(dest/"ActualBoundaryCup.olean"),"cached_imports":"Pinned Mathlib cache; not a full dependency source rebuild"}
    (out/"RESULT.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"status":"PASS","theorems":7,"source_sha256":sha(src),"result":str(out/"RESULT.json")}))
if __name__=="__main__":main()
