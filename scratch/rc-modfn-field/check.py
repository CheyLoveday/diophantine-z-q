import os
import subprocess
import sys

up = subprocess.check_output(["uptime"], text=True).strip()
mem = subprocess.check_output(["free", "-g"], text=True).strip()
print(up, mem, sep="\n", flush=True)
load = float(up.split("load average:")[1].split(",")[0])
available = int(next(line for line in mem.splitlines() if line.startswith("Mem:")).split()[-1])
if load > 120 or available < 20:
    raise SystemExit("Host resource limit reached")
os.execvp("lake", ["lake", "env", "lean", "-j1", "-DautoImplicit=false", *sys.argv[1:]])
