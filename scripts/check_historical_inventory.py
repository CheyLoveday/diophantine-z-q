"""Run an unchanged historical inventory after the manuscript-file relocation.

Only physical file lookup changes. The frozen acceptance records, manuscript
bytes, source hashes, logical paths and inventory validators remain unchanged.
"""
import importlib.util
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
MANUSCRIPTS = {'quartic_12504.tex', 'quartic_9625.tex', 'quartic_4973.tex', 'quartic_1272.tex'}

def physical(root, name):
    if name in MANUSCRIPTS and not (Path(root)/name).exists():
        return 'manuscripts/archive/'+name
    return name

def main():
    if len(sys.argv)<2 or sys.argv[1] not in ('4','5'):
        raise SystemExit('Usage: check_historical_inventory.py {4|5} [inventory arguments]')
    version = sys.argv.pop(1)
    directory = ROOT/'docs'/('quartic-4973' if version=='4' else 'quartic-1272')
    sys.path.insert(0,str(directory))
    spec=importlib.util.spec_from_file_location('historical_inventory',directory/'inventory.py')
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    if version=='4':
        original=module.c.inside
        module.c.inside=lambda root,name: original(root,physical(root,name))
    else:
        original=module.read
        module.read=lambda root,name: original(root,physical(root,name))
    module.main()

if __name__=='__main__': main()
