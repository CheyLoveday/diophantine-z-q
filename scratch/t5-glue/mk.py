#!/usr/bin/env python3
"""Assemble T5Glue.lean = kernel imports + Elliptic.lean body + parts/*.lean (in order)."""
import sys, os
here = os.path.dirname(os.path.abspath(__file__))
ell = open(os.path.join(here, 'Elliptic.lean')).read()
# drop the `import Mathlib` line and the module docstring of Elliptic.lean
body = ell.split('\n', 1)[1]
i = body.index('-/') + 2
body = body[i:]
header = open(os.path.join(here, 'parts', 'Header.lean')).read()
parts = ['X0.lean', 'CM.lean', 'Row.lean', 'Footer.lean']
out = header + '\n-- ===== Elliptic.lean body (verbatim) =====\n' + body
for p in parts:
    fp = os.path.join(here, 'parts', p)
    if os.path.exists(fp):
        out += '\n-- ===== parts/' + p + ' =====\n' + open(fp).read()
open(os.path.join(here, 'T5Glue.lean'), 'w').write(out)
print('wrote T5Glue.lean', len(out.splitlines()), 'lines')
