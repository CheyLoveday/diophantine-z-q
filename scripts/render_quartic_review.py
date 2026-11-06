"""Locate and render changed manuscript pages for visual inspection."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import unicodedata

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--pdf', type=Path, default=ROOT / 'quartic_12504.pdf')
PDF = parser.parse_args().pdf.resolve()
OUT = ROOT / 'build/pdf-review'
OUT.mkdir(parents=True, exist_ok=True)
subprocess.run(['pdftotext', '-layout', str(PDF), str(OUT / 'paper.txt')], check=True)
pages = (OUT / 'paper.txt').read_text(encoding='utf-8').split('\f')
normalized = [re.sub(r'\s+', ' ', unicodedata.normalize('NFKC', text)) for text in pages]
starts = [i for i, text in enumerate(normalized) if i > 10 and 'We now give the second final polynomial' in text]
ends = [i for i, text in enumerate(normalized) if i > 10 and 'The finite source and algebraic checks do not replace' in text]
assert len(starts) == len(ends) == 1, (starts, ends)
last = max(i for i, text in enumerate(normalized) if text.strip())
theta_pages = [i for i, text in enumerate(normalized) if 'We check every theta convolution term' in text]
selected = sorted(set([0, 1, 2, last] + theta_pages + list(range(starts[0], ends[0] + 1))))
for index in selected:
    subprocess.run(['pdftoppm', '-png', '-r', '105', '-singlefile', '-f', str(index + 1),
                    '-l', str(index + 1), str(PDF), str(OUT / f'page-{index + 1:03}')], check=True)
report = {'pages': last + 1, 'changed_quartic_pages': [starts[0] + 1, ends[0] + 1],
          'pdf_sha256': hashlib.sha256(PDF.read_bytes()).hexdigest(),
          'rendered_pages': [i + 1 for i in selected], 'visual_inspection': 'PENDING'}
(OUT / 'rendered.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
