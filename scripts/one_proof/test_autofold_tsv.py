"""Unit tests of autofold.py's table writing: a row the fold keeps is written back byte for byte, so a cell with a
double quote in its middle (hCT's flag quotes the owner's ruling) is not re-serialized with csv quoting.

Run from the repository root: python3 -I scripts/one_proof/test_autofold_tsv.py   (or pytest)
"""
import csv, os, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import autofold  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(HERE))
KINDS = os.path.join(ROOT, autofold.KINDS)
CLAIMS = os.path.join(ROOT, autofold.CLAIMS)


def raw_bytes(path):
    with open(path, 'rb') as fh:
        return fh.read()


class RoundTrip(unittest.TestCase):
    def rewrite(self, path, keep=lambda r: True, add=(), quoting=csv.QUOTE_MINIMAL):
        head, cols, rows, raw = autofold.read_tsv_raw(path, quoting=quoting)
        kept = [r for r in rows if keep(r)] + list(add)
        with tempfile.TemporaryDirectory() as d:
            out = os.path.join(d, 't.tsv')
            autofold.write_tsv_raw(out, head, cols, kept, {id(r): t for r, t in zip(rows, raw)}, quoting=quoting)
            return raw_bytes(out)

    def test_kinds_unchanged_is_identical(self):
        self.assertEqual(self.rewrite(KINDS), raw_bytes(KINDS))

    def test_claims_unchanged_is_identical(self):
        self.assertEqual(self.rewrite(CLAIMS, quoting=csv.QUOTE_NONE), raw_bytes(CLAIMS))

    def test_hct_row_survives_a_fold_byte_for_byte(self):
        lines = raw_bytes(KINDS).decode().splitlines(keepends=True)
        hct = [l for l in lines if l.startswith('frozenTarget\thCT\t')]
        self.assertEqual(len(hct), 1)
        self.assertIn('"', hct[0].split('\t')[3][1:])  # a quote in the middle of the flag: the case that broke
        victim = next(l.split('\t')[1] for l in lines[1:] if l.split('\t')[1] != 'hCT')
        out = self.rewrite(KINDS, keep=lambda r: r['field'] != victim).decode()
        self.assertEqual(out, ''.join(l for l in lines if l.split('\t')[1:2] != [victim]))
        self.assertIn(hct[0], out)

    def test_new_row_is_read_back_by_render_open(self):
        with tempfile.TemporaryDirectory() as d:
            src = os.path.join(d, 'k.tsv')
            with open(src, 'w', newline='') as fh:
                fh.write('bundle\tfield\tflag\n'
                         'research\tmid\tsaid "glue until read" here\n'
                         'research\tquoted\t"p. 1: ""x""\nsecond line"\n'
                         'research\tgone\tplain\n')
            head, cols, rows, raw = autofold.read_tsv_raw(src)
            self.assertEqual(rows[1]['flag'], 'p. 1: "x"\nsecond line')
            new = dict(bundle='research', field='leaf', flag='"starts with a quote')
            kept = [r for r in rows if r['field'] != 'gone'] + [new]
            out = os.path.join(d, 'o.tsv')
            autofold.write_tsv_raw(out, head, cols, kept, {id(r): t for r, t in zip(rows, raw)})
            with open(out, newline='') as fh:
                text = fh.read()
            self.assertTrue(text.startswith(head + raw[0] + raw[1]))
            back = autofold.render_open.read_tsv(out, quoting=csv.QUOTE_MINIMAL)
            self.assertEqual([r['flag'] for r in back], [rows[0]['flag'], rows[1]['flag'], new['flag']])


if __name__ == '__main__':
    unittest.main()
