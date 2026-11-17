"""Unit tests of the LEAF/GLUE scoring rule (ruling 2026-11-17: unread and unverified rows count as glue).

Run: python3 -I scripts/one_proof/test_scoring.py   (or pytest scripts/one_proof/test_scoring.py)
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import render_open  # noqa: E402


def row(flag, strict='LEAF', strictest='LEAF', kind='published', flag_class='unread'):
    return dict(bundle='research', field='x', kind=kind, flag=flag, strict=strict, strictest=strictest,
                source='', rated_by='', packet='', label='', tier='', flag_class=flag_class,
                area_issue='elliotglazer/diophantine-z-q#1')


def test_unread_published_row_scores_glue():
    assert render_open.must_be_glue('unread: new printed leaf, no reading recorded')
    probs = render_open.kinds_row_problems(row('unread: new printed leaf'), [], set())
    assert any('counts GLUE' in p for p in probs), probs
    assert not [p for p in render_open.kinds_row_problems(row('unread: new printed leaf', 'GLUE', 'GLUE'), [], set())
                if 'counts GLUE' in p]


def test_each_marker():
    for m in ('unread', 'locator UNVERIFIED', 'recalled from memory', 'one model review', 'pending reading: x',
              'pending review (new leaf)'):
        assert render_open.must_be_glue(m), m


def test_read_row_keeps_leaf():
    flag = 'reading 11-17: direct instance of the printed proposition, p. 366'
    assert not render_open.must_be_glue(flag)
    assert not [p for p in render_open.kinds_row_problems(row(flag, flag_class='note'), [], set()) if 'counts GLUE' in p]


if __name__ == '__main__':
    for name, fn in list(globals().items()):
        if name.startswith('test_'):
            fn()
            print('ok', name)
