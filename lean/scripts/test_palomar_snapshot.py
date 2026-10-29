#!/usr/bin/env python3
"""Regression checks for the snapshot's document parsing and local-link containment.

Run with the Python environment used by the snapshot script:
    python3 -m unittest discover -s lean/scripts -p test_palomar_snapshot.py
"""

import importlib.util
import pathlib
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    'snapshot', pathlib.Path(__file__).with_name('palomar-snapshot.py'))
snapshot = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(snapshot)


class SnapshotLinks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = pathlib.Path(self.temp.name)
        self.out = self.root / 'snapshot'
        self.repo = self.root / 'source'
        self.out.mkdir()
        self.repo.mkdir()
        self.original_repo = snapshot.REPO
        snapshot.REPO = self.repo
        self.addCleanup(setattr, snapshot, 'REPO', self.original_repo)
        (self.repo / 'HiddenGuide.md').write_text('Untracked source-only file.\n')
        (self.out / 'docs').mkdir()
        (self.out / 'Guide.md').write_text('Published.\n')
        (self.out / 'A (B)&C.md').write_text('Published with URL-sensitive name.\n')

    def errors(self, document, src='README.md'):
        snapshot.errors.clear()
        snapshot.check_links(self.out, pathlib.Path(src), src, document)
        return list(snapshot.errors)

    def test_unpublished_destinations(self):
        cases = [
            '[guide](HiddenGuide.md#details)',
            '[guide](HiddenGuide.md "a title")',
            '[guide](<HiddenGuide.md> (a title))',
            '[guide](\n HiddenGuide.md\n "title"\n)',
            '[guide][g]\n\n[g]: HiddenGuide.md',
            '[guide][g]\n\n[g]:\n  HiddenGuide.md',
            '> [guide][g]\n>\n> [g]: HiddenGuide.md',
            '- [guide][g]\n\n  [g]:\n    HiddenGuide.md',
            '[g][]\n\n[g]: HiddenGuide.md',
            '[g]\n\n[g]: HiddenGuide.md',
            '![image][g]\n\n[g]: HiddenGuide.md',
            '[unused]: HiddenGuide.md',
            '[g]: Guide.md\n[g]: HiddenGuide.md',
            '<a href=HiddenGuide.md>guide</a>',
            '<a HREF="HiddenGuide.md">guide</a>',
            '<a\n HREF =\n HiddenGuide.md>guide</a>',
            '<IMG SrC=HiddenGuide.md>',
            '<a href="Hidden&#71;uide.md">guide</a>',
            '`` [guide](HiddenGuide.md) `',
            '[guide](Hidden%47uide.md)',
            '| A |\n|---|\n| [guide](HiddenGuide.md) |',
        ]
        for document in cases:
            with self.subTest(document=document):
                errors = self.errors(document)
                self.assertTrue(errors)
                self.assertTrue(all('not published' in e for e in errors), errors)

    def test_valid_destinations_and_literal_examples(self):
        cases = [
            '[guide](Guide.md)',
            '[guide](/Guide.md?raw=1#details "title")',
            '[guide](<A (B)&C.md>)',
            '[guide](A%20%28B%29%26C.md)',
            '<a href="A%20(B)&amp;C.md">guide</a>',
            '[guide][g]\n\n[g]:\n Guide.md',
            '[external](https://example.org/missing.md)',
            '[external](//example.org/missing.md)',
            '[anchor](#missing-anchor)',
            '`[guide](Missing.md)`',
            '`` [guide](Missing.md) ` ``',
            '```md\n[guide](Missing.md)\n```',
            '    [guide](Missing.md)',
            '<!-- <a href=Missing.md> -->',
            '`<a href=Missing.md>`',
            '[guide](Missing.md "unterminated title)',
        ]
        for document in cases:
            with self.subTest(document=document):
                self.assertEqual(self.errors(document), [])

    def test_missing_relative_and_escaping_destinations(self):
        self.assertIn('does not exist', self.errors('[g](Missing.md)')[0])
        self.assertIn('does not exist', self.errors('[g](Guide.md)', 'docs/Notes.md')[0])
        self.assertEqual(self.errors('[g](../Guide.md)', 'docs/Notes.md'), [])
        (self.root / 'Outside.md').write_text('Outside.\n')
        for target in ['../Outside.md', '%2e%2e/Outside.md', '/%2e%2e/Outside.md']:
            with self.subTest(target=target):
                self.assertIn('outside the snapshot', self.errors(f'[g]({target})')[0])
        (self.out / 'shortcut.md').symlink_to(self.root / 'Outside.md')
        self.assertIn('outside the snapshot', self.errors('[g](shortcut.md)')[0])

    def test_lean_comments_are_complete_documents(self):
        sources = [
            '/-!\n[guide][g]\n\n[g]:\n  HiddenGuide.md\n-/',
            'theorem p : True := by\n  /-! [guide](HiddenGuide.md) -/\n  trivial',
            '-- [guide][g]\n--\n-- [g]:\n--   HiddenGuide.md',
            'def n := 1 -- [guide](HiddenGuide.md)',
            '/-! text /- nested -/ [guide](HiddenGuide.md) -/',
        ]
        for source in sources:
            with self.subTest(source=source):
                docs = snapshot.comment_documents(source)
                self.assertTrue(any(self.errors(doc) for doc in docs), docs)

    def test_lean_strings_do_not_hide_or_invent_comments(self):
        source = '''module
def s := "/- [g](Missing.md)"
def r := r##"/- [g](Missing.md)"##
def c := '"'
def «--name» := 0
/-! [g](HiddenGuide.md) -/
'''
        docs = snapshot.comment_documents(source)
        self.assertEqual(len(docs), 1)
        self.assertIn('not published', self.errors(docs[0])[0])

    def test_lean_raw_string_backslash_does_not_escape_its_end(self):
        source = 'def s := r"\\"\n-- [g](HiddenGuide.md)\n'
        docs = snapshot.comment_documents(source)
        self.assertEqual(len(docs), 1)
        self.assertIn('not published', self.errors(docs[0])[0])


if __name__ == '__main__':
    unittest.main()
