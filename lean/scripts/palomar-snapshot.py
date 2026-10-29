#!/usr/bin/env python3
"""palomar-snapshot.py — write and check the Palomar submission snapshot (PLAN-19.md §7).

    scripts/palomar-snapshot.py [--draft] OUT

Called by `scripts/palomar-snapshot.sh`, which can also build the result. OUT must not exist. It
receives this repository's tracked files (`git ls-files`; never an untracked one), with their
working-tree contents. Without `--draft`, the published files must have no uncommitted changes, so
that the snapshot is that of a commit:

* every tracked file except what decision D1 leaves out: the audit reports `AUDIT*`, the audit
  evidence, the loop's state and the paper PDFs (`LEFT_OUT`);
* `README.md` and `LICENSE` at the root, and `lean/formalization.yaml`, from `lean/palomar/`;
* the manually dispatched `.github/workflows/palomar-preflight.yml`, from `lean/palomar/`;
* in `lean/`: `Challenge.lean`, the text of `GraphIso/Palomar/Statement.lean` followed by the
  advertised theorems of `PLAN-19.md`'s Appendices A and B, each with its proof left as `sorry`
  (decision D3: the only `sorry`, and only in the snapshot); `Solution.lean`, the same statements
  proved by the library (`GraphIso.Palomar.Bridge`); `comparator.json`; and the lakefile, with
  the libraries `Challenge` and `Solution` and the default targets `GraphIso` and `Solution`.

Then it checks the snapshot and fails on any violation:

* Palomar's source rules: every `.lean` file starts with `module` and has at most 10,000 lines;
  `Challenge.lean` has at most 1,000 lines and 100 KiB (a warning above 300 lines or 32 KiB); no
  compiled artifact; at most 500 MiB in all;
* the statement: `Statement.lean`, without its module docstring, consists of the appendices'
  imports and definitions, line for line; `Challenge.lean` begins with `Statement.lean`'s text,
  byte for byte; `sorry` occurs only in `Challenge.lean`, once per advertised theorem;
* D1: no left-out file is present. A name matching `LEFT_OUT_NAMES` fails (this script, which
  defines them, excepted). Markdown documents and Lean comments are parsed as whole CommonMark
  documents, with tables enabled, using markdown-it-py. Links, images, reference definitions
  (including unused definitions), and HTML `href` and `src` attributes must resolve inside the
  snapshot relative to their document (a leading `/` means the snapshot's root). URL escapes
  are decoded; queries and fragments are dropped; external URLs and pure anchors are skipped.
  Code spans, code blocks and malformed link-like text are not CommonMark links. This is a
  local-file check, not an external-URL, anchor, or arbitrary Markdown-extension validator. A
  backticked path, which the documents write relative to the document, to `lean/` or to a source
  directory, or as a bare file name, must name an existing file there. A template of
  `lean/palomar/` is checked as at its published place (`TEMPLATES`). A path that exists in
  neither repository fails too, unless `ELSEWHERE` lists it with its reason (a file of another
  repository, or one a plan proposed and the milestone did not create); an exception that is not
  used fails as well, so the list stays exact;
* D5: `formalization.yaml` no longer starts with its DRAFT line, unless `--draft` is given.
"""

import glob
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import textwrap
from html.parser import HTMLParser
from urllib.parse import unquote, urlsplit

try:
    from markdown_it import MarkdownIt
except ImportError:
    sys.exit('palomar-snapshot: install the pinned parser in your Python environment with '
             'python3 -m pip install -r lean/scripts/palomar-snapshot-requirements.txt')

LEAN = pathlib.Path(__file__).resolve().parent.parent
REPO = LEAN.parent
SELF = 'lean/scripts/palomar-snapshot.py'
# D1: tracked paths that are not published
LEFT_OUT = re.compile(r'^(AUDIT[-_]|audit-evidence/|\.lean-loop/|REFERENCES/)')
# names of unpublished files and directories, as text may mention them (with untracked ones)
LEFT_OUT_NAMES = re.compile(r'REFERENCES/|audit-evidence|AUDIT_LOG|AUDIT-[A-Z0-9*]|\.lean-loop/'
                            r'|M5-CHECKS|perf-evidence|\.claude/')
ARTIFACTS = ('.olean', '.ilean', '.a', '.bc', '.dll', '.dylib', '.o', '.obj', '.so', '.trace')
TEXT = ('.md', '.lean', '.py', '.sh', '.toml', '.yaml', '.yml', '.json', '.txt', '.in')
EXT = r'(?:md|lean|pdf|py|sh|json|yaml|toml|txt|rb)'
CODE = re.compile(r'`([A-Za-z0-9_./*~-]+(?:\.' + EXT + r'|/))`')
BASES = ['', 'lean', 'lean/GraphIso', 'lean/GraphIsoChecks', 'lean/docs', 'lean/scripts']
DRAFT = '# DRAFT'
# backticked paths that name no file of either repository, by (document, path), with the reason
ELSEWHERE = {
    ('PLAN-3.md', 'Partition.lean'): 'proposed by the plan, not created',
    ('PLAN-3.md', 'ClosureProg.lean'): 'proposed by the plan, not created',
    ('PLAN-14.md', 'Main/LabLen.lean'): 'proposed by the plan, not created',
    ('PLAN-17.md', 'Computable.lean'): "Mathlib's file",
    ('PLAN-18.md', 'StackTuringMachine.lean'): "Mathlib's file",
    ('PLAN-18.md', 'PostTuringMachine.lean'): "Mathlib's file",
    ('PLAN-19.md', 'verification-profile.json'): "PalomarSubmission's file",
    ('PLAN-19.md', 'execution-profiles.json'): "PalomarSubmission's file",
    ('PLAN-19.md', 'scripts/check-lean-sources.py'): "PalomarTemplate's file",
    ('lean/docs/status.md', 'check-lean-sources.py'): "PalomarTemplate's file",
    ('lean/docs/status.md', 'validate-formalization.rb'): "PalomarTemplate's file",
    ('lean/docs/status.md', 'verify-comparator.sh'): "PalomarTemplate's file",
}
# the templates of `lean/palomar/` with their published places: their references are resolved there
TEMPLATES = {'lean/palomar/README.md': 'README.md',
             'lean/palomar/formalization.yaml': 'lean/formalization.yaml'}

errors: list[str] = []
notes: list[str] = []


def fail(msg: str) -> None:
    errors.append(msg)


# ---------------------------------------------------------------------------------------------
# The advertised statements: PLAN-19.md's appendices

def chunks(text: str) -> list[str]:
    """Blank-line separated chunks, without surrounding blank lines."""
    return [c.strip('\n') for c in re.split(r'\n\s*\n', text) if c.strip()]


def appendix(plan: str, letter: str) -> list[str]:
    """The ```lean blocks of `## Appendix <letter>`."""
    section = plan.split(f'\n## Appendix {letter}', 1)[1].split('\n## ', 1)[0]
    return re.findall(r'```lean\n(.*?)```', section, re.S)


def is_import(c: str) -> bool:
    return all(line.startswith('public import ') for line in c.split('\n'))


def is_theorem(c: str) -> bool:
    return re.search(r'^theorem ', c, re.M) is not None


def is_definition(c: str) -> bool:
    return re.search(r'^(def|inductive) ', c, re.M) is not None and not is_theorem(c)


def statements() -> tuple[list[str], list[str], list[str]]:
    """The appendices' imports, definitions and theorems, in order (A, then B)."""
    plan = (REPO / 'PLAN-19.md').read_text()
    a = chunks(appendix(plan, 'A')[0])
    b = [c for block in appendix(plan, 'B') for c in chunks(block)]
    imports = [line for c in a + b if is_import(c) for line in c.split('\n')]
    defs = [c for c in a + b if is_definition(c)]
    thms = [c for c in a + b if is_theorem(c)]
    return imports, defs, thms


def theorem_name(thm: str) -> str:
    return re.search(r'^theorem (\S+)', thm, re.M).group(1)


def solution_theorem(thm: str) -> str:
    """The statement proved by the library: `NAME_proof` applied to the explicit binders."""
    name = theorem_name(thm)
    header = re.search(r'^theorem \S+((?:\s*\([^()]*\))*)\s*:', thm, re.M).group(1)
    args = re.findall(r'\((\w+) :', header)
    assert thm.endswith(':= by\n  sorry'), name
    return thm[:-len(' by\n  sorry')] + '\n  ' + ' '.join([name + '_proof'] + args)


def check_statement(statement: str, imports: list[str], defs: list[str]) -> None:
    """`Statement.lean` without its module docstring: the appendices' imports and definitions."""
    cs = chunks(re.sub(r'\n/-!.*?-/\n', '\n', statement, count=1, flags=re.S))
    expected = ['module', '\n'.join(imports), '@[expose] public section',
                'namespace GraphIsoPalomar'] + defs + ['end GraphIsoPalomar']
    if cs != expected:
        for i, (x, y) in enumerate(zip(cs, expected)):
            if x != y:
                fail(f'Statement.lean differs from PLAN-19.md\'s appendices at chunk {i}:\n'
                     f'{x[:200]}\n--- expected ---\n{y[:200]}')
                return
        fail('Statement.lean and PLAN-19.md\'s appendices differ in their number of chunks')


# ---------------------------------------------------------------------------------------------
# Writing the snapshot

def git(*args: str) -> list[str]:
    out = subprocess.run(['git', '-C', str(REPO), *args, '-z'], check=True,
                         capture_output=True).stdout.decode()
    return [p for p in out.split('\0') if p]


def tracked() -> list[str]:
    """The tracked files that are published."""
    return [p for p in git('ls-files') if not LEFT_OUT.match(p)]


def uncommitted() -> list[str]:
    """The published files whose working-tree contents differ from `HEAD`."""
    return [p for p in git('diff', 'HEAD', '--name-only') if not LEFT_OUT.match(p)]


LAKE_LIBS = '''
[[lean_lib]]
name = "Challenge"
roots = ["Challenge"]
[lean_lib.leanOptions]
autoImplicit = false

[[lean_lib]]
name = "Solution"
roots = ["Solution"]
[lean_lib.leanOptions]
autoImplicit = false
'''

SOLUTION_HEAD = '''module

public import GraphIso.Palomar.Bridge

/-!
# The Palomar solution

The advertised theorems of `Challenge.lean`, with the same statements, proved by the library
(`GraphIso/Palomar/Bridge.lean`). Written by `scripts/palomar-snapshot.sh`.
-/

@[expose] public section

namespace GraphIsoPalomar
'''


def write(out: pathlib.Path) -> list[str]:
    for p in tracked():
        if not (REPO / p).is_file():
            fail(f'{p}: tracked but missing from the working tree')
            continue
        dst = out / p
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(REPO / p, dst)
    shutil.copy2(LEAN / 'palomar' / 'README.md', out / 'README.md')
    shutil.copy2(LEAN / 'palomar' / 'LICENSE', out / 'LICENSE')
    shutil.copy2(LEAN / 'palomar' / 'formalization.yaml', out / 'lean' / 'formalization.yaml')
    workflow = out / '.github' / 'workflows' / 'palomar-preflight.yml'
    workflow.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(LEAN / 'palomar' / 'palomar-preflight.yml', workflow)

    imports, defs, thms = statements()
    statement = (LEAN / 'GraphIso' / 'Palomar' / 'Statement.lean').read_text()
    check_statement(statement, imports, defs)
    end = 'end GraphIsoPalomar\n'
    assert statement.endswith('\n\n' + end)
    challenge = statement[:-len(end)] + '\n\n'.join(thms) + '\n\n' + end
    (out / 'lean' / 'Challenge.lean').write_text(challenge)
    solution = SOLUTION_HEAD + '\n' + '\n\n'.join(solution_theorem(t) for t in thms) + '\n\n' + end
    (out / 'lean' / 'Solution.lean').write_text(solution)
    names = ['GraphIsoPalomar.' + theorem_name(t) for t in thms]
    (out / 'lean' / 'comparator.json').write_text(json.dumps({
        'challenge_module': 'Challenge', 'solution_module': 'Solution', 'theorem_names': names,
        'definition_names': [], 'permitted_axioms': ['propext', 'Quot.sound',
                                                     'Classical.choice']}, indent=2) + '\n')
    lakefile = out / 'lean' / 'lakefile.toml'
    text = lakefile.read_text()
    default = 'defaultTargets = ["GraphIso", "GraphIsoChecks"]'
    assert text.count(default) == 1
    lakefile.write_text(text.replace(default, 'defaultTargets = ["GraphIso", "Solution"]') +
                        LAKE_LIBS)

    if not challenge.startswith(statement[:-len(end)]):
        fail('Challenge.lean does not begin with Statement.lean\'s text')
    return names


# ---------------------------------------------------------------------------------------------
# Checks

def has_module_header(text: str) -> bool:
    """`module` first, after blanks, line comments and plain block comments (not doc comments)."""
    i = 0
    while i < len(text):
        if text[i] in ' \r\n':
            i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j + 1
        elif text.startswith('/-', i) and not text.startswith(('/--', '/-!'), i):
            depth, i = 1, i + 2
            while depth and i < len(text):
                if text.startswith('/-', i):
                    depth, i = depth + 1, i + 2
                elif text.startswith('-/', i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        else:
            return re.match(r'module(?![A-Za-z0-9_\'!?.])', text[i:]) is not None
    return False


def strip_comments(text: str) -> str:
    """The text without line comments and (nested) block comments, doc comments included."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth, i = depth + 1, i + 2
        elif depth and text.startswith('-/', i):
            depth, i = depth - 1, i + 2
        elif not depth and text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        else:
            if not depth:
                out.append(text[i])
            i += 1
    return ''.join(out)


def lines(text: str) -> int:
    return text.count('\n') + int(bool(text) and not text.endswith('\n'))


def source_files(base: pathlib.Path) -> set[str]:
    """The names of the files under `base`, outside `.git` and `.lake` (dependencies)."""
    return {p.name for p in base.rglob('*')
            if not {'.git', '.lake'} & set(p.relative_to(base).parts)}


NAMES: dict[pathlib.Path, set[str]] = {}


class HTMLTargets(HTMLParser):
    """HTML attribute names are case-insensitive; values may be quoted or unquoted."""

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.targets: list[tuple[int, str]] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        for name, value in attrs:
            if name in ('href', 'src') and value is not None:
                self.targets.append((self.getpos()[0], value))


MARKDOWN = MarkdownIt('commonmark', {'html': True}).enable('table')


def link_targets(document: str) -> list[str]:
    """Destinations in a complete document, not lines considered in isolation.

    Parse the rendered HTML to handle raw HTML and Markdown links/images uniformly. Escaped
    HTML in code remains text. Also inspect definitions, including unused/duplicate ones.
    """
    env: dict = {}
    rendered = MARKDOWN.render(document, env)
    html = HTMLTargets()
    html.feed(rendered)
    html.close()
    targets = [target for _, target in html.targets]
    refs = list(env.get('references', {}).values()) + env.get('duplicate_refs', [])
    targets.extend(ref['href'] for ref in refs)
    return list(dict.fromkeys(targets))


def inside(path: str) -> bool:
    """A normalized relative path that does not leave the root."""
    return path != '..' and not path.startswith('../') and not os.path.isabs(path)


def comment_documents(text: str) -> list[str]:
    """Lean comments as Markdown documents; skip strings and quoted identifiers.

    Consecutive line comments form one document. Each outer block comment forms another,
    with nested comment delimiters removed. Dedent so an inline/indented comment is not
    mistaken for a Markdown code block solely because of its position in Lean code.
    """
    docs: list[str] = []
    i = 0
    while i < len(text):
        boundary = i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'»")
        raw = re.match(r'r(#*)"', text[i:]) if text[i] == 'r' and boundary else None
        char = re.match(r"'(?:\\[^\n]|[^'\\\n])'", text[i:]) if text[i] == "'" else None
        if raw:
            end = text.find('"' + raw[1], i + len(raw[0]))
            i = len(text) if end < 0 else end + 1 + len(raw[1])
        elif char:
            i += len(char[0])
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        elif text[i] == '«':
            end = text.find('»', i + 1)
            i = len(text) if end < 0 else end + 1
        elif text.startswith('/-', i):
            i += 2
            if i < len(text) and text[i] in '!':
                i += 1
            elif text.startswith('- ', i) or text.startswith('-\n', i):
                i += 1
            depth, out = 1, []
            while depth and i < len(text):
                if text.startswith('/-', i):
                    depth, i = depth + 1, i + 2
                    out.append(' ')
                elif text.startswith('-/', i):
                    depth, i = depth - 1, i + 2
                    out.append(' ')
                else:
                    out.append(text[i])
                    i += 1
            docs.append(textwrap.dedent(''.join(out)))
        elif text.startswith('--', i):
            out = []
            while text.startswith('--', i):
                end = text.find('\n', i)
                if end < 0:
                    end = len(text)
                out.append(text[i + 2:end])
                i = end + 1
                while i < len(text) and text[i] in ' \t':
                    i += 1
            docs.append(textwrap.dedent('\n'.join(out)))
        else:
            i += 1
    return docs


def check_links(out: pathlib.Path, src: pathlib.Path, rel: str, document: str) -> None:
    """Check local destinations, decoding URL paths before enforcing containment."""
    for target in link_targets(document):
        try:
            url = urlsplit(target)
            if url.scheme or url.netloc or not url.path:
                continue
            decoded = unquote(url.path, errors='strict').replace('\\', '/')
            path = os.path.normpath(decoded[1:] if decoded.startswith('/') else
                                    os.path.join(str(src.parent), decoded))
            if not inside(path) or not (out / path).resolve().is_relative_to(out.resolve()):
                fail(f'{rel}: links to `{target}`, outside the snapshot')
            elif (out / path).exists():
                continue
            elif (REPO / path).exists():
                fail(f'{rel}: links to `{target}`, which is not published')
            else:
                fail(f'{rel}: links to `{target}`, which does not exist')
        except (ValueError, OSError) as error:
            fail(f'{rel}: invalid link destination {target!r}: {error}')


def resolves(base: pathlib.Path, src: pathlib.Path, tok: str) -> bool:
    if '/' not in tok.rstrip('/') and '*' not in tok:
        if base not in NAMES:
            NAMES[base] = source_files(base)
        return tok.rstrip('/') in NAMES[base]
    if '/' not in tok and '*' in tok:
        tok = '**/' + tok
    for b in [str(src.parent)] + BASES:
        rel = os.path.normpath(os.path.join(b, tok))
        if not inside(rel):
            continue
        p = str(base / rel)
        if '*' in tok and glob.glob(p, recursive=True):
            return True
        if '*' not in tok and pathlib.Path(p).exists():
            return True
    return False


def check(out: pathlib.Path, names: list[str], draft: bool) -> None:
    used: set[tuple[str, str]] = set()
    files = sorted(p for p in out.rglob('*') if p.is_file())
    size = sum(p.stat().st_size for p in files)
    if size > 500 * 2 ** 20:
        fail(f'the snapshot has {size} bytes, more than 500 MiB')
    for p in files:
        rel = p.relative_to(out).as_posix()
        if LEFT_OUT.match(rel):
            fail(f'{rel}: left out by D1, but present')
        if p.suffix in ARTIFACTS:
            fail(f'{rel}: compiled artifact')
        if p.suffix == '.lean':
            text = p.read_text()
            if not has_module_header(text):
                fail(f'{rel}: does not start with `module`')
            if lines(text) > 10_000:
                fail(f'{rel}: more than 10,000 lines')
            n = len(re.findall(r'\bsorry\b', strip_comments(text)))
            if rel == 'lean/Challenge.lean':
                if n != len(names):
                    fail(f'{rel}: {n} `sorry`, expected one per advertised theorem')
                if lines(text) > 1000 or len(text.encode()) > 100 * 1024:
                    fail(f'{rel}: more than 1,000 lines or 100 KiB')
                elif lines(text) > 300 or len(text.encode()) > 32 * 1024:
                    notes.append(f'{rel}: more than 300 lines or 32 KiB (a Palomar warning)')
            elif n:
                fail(f'{rel}: `sorry` outside Challenge.lean')
        if p.suffix not in TEXT or rel == SELF:
            continue
        src = pathlib.Path(TEMPLATES.get(rel, rel))
        text = p.read_text(errors='replace')
        documents = comment_documents(text) if p.suffix == '.lean' else (
            [text] if p.suffix == '.md' else [])
        for document in documents:
            check_links(out, src, rel, document)
        for i, line in enumerate(text.split('\n'), 1):
            if LEFT_OUT_NAMES.search(line):
                fail(f'{rel}:{i}: names an unpublished file: {line.strip()[:120]}')
                continue
            for m in CODE.finditer(line):
                tok = m.group(1)
                if tok.startswith(('~', '/', 'Mathlib/')):
                    continue
                if resolves(out, src, tok):
                    continue
                if (rel, tok) in ELSEWHERE:
                    used.add((rel, tok))
                    notes.append(f'{rel}:{i}: `{tok}`: {ELSEWHERE[(rel, tok)]}')
                elif resolves(REPO, src, tok):
                    fail(f'{rel}:{i}: refers to `{tok}`, which is not published')
                else:
                    fail(f'{rel}:{i}: refers to `{tok}`, which exists nowhere')
    for key in ELSEWHERE.keys() - used:
        fail(f'ELSEWHERE lists {key}, which no longer occurs')
    yaml = (out / 'lean' / 'formalization.yaml').read_text()
    if yaml.startswith(DRAFT) and not draft:
        fail('lean/formalization.yaml is still a draft (D5: the author confirms it)')


def main() -> int:
    args = sys.argv[1:]
    draft = '--draft' in args
    rest = [a for a in args if a != '--draft']
    if len(rest) != 1:
        sys.exit(__doc__.split('\n\n')[1])
    out = pathlib.Path(rest[0]).resolve()
    if out.exists():
        sys.exit(f'{out} exists')
    if not draft and uncommitted():
        sys.exit('palomar-snapshot: commit first; uncommitted changes in '
                 + ', '.join(uncommitted()))
    names = write(out)
    check(out, names, draft)
    head = subprocess.run(['git', '-C', str(REPO), 'rev-parse', 'HEAD'], check=True,
                          capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(['git', '-C', str(REPO), 'status', '--porcelain',
                            '--untracked-files=no'],
                           check=True, capture_output=True, text=True).stdout.strip()
    print(f'snapshot of {head}{" with uncommitted changes" if dirty else ""}: {out}')
    print(f'advertised: {", ".join(names)}')
    for n in notes:
        print(f'note: {n}')
    for e in errors:
        print(f'error: {e}')
    return 1 if errors else 0


if __name__ == '__main__':
    sys.exit(main())
