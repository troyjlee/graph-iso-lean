#!/usr/bin/env python3
"""port-module.py — put Lean source files into Lean's module system (PLAN-19 §3, §4).

    scripts/port-module.py [--meta] [--bodies] FILE...

Each file gets three changes:
  * `module` as its first line;
  * every `import M` of its header becomes `public import M`;
  * `@[expose] public section` after the module docstring (or after the imports when there is
    none), so that every declaration stays public and every definition's body stays visible to
    the importing modules, as before the port.

A file whose first line is already `module` is left unchanged, so the script is idempotent.

With `--meta` (for files that evaluate code at elaboration time: `#eval`, `#guard`,
`run_cmd`), every `public import M` of the ported header is also followed by `meta import M`,
which makes the code of `M` and of its imports available to that evaluation. Meta imports
already present are kept, so this is idempotent too.

With `--bodies` (for check files that reduce the library's code: `decide`, `decide +kernel`,
`execRuns`), the header also gets `import all M` for each module of `BODIES`. A module sees the
body of an imported definition only if the definition is exposed or its module is imported
with `import all`; otherwise the definition is an axiom to the elaborator and to the kernel, and
reduction stops there. `BODIES` are the core and Mathlib modules whose unexposed definitions the
library's code reaches (`Array.range`, `List.mergeSort`, `List.insertionSort`, `Nat.land`).
"""

BODIES = ['Init.Data.Array.Basic', 'Init.Data.List.Sort.Basic', 'Init.Data.Nat.Bitwise.Basic',
          'Mathlib.Data.List.Sort']

import pathlib
import sys


def port(text: str) -> str:
    lines = text.split('\n')
    if lines and lines[0] == 'module':
        return text
    out = ['module', '']
    i = 0
    while i < len(lines) and (lines[i].startswith('import ') or not lines[i].strip()):
        out.append('public ' + lines[i] if lines[i].startswith('import ') else lines[i])
        i += 1
    rest = lines[i:]
    if not rest:  # imports only (a library root): no section
        while out[-1] == '':
            out.pop()
        return '\n'.join(out) + '\n'
    j = 0
    if rest and rest[0].startswith('/-!'):
        while not rest[j].rstrip().endswith('-/'):
            j += 1
        j += 1
    # drop the blank lines kept after the imports when the section follows them directly
    while j == 0 and out[-1] == '':
        out.pop()
    section = ['', '@[expose] public section'] + ([''] if rest[j:] and rest[j].strip() else [])
    return '\n'.join(out + rest[:j] + section + rest[j:])


def add_meta(text: str) -> str:
    lines = text.split('\n')
    # the header: `module`, imports and blank lines
    h = 0
    while h < len(lines) and (lines[h] == 'module' or 'import ' in lines[h][:20]
                              or not lines[h].strip()):
        h += 1
    present = {l for l in lines[:h] if l.startswith('meta import ')}
    out = []
    for l in lines[:h]:
        out.append(l)
        if l.startswith('public import ') and 'meta ' + l[len('public '):] not in present:
            out.append('meta ' + l[len('public '):])
    return '\n'.join(out + lines[h:])


def add_bodies(text: str) -> str:
    lines = text.split('\n')
    h = 0
    while h < len(lines) and (lines[h] == 'module' or 'import ' in lines[h][:20]
                              or not lines[h].strip()):
        h += 1
    # after the last import of the header
    last = max(i for i in range(h) if 'import ' in lines[i][:20])
    new = [f'import all {m}' for m in BODIES if f'import all {m}' not in lines[:h]]
    return '\n'.join(lines[:last + 1] + new + lines[last + 1:])


args = sys.argv[1:]
opts = [a for a in args if a.startswith('--')]
for name in [a for a in args if not a.startswith('--')]:
    path = pathlib.Path(name)
    text = path.read_text()
    new = port(text)
    if '--meta' in opts:
        new = add_meta(new)
    if '--bodies' in opts:
        new = add_bodies(new)
    if new != text:
        path.write_text(new)
