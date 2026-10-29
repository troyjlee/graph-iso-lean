#!/usr/bin/env python3
"""gen-audit-imports.py — write the header of GraphIsoChecks/AxiomAudit.lean (PLAN-19 §4).

    scripts/gen-audit-imports.py           rewrite the header
    scripts/gen-audit-imports.py --check   fail if the header is out of date

In Lean's module system a module sees the private declarations of another module only when it
imports that module directly with `import all`; `import all M` does not reach the private
declarations of `M`'s own imports. The audit must enumerate every project declaration, private
ones included, so its header imports every module of the package directly with `import all`:
the root `GraphIso`, every `GraphIso/**/*.lean` and every `GraphIsoChecks/**/*.lean`, except
the audit itself and the `GraphIsoChecks` root (which imports the audit). The audit also checks
this in Lean: every module file on disk must be loaded with all its data.
"""

import pathlib
import sys

LEAN = pathlib.Path(__file__).resolve().parent.parent
AUDIT = LEAN / 'GraphIsoChecks' / 'AxiomAudit.lean'
TAIL = ['meta import Lean.Elab.Command', 'meta import Lean.Util.CollectAxioms']


def modules() -> list[str]:
    names = ['GraphIso']
    for root in ['GraphIso', 'GraphIsoChecks']:
        for path in (LEAN / root).rglob('*.lean'):
            names.append('.'.join(path.relative_to(LEAN).with_suffix('').parts))
    names.remove('GraphIsoChecks.AxiomAudit')
    return sorted(names)


def generate(text: str) -> str:
    lines = text.split('\n')
    i = lines.index(next(l for l in lines if l.startswith('/-!')))
    header = ['module', ''] + [f'import all {m}' for m in modules()] + TAIL + ['']
    return '\n'.join(header + lines[i:])


text = AUDIT.read_text()
new = generate(text)
if sys.argv[1:] == ['--check']:
    if new != text:
        sys.exit('gen-audit-imports.py: the header of AxiomAudit.lean is out of date')
elif new != text:
    AUDIT.write_text(new)
