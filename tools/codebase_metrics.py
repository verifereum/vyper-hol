#!/usr/bin/env python3
"""Size and complexity of the project's theory scripts, read from source text alone (no build).

    python3 tools/codebase_metrics.py [ROOT] [--json]

ROOT defaults to the current directory; it may be any checkout, an old
commit's included. Metrics:

- theory scripts (`*Script.sml`) and their lines, per top-level directory
  (`.` for the root) and in total;
- `Theorem` (with `store_thm` and `save_thm` under a literal name),
  `Triviality`, `[local]` theorems, `Definition`, `Datatype` and `cheat`
  counts, outside comments;
- duplicate statements: theorems whose whitespace-normalized statement
  also appears in another file, counting each copy after the first;
- theorem uses: how many distinct theorem names appear in no top-level
  declaration besides their own, in exactly one, or in more (a proxy for
  helpers never reused; a `[simp]` theorem used only through the simp set
  counts as unused);
- import cones: the project theories a theory reaches through its
  `Ancestors` header and the `<name>Theory` references in its text
  (`open fooTheory`, `fooTheory.thm`), transitively; HOL's own theories,
  and theories reached only through a project library, are left out.
  Reported as the median over all theories and the largest.
"""

from __future__ import annotations

import argparse
import json
import re
import statistics
import sys
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path

from cheat_audit import strip_comments
from ci_targets import NAME, Header, Project

THEOREM = re.compile(r"^(Theorem|Triviality)\s+([\w']+)\s*(\[[^]]*\])?\s*(:?)", re.MULTILINE)
STORED = re.compile(r'\b(?:store_thm|save_thm)\s*\(\s*"([\w\']+)(\[[^]"]*\])?"')
DECLARATION = re.compile(r"^(?=(?:Theorem|Triviality|Definition|Datatype|Inductive|CoInductive|Overload|val|fun)\b)",
                         re.MULTILINE)
PROOF = re.compile(r"^Proof\b", re.MULTILINE)
DEFINITION = re.compile(r"^Definition\b", re.MULTILINE)
DATATYPE = re.compile(r"^Datatype\b", re.MULTILINE)
CHEAT = re.compile(r"\bcheat\b")
THEORY_REF = re.compile(r"\b([\w']+)Theory\b")
LARGEST_CONES = 5


@dataclass
class Metrics:
    """One checkout's metrics; `dirs` maps a top-level directory to its [files, lines]."""

    dirs: dict[str, list[int]]
    files: int
    lines: int
    theorems: int
    trivialities: int
    local_theorems: int
    definitions: int
    datatypes: int
    cheats: int
    duplicate_statements: int
    used_nowhere: int
    used_once: int
    used_more: int
    cone_median: float
    cone_largest: list[tuple[str, int]]


def cone_sizes(refs: dict[str, set[str]]) -> dict[str, int]:
    """For each theory, how many other theories it reaches through `refs`."""
    sizes = {}
    for theory in refs:
        seen = {theory}
        stack = [theory]
        while stack:
            for ref in refs[stack.pop()] - seen:
                seen.add(ref)
                stack.append(ref)
        sizes[theory] = len(seen) - 1
    return sizes


def measure(root: Path) -> Metrics:
    """The metrics of the theory scripts under `root`."""
    project = Project(root)
    dirs: dict[str, list[int]] = defaultdict(lambda: [0, 0])
    kinds: Counter[str] = Counter()
    names: Counter[str] = Counter()
    statements: dict[str, list[str]] = defaultdict(list)
    places: Counter[str] = Counter()
    refs: dict[str, set[str]] = {}
    for theory, script in project.theories.items():
        raw = script.read_text()
        text = strip_comments(raw)
        parts = script.relative_to(root).parts
        counts = dirs[parts[0] if len(parts) > 1 else "."]
        counts[0] += 1
        counts[1] += raw.count("\n")
        for declaration in DECLARATION.split(text):
            places.update(set(NAME.findall(declaration)))
        for thm in THEOREM.finditer(text):
            kinds[thm[1]] += 1
            names[thm[2]] += 1
            if thm[1] == "Theorem" and "local" in NAME.findall(thm[3] or ""):
                kinds["local"] += 1
            proof = PROOF.search(text, thm.end())
            if thm[4] and proof:
                statement = " ".join(text[thm.end():proof.start()].split())
                statements[statement].append(str(script))
        for thm in STORED.finditer(text):
            kinds["Theorem"] += 1
            names[thm[1]] += 1
            if "local" in NAME.findall(thm[2] or ""):
                kinds["local"] += 1
        kinds["Definition"] += len(DEFINITION.findall(text))
        kinds["Datatype"] += len(DATATYPE.findall(text))
        kinds["cheat"] += len(CHEAT.findall(text))
        try:
            ancestors = set(Header.read(script).ancestors)
        except ValueError:  # an old-style script, with `open` and `new_theory` instead of a header
            ancestors = set()
        refs[theory] = (ancestors | set(THEORY_REF.findall(text))) & project.theories.keys() - {theory}
    uses = Counter(min(places[name] - declared, 2) for name, declared in names.items())
    cones = cone_sizes(refs)
    return Metrics(
        dirs=dict(sorted(dirs.items())),
        files=sum(files for files, _ in dirs.values()),
        lines=sum(lines for _, lines in dirs.values()),
        theorems=kinds["Theorem"],
        trivialities=kinds["Triviality"],
        local_theorems=kinds["local"],
        definitions=kinds["Definition"],
        datatypes=kinds["Datatype"],
        cheats=kinds["cheat"],
        duplicate_statements=sum(len(files) - 1 for files in statements.values() if len(set(files)) > 1),
        used_nowhere=uses[0],
        used_once=uses[1],
        used_more=uses[2],
        cone_median=statistics.median(cones.values()) if cones else 0,
        cone_largest=sorted(cones.items(), key=lambda item: (-item[1], item[0]))[:LARGEST_CONES],
    )


def table(metrics: Metrics) -> str:
    """`metrics` as a Markdown table."""
    rows = [("files / lines", f"{metrics.files} / {metrics.lines}")]
    rows += [(f"  {name}/", f"{files} / {lines}") for name, (files, lines) in metrics.dirs.items()]
    rows += [(key.replace("_", " "), str(value)) for key, value in asdict(metrics).items()
             if key not in ("dirs", "files", "lines", "cone_largest")]
    rows += [(f"cone of {name}", str(size)) for name, size in metrics.cone_largest]
    width = max(len(name) for name, _ in rows)
    return "\n".join([f"| {'metric':<{width}} | value |", f"|{'-' * (width + 2)}|-------|"]
                     + [f"| {name:<{width}} | {value} |" for name, value in rows])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("root", nargs="?", type=Path, default=Path("."), help="checkout to measure")
    parser.add_argument("--json", action="store_true", help="print JSON instead of a table")
    args = parser.parse_args()
    if not args.root.is_dir():
        sys.exit(f"{args.root} is not a directory")
    metrics = measure(args.root)
    print(json.dumps(asdict(metrics)) if args.json else table(metrics))


if __name__ == "__main__":
    main()
