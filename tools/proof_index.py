#!/usr/bin/env python3
"""Index a built vyper-hol tree: which theorems the roots and outside
consumers use, each theory's stage, and every theorem's statement.

Usage, from the project root after `holbuild build` (the default roots):

    python3 tools/proof_index.py OUT_DIR [--consumer-src DIR]...
        [--staged-ref REF]... [--staged-file FILE]...

Uses of exported theorems come from the kernel dependencies recorded in the
built theory data (`.holbuild/obj/**/*Theory.dat`). `[local]` and
`Triviality` theorems never reach the theory data, so their uses come from
their own script: a local is used when a used theorem of the same script names
it, a local uses the theorems its proof names, and a `[simp]` local is used by
every theorem after it in its script. ML code outside theorem blocks, and in
the project libraries a script's `Libs` line names, uses the theorems it names
once any theorem of that script is used. The original proof kept in a comment above a
`TEMPORARILY CHEATED` theorem (or above a `Resume` of it) counts as part of
that theorem's proof.

Consumer groups, reported separately:
  top        the four top-level theorems
  whitelist  theorems of the whitelist roots in holproject.toml
  checks     theorems of the theories the test and check roots list
  native     theorem names in compilerNativeEmitScript.sml (the native-emit
             action), which the default roots don't build
  unrooted   theorems of built theories no build root reaches, and theorem
             names in the scripts the build left unbuilt (such as theories
             CI builds and checks outside the roots, whose own theorems
             aren't indexed)
  outside:<checkout>
             theorem names in the sources of that --consumer-src checkout
  staged     theorem names on the added lines of each --staged-ref's diff
             from HEAD, and in each --staged-file
  rollup     theorems of the theories the vyperHol rollup lists
Name matches (native, unrooted, outside, staged) over-approximate: every theorem of that name
counts. A theorem only `rollup` reaches is rollup-only; one nothing reaches
is unused.

Kinds in theorems.tsv: thm (a theorem block saved in the theory data), local
(a `[local]` or `Triviality` theorem, or one the data lacks), gen (saved by a
library, such as a definition's induction theorem or a translator
certificate; no statement here) and def (a definition; its uses are the
kernel's, so a use only as a constant is not one). Counts are of thm and
local. duplicates.tsv lists the names with a theorem block in more than one
script, and which have the same statement text (an empty statement or an ML
expression matches none). In both files a
`Theorem name = other` re-export has the statement of the theorem it names.

Stages in theories.tsv: the stage contracts the top theorems use (STAGES)
whose dependency cones reach the theory.

Writes OUT_DIR/theorems.tsv, theories.tsv, duplicates.tsv and summary.txt.
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path

from ci_targets import Header

TOPS = [
    ("e2eCorrectness", "vyper_call_correct"),
    ("e2eDeployCorrectness", "e2e_deploy_correctness"),
    ("e2eGasSufficientTop", "vyper_call_gas_sufficient"),
    ("e2eGasSufficientTop", "e2e_deploy_gas_sufficient"),
]
# Stage contracts the top theorems use: (stage, theory, theorem). A theory's
# stages are those whose contract's dependency cone reaches it.
STAGES = [
    ("S1", "loweringCalldataCorrect", "lower_vyper_runtime_unit_correct_dispatched_with"),
    ("S2", "vyperLoweringCorrect", "lower_vyper_runtime_unit_source_unit_ok"),
    ("S3", "loweringMemCorrect", "lower_vyper_runtime_unit_memory_ok"),
    ("S3d", "loweringMemCorrect", "lower_vyper_runtime_unit_dload_offset_ok"),
    ("S4", "o1PipelineCorrect", "run_venom_pipeline_correct"),
    ("S5", "o1PipelineCorrect", "o1_pipeline_memory_obligations"),
    ("S5", "e2eProducers", "o1_pipeline_memory_obligations_raw"),
    ("S6", "o1PipelineCorrect", "run_venom_pipeline_output_shape"),
    ("S7", "codegenCorrectness", "codegen_correct"),
    ("S7", "codegenAsmOpt", "codegen_correct_asm_opt"),
]
RESULTS_ROLLUP = "vyperHol"
CHECK_ROOTS = ["vyperTestsHol", "loweringChecks", "venomChecks"]
NATIVE = "compilerNativeEmit"

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
QUALIFIED = re.compile(r"([A-Za-z_][A-Za-z0-9_']*)Theory\.([A-Za-z_][A-Za-z0-9_']*)")
SEXP_TOKEN = re.compile(r'\s*(?:(\()|(\))|("(?:[^"\\]|\\.)*")|([^\s()"]+))')
COMMENT_TOKEN = re.compile(r'\(\*|\*\)|"(?:[^"\\\n]|\\.)*"')
BLOCK = re.compile(
    r"^(Theorem|Triviality|Definition|Inductive|CoInductive|Datatype|Resume|Finalise"
    r"|Overload|Type|Theory|Ancestors|Libs|val|fun|local|open|structure|Quote)\b"
    r"(?:\s+([A-Za-z_][A-Za-z0-9_']*))?(\[[^\]\n]*\])?",
    re.M,
)
PROOF = re.compile(r"^Proof\b", re.M)
SAVED = re.compile(r'(?:store_thm|save_thm)\s*\(\s*"([A-Za-z_][A-Za-z0-9_\']*)"\s*,')
# a save call with the `val` binding and, for `save_thm ("x", x)`, the argument
# that only repeat the saved name
SAVED_DECL = re.compile(r'(?:val\s+[A-Za-z_][A-Za-z0-9_\']*\s*=\s*)?(?:store_thm|save_thm)\s*\(\s*"([A-Za-z_][A-Za-z0-9_\']*)"\s*,(?:\s*\1\s*\))?')
SAVED_TERM = re.compile(r'\s*(?:prove\s*\(\s*)?(?:``|“)(.*?)(?:``|”)', re.S)
SAVED_ALIAS = re.compile(r"\s*([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)?)\s*\)")
CHEATED = "TEMPORARILY CHEATED"
ALIAS = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)?")

Key = tuple[str, str]  # (theory, theorem)


@dataclass
class Saved:
    """A theorem as the theory data records it."""
    name: str
    number: int
    kind: str
    deps: list[tuple[str, list[int]]]


@dataclass
class Theory:
    name: str
    script: str
    parents: list[str]
    saved: list[Saved]


@dataclass
class Block:
    """A theorem block in a script."""
    local: bool
    simp: bool
    statement: str
    proof: str
    kept: str  # original proof kept in a comment above a cheated theorem
    line: int
    alias: str = ""  # the theorem a `Theorem name = other` block re-exports


@dataclass
class Node:
    kind: str
    deps: list[tuple[str, list[int]]] = field(default_factory=list)
    blocks: list[Block] = field(default_factory=list)


@dataclass
class Graph:
    nodes: dict[Key, Node]
    edges: dict[Key, set[Key]]
    file_uses: dict[str, set[Key]]  # theorems named by a script's code outside theorem blocks
    by_name: dict[str, set[str]]

    def closure(self, start: set[Key] | list[Key]) -> set[Key]:
        seen = set(start)
        todo = list(seen)
        files: set[str] = set()
        while todo:
            key = todo.pop()
            more = self.edges.get(key, set())
            if key[0] not in files:
                files.add(key[0])
                more = more | self.file_uses.get(key[0], set())
            for u in more - seen:
                seen.add(u)
                todo.append(u)
        return seen


def parse_sexp(text: str) -> list:
    stack: list[list] = [[]]
    for m in SEXP_TOKEN.finditer(text):
        if m.group(1):
            stack.append([])
        elif m.group(2):
            done = stack.pop()
            stack[-1].append(done)
        elif m.group(3) is not None:
            stack[-1].append(m.group(3)[1:-1])
        elif m.group(4):
            stack[-1].append(m.group(4))
    return stack[0][0]


def parse_dat(text: str, script: str) -> Theory:
    """A theory's name, parents and saved theorems from its `.dat` text."""
    d = parse_sexp(text)
    header = d[1]
    core = next(x for x in d if isinstance(x, list) and x and x[0] == "core-data")
    strings = next(x for x in core[1] if isinstance(x, list) and x[0] == "string-table")[1:]
    records = core[core.index("exports") + 3]
    saved = []
    for rec in records if isinstance(records, list) else []:
        tag = rec[1][0]  # ((own theory, number) (theory, number...)...) "DISK_THM"
        deps = [(strings[int(dl[0])], [int(n) for n in dl[1:]]) for dl in tag[1:]]
        kind = {"0": "axiom", "1": "def"}.get(rec[2][0], "thm")
        saved.append(Saved(strings[int(rec[0])], int(tag[0][1]), kind, deps))
    parents = [p[0] for p in header[1:] if isinstance(p, list)]
    return Theory(header[0], script, parents, saved)


def load_theories(obj: str) -> dict[str, Theory]:
    theories = {}
    for dirpath, dirs, files in os.walk(obj):
        dirs[:] = [d for d in dirs if not d.startswith(".")]  # .hol/objs holds copies
        for f in files:
            if f.endswith("Theory.dat"):
                path = os.path.join(dirpath, f)
                script = os.path.relpath(path, obj)[: -len("Theory.dat")] + "Script.sml"
                with open(path, errors="replace") as fh:
                    thy = parse_dat(fh.read(), script)
                theories[thy.name] = thy
    return theories


def blank_comments(src: str) -> tuple[str, list[tuple[int, int]]]:
    """The source with its comments blanked out (same length, newlines kept),
    and the spans of its outermost comments."""
    spans = []
    depth = 0
    start = 0
    for m in COMMENT_TOKEN.finditer(src):
        if m.group(0) == "(*":
            if depth == 0:
                start = m.start()
            depth += 1
        elif m.group(0) == "*)" and depth:
            depth -= 1
            if depth == 0:
                spans.append((start, m.end()))
    if depth:
        spans.append((start, len(src)))
    parts = []
    last = 0
    for a, b in spans:
        parts.append(src[last:a])
        parts.append(re.sub(r"[^\n]", " ", src[a:b]))
        last = b
    parts.append(src[last:])
    return "".join(parts), spans


def scan_script(src: str) -> tuple[dict[str, list[Block]], str]:
    """A script's theorem blocks by name, and the text outside them
    (definitions and ML code)."""
    clean, spans = blank_comments(src)
    cheated = [(a, b) for a, b in spans if CHEATED in src[a:b]]
    starts = list(BLOCK.finditer(clean))
    blocks: dict[str, list[Block]] = defaultdict(list)
    outside = []
    for k, m in enumerate(starts):
        end = starts[k + 1].start() if k + 1 < len(starts) else len(clean)
        kind, name, attrs = m.group(1), m.group(2), m.group(3) or ""
        text = clean[m.end():end]
        prev_end = starts[k - 1].end() if k else 0
        kept = " ".join(src[a:b] for a, b in cheated if prev_end <= a < m.start())
        if kind in ("Resume", "Finalise") and blocks.get(name):
            blocks[name][-1].proof += text
            blocks[name][-1].kept += kept
            blocks[name][-1].local |= kind == "Finalise" and "local" in attrs
            continue
        if kind not in ("Theorem", "Triviality") or not name:
            outside.append(clean[m.start():end])
            continue
        head = text.lstrip()
        if head.startswith(":"):
            proof = PROOF.search(text)
            statement = text[: proof.start()] if proof else text
            statement = statement.lstrip()[1:]
        else:  # Theorem name = ML expression
            statement = head.split("\n\n")[0]
        alias = statement.strip()[1:].strip().rstrip(";").strip() if statement.strip().startswith("=") else ""
        blocks[name].append(Block(
            local=kind == "Triviality" or "local" in attrs,
            simp="simp" in attrs,
            alias=alias if ALIAS.fullmatch(alias) else "",
            statement=" ".join(statement.split()),
            proof=text,
            kept=kept,
            line=src.count("\n", 0, m.start()) + 1,
        ))
    # store_thm ("name", ``statement``, tac), save_thm ("name", prove (``statement``, tac))
    # and save_thm ("name", other)
    for m in SAVED.finditer(clean):
        if m.group(1) in blocks:
            continue
        term = SAVED_TERM.match(clean, m.end())
        alias = SAVED_ALIAS.match(clean, m.end())
        blocks[m.group(1)].append(Block(
            local=False, simp=False,
            statement=" ".join(term.group(1).split()) if term else "",
            proof="", kept="", line=src.count("\n", 0, m.start()) + 1,
            alias=alias.group(1) if alias and not term else "",
        ))
    # the code outside theorem blocks, without the names its save calls declare
    return blocks, SAVED_DECL.sub(" ", " ".join(outside))


def ancestor_sets(theories: dict[str, Theory]) -> dict[str, set[str]]:
    memo: dict[str, set[str]] = {}

    def parents(t: str) -> list[str]:
        return theories[t].parents if t in theories else []

    for root in theories:
        stack = [(root, False)]
        while stack:
            t, ready = stack.pop()
            if t in memo:
                continue
            if ready:  # every parent was finished before this entry was popped
                memo[t] = set().union(*({p} | memo[p] for p in parents(t)))
            else:
                stack.append((t, True))
                stack.extend((p, False) for p in parents(t) if p not in memo)
    return memo


def listed(theories: dict[str, Theory], declared: dict[str, list[str]], root: str) -> set[str]:
    """The theories a rollup lists, looking through nested rollups (theories
    that save nothing). `declared` holds the `Ancestors` a rollup's script
    names: the theory data keeps only those no other listed theory imports."""
    out: set[str] = set()
    seen: set[str] = set()
    todo = [root]
    while todo:
        t = todo.pop()
        if t in seen or t not in theories:
            continue
        seen.add(t)
        if theories[t].saved and t != root:
            out.add(t)
        else:
            todo.extend(declared.get(t, theories[t].parents))
    return out


def names_in(text: str) -> set[str]:
    return set(IDENT.findall(text))


def build_graph(theories: dict[str, Theory], scripts: dict[str, str], libs: dict[str, str]) -> Graph:
    """Theorems and their uses: the theory data's dependencies, plus the names
    in locals' proofs, kept original proofs, and the ML code outside theorem
    blocks, with `libs[t]` the code of the project libraries theory t's
    `Libs` line names."""
    ancestors = ancestor_sets(theories)
    by_number: dict[tuple[str, int], str] = {}
    nodes: dict[Key, Node] = {}
    for t, thy in theories.items():
        for s in thy.saved:
            by_number[(t, s.number)] = s.name
            nodes[(t, s.name)] = Node(s.kind, s.deps)
    outside: dict[str, str] = {}
    for t, src in scripts.items():
        blocks, outside[t] = scan_script(src)
        for name, bs in blocks.items():
            # the theory data decides the kind: a `[local]` theorem a script
            # saves with `save_thm` is exported
            nodes.setdefault((t, name), Node("local")).blocks = bs
    for node in nodes.values():
        if node.kind == "thm" and not node.blocks:
            node.kind = "gen"
    by_name: dict[str, set[str]] = defaultdict(set)
    for t, n in nodes:
        by_name[n].add(t)

    def locals_named(t: str, text: str) -> set[Key]:
        return {(t, n) for n in names_in(text) if (t, n) in nodes and nodes[(t, n)].kind == "local"}

    def theorems_named(t: str, text: str) -> set[Key]:
        scope = ancestors.get(t, set()) | {t}
        found = {(m.group(1), m.group(2)) for m in QUALIFIED.finditer(text)} & nodes.keys()
        for n in names_in(text):
            found |= {(u, n) for u in by_name.get(n, ()) if u in scope}
        return found

    edges: dict[Key, set[Key]] = {}
    for key, node in nodes.items():
        uses = {(thy, by_number[(thy, n)]) for thy, ns in node.deps for n in ns if (thy, n) in by_number}
        for b in node.blocks:
            # a local has no kernel dependencies: its proof's names stand in for them
            uses |= theorems_named(key[0], b.proof) if node.kind == "local" else locals_named(key[0], b.proof)
            if b.kept:
                uses |= theorems_named(key[0], b.kept)
        uses.discard(key)
        edges[key] = uses
    # a `[simp]` local is used implicitly by the theorems after it in its script
    simp_locals: dict[str, list[tuple[int, Key]]] = defaultdict(list)
    for key, node in nodes.items():
        if node.kind == "local" and any(b.simp for b in node.blocks):
            simp_locals[key[0]].append((node.blocks[0].line, key))
    for key, node in nodes.items():
        if node.blocks and key[0] in simp_locals:
            line = node.blocks[0].line
            edges[key] |= {k for l, k in simp_locals[key[0]] if l < line}
    file_uses = {t: theorems_named(t, text + " " + libs.get(t, "")) for t, text in outside.items()}
    return Graph(nodes, edges, file_uses, by_name)


def git_output(args: list[str]) -> str:
    return subprocess.run(["git"] + args, capture_output=True, text=True, check=True).stdout


def source_names(checkout: str) -> set[str]:
    names: set[str] = set()
    for f in git_output(["-C", checkout, "ls-files", "*.sml", "*.sig", "*.py"]).splitlines():
        with open(os.path.join(checkout, f), errors="replace") as fh:
            names |= names_in(fh.read())
    return names


def added_names(ref: str) -> set[str]:
    diff = git_output(["diff", "HEAD..." + ref, "--", "*.sml"])
    return names_in("\n".join(l[1:] for l in diff.splitlines() if l.startswith("+") and not l.startswith("+++")))


def script_names(path: str) -> set[str]:
    """The names a script's code uses: outside comments, and in the original
    proofs kept above `TEMPORARILY CHEATED` theorems."""
    with open(path, errors="replace") as fh:
        src = fh.read()
    clean, spans = blank_comments(src)
    return names_in(clean) | names_in(" ".join(src[a:b] for a, b in spans if CHEATED in src[a:b]))


def read_scripts(theories: dict[str, Theory]) -> dict[str, str]:
    scripts = {}
    for t, thy in theories.items():
        if os.path.exists(thy.script):
            with open(thy.script, errors="replace") as fh:
                scripts[t] = fh.read()
    return scripts


def read_libs(theories: dict[str, Theory]) -> dict[str, str]:
    """Per theory, the code (comments blanked) of the project libraries its
    `Libs` line names."""
    paths = {os.path.basename(f)[: -len(".sml")]: f for f in git_output(["ls-files", "*.sml"]).split()
             if not f.endswith("Script.sml")}
    code: dict[str, str] = {}
    for t, thy in theories.items():
        texts = []
        for lib in Header.read(Path(thy.script)).libs:
            if lib in paths:
                with open(paths[lib], errors="replace") as fh:
                    texts.append(blank_comments(fh.read())[0])
        code[t] = " ".join(texts)
    return code


def build_roots(toml: str) -> list[str]:
    section = toml.split("\n[build]")[1].split("\n[")[0]
    return [os.path.basename(p)[: -len("Script.sml")] for p in re.findall(r'"([^"]+Script\.sml)"', section)]


def statement_of(graph: Graph, ancestors: dict[str, set[str]], t: str, n: str) -> str:
    """A theorem block's statement, following `Theorem n = other` re-exports to
    the statement of the theorem they name."""
    seen: set[Key] = set()
    key = (t, n)
    while key not in seen:
        seen.add(key)
        b = graph.nodes[key].blocks[0]
        if not b.alias:
            return b.statement
        thy, _, name = b.alias.rpartition(".")
        thy = thy[: -len("Theory")] if thy.endswith("Theory") else thy
        scope = [thy] if thy else [key[0]] + sorted(ancestors.get(key[0], set()))
        found = [(u, name) for u in scope if (u, name) in graph.nodes and graph.nodes[(u, name)].blocks
                 and (u, name) != key]
        if len(found) != 1:
            return b.statement
        key = found[0]
    return graph.nodes[key].blocks[0].statement


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("out")
    ap.add_argument("--obj", default=".holbuild/obj")
    ap.add_argument("--consumer-src", action="append", default=[])
    ap.add_argument("--staged-ref", action="append", default=[])
    ap.add_argument("--staged-file", action="append", default=[])
    a = ap.parse_args()

    # a theory data file whose script is gone is a stale build product
    theories = {t: thy for t, thy in load_theories(a.obj).items() if os.path.exists(thy.script)}
    graph = build_graph(theories, read_scripts(theories), read_libs(theories))
    ancestors = ancestor_sets(theories)
    declared = {t: list(Header.read(Path(thy.script)).ancestors) for t, thy in theories.items() if not thy.saved}
    nodes = graph.nodes
    missing = [k for k in TOPS + [(t, n) for _, t, n in STAGES] if k not in nodes]
    if missing:
        sys.exit(f"top or stage theorems missing from the theory data under {a.obj}: {missing}")
    with open("holproject.toml") as fh:
        toml = fh.read()
    roots = build_roots(toml)
    if missing := [r for r in roots if r not in theories]:
        sys.exit(f"build roots missing from the theory data under {a.obj} (build them first): {missing}")
    outside_names = [os.path.basename(os.path.normpath(c)) for c in a.consumer_src]
    if len(set(outside_names)) != len(outside_names):
        sys.exit(f"--consumer-src checkouts need distinct directory names: {a.consumer_src}")

    def in_theories(ts: set[str]) -> set[Key]:
        return {k for k in nodes if k[0] in ts}

    def named(names: set[str]) -> set[Key]:
        return {k for k in nodes if k[1] in names}

    staged: set[str] = set()
    for ref in a.staged_ref:
        staged |= added_names(ref)
    for path in a.staged_file:
        with open(path, errors="replace") as fh:
            staged |= names_in(fh.read())
    rooted = set(roots).union(*(ancestors.get(r, set()) for r in roots))
    native: set[str] = set()
    unbuilt: set[str] = set()
    unbuilt_scripts: list[str] = []
    for f in git_output(["ls-files", "*Script.sml"]).split():
        thy = os.path.basename(f)[: -len("Script.sml")]
        if thy == NATIVE:
            native |= script_names(f)
        elif thy not in theories:
            unbuilt_scripts.append(f)
            unbuilt |= script_names(f)
    seeds = {
        "top": set(TOPS),
        "whitelist": in_theories({r for r in roots if r.startswith("whitelist")}),
        "checks": in_theories(set().union(*(listed(theories, declared, r) for r in CHECK_ROOTS))),
        "native": named(native),
        "unrooted": in_theories(set(theories) - rooted - {NATIVE}) | named(unbuilt),
    }
    for name, c in zip(outside_names, a.consumer_src):
        seeds["outside:" + name] = named(source_names(c))
    seeds["staged"] = named(staged)
    seeds["rollup"] = in_theories(listed(theories, declared, RESULTS_ROLLUP))
    groups = list(seeds)
    use_groups = groups[:-1]
    reach = {g: graph.closure(seeds[g]) for g in groups}
    stages: dict[str, set[str]] = defaultdict(set)
    for stage, t, n in STAGES:
        for k in graph.closure([(t, n)]):
            stages[k[0]].add(stage)

    os.makedirs(a.out, exist_ok=True)
    counts: dict[str, dict[str, int]] = {t: {"theorems": 0, "used": 0, "rollup_only": 0, "unused": 0} for t in theories}
    groups_of: dict[str, set[str]] = defaultdict(set)
    with open(os.path.join(a.out, "theorems.tsv"), "w") as f:
        f.write("theory\tname\tkind\tscript\tline\tused_by\tstatement\n")
        for key in sorted(nodes):
            t, n = key
            node = nodes[key]
            by = [g for g in groups if key in reach[g]]
            b = node.blocks[0] if node.blocks else None
            statement = statement_of(graph, ancestors, t, n) if b else ""
            f.write(f"{t}\t{n}\t{node.kind}\t{theories[t].script}\t{b.line if b else ''}\t"
                    f"{','.join(by) or '-'}\t{statement}\n")
            if node.kind not in ("thm", "local"):
                continue
            c = counts[t]
            c["theorems"] += 1
            groups_of[t].update(by)
            if any(g in use_groups for g in by):
                c["used"] += 1
            elif by:
                c["rollup_only"] += 1
            else:
                c["unused"] += 1
    with open(os.path.join(a.out, "theories.tsv"), "w") as f:
        f.write("theory\tscript\tstages\troots\tused_by\ttheorems\tused\trollup_only\tunused\n")
        for t in sorted(theories):
            c = counts[t]
            reached = [r for r in roots if r == t or t in ancestors.get(r, set())]
            f.write(f"{t}\t{theories[t].script}\t{','.join(sorted(stages[t])) or '-'}\t"
                    f"{','.join(reached) or '-'}\t{','.join(g for g in groups if g in groups_of[t]) or '-'}\t"
                    f"{c['theorems']}\t{c['used']}\t{c['rollup_only']}\t{c['unused']}\n")
    with open(os.path.join(a.out, "duplicates.tsv"), "w") as f:
        f.write("name\tcopies\tdistinct_statements\tidentical_extra_copies\tscripts\n")
        for n in sorted(graph.by_name):
            ts = sorted(t for t in graph.by_name[n] if nodes[(t, n)].blocks)
            if len(ts) < 2:
                continue
            by_statement: dict[str, list[str]] = defaultdict(list)
            for t in ts:
                statement = statement_of(graph, ancestors, t, n)
                # an empty statement or an ML expression (`Theorem n = f x`) isn't comparable
                comparable = statement and not statement.startswith("=")
                by_statement[statement if comparable else "\0" + t].append(theories[t].script)
            identical = sum(len(c) - 1 for c in by_statement.values())
            # scripts with the same statement are grouped, groups separated by " | "
            f.write(f"{n}\t{len(ts)}\t{len(by_statement)}\t{identical}\t"
                    f"{' | '.join(' '.join(c) for c in by_statement.values())}\n")
    total = {k: sum(c[k] for c in counts.values()) for k in ("theorems", "used", "rollup_only", "unused")}
    summary = (f"theories {len(theories)} theorems {total['theorems']} used {total['used']} "
               f"rollup_only {total['rollup_only']} unused {total['unused']}\n"
               + "".join(f"{g}: seeds {len(seeds[g])} reach {len(reach[g])}\n" for g in groups)
               + f"unbuilt scripts (not indexed; their names count as unrooted uses): {len(unbuilt_scripts)}\n"
               + f"consumer checkouts: {' '.join(a.consumer_src) or 'none'}\n"
               + f"staged refs: {' '.join(a.staged_ref) or 'none'}\nstaged files: {' '.join(a.staged_file) or 'none'}\n")
    with open(os.path.join(a.out, "summary.txt"), "w") as f:
        f.write(summary)
    sys.stdout.write(summary)


if __name__ == "__main__":
    main()
