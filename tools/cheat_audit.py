#!/usr/bin/env python3
"""Cheat audit for the HOL4 proof development.

Subcommands (run from the repository root, after `holbuild`):

  sites                 List live (uncommented) `cheat` sites in *Script.sml,
                        with the enclosing Theorem or Resume.
  deps THY.THM ...      For each named theorem, list the cheated theorems it
                        transitively depends on (from the built .dat files).
  dependents            For each directly cheated theorem, count the theorems
                        depending on it and list the maximal ones.

Dependency information is read from `.holbuild/obj/**/*Theory.dat`: each
saved theorem records its own dependency id, the ids of the saved theorems
its proof used, and its oracle tags (`cheat` for cheated theorems and
everything derived from them).  A theorem is a *direct* cheat if it carries
the `cheat` tag but none of its dependencies do.  Local ([local]) theorems
are not saved, so their cheats are attributed to their saved dependents.

Used to produce docs/compiler-proof-status-2026-09-28.md.
"""

import argparse
import collections
import glob
import re
import subprocess
import sys

# ===== Source cheat sites =====

THM_RE = re.compile(r"\s*(?:Theorem|Triviality|Lemma)\s+([A-Za-z0-9_']+)")
RESUME_RE = re.compile(r"\s*Resume\s+([A-Za-z0-9_']+)\[([^\]]*)\]")
CHEAT_RE = re.compile(r"\bcheat\b")


def strip_comments(src):
    """Blank out (possibly nested) SML comments, keeping line structure."""
    out = []
    depth = 0
    i = 0
    while i < len(src):
        if src.startswith("(*", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth and src.startswith("*)", i):
            depth -= 1
            out.append("  ")
            i += 2
        else:
            ch = src[i]
            out.append(ch if not depth or ch == "\n" else " ")
            i += 1
    return "".join(out)


def cheat_sites():
    files = subprocess.check_output(
        ["git", "grep", "-lw", "cheat", "--", "*Script.sml"], text=True
    ).split()
    for path in sorted(files):
        lines = strip_comments(open(path, encoding="utf8").read()).split("\n")
        current = None
        for n, line in enumerate(lines, 1):
            m = THM_RE.match(line)
            if m:
                current = m.group(1)
            m = RESUME_RE.match(line)
            if m:
                current = f"{m.group(1)}[{m.group(2)}]"
            if CHEAT_RE.search(line):
                yield path, n, current


def cmd_sites(_args):
    count = 0
    for path, n, thm in cheat_sites():
        print(f"{path}:{n}\t{thm}")
        count += 1
    print(f"{count} cheat sites", file=sys.stderr)


# ===== .dat parsing =====

TOKEN_RE = re.compile(r'\s*(?:(\()|(\))|("(?:[^"\\]|\\.)*")|([^\s()"]+))')


def parse_sexp(text):
    stack = [[]]
    pos = 0
    while True:
        m = TOKEN_RE.match(text, pos)
        if not m:
            break
        pos = m.end()
        if m.group(1):
            stack.append([])
        elif m.group(2):
            done = stack.pop()
            stack[-1].append(done)
        elif m.group(3):
            stack[-1].append(("S", m.group(3)[1:-1]))
        else:
            tok = m.group(4)
            try:
                stack[-1].append(int(tok))
            except ValueError:
                stack[-1].append(tok)
    return stack[0]


def find_tagged(items, tag):
    for x in items:
        if isinstance(x, list) and x and x[0] == tag:
            return x
    return None


def load_theorems():
    """Map depid (theory, n) -> (theory, name, [depid], [oracle])."""
    thms = {}
    paths = [p for p in glob.glob(".holbuild/obj/**/*Theory.dat", recursive=True)
             if "/.hol/" not in p]
    if not paths:
        sys.exit("no built theories under .holbuild/obj; run holbuild first")
    for path in paths:
        top = parse_sexp(open(path, encoding="utf8", errors="replace").read())[0]
        thy = top[1][0][1]
        core = find_tagged(top, "core-data")
        strs = [s[1] for s in find_tagged(find_tagged(core, "tables"),
                                          "string-table")[1:]]
        k = core.index("exports")
        exported = core[k + 3] if len(core) > k + 3 else []
        for th in exported if isinstance(exported, list) else []:
            if not (isinstance(th, list) and isinstance(th[0], int)):
                continue
            deps, oracles = th[1][0], [o[1] for o in th[1][1:]]
            self_id = (strs[deps[0][0]], deps[0][1])
            dep_ids = [(strs[d[0]], i) for d in deps[1:] for i in d[1:]]
            thms[self_id] = (thy, strs[th[0]], dep_ids, oracles)
    return thms


class DepGraph:
    def __init__(self):
        self.thms = load_theorems()
        self.by_name = collections.defaultdict(list)
        self.rev = collections.defaultdict(set)
        for key, (thy, name, deps, _) in self.thms.items():
            self.by_name[(thy, name)].append(key)
            for d in deps:
                self.rev[d].add(key)
        self.direct = {k for k in self.thms
                       if self.tagged(k)
                       and not any(self.tagged(d) for d in self.thms[k][2])}

    def tagged(self, key):
        return key in self.thms and "cheat" in self.thms[key][3]

    def label(self, key):
        return f"{self.thms[key][0]}.{self.thms[key][1]}"

    def closure(self, key, edges):
        seen = {key}
        todo = [key]
        while todo:
            for nxt in edges(todo.pop()):
                if nxt not in seen:
                    seen.add(nxt)
                    todo.append(nxt)
        return seen

    def forward(self, key):
        return self.thms[key][2] if key in self.thms else []


def cmd_deps(args):
    g = DepGraph()
    for spec in args.theorems:
        thy, _, name = spec.partition(".")
        keys = g.by_name.get((thy, name))
        if not keys:
            print(f"== {spec}: not found in build")
            continue
        for key in keys:
            reach = g.closure(key, g.forward)
            leaves = sorted(g.label(x) for x in reach if x in g.direct)
            print(f"== {spec}  cheat-tagged={g.tagged(key)}  "
                  f"direct-cheat-deps={len(leaves)}")
            for leaf in leaves:
                print(f"    {leaf}")


def cmd_dependents(_args):
    g = DepGraph()
    for key in sorted(g.direct, key=g.label):
        users = g.closure(key, lambda k: g.rev[k]) - {key}
        maximal = sorted({g.label(u) for u in users if not (g.rev[u] & users)})
        print(f"{g.label(key)}\tdependents={len(users)}\tmaximal={maximal}")


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("sites").set_defaults(fn=cmd_sites)
    p = sub.add_parser("deps")
    p.add_argument("theorems", nargs="+", metavar="THY.THM")
    p.set_defaults(fn=cmd_deps)
    sub.add_parser("dependents").set_defaults(fn=cmd_dependents)
    args = ap.parse_args()
    args.fn(args)


if __name__ == "__main__":
    main()
