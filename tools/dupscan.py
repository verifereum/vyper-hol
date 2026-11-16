#!/usr/bin/env python3
"""Find theorems a branch adds that restate existing ones.

Usage: python3 -I tools/dupscan.py <worktree> <base-ref> <root>...

New theorems are those in *Script.sml files changed between <base-ref> and
the worktree whose name was absent from the file at <base-ref> or whose
statement changed.  Each is compared with every theorem in the git-tracked
*Script.sml files under the roots (the worktree itself is always scanned):
SAME (statements equal up to whitespace and comments), ALPHA (equal after
renaming bound variables and dropping simple type annotations), FUZZY
(token-set Jaccard >= 0.85, a hint to check by eye).  WITHIN-NEW lists new
theorems that are ALPHA-equal to each other.

SAME, ALPHA and WITHIN-NEW hits are duplicates to remove; read FUZZY hits.
"""
import collections
import os
import re
import subprocess
import sys

PAT = re.compile(r'^(Theorem|Triviality|Lemma)\s+([A-Za-z0-9_\']+)'
                 r'(\[[^\]]*\])?\s*:\s*\n(.*?)\n(Proof|Termination)\b',
                 re.S | re.M)
SKIP_DIRS = ('/.claude/', '/.hol/', '/.holbuild/', '/alan-ref/', '/.worktrees/')


def norm(s: str) -> str:
    s = re.sub(r'\(\*.*?\*\)', ' ', s, flags=re.S)
    return re.sub(r'\s+', ' ', s).strip()


def thms(txt: str) -> list[tuple[str, str]]:
    return [(m.group(2), norm(m.group(4))) for m in PAT.finditer(txt)]


def alpha(s: str) -> str:
    s = re.sub(r':\s*[A-Za-z0-9_\' ]+?(?=[)\s])', '', s)
    s = re.sub(r'\(\s*([A-Za-z0-9_\']+)\s*\)', r'\1', s)
    names = []
    for m in re.finditer(r'[!?∀∃]\s*([A-Za-z0-9_\' ]+?)\s*\.', s):
        for v in m.group(1).split():
            if v not in names:
                names.append(v)
    for i, v in enumerate(names):
        s = re.sub(r'(?<![A-Za-z0-9_\'])' + re.escape(v) +
                   r'(?![A-Za-z0-9_\'])', f'V{i}', s)
    return re.sub(r'\s+', '', s)


def toks(s: str) -> set[str]:
    s = re.sub(r'V\d+', 'V', alpha(s))
    return set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*|\d+|[^\sA-Za-z0-9_]{1,3}", s))


def git(wt: str, *args: str) -> str:
    # No check: `git show <base>:<file>` fails for a file the branch adds,
    # and an empty result then means "no theorems at base".
    return subprocess.run(['git', '-C', wt, *args], capture_output=True,
                          text=True).stdout


def main(wt: str, base: str, roots: list[str]) -> None:
    wt = os.path.realpath(wt)
    if not git(wt, 'rev-parse', '--verify', '--quiet', f'{base}^{{commit}}'):
        sys.exit(f"base {base!r} is not a commit in {wt}")
    changed = [f for f in git(wt, 'diff', '--name-only', base, '--',
                              '*Script.sml').split()
               if os.path.exists(f"{wt}/{f}")]
    new = []
    for f in changed:
        old = dict(thms(git(wt, 'show', f'{base}:{f}')))
        for n, s in thms(open(f"{wt}/{f}", errors='replace').read()):
            if old.get(n) != s:
                new.append((f, n, s))
    print(f"new or restated theorems: {len(new)} in {len(changed)} changed files")

    newkeys = {(os.path.realpath(f"{wt}/{f}"), n) for f, n, _ in new}
    corpus, seen_paths = [], set()
    for r in [wt] + roots:
        for p in [os.path.join(r, f)
                  for f in git(r, 'ls-files', '*Script.sml').splitlines()]:
            rp = os.path.realpath(p)
            if (rp in seen_paths or not os.path.exists(p)
                    or any(x in p[len(r):] for x in SKIP_DIRS)):
                continue
            seen_paths.add(rp)
            for n, s in thms(open(p, errors='replace').read()):
                if (rp, n) not in newkeys:
                    corpus.append((os.path.relpath(rp, wt), n, s))

    by_stmt, by_alpha = collections.defaultdict(list), collections.defaultdict(list)
    for f, n, s in corpus:
        by_stmt[s].append((f, n))
        by_alpha[alpha(s)].append((f, n))
    corpus_toks = [(f, n, toks(s)) for f, n, s in corpus]

    within = collections.defaultdict(list)
    for f, n, s in new:
        within[alpha(s)].append((f, n))
    for l in within.values():
        if len(l) > 1:
            print("WITHIN-NEW", l)
    for f, n, s in new:
        if s in by_stmt:
            print("SAME ", f, n, "->", by_stmt[s][:3])
        elif alpha(s) in by_alpha:
            print("ALPHA", f, n, "->", by_alpha[alpha(s)][:3])
        else:
            a = toks(s)
            if len(a) >= 6:
                for g, m, b in corpus_toks:
                    j = len(a & b) / len(a | b)
                    if j >= 0.85:
                        print(f"FUZZY {j:.2f}", f, n, "~", g, m)


if __name__ == '__main__':
    if len(sys.argv) < 3:
        sys.exit(f"usage: {sys.argv[0]} <worktree> <base-ref> <root>...")
    main(sys.argv[1], sys.argv[2], sys.argv[3:])
