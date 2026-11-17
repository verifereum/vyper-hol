#!/usr/bin/env python3
"""Find theorems a branch adds that restate existing ones.

Usage: python3 -I tools/dupscan.py <worktree> <base-ref> <root>...

New theorems are those in *Script.sml files changed between <base-ref> and
the worktree whose name was absent from the file at <base-ref> or whose
statement changed.  Each is compared with every theorem in the git-tracked
*Script.sml files under the roots (the worktree itself is always scanned):
SAME (statements equal up to whitespace and comments), ALPHA (equal after
dropping simple type annotations and an outer `!` binder, and renaming
variables), FUZZY (token-set Jaccard >= 0.85, a hint to check by eye).
WITHIN-NEW lists new theorems that are ALPHA-equal to each other.

HOL closes a theorem over its free variables, so ALPHA renames free ones
too: a free name is a variable if some scanned statement binds it and no
scanned script defines it.

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


ID = r"[A-Za-z_][A-Za-z0-9_']*"
BINDER = r"(?:[!?∀∃λ@]|(?<!/)\\)\s*([A-Za-z0-9_' ]+?)\s*\."
NOT_HOL = re.compile(r'"(?:[^"\\]|\\.)*"?|\^\(')
FIELD_OR_QUAL = re.compile(r'\$|\s*(:=|updated_by)')


def consts(txt: str) -> set[str]:
    """Constants a script defines, as far as cheap parsing finds: definitions,
    inductive relations, overloads, datatype constructors, and `foo` for a
    `foo_def` in a theorem list, a string or a theorem's name (from these
    roots or HOL's libraries) that the script doesn't bind itself."""
    out = {re.sub(r'_def$', '', n) for n in re.findall(
        r'^(?:Definition|Inductive|CoInductive|Overload)\s+(' + ID + ')', txt, re.M)}
    for body in re.findall(r'^Datatype\b(.*?)^End\b', txt, re.S | re.M):
        body = re.sub(r'\(\*.*?\*\)|<\|.*?\|>', ' ', body, flags=re.S)
        out.update(re.findall(r'[=|]\s*(' + ID + ')', body))
    ml = re.sub(r'\(\*.*?\*\)|``.*?``|`[^`]*`|‘[^’]*’|“[^”]*”', ' ', txt, flags=re.S)
    out.update(set(re.findall(r'(?:[\[,(]|^Theorem|")\s*(' + ID + r')_def\b', ml, re.M))
               - set(re.findall(r'(' + ID + r')_def\s*=(?!=)', ml)))
    return out


def hol_parts(s: str) -> list[tuple[str, bool]]:
    """`s` split into (text, is_hol) parts: strings and antiquoted ML `^(...)`
    are not HOL."""
    parts, i = [], 0
    while m := NOT_HOL.search(s, i):
        j = m.end()
        if m.group() == '^(':
            depth = 1
            while j < len(s) and depth:
                depth += {'(': 1, ')': -1}.get(s[j], 0)
                j += 1
        parts += [(s[i:m.start()], True), (s[m.start():j], False)]
        i = j
    return parts + [(s[i:], True)]


def bound(s: str) -> set[str]:
    """Names a binder in `s` binds."""
    return {v for b in re.findall(BINDER, s) for v in b.split()}


def drop_types(s: str) -> str:
    """`s` with simple type annotations and the parentheses they leave dropped."""
    s = re.sub(r':\s*[A-Za-z0-9_\' ]+?(?=[)\s])', '', s)
    return re.sub(r'\(\s*([A-Za-z0-9_\']+)\s*\)', r'\1', s)


def alpha(s: str, free: set[str] = frozenset()) -> str:
    """`s` with type annotations dropped, an outer `!` binder removed and its
    variables renamed V0, V1, ... in order of first occurrence.  Variables are
    the names `s` binds and the names in `free`, other than record fields,
    antiquotations and qualified names."""
    s = drop_types(s)
    variables = bound(s) | free
    s = re.sub(r'^\s*[!∀][^.]*\.', '', s)
    names = {}

    def rename(m: re.Match) -> str:
        v, i = m.group(0), m.start()
        before = m.string[max(i - 2, 0):i]
        if (v not in variables or before[-1:] in ('^', '$')
                or re.fullmatch(r"[A-Za-z0-9_')]\.", before)
                or FIELD_OR_QUAL.match(m.string, m.end())):
            return v  # a constant, antiquoted, qualified or a record field
        return names.setdefault(v, f'V{len(names)}')
    s = ''.join(re.sub(r"(?<![A-Za-z0-9_'])" + ID, rename, t) if hol else t
                for t, hol in hol_parts(s))
    return re.sub(r'\s+', '', s)


def toks(s: str) -> set[str]:
    """FUZZY's tokens: `s` with type annotations dropped and the names a
    `!`/`?` binder binds written V.  Unlike `alpha`, they keep the outer binder
    and free names, so the Jaccard threshold keeps its meaning."""
    s = drop_types(s)
    names = {v for b in re.findall(r"[!?∀∃]\s*([A-Za-z0-9_' ]+?)\s*\.", s)
             for v in b.split()}
    s = re.sub(r"(?<![A-Za-z0-9_'])" + ID,
               lambda m: 'V' if m.group() in names else m.group(), s)
    s = re.sub(r'V\d+', 'V', re.sub(r'\s+', '', s))
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
    corpus, seen_paths, known, binders = [], set(), set(), set()
    for r in [wt] + roots:
        for p in [os.path.join(r, f)
                  for f in git(r, 'ls-files', '*Script.sml').splitlines()]:
            rp = os.path.realpath(p)
            if (rp in seen_paths or not os.path.exists(p)
                    or any(x in p[len(r):] for x in SKIP_DIRS)):
                continue
            seen_paths.add(rp)
            txt = open(p, errors='replace').read()
            known |= consts(txt)
            for n, s in thms(txt):
                binders |= bound(s)
                if (rp, n) not in newkeys:
                    corpus.append((os.path.relpath(rp, wt), n, s))

    # `T` and `F` are bound now and then, but free they mean true and false.
    free = binders - known - {'T', 'F'}
    by_stmt, by_alpha = collections.defaultdict(list), collections.defaultdict(list)
    for f, n, s in corpus:
        by_stmt[s].append((f, n))
        by_alpha[alpha(s, free)].append((f, n))
    corpus_toks = [(f, n, toks(s)) for f, n, s in corpus]

    within = collections.defaultdict(list)
    for f, n, s in new:
        within[alpha(s, free)].append((f, n))
    for l in within.values():
        if len(l) > 1:
            print("WITHIN-NEW", l)
    for f, n, s in new:
        if s in by_stmt:
            print("SAME ", f, n, "->", by_stmt[s][:3])
        elif alpha(s, free) in by_alpha:
            print("ALPHA", f, n, "->", by_alpha[alpha(s, free)][:3])
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
