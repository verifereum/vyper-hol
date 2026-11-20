#!/usr/bin/env python3
r"""Find theorems a branch adds that restate existing ones, or list repeated
statements, proofs and shapes over a whole tree.

Usage: python3 -I tools/dupscan.py <worktree> <base-ref> <root>...
       python3 -I tools/dupscan.py --tree <out-dir> <root>...

Branch mode (the first form):

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

Whole-tree mode (`--tree`) needs no base ref.  It reads every theorem of the
git-tracked *Script.sml files under the roots (the first is the checkout the
paths are relative to; comments are skipped) and writes to <out-dir> one row
per theorem of each cluster, sorted and without line numbers, so that two
runs diff cleanly:
  same.tsv    statements equal up to whitespace and comments;
  alpha.tsv   statements equal as for ALPHA above but differing in text;
  wrappers.tsv  theorems left out of both: those whose proof is 4 lines or
              fewer and names another theorem with an ALPHA-equal statement
              outside quotations (a re-export, not a copy), bare or qualified
              by its theory or by one that aliases it under that name, and
              `Theorem x = y` aliases, `y` a theorem name (qualified or not);
  proofs.tsv  near-identical proofs (a proof with its `Resume` blocks): 5 or
              more lines each and a difflib ratio of 0.8 or more over their
              lines, with whitespace collapsed and identifiers lower-cased
              without `_`, digits and the layer markers mem, ptr, full, body,
              own, static, reloc;
  hints.tsv   shapes for a reviewer to look at, not duplicates to remove:
    restates  a statement that doesn't name a predicate `p` but has 8 or
              more of the conjuncts of `p`'s body among its premises, or
              the premises of those (compared as for ALPHA), where `p` is a
              `Definition` of the form `p ... <=> c1 /\ c2 /\ ...` or
              `p ... <=> !xs. c1 /\ c2 /\ ... ==> post` (or `=` for `<=>`);
              one row per theorem, for the predicate with most conjuncts
              restated;
    variant   a theorem `foo_<s>`, <s> in VARIANTS, whose proof doesn't name
              the theorem `foo`;
    instance  a statement naming a `compile_*` function or a constructor of
              the Venom `opcode` datatype that, with that constant made a
              variable, is another theorem's statement (as for ALPHA), which
              its proof doesn't name.  Only exact instances: a generic lemma
              with an extra premise (an opcode class, say) isn't found.
It prints the counts and exits 0 whatever it finds.  Run it offline and when
a lane's work is harvested, not as a synchronous READY gate: it reads the
whole tree (about two minutes on vyper-hol).
"""
import collections
import dataclasses
import difflib
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


def scripts(roots: list[str]):
    """(real path, text) of each git-tracked *Script.sml under the roots, once
    each, skipping build and worktree directories."""
    seen = set()
    for r in roots:
        for p in [os.path.join(r, f)
                  for f in git(r, 'ls-files', '*Script.sml').splitlines()]:
            rp = os.path.realpath(p)
            if (rp in seen or not os.path.exists(p)
                    or any(x in p[len(r):] for x in SKIP_DIRS)):
                continue
            seen.add(rp)
            with open(p, errors='replace') as f:
                yield rp, f.read()


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
    corpus, known, binders = [], set(), set()
    for rp, txt in scripts([wt] + roots):
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


# Whole-tree mode.

# As PAT, but also for a statement on the `Theorem` line.
THM = re.compile(r'^(Theorem|Triviality|Lemma)\s+([A-Za-z0-9_\']+)'
                 r'(\[[^\]]*\])?\s*:\s*(.*?)\n(Proof|Termination)\b(.*?)^QED\b',
                 re.S | re.M)
RESUME = re.compile(r'^Resume\s+(' + ID + r')(?:\[[^\]]*\])?\s*:\s*\n(.*?)^QED\b',
                    re.S | re.M)
QUOTED = re.compile(r'``.*?``|`[^`]*`|‘[^’]*’|“[^”]*”|"(?:[^"\\]|\\.)*"', re.S)
ALIAS = re.compile(r"^(?:Theorem|Triviality)\s+([A-Za-z0-9_']+)(?:\[[^\]]*\])?\s*=\s*"
                   r"((?:" + ID + r"\.)?" + ID + r")\s*;?[ \t]*"
                   r"(?=\n(?:[ \t]*\n)*(?:[^ \t|\n]|\Z)|\Z)", re.M)  # not continued
DEF = re.compile(r'^Definition\s+(' + ID + r')(?:\[[^\]]*\])?\s*:\s*\n(.*?)'
                 r'^(?:End|Termination)\b', re.S | re.M)
OPCODES = re.compile(r'^Datatype:\s*\n\s*opcode\s*=(.*?)^End\b', re.S | re.M)
VARIANTS = ('own', 'live', 'mem', 'ptr', 'full', 'static', 'reloc', 'strong',
            'general', 'gen', 'ext', 'exact', 'safe', 'bounded', 'observed',
            'world', 'intervals', 'complete', 'alt', 'weak', 'v2')
MARKERS = re.compile(r"mem|ptr|full|body|own|static|reloc|v\d|\d+|_", re.I)

Member = tuple[str, str]               # (path, theorem name)
Hint = tuple[str, str, str, str]       # (kind, path, theorem name, detail)


@dataclasses.dataclass(frozen=True)
class Thm:
    path: str
    name: str
    stmt: str   # normalised as by `norm`
    proof: str


@dataclasses.dataclass
class Found:
    clusters: dict[str, list[list[Member]]]   # same, alpha, proofs
    wrappers: set[tuple[str, str, str]]       # (path, name, names it cites)
    hints: set[Hint]


def mask_comments(s: str) -> str:
    """`s` with its (nested) comments blanked, newlines kept."""
    out, depth, i = list(s), 0, 0
    while i < len(s):
        if s.startswith('(*', i) and not s.startswith('(*)', i):
            depth += 1
            out[i] = out[i + 1] = ' '
            i += 2
        elif depth and s.startswith('*)', i):
            depth -= 1
            out[i] = out[i + 1] = ' '
            i += 2
        else:
            if depth and s[i] != '\n':
                out[i] = ' '
            i += 1
    return ''.join(out)


def split_top(s: str, ops: tuple[str, ...]) -> list[str]:
    """`s` split at the operators `ops` outside brackets."""
    parts, depth, start, i = [], 0, 0, 0
    while i < len(s):
        depth += (s[i] in '([{') - (s[i] in ')]}')
        op = depth == 0 and next((o for o in ops if s.startswith(o, i)), None)
        if op:
            parts.append(s[start:i])
            i = start = i + len(op)
        else:
            i += 1
    return [p.strip() for p in parts + [s[start:]]]


def strip_binders(s: str) -> str:
    """`s` without its outer `!` binders."""
    while m := re.match(r"\s*[!∀][A-Za-z0-9_' :]+?\.", s):
        s = s[m.end():]
    return s.strip()


def unparen(s: str) -> str:
    """`s` without parentheses around all of it."""
    if not (s.startswith('(') and s.endswith(')')):
        return s
    depth = 0
    for c in s[:-1]:
        depth += (c == '(') - (c == ')')
        if depth == 0:
            return s
    return s[1:-1].strip()


def conjuncts(s: str) -> list[str]:
    """The conjuncts of `s`, parenthesised groups of conjuncts flattened."""
    parts = [c for c in split_top(unparen(s), ('/\\', '∧')) if c]
    return [s] if len(parts) == 1 else [d for c in parts for d in conjuncts(c)]


def premises(stmt: str) -> list[str]:
    """The conjuncts of the antecedents of `stmt`, under its outer binders."""
    imp = split_top(strip_binders(unparen(strip_binders(stmt))), ('==>', '⇒'))
    return [c for a in imp[:-1] for c in conjuncts(strip_binders(a))]


def nested_premises(stmt: str) -> list[str]:
    """`premises(stmt)` and, in turn, the nested premises of each."""
    return [d for c in premises(stmt) for d in [c] + nested_premises(unparen(c))]


def theory(path: str) -> str:
    """The name of the theory the script at `path` makes."""
    return os.path.basename(path).removesuffix('Script.sml')


def names(text: str, name: str) -> bool:
    """Whether `name` occurs in `text` as an identifier."""
    return re.search(r"(?<![A-Za-z0-9_'])" + re.escape(name)
                     + r"(?![A-Za-z0-9_'])", text) is not None


def proof_lines(proof: str) -> list[str]:
    """`proof`'s lines as proofs.tsv compares them."""
    return [re.sub(ID, lambda m: MARKERS.sub('', m.group().lower()) or 'x',
                   ' '.join(l.split()))
            for l in proof.splitlines() if l.strip()]


def components(edges: list[tuple[Member, Member]]) -> list[list[Member]]:
    """Connected components of the graph with `edges`."""
    parent: dict[Member, Member] = {}

    def find(x: Member) -> Member:
        parent.setdefault(x, x)
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for a, b in edges:
        parent[find(a)] = find(b)
    comps = collections.defaultdict(list)
    for x in parent:
        comps[find(x)].append(x)
    return list(comps.values())


def similar_proofs(proofs: dict[Member, list[str]]) -> list[tuple[Member, Member]]:
    """Pairs of proofs of 5 or more lines with a difflib ratio of 0.8 or more.
    Only pairs that share 2 or more rare lines (12+ characters, in at most 60
    proofs), and 30% of the rare lines of the one with fewer, are compared."""
    P = {k: ls for k, ls in proofs.items() if len(ls) >= 5}
    df = collections.Counter(l for ls in P.values() for l in set(ls) if len(l) >= 12)
    post = collections.defaultdict(list)
    for k, ls in P.items():
        for l in set(ls):
            if len(l) >= 12 and df[l] <= 60:
                post[l].append(k)
    rare = collections.Counter(k for ks in post.values() for k in ks)
    shared = collections.Counter()
    for ks in post.values():
        for i, a in enumerate(ks):
            for b in ks[i + 1:]:
                shared[(a, b)] += 1
    return [(a, b) for (a, b), c in shared.items()
            if c >= 2 and c >= 0.3 * min(rare[a], rare[b])
            and max(len(P[a]), len(P[b])) <= 2.5 * min(len(P[a]), len(P[b]))
            and difflib.SequenceMatcher(None, P[a], P[b], autojunk=False).ratio() >= 0.8]


def scan_tree(files: dict[str, str]) -> Found:
    """Clusters and hints over the scripts `files` (path -> text)."""
    thms, defs, known, binders, special = [], [], set(), set(), set()
    wrappers = set()
    for path, txt in files.items():
        txt = mask_comments(txt)
        known |= consts(txt)
        wrappers |= {(path, m.group(1), m.group(2)) for m in ALIAS.finditer(txt)}
        resumed = collections.defaultdict(str)   # suspended goals' later proofs
        for m in RESUME.finditer(txt):
            resumed[m.group(1)] += m.group(2)
        for m in THM.finditer(txt):
            thms.append(Thm(path, m.group(2), norm(m.group(4)),
                            m.group(6) + resumed[m.group(2)]))
            binders |= bound(thms[-1].stmt)
        for m in DEF.finditer(txt):
            p = m.group(1).removesuffix('_def')
            defs.append((p, norm(m.group(2))))
            if p.startswith('compile_'):
                special.add(p)
        for body in OPCODES.findall(txt):
            special.update(re.findall(r'\|\s*(' + ID + ')', '|' + body))
    free = binders - known - {'T', 'F'}
    by_alpha = collections.defaultdict(list)
    for t in thms:
        by_alpha[alpha(t.stmt, free)].append(t)
    # Mentions inside quotations and strings aren't citations.
    unquoted = {t: QUOTED.sub(' ', t.proof) for t in thms}
    # The names that cite a theorem: its own, bare or qualified by its theory,
    # and those of its aliases, bare or qualified by the alias's theory.
    alias_names = collections.defaultdict(set)   # alias target -> alias names
    for p, n, y in wrappers:
        alias_names[y] |= {n, theory(p) + 'Theory.' + n}

    def cites(t: Thm, u: Thm) -> bool:
        own = {u.name, theory(u.path) + 'Theory.' + u.name}
        refs = set(re.findall(r"(?<![A-Za-z0-9_'.])(?:" + ID + r"\.)?" + ID, unquoted[t]))
        return not refs.isdisjoint(own.union(*(alias_names[x] for x in own)))
    for c in by_alpha.values():
        for t in c:
            if len(proof_lines(t.proof)) > 4:
                continue
            cited = sorted({u.name for u in c if u is not t and cites(t, u)})
            if cited:
                wrappers.add((t.path, t.name, ' '.join(cited)))
    wrapped = {(p, n) for p, n, _ in wrappers}  # aliases aren't in `thms`
    by_alpha = {k: [t for t in c if (t.path, t.name) not in wrapped]
                for k, c in by_alpha.items()}
    by_stmt = collections.defaultdict(list)
    for c in by_alpha.values():
        for t in c:
            by_stmt[t.stmt].append((t.path, t.name))
    found = Found({
        'same': [c for c in by_stmt.values() if len(c) > 1],
        'alpha': [[(t.path, t.name) for t in c] for c in by_alpha.values()
                  if len({t.stmt for t in c}) > 1],
        'proofs': components(similar_proofs(
            {(t.path, t.name): proof_lines(t.proof) for t in thms})),
    }, wrappers, set())

    conj: dict[str, str] = {}

    def conj_key(c: str) -> str:
        if c not in conj:
            conj[c] = alpha(c, free)
        return conj[c]
    preds = collections.defaultdict(set)   # conjunct -> predicates with it
    for p, body in defs:
        eq = split_top(strip_binders(body), ('<=>', '⇔'))
        if len(eq) != 2:   # `p ... = rhs`, split at its first ` = `
            lhs, *rhs = split_top(strip_binders(body), (' = ',))
            eq = [lhs, ' = '.join(rhs)] if rhs else []
        if len(eq) == 2:
            args = set(re.findall(ID, eq[0])) - known - {p}
            rhs = strip_binders(eq[1])
            cs = {alpha(c, free | args) for c in
                  premises(rhs) or conjuncts(rhs)}
            if len(cs) >= 8:
                for c in cs:
                    preds[c].add(p)
    for t in thms:
        hit = collections.Counter(p for c in {conj_key(c) for c in nested_premises(t.stmt)}
                                  for p in preds.get(c, ()))
        best = sorted((-n, p) for p, n in hit.items()
                      if n >= 8 and not names(t.stmt, p))
        if best:
            found.hints.add(('restates', t.path, t.name,
                             f'{best[0][1]} ({-best[0][0]} conjuncts)'))

    all_names = {t.name for t in thms} | {n for _, n, _ in wrappers}
    for t in thms:
        base, _, suffix = t.name.rpartition('_')
        if suffix in VARIANTS and base in all_names and not names(unquoted[t], base):
            found.hints.add(('variant', t.path, t.name, base))

    if special:
        const = re.compile(r"(?<![A-Za-z0-9_'$.])(" + '|'.join(sorted(special))
                           + r")(?![A-Za-z0-9_'])")
        for t in thms:
            for c in set(const.findall(t.stmt)):
                k = alpha(re.sub(r"(?<![A-Za-z0-9_'$.])" + c + r"(?![A-Za-z0-9_'])",
                                 'generic_', t.stmt), free | {'generic_'})
                found.hints |= {('instance', t.path, t.name, f'{u.path}:{u.name} at {c}')
                                for u in by_alpha.get(k, ())
                                if not names(unquoted[t], u.name)}
    return found


def tree(out: str, roots: list[str]) -> None:
    """Whole-tree mode: write scan_tree's clusters and hints under `out`."""
    for r in roots:
        if not git(r, 'rev-parse', '--git-dir'):
            sys.exit(f"root {r!r} is not a git checkout")
    wt = os.path.realpath(roots[0])
    found = scan_tree({os.path.relpath(rp, wt): txt for rp, txt in scripts(roots)})
    os.makedirs(out, exist_ok=True)
    for kind, comps in found.clusters.items():
        with open(os.path.join(out, f'{kind}.tsv'), 'w') as f:
            f.write('cluster\tsize\tpath\tname\n')
            for c in sorted(sorted(c) for c in comps):
                f.writelines(f'{c[0][0]}:{c[0][1]}\t{len(c)}\t{p}\t{n}\n' for p, n in c)
        print(f"{kind}: {len(comps)} clusters, {sum(map(len, comps))} theorems")
    with open(os.path.join(out, 'wrappers.tsv'), 'w') as f:
        f.write('path\tname\tcites\n')
        f.writelines('\t'.join(w) + '\n' for w in sorted(found.wrappers))
    print(f"wrappers: {len(found.wrappers)}")
    with open(os.path.join(out, 'hints.tsv'), 'w') as f:
        f.write('hint\tpath\tname\tdetail\n')
        f.writelines('\t'.join(h) + '\n' for h in sorted(found.hints))
    for kind in ('restates', 'variant', 'instance'):
        print(f"{kind} hints: {sum(h[0] == kind for h in found.hints)}")


if __name__ == '__main__':
    if sys.argv[1:2] in (['-h'], ['--help']):
        print(__doc__)
        sys.exit(0)
    if len(sys.argv) < (4 if sys.argv[1:2] == ['--tree'] else 3):
        sys.exit(f"usage: {sys.argv[0]} <worktree> <base-ref> <root>...\n"
                 f"       {sys.argv[0]} --tree <out-dir> <root>...\n"
                 f"(--help for what each reports)")
    if sys.argv[1] == '--tree':
        tree(sys.argv[2], sys.argv[3:])
        sys.exit(0)
    main(sys.argv[1], sys.argv[2], sys.argv[3:])
