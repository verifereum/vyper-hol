#!/usr/bin/env python3
"""Fuzz compile_vyper's bytecode against the pinned Python Vyper compiler.

Generates small random Vyper programs, exports each one as the bytecode
witness suites do (`vyper -f annotated_ast,layout`, merged by
tests/sanitize_check_contract_json.py, and the oracle bytecode from the same
flags as bytecode/memory_store_witnesses.py), then compiles the
JSON with the native runner (tools/build_native_json_parity.py) and compares.

Run it with the canonical oracle venv's `vyper` first on PATH (see
bytecode/README.md). Programs Python Vyper rejects are
discarded; programs the HOL frontend, check_contract or the compiler rejects
are coverage gaps, counted separately from divergences. check_contract runs
through `holbuild run` on bytecode/native/check_programs.sml,
after the driver brings vyperCheckContractFrontendLib up to date with
`holbuild build`. Every program that is not a PASS is kept in the output
directory with its JSON, oracle, native bytes and verdict.

Vyper's bytecode at the pin depends on PYTHONHASHSEED for some programs, so
the oracle uses seed 0, and a mismatch counts as a divergence only if seeds
1-7 do not produce the native bytes either ("seed-dependent" otherwise).
With --minimize, each divergence is also reduced, by deleting statements and
unwrapping blocks, to <name>.min.vy; the reduced program is not rechecked
with check_contract.
"""

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import random
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "bytecode/native/bytecode_parity_json.exe"
SANITIZER = ROOT / "tests/sanitize_check_contract_json.py"
CHECKER = ROOT / "bytecode/native/check_programs.sml"
ORACLE_FLAGS = ["--experimental-codegen", "--evm-version", "prague", "-O", "none",
                "--disable-bytecode-metadata", "-f", "bytecode,bytecode_runtime"]
# The hash seeds tried before a mismatch counts as a divergence.
OTHER_SEEDS = range(1, 8)

# (name, bits, signed) for the integer types the generator uses.
INTS = [("uint256", 256, False), ("uint8", 8, False), ("uint128", 128, False),
        ("int256", 256, True), ("int128", 128, True), ("int8", 8, True)]
INT_TYPES = {name: (bits, signed) for name, bits, signed in INTS}
SCALARS = list(INT_TYPES) + ["bool", "address", "bytes32"]
SARRAY, DARRAY = "uint256[2]", "DynArray[uint256, 3]"
TYPES = SCALARS + [SARRAY, DARRAY]
# Generated names (a0, v3, s1, i4, m2) and the non-literal addresses.
VARIABLE = re.compile(r"\b[avsim]\d+\b|msg\.sender|\bself\b")
LEAF = re.compile(r"-?\d+|True|False|0x[0-9a-f]+|empty\(.*\)|\[[-\d, ]*\]|(self\.)?[avsim]\d+|msg\.sender|self")


class Program:
    """A random program; every expression is generated at a known type."""

    def __init__(self, rng: random.Random):
        self.rng = rng
        self.storage = {}   # name -> type
        self.maps = {}      # name -> (key type, value type)
        self.internals = [] # (name, argument types, return type) callable so far
        self.lines = []
        self.fresh = 0

    def name(self, prefix):
        self.fresh += 1
        return f"{prefix}{self.fresh}"

    # ---- expressions ----
    def literal(self, ty):
        rng = self.rng
        if ty in INT_TYPES:
            bits, signed = INT_TYPES[ty]
            low, high = (-(2 ** (bits - 1)), 2 ** (bits - 1) - 1) if signed else (0, 2 ** bits - 1)
            value = rng.choice([0, 1, 2, 3, 7, 255, high, low, rng.randint(low, high)])
            return str(max(low, min(high, value)))
        if ty == "bool":
            return rng.choice(["True", "False"])
        if ty == "address":
            return rng.choice(["msg.sender", "self", "empty(address)"])
        if ty == SARRAY:
            return f"[{rng.choice([0, 1, 7])}, {rng.choice([0, 2, 9])}]"
        if ty == DARRAY:
            return rng.choice([f"empty({DARRAY})", "[]", "[5]", "[1, 2]"])
        return "0x" + "".join(rng.choice("0123456789abcdef") for _ in range(64))

    def expr(self, ty, env, depth):
        """An expression of type ty that Vyper does not constant-fold: the
        frontend ignores Vyper's folded values (vyper-hol#543), so folding
        is a known divergence, not one to look for."""
        for _ in range(5):
            e = self.unfolded_expr(ty, env, depth)
            if LEAF.fullmatch(e) or VARIABLE.search(e):
                return e
        return self.literal(ty)

    def unfolded_expr(self, ty, env, depth):
        rng = self.rng
        names = [n for n, t in env.items() if t == ty]
        names += [f"self.{n}" for n, t in self.storage.items() if t == ty]
        maps = [n for n, (_, v) in self.maps.items() if v == ty]
        if depth <= 0 or rng.random() < 0.3:
            if names and rng.random() < 0.7:
                return rng.choice(names)
            return self.literal(ty)
        if maps and rng.random() < 0.15:
            m = rng.choice(maps)
            return f"self.{m}[{self.expr(self.maps[m][0], env, depth - 1)}]"
        sub = lambda t=ty: self.expr(t, env, depth - 1)
        calls = [f for f in self.internals if f[2] == ty]
        if calls and rng.random() < 0.15:
            fname, argtys, _ = rng.choice(calls)
            return f"self.{fname}({', '.join(self.expr(t, env, depth - 1) for t in argtys)})"
        if rng.random() < 0.1:
            return f"({sub()} if {self.expr('bool', env, depth - 1)} else {sub()})"
        if ty == "uint256" and rng.random() < 0.2:
            arrays = [n for n, t in env.items() if t in (SARRAY, DARRAY)]
            arrays += [f"self.{n}" for n, t in self.storage.items() if t in (SARRAY, DARRAY)]
            if arrays:
                a = rng.choice(arrays)
                if self.type_of(a, env) == DARRAY and rng.random() < 0.4:
                    return f"len({a})"
                return f"{a}[{rng.choice(['0', '1', self.expr('uint256', env, 0)])}]"
        if ty in (SARRAY, DARRAY):
            n = 2 if ty == SARRAY else rng.randint(0, 3)
            return "[" + ", ".join(self.expr("uint256", env, depth - 1) for _ in range(n)) + "]"
        if ty in INT_TYPES:
            # Vyper folds literal-only arithmetic and types the result as a
            # literal, which rarely fits ty; anchor each operation on a name.
            if not names:
                return self.literal(ty)
            anchor = rng.choice(names)
            bits, signed = INT_TYPES[ty]
            ops = ["+", "-", "*", "//", "%", "min", "max"]
            ops += ["neg"] if signed else ["&", "|", "^"]
            op = rng.choice(ops)
            if op in ("min", "max"):
                return f"{op}({anchor}, {sub()})"
            if op == "neg":
                return f"-{anchor}"
            if op in ("//", "%"):
                # A literal zero divisor is a compile-time error.
                return f"({anchor} {op} {rng.choice(['1', '3', '7'] + names)})"
            if rng.random() < 0.2 and op in ("+", "-", "*"):
                fn = {"+": "unsafe_add", "-": "unsafe_sub", "*": "unsafe_mul"}[op]
                return f"{fn}({anchor}, {sub()})"
            return f"({anchor} {op} {sub()})"
        if ty == "bool":
            choice = rng.randrange(4)
            if choice == 0:
                t = rng.choice(list(INT_TYPES))
                op = rng.choice(["<", "<=", ">", ">=", "==", "!="])
                return f"({self.expr(t, env, depth - 1)} {op} {self.expr(t, env, depth - 1)})"
            if choice == 1:
                return f"({sub()} {rng.choice(['and', 'or'])} {sub()})"
            if choice == 2:
                return f"(not {sub()})"
            t = rng.choice(["address", "bytes32"])
            return f"({self.expr(t, env, depth - 1)} {rng.choice(['==', '!='])} {self.expr(t, env, depth - 1)})"
        if ty == "bytes32":
            if rng.random() < 0.5:
                return f"keccak256({sub()})"
            return f"convert({self.expr('uint256', env, depth - 1)}, bytes32)"
        return names[0] if names else self.literal(ty)

    def type_of(self, name, env):
        return self.storage[name[5:]] if name.startswith("self.") else env[name]

    # ---- statements ----
    def block(self, env, indent, depth, ret):
        rng = self.rng
        pad = "    " * indent
        out = []
        for _ in range(rng.randint(1, 4)):
            choice = rng.randrange(8)
            if choice == 0 or not env:
                ty = rng.choice(TYPES)
                n = self.name("v")
                out.append(f"{pad}{n}: {ty} = {self.expr(ty, env, 2)}")
                env = {**env, n: ty}
            elif choice == 1:
                n, ty = rng.choice(list(env.items()))
                if n.startswith("v"):  # arguments and loop variables are immutable
                    out.append(f"{pad}{n} = {self.expr(ty, env, 2)}")
            elif choice == 2 and self.storage:
                n, ty = rng.choice(list(self.storage.items()))
                out.append(f"{pad}self.{n} = {self.expr(ty, env, 2)}")
            elif choice == 3 and self.maps:
                n, (k, v) = rng.choice(list(self.maps.items()))
                out.append(f"{pad}self.{n}[{self.expr(k, env, 1)}] = {self.expr(v, env, 2)}")
            elif choice == 4 and depth > 0:
                out.append(f"{pad}if {self.expr('bool', env, 2)}:")
                out += self.block(env, indent + 1, depth - 1, ret)
                if rng.random() < 0.5:
                    out.append(f"{pad}else:")
                    out += self.block(env, indent + 1, depth - 1, ret)
            elif choice == 5 and depth > 0:
                i = self.name("i")
                out.append(f"{pad}for {i}: uint256 in range({rng.randint(1, 4)}):")
                out += self.block({**env, i: "uint256"}, indent + 1, depth - 1, ret)
            elif choice == 7 and rng.random() < 0.5:
                dyns = [n for n, t in env.items() if t == DARRAY and n.startswith("v")]
                dyns += [f"self.{n}" for n, t in self.storage.items() if t == DARRAY]
                if dyns:
                    d = rng.choice(dyns)
                    out.append(f"{pad}{d}.pop()" if rng.random() < 0.3
                               else f"{pad}{d}.append({self.expr('uint256', env, 1)})")
            elif choice == 6:
                # A condition that folds to False is a compile-time error.
                ints = [n for n, t in env.items() if t in INT_TYPES]
                if ints:
                    n = rng.choice(ints)
                    op = rng.choice(["<", "<=", ">", ">=", "==", "!="])
                    out.append(f"{pad}assert {n} {op} {self.expr(env[n], env, 2)}")
            elif ret and depth < 2:
                out.append(f"{pad}return {self.expr(ret, env, 2)}")
                break
        return out or [f"{pad}pass"]

    def ended(self, body, ret, args):
        """body, with a final return unless it already ends with one."""
        if body[-1].startswith("    return "):
            return body
        return body + [f"    return {self.expr(ret, args, 2)}"]

    def generate(self):
        rng = self.rng
        for _ in range(rng.randint(0, 3)):
            ty = rng.choice(TYPES)
            self.storage[self.name("s")] = ty
            self.lines.append(f"s{self.fresh}: {ty}")
        for _ in range(rng.randint(0, 2)):
            k, v = rng.choice(SCALARS), rng.choice(TYPES)
            self.maps[self.name("m")] = (k, v)
            self.lines.append(f"m{self.fresh}: HashMap[{k}, {v}]")
        for _ in range(rng.randint(0, 2)):
            args = {f"a{j}": rng.choice(TYPES) for j in range(rng.randint(0, 2))}
            ret = rng.choice(TYPES)
            fname = self.name("g")
            signature = ", ".join(f"{n}: {t}" for n, t in args.items())
            self.lines += ["", "@internal", f"def {fname}({signature}) -> {ret}:"]
            self.lines += self.ended(self.block(args, 1, 1, ret), ret, args)
            # Declared after its body, so internal calls cannot recurse.
            self.internals.append((fname, list(args.values()), ret))
        for _ in range(rng.randint(1, 3)):
            args = {f"a{j}": rng.choice(TYPES) for j in range(rng.randint(0, 3))}
            ret = rng.choice(TYPES + [None])
            signature = ", ".join(f"{n}: {t}" for n, t in args.items())
            self.lines += ["", "@external",
                           f"def {self.name('f')}({signature})" +
                           (f" -> {ret}:" if ret else ":")]
            body = self.block(args, 1, 2, ret)
            self.lines += self.ended(body, ret, args) if ret else body
        return "\n".join(self.lines) + "\n"


def run(args, seed=0, env=()):
    """Run a command; PYTHONHASHSEED is fixed because Vyper's bytecode at the
    pin depends on Python's string hashing (set iteration order)."""
    env = {**os.environ, "PYTHONHASHSEED": str(seed), **dict(env)}
    return subprocess.run(args, capture_output=True, text=True, env=env)


def run_native(work: Path):
    """Runner output lines for the exports in work, and its exit status; native
    bytes go to work/native."""
    (work / "native").mkdir(exist_ok=True)
    result = run([str(RUNNER), str(work)], env={"NATIVE_PARITY_DUMP": str(work / "native")})
    lines = [l for l in result.stdout.splitlines() if l.split(" ", 1)[0] in ("PASS", "FAIL", "REJECT")]
    return lines, result.returncode


def checker_rejects(paths):
    """{stem: reason} for the JSON files check_contract rejects, in runtime or
    deploy mode."""
    listing = paths[0].parent / f"check-{paths[0].stem}.txt"
    listing.write_text("".join(f"{p}\n" for p in paths))
    result = subprocess.run(["holbuild", "run", str(CHECKER)], cwd=ROOT, capture_output=True,
                            stdin=subprocess.DEVNULL, text=True,
                            env={**os.environ, "CHECK_LIST": str(listing)})
    listing.unlink()
    lines = [l.split(" ", 1) for l in result.stdout.splitlines() if l.startswith("CHECK")]
    if len(lines) != len(paths):
        raise SystemExit(f"checker gave {len(lines)} results for {len(paths)} programs:\n"
                         + result.stderr[-2000:])
    return {Path(rest.split(": ", 1)[0]).stem: rest.partition(": ")[2]
            for tag, rest in lines if tag == "CHECKER-REJECT"}


def checked_verdict(line, work: Path):
    """(name, category, detail) of a runner line, where a mismatch that Vyper
    itself produces under another hash seed is "seed-dependent"."""
    name, category, detail = classify(line)
    if category == "divergence" and seed_dependent(work / (name + ".vy"), work / "native" / (name + ".hex")):
        category = "seed-dependent"
    return name, category, detail


def hex_entries(path: Path):
    return dict(line.split("=", 1) for line in path.read_text().split())


def seed_dependent(source: Path, native: Path):
    """Whether Vyper produces the native bytes under some other hash seed."""
    want = hex_entries(native)
    for seed in OTHER_SEEDS:
        code = run(["vyper", *ORACLE_FLAGS, str(source.resolve())], seed=seed)
        if code.returncode == 0:
            deploy, runtime = code.stdout.split()
            if (deploy.removeprefix("0x"), runtime.removeprefix("0x")) == (want["deploy"], want["runtime"]):
                return True
    return False


def vyper_error(stderr):
    """The exception line of a Vyper failure (it precedes the source excerpt)."""
    lines = [l for l in stderr.splitlines() if l.startswith("vyper.exceptions.")]
    line = (lines or stderr.strip().splitlines()[-1:] or ["vyper failed"])[0]
    return line.removeprefix("vyper.exceptions.")[:100]


def export(source: Path):
    """The witness-suite export of one source, or None if Vyper rejects it."""
    source = source.resolve()  # the sanitizer strips the absolute directory
    stem = source.with_suffix("")
    raw = run(["vyper", "-f", "annotated_ast,layout", str(source)])
    if raw.returncode != 0:
        return [vyper_error(raw.stderr)]
    raw_path = stem.with_suffix(".raw.json")
    raw_path.write_text(raw.stdout)
    merged = run([sys.executable, str(SANITIZER), str(raw_path), str(stem.with_suffix(".json")),
                  "--replace", str(source.parent) + "/="])
    raw_path.unlink()
    if merged.returncode != 0:
        return [merged.stderr.strip()]
    code = run(["vyper", *ORACLE_FLAGS, str(source)])
    if code.returncode != 0:
        return [vyper_error(code.stderr)]
    deploy, runtime = code.stdout.split()
    stem.with_suffix(".hex").write_text(
        f"deploy={deploy.removeprefix('0x')}\nruntime={runtime.removeprefix('0x')}\n")
    return None


def classify(line):
    """Map a runner line to (name, category, detail)."""
    tag, rest = line.split(" ", 1)
    name, _, detail = rest.partition(": ")
    name = name.split(" ")[0]
    if tag == "PASS":
        return name, "pass", ""
    if tag == "REJECT":
        return name, "frontend-gap", detail
    if detail == "compiler returned NONE":
        return name, "compiler-gap", detail
    if detail.startswith(("deploy differs", "runtime differs")):
        return name, "divergence", detail
    return name, "runner-error", detail


def verdict(source: Path, work: Path):
    """The runner's (category, detail) for one source, or None if Vyper rejects it."""
    shutil.rmtree(work, ignore_errors=True)
    work.mkdir(parents=True)
    copy = work / source.name
    copy.write_text(source.read_text())
    if export(copy) is not None:
        return None
    lines, _ = run_native(work)
    return checked_verdict(lines[0], work)[1:] if lines else None


def minimize(source: Path):
    """Delete statements (a line and the block under it) and unwrap if/for/else
    blocks while the program stays a divergence; write <name>.min.vy."""
    work = source.parent / (source.stem + "_minwork")
    lines = source.read_text().splitlines()
    indent = lambda l: len(l) - len(l.lstrip())
    def still_diverges(candidate):
        trial = work.parent / (source.stem + "_trial.vy")  # export() uses with_suffix
        trial.write_text("\n".join(candidate) + "\n")
        v = verdict(trial, work)
        trial.unlink()
        return v is not None and v[0] == "divergence"
    changed = True
    while changed:
        changed = False
        i = 0
        while i < len(lines):
            # A decorator goes with the function under it.
            head = i + 1 if lines[i].startswith("@") and i + 1 < len(lines) else i
            end = head + 1
            while end < len(lines) and (not lines[end].strip() or indent(lines[end]) > indent(lines[head])):
                end += 1
            body = lines[head + 1:end]
            candidates = [lines[:i] + lines[end:]]
            if body and lines[i].rstrip().endswith(":") and indent(lines[i]) > 0:
                candidates.append(lines[:i] + [l[4:] for l in body] + lines[end:])
            for candidate in candidates:
                if still_diverges(candidate):
                    lines, changed = candidate, True
                    break
            else:
                i += 1
    shutil.rmtree(work, ignore_errors=True)
    source.with_suffix(".min.vy").write_text("\n".join(lines) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--count", type=int, default=100)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--out", type=Path, required=True,
                        help="directory for the programs that do not pass")
    parser.add_argument("--minimize", action="store_true",
                        help="also reduce each divergence to <name>.min.vy")
    args = parser.parse_args()
    args.out = args.out.resolve()  # the checker runs from the repository root
    if not RUNNER.exists():
        raise SystemExit(f"missing {RUNNER}; run tools/build_native_json_parity.py")
    pin = (ROOT / "VYPER_PIN").read_text().strip()
    compiler = run(["vyper", "--version"]).stdout.strip()
    # vyper prints an abbreviated hash, of whatever length git chose.
    commit = compiler.rpartition("commit.")[2]
    if len(commit) < 7 or not pin.startswith(commit):
        raise SystemExit(f"vyper on PATH is {compiler!r}, not VYPER_PIN {pin}")
    # holbuild run loads the checker's theories as built; stale ones fail to load.
    subprocess.run(["holbuild", "build", "--skip-checkpoints", "--skip-proof-steps",
                    "vyperCheckContractFrontendLib"], cwd=ROOT, check=True,
                   stdin=subprocess.DEVNULL)
    args.out.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="work-", dir=args.out))  # private to this run
    sources = []
    for i in range(args.count):
        source = work / f"p{args.seed}_{i:05d}.vy"
        source.write_text(Program(random.Random(f"{args.seed}:{i}")).generate())
        sources.append(source)
    with ThreadPoolExecutor(args.jobs) as pool:
        rejected = dict(zip(sources, pool.map(export, sources)))
    counts = Counter()
    vyper_errors = Counter()
    for source, error in rejected.items():
        if error is not None:
            counts["vyper-reject"] += 1
            vyper_errors[error[0][:100]] += 1
            source.unlink()
    exported = sorted(work.glob("*.hex"))
    chunks = [[p.with_suffix(".json") for p in exported[i::args.jobs]] for i in range(args.jobs)]
    with ThreadPoolExecutor(args.jobs) as pool:
        unchecked = {}
        for rejects in pool.map(checker_rejects, [c for c in chunks if c]):
            unchecked.update(rejects)
    lines, status = run_native(work)
    with ThreadPoolExecutor(args.jobs) as pool:
        checked = list(pool.map(lambda l: checked_verdict(l, work), lines))
    verdicts = {name: (category, detail) for name, category, detail in checked}
    for source in exported:  # programs after a runner crash
        verdicts.setdefault(source.stem, ("runner-error", f"no runner verdict (runner exit {status})"))
    for name, reason in unchecked.items():
        if verdicts[name][0] != "frontend-gap":
            verdicts[name] = ("checker-gap", f"{reason[:200]} (runner: {verdicts[name][1] or 'pass'})")
    counts.update(category for category, _ in verdicts.values())
    for name, (category, detail) in verdicts.items():
        if category != "pass":
            keep = args.out / category
            keep.mkdir(exist_ok=True)
            for ext in (".vy", ".json", ".hex"):
                shutil.copy(work / (name + ext), keep / (name + ext))
            native = work / "native" / (name + ".hex")
            if native.exists():
                shutil.copy(native, keep / (name + ".native.hex"))
            (keep / (name + ".verdict")).write_text(detail + "\n")
    shutil.rmtree(work)
    if args.minimize and (args.out / "divergence").exists():
        with ThreadPoolExecutor(args.jobs) as pool:
            list(pool.map(minimize, sorted((args.out / "divergence").glob("*[0-9].vy"))))
    print(json.dumps({"seed": args.seed, "generated": args.count, **counts}, indent=2))
    for error, n in vyper_errors.most_common(5):
        print(f"vyper-reject x{n}: {error}")
    for category in ("divergence", "runner-error", "compiler-gap", "frontend-gap", "checker-gap"):
        details = Counter(d.split(" (")[0] for c, d in verdicts.values() if c == category)
        for detail, n in details.most_common(5):
            print(f"{category} x{n}: {detail[:160]}")


if __name__ == "__main__":
    main()
