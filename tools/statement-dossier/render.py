#!/usr/bin/env python3
"""Render the compiler correctness dossier with the project's pinned HOL."""

import argparse
from collections.abc import Iterator
from contextlib import contextmanager, nullcontext
import hashlib
from pathlib import Path
import re
import subprocess
import tempfile


CONFIG = Path(__file__).resolve().parent
ROOT = CONFIG.parent.parent
THEORY = "compilerCorrectnessDossierTarget"
VYPER_URL = "https://github.com/verifereum/vyper-hol"
PROVED = ["e2eDeployed", "e2eGasSufficientTop"]
# The overview says these are proved with no admitted step.
PUBLIC_THEOREMS = ["e2eDeployedTheory:e2e_deploy_correctness_deployed",
                   "e2eDeployedTheory:vyper_call_correct_deployed",
                   "e2eGasSufficientTopTheory:e2e_deploy_gas_sufficient",
                   "e2eDeployedTheory:vyper_call_gas_sufficient_deployed"]


def output(*command: str) -> str:
    return subprocess.check_output(command, cwd=ROOT, text=True).strip()


def sml_string(value: str | Path) -> str:
    # SML strings use decimal escapes for bytes outside printable ASCII.
    escaped = []
    for byte in str(value).encode():
        if byte in (34, 92):
            escaped.append("\\" + chr(byte))
        elif 32 <= byte < 127:
            escaped.append(chr(byte))
        else:
            escaped.append(f"\\{byte:03d}")
    return '"' + "".join(escaped) + '"'


def package(context: str, name: str) -> tuple[Path, str, str]:
    snapshot = re.search(rf"^package-snapshot: {name} (.+)$", context, re.M)
    root = re.search(rf"^package-source-root: {name} (.+)$", context, re.M)
    pin = re.search(r"\|\d+:(https://[^|]+?)\.git\|40:([a-f0-9]{40})", snapshot[1]) if snapshot else None
    if not root or not pin:
        raise SystemExit(f"holbuild context did not report a pinned Git source for {name}")
    url, revision = pin.groups()
    return Path(root[1]), f"{url}/blob/{revision}", revision


def source_links(root: Path, base: str) -> Iterator[tuple[str, str]]:
    for script in sorted(root.rglob("*Script.sml")):
        path = script.relative_to(root)
        if not any(part.startswith(".") for part in path.parts):
            yield script.name.removesuffix("Script.sml"), f"{base}/{path.as_posix()}"


def code_lines(source: str) -> str:
    """Mask nested comments while retaining line boundaries and offsets."""
    masked = list(source)
    depth = 0
    cursor = 0
    markers = re.compile(r'\(\*|\*\)|"')
    quoted = re.compile(r'"(?:[^"\\]|\\[\s\S])*"')
    while marker := markers.search(source, cursor):
        if not depth and marker[0] == '"':
            literal = quoted.match(source, marker.start())
            cursor = literal.end() if literal else marker.end()
            continue
        if marker[0] == "(*":
            if not depth:
                start = marker.start()
            depth += 1
        elif marker[0] == "*)" and depth:
            depth -= 1
            if not depth:
                masked[start:marker.end()] = ["\n" if c == "\n" else " " for c in source[start:marker.end()]]
        cursor = marker.end()
    if depth:
        raise SystemExit("unterminated comment in the module-list draft")
    return "".join(masked)


def draft_statement(spec: str) -> tuple[str, str]:
    revision, separator, path = spec.partition(":")
    if not (revision and separator and path):
        raise SystemExit("--draft expects REVISION:path/to/e2eModsTopsDraftScript.sml")
    commit = output("git", "rev-parse", "--verify", "--end-of-options", f"{revision}^{{commit}}")
    source = output("git", "show", f"{commit}:{path}")
    matches = list(re.finditer(r"^Theorem vyper_call_correct_mods:\n(.*?)^Proof\b", code_lines(source), re.M | re.S))
    if len(matches) != 1:
        raise SystemExit("expected exactly one live Theorem vyper_call_correct_mods declaration followed by Proof")
    term = source[matches[0].start(1):matches[0].end(1)]
    digest = hashlib.sha256(term.encode()).hexdigest()
    statement = f"Theorem vyper_call_correct_mods:\n{term}Proof\n  cheat\nQED\n"
    return statement, f"Draft source: `{commit}:{path}`. Statement SHA-256: `{digest}`."


def public_expansion() -> tuple[list[str], list[tuple[str, str]]]:
    """The allowlist's theories and single `Thy$name` constants."""
    theories, constants = [], []
    for line in (CONFIG / "public-expand.txt").read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        thy, dollar, name = line.partition("$")
        if dollar:
            constants.append((thy, name))
        else:
            theories.append(line)
    return theories, constants


def write_overview(destination: Path, revision: str, dossier: str) -> None:
    """Render the overview to HTML, checking its links into the dossier."""
    source = (CONFIG / "overview.md").read_text()
    stamp = f"\n\nBuilt from [vyper-hol {revision}]({VYPER_URL}/tree/{revision}).\n"
    subprocess.run(["pandoc", "--standalone", "--from", "markdown", "--to", "html5",
                    "--output", str(destination)], input=source + stamp, text=True, check=True)
    ids = set(re.findall(r'\bid="([^"]+)"', dossier))
    links = set(re.findall(r'\bhref="(?:\./)?dossier\.html#([^"]+)"', destination.read_text()))
    missing = sorted(links - ids)
    if missing:
        raise SystemExit("overview.md links to dossier anchors that do not exist: " + ", ".join(missing))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--draft", metavar="REVISION:PATH", help="render the module-list target from a Git object")
    parser.add_argument("--exporter", type=Path, help="use statementDossierLib.sml from this HOL checkout's HEAD")
    output_arg = parser.add_mutually_exclusive_group(required=True)
    output_arg.add_argument("--output", type=Path, help="HTML file to write")
    output_arg.add_argument("--public", metavar="DIR", type=Path,
                            help="write the public overview and dossier, index.html and dossier.html, "
                                 "expanding only the definitions public-expand.txt lists")
    parser.add_argument("--depth", type=int,
                        help="expand only definitions this many steps below the theorems (default 4)")
    args = parser.parse_args()
    if args.public and (args.draft or args.depth is not None):
        raise SystemExit("--public takes neither --draft nor --depth")
    if args.depth is None:
        args.depth = 4
    if args.depth < 1:
        raise SystemExit(f"--depth must be at least 1, not {args.depth}")
    target, draft_source = draft_statement(args.draft) if args.draft else ("", "")
    patch = ""
    exporter_revision = ""
    if args.exporter:
        exporter_revision = output("git", "-C", str(args.exporter.resolve()), "rev-parse", "HEAD")
        patch = output("git", "-C", str(args.exporter.resolve()), "show",
                       f"{exporter_revision}:src/statementdossier/statementDossierLib.sml")
    if output("git", "status", "--porcelain", "--untracked-files=no"):
        raise SystemExit("commit or restore modified tracked files before rendering")
    revision = output("git", "rev-parse", "HEAD")
    context = output("holbuild", "context")
    hol, hol_url, hol_revision = package(context, "hol")
    vfm, vfm_url, _ = package(context, "verifereum")
    links = [*source_links(vfm, vfm_url), *source_links(hol / "src", hol_url + "/src")]
    links += [(Path(path).name.removesuffix("Script.sml"), f"{VYPER_URL}/blob/{revision}/{path}")
              for path in output("git", "ls-files", "*Script.sml").splitlines()]
    sources = ",\n  ".join(f"({sml_string(theory)}, {sml_string(url)})" for theory, url in links)
    public_theories, public_consts = public_expansion() if args.public else ([], [])
    public_dir = args.public.resolve() if args.public else None
    destination = public_dir / "dossier.html" if public_dir else args.output.resolve()
    scratch = target_script(target) if target else nullcontext()
    with tempfile.TemporaryDirectory(prefix=".compiler-dossier-", dir=destination.parent) as temp, scratch:
        html = Path(temp) / "dossier.html"
        theories = [THEORY] if target else PROVED
        subprocess.run(["holbuild", "-j4", "build", *[thy + "Theory" for thy in theories]],
                       cwd=ROOT, check=True)
        if args.public:
            subprocess.run(["holbuild", "check", *PUBLIC_THEOREMS], cwd=ROOT, check=True)
        objects = [ROOT / ".holbuild" / "obj" / "lowering" / (thy + "Theory") for thy in theories]
        loads = ",\n  ".join(map(sml_string, objects))
        script = f"""val () = Globals.print_thy_loads := false;
val () = List.app load [
  {loads}];
val () = load "statementDossierLib";

{patch}

val projectRoot = {sml_string(ROOT)}
val configDir = {sml_string(CONFIG)}
val htmlOutput = {sml_string(html)}
val sourceRevision = {sml_string(revision)}
val holRevision = {sml_string(hol_revision)}
val exporterRevision = {sml_string(exporter_revision)}
val draftSource = {sml_string(draft_source)}
val draftTheory = {sml_string(THEORY)}
val depth = {args.depth}
val public = {"true" if args.public else "false"}
val publicTheories = [{", ".join(map(sml_string, public_theories))}]
val publicConsts = [{", ".join(f"{{Thy = {sml_string(t)}, Name = {sml_string(n)}}}" for t, n in public_consts)}]
val theorySources = [
  {sources}]

""" + (CONFIG / "render.sml").read_text()
        driver = Path(temp) / "render.sml"
        driver.write_text(script, encoding="utf-8")
        subprocess.run([hol / "bin" / "hol", "--maxheap", "4096", "--gcthreads", "1",
                        "run", driver], cwd=ROOT, check=True)
        if args.public:
            overview = Path(temp) / "index.html"
            write_overview(overview, revision, html.read_text())
        html.replace(destination)
        if args.public:
            overview.replace(public_dir / "index.html")


@contextmanager
def target_script(target: str) -> Iterator[None]:
    scratch = ROOT / "lowering" / f"{THEORY}Script.sml"
    stream = scratch.open("x", encoding="utf-8")
    try:
        with stream:
            stream.write(f"""Theory {THEORY}
Ancestors
  e2eModsDefs e2eCorrectness[qualified] e2eDefs compileUnit compileVyper
  vyperInterpreter frameOutcome frameGas callTrace vfmExecution vfmConstants
  vfmContext

(* Presentation only. This scratch theory is never committed. *)
{target}""")
        yield
    finally:
        scratch.unlink()


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit(error.returncode) from error
