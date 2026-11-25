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


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--draft", metavar="REVISION:PATH", help="render the module-list target from a Git object")
    parser.add_argument("--exporter", type=Path, help="use statementDossierLib.sml from this HOL checkout's HEAD")
    parser.add_argument("--output", required=True, type=Path, help="HTML file to write")
    args = parser.parse_args()
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
    links += [
        ("compileUnit", f"{VYPER_URL}/blob/{revision}/lowering/defs/compileUnitScript.sml"),
        ("compileVyper", f"{VYPER_URL}/blob/{revision}/lowering/defs/compileVyperScript.sml"),
        ("vyperTypeContract", f"{VYPER_URL}/blob/{revision}/semantics/type/vyperTypeContractScript.sml"),
        ("vyperInterpreter", f"{VYPER_URL}/blob/{revision}/semantics/vyperInterpreterScript.sml"),
    ]
    sources = ",\n  ".join(f"({sml_string(theory)}, {sml_string(url)})" for theory, url in links)
    destination = args.output.resolve()
    scratch = target_script(target) if target else nullcontext()
    with tempfile.TemporaryDirectory(prefix=".compiler-dossier-", dir=destination.parent) as temp, scratch:
        html = Path(temp) / "dossier.html"
        theories = [THEORY] if target else PROVED
        subprocess.run(["holbuild", "-j4", "build", *[thy + "Theory" for thy in theories]],
                       cwd=ROOT, check=True)
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
val theorySources = [
  {sources}]

""" + (CONFIG / "render.sml").read_text()
        driver = Path(temp) / "render.sml"
        driver.write_text(script, encoding="utf-8")
        subprocess.run([hol / "bin" / "hol", "--maxheap", "4096", "--gcthreads", "1",
                        "run", driver], cwd=ROOT, check=True)
        html.replace(destination)


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
