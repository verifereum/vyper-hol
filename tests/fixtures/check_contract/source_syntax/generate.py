"""Retain pinned parser syntax BEFORE vy_ast.get_node erases qualifiers.

Run with PYTHONPATH=<VYPER_PIN checkout> <pinned venv python> generate.py
(or --check). This is untrusted frontend fixture generation, not evaluation or
source acceptance evidence. No semantic analysis or constant folder is invoked.
Python AST -> JSON adapts only field names/shapes expected by Vyper JSON:
top-level AnnAssign -> VariableDecl; singleton Assign.targets -> target;
Compare ops/comparators -> op/right; List/Tuple elts -> elements.
The pinned AnnotatingVisitor performs its usual lexical literal normalization.
"""
import argparse
import ast
import hashlib
import json
import runpy
import subprocess
import vyper
from pathlib import Path

from vyper.ast.parse import annotate_python_ast
from vyper.ast.pre_parser import PreParser

ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / "lowering/defs/bytecode"
OUT = Path(__file__).resolve().parent
PIN = "cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c"


convert = runpy.run_path(str(ROOT / "tools/source_module_loader.py"))["convert"]


def retained(source, name):
    pre = PreParser(False)
    pre.parse(source)
    tree = ast.parse(pre.reformatted_code)
    annotate_python_ast(tree, source, pre, module_path=name + ".vy", resolved_path=name + ".vy")
    result = convert(tree)
    for decl in result["body"]:
        if decl["ast_type"] == "AnnAssign":
            decl["ast_type"] = "VariableDecl"
    return {"ast": result, "imports": []}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    checkout = Path(vyper.__file__).resolve().parent.parent
    revision = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
    assert revision == PIN, (revision, PIN)
    hashes = {}
    for name in (BASE / "folded-value-witnesses.txt").read_text().split():
        source = (BASE / "folded-value-sources" / (name + ".vy")).read_text()
        hashes[name] = hashlib.sha256(source.encode()).hexdigest()
        data = json.dumps(retained(source, name), sort_keys=True, separators=(",", ":")) + "\n"
        path = OUT / (name + ".json")
        if args.check:
            assert path.read_text() == data, name
        else:
            path.write_text(data)
    data = json.dumps({"vyper_pin": PIN, "source_sha256": hashes,
                       "boundary": "annotate_python_ast before vy_ast.get_node; no semantic analysis"},
                      indent=2, sort_keys=True) + "\n"
    if args.check:
        assert (OUT / "provenance.json").read_text() == data
    else:
        (OUT / "provenance.json").write_text(data)
    print("37 retained pre-erasure syntax fixtures " + ("checked" if args.check else "generated"))


if __name__ == "__main__":
    main()
