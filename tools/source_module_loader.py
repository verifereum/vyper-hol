"""Explicitly trusted pre-erasure source loader for ordinary source pairing.

Run with the pinned Vyper checkout on PYTHONPATH and its supported Python.
The manifest supplies canonical namespace keys in main, dependency-first order:
  [{"key": ["main"], "path": "contract.vy"},
   {"key": ["lib"], "path": "lib.vy"}]

This is a syntax/namespace trust boundary, NOT a source acceptance oracle. It
never runs get_node, semantic analysis, the constant folder, or jsonToVyper.
A protocol label/hash records a claim; it does not authenticate the loader.
"""
import argparse
import ast
import hashlib
import json
import subprocess
from decimal import Decimal
from pathlib import Path

PROTOCOL = "vyper-hol/source-loader-v1"
BOUNDARY = "annotate_python_ast-before-get_node"
PIN = "cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c"


def convert(value):
    if isinstance(value, ast.AST):
        result = {
            key: convert(child)
            for key, child in vars(value).items()
            if key not in {"ctx", "full_source_code", "node_source_code", "type_ignores"}
        }
        kind = result.get("ast_type")
        if kind == "Assign":
            targets = result.pop("targets")
            if len(targets) != 1:
                raise ValueError("multiple assignment targets are not sourceSyntax")
            result["target"] = targets[0]
        if kind == "Compare":
            operators, operands = result.pop("ops"), result.pop("comparators")
            if len(operators) != 1 or len(operands) != 1:
                raise ValueError("chained comparisons are not sourceSyntax")
            result["op"], result["right"] = operators[0], operands[0]
        if kind in {"Tuple", "List"}:
            result["elements"] = result.pop("elts")
        if kind == "ImportFrom" and result.get("module") is None:
            result["module"] = ""
        return result
    if isinstance(value, list):
        return [convert(child) for child in value]
    if isinstance(value, bytes):
        return "0x" + value.hex()
    if isinstance(value, Decimal):
        return str(value)
    # annotate_python_ast has already marked the node ast_type="Ellipsis".
    # Its redundant Python singleton payload is not a JSON value; the source
    # decoder consumes the node tag, never this payload (or a fabricated body).
    if value is Ellipsis:
        return None
    return value


def capture(manifest):
    import vyper
    from vyper.ast.parse import annotate_python_ast
    from vyper.ast.pre_parser import PreParser

    checkout = Path(vyper.__file__).resolve().parent.parent
    revision = subprocess.check_output(
        ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True
    ).strip()
    if revision != PIN:
        raise ValueError(f"source loader requires Vyper {PIN}, found {revision}")
    keys, trees, policies, interfaces, provenance = [], [], [], [], []
    for entry in manifest:
        key, path = entry["key"], Path(entry["path"])
        if not key or not all(isinstance(part, str) and part for part in key):
            raise ValueError("nonempty canonical module keys required")
        if key in keys:
            raise ValueError(f"duplicate module key: {key}")
        if path.suffix not in {".vy", ".vyi"}:
            raise ValueError("only actual .vy/.vyi source; JSON ABI is not source syntax")
        source = path.read_text()
        interface = path.suffix == ".vyi"
        pre = PreParser(interface)
        pre.parse(source)
        tree = ast.parse(pre.reformatted_code)
        annotate_python_ast(tree, source, pre, source_id=entry.get("source_id", 0),
                            module_path=str(path), resolved_path=str(path.resolve()))
        syntax = convert(tree)
        # Mirror only get_node's syntactic top-level classification. Crucially,
        # do NOT call it: VariableDecl construction erases qualifier syntax.
        structural = {"exports": "ExportsDecl", "initializes": "InitializesDecl",
                      "uses": "UsesDecl", "implements": "ImplementsDecl"}
        for declaration in syntax["body"]:
            if declaration["ast_type"] == "AnnAssign":
                target = declaration["target"]
                name = target.get("id") if target.get("ast_type") == "Name" else None
                declaration["ast_type"] = structural.get(name, "VariableDecl")
        keys.append(key)
        trees.append(syntax)
        policies.append(bool(pre.settings.nonreentrancy_by_default))
        interfaces.append(interface)
        provenance.append({"key": key, "path": str(path.resolve()),
                           "source_sha256": hashlib.sha256(source.encode()).hexdigest()})
    if not trees:
        raise ValueError("main source module is required")
    return {"protocol": PROTOCOL, "phase": BOUNDARY, "vyper_pin": revision,
            "keys": keys, "nonreentrancy_by_default": policies,
            "declaration_only": interfaces,
            "annotated_ast": {"ast": trees[0], "imports": trees[1:]},
            "provenance": provenance}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    result = capture(json.loads(args.manifest.read_text()))
    args.output.write_text(json.dumps(result, sort_keys=True, separators=(",", ":")) + "\n")


if __name__ == "__main__":
    main()
