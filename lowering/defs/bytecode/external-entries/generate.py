#!/usr/bin/env python3
"""Generate or check the task's pinned external-entry bytecode/AST fixtures."""

import argparse
import hashlib
import importlib.util
import json
import platform
from pathlib import Path

import vyper
from vyper.compiler.settings import OptimizationLevel, Settings
from vyper.exceptions import VyperException
from vyper.venom import OPTIMIZATION_PASSES


def check_rejected_headers(settings):
    """Keep the task's real-compiler rejection probes alongside its fixtures."""
    probes = {
        "nr_init": (
            "@deploy\n@nonreentrant\ndef __init__():\n    pass\n",
            "decorator disallowed on `__init__`"),
        "nr_pure": (
            "@external\n@pure\n@nonreentrant\ndef f() -> uint256:\n    return 1\n",
            "Cannot use reentrancy guard on pure functions"),
        "nr_nested_internal": (
            "@internal\n@nonreentrant\ndef g():\n    pass\n\n"
            "@external\n@nonreentrant\ndef f():\n    self.g()\n",
            "Cannot call `g` since it is `@nonreentrant`"),
        "p15_constructor_defaults": (
            "@deploy\ndef __init__(a: uint8 = 5):\n    pass\n",
            "Constructor may not use default arguments"),
    }
    for name, (source, reason) in probes.items():
        try:
            vyper.compile_code(
                source, contract_path=Path(name + ".vy"),
                output_formats=("annotated_ast_dict", "bytecode"),
                settings=settings, no_bytecode_metadata=True)
        except VyperException as error:
            if reason not in str(error):
                raise RuntimeError(f"unexpected rejection for {name}: {error}") from error
        else:
            raise RuntimeError(f"invalid header unexpectedly accepted: {name}")


def artifacts():
    here = Path(__file__).resolve().parent
    root = here.parents[3]
    pin = (root / "VYPER_PIN").read_text().strip()
    actual_commit = vyper.__commit__.strip()
    if len(actual_commit) < 8 or not pin.startswith(actual_commit):
        raise RuntimeError("Vyper does not match VYPER_PIN")
    if OPTIMIZATION_PASSES[OptimizationLevel.NONE] != OPTIMIZATION_PASSES[OptimizationLevel.O1]:
        raise RuntimeError("NONE no longer selects the pinned O1 Venom pipeline")
    spec = importlib.util.spec_from_file_location(
        "sanitize_check_contract_json", root / "tests/sanitize_check_contract_json.py")
    sanitizer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(sanitizer)
    names = {"nr_ext_nonpayable", "nr_multi", "nr_internal", "nr_pragma",
             "dflt_one_lit", "dflt_multi", "dflt_bytes", "dflt_sender",
             "nr_internal_return", "nr_internal_early_return",
             "base_dom1", "nr_ext_payable", "nr_ext_view", "nr_internal_view",
             "nr_default_fn", "nr_early_return", "nr_no_storage", "nr_transient_var",
             "nr_pragma_default", "nr_pragma_init", "nr_pragma_reentrant", "nr_pragma_pure",
             "dflt_only", "dflt_const", "dflt_payable", "dflt_internal_full",
             "c28_const_in_default_arg", "g37_pub_nonreentrancy_pragma", "rr_nr",
             "nr_fallback_early_return", "dflt_balance_after_transfer",
             "dflt_effectful_constant_index"}
    sources = sorted((here / "sources").glob("*.vy"))
    if {p.stem for p in sources} != names:
        raise RuntimeError("external-entry fixture source set changed")
    settings = Settings(optimize=OptimizationLevel.NONE, evm_version="prague",
                        experimental_codegen=True)
    check_rejected_headers(settings)
    files, fixtures = {}, {}
    for source in sources:
        result = vyper.compile_code(
            source.read_text(), contract_path=Path(source.name),
            output_formats=("annotated_ast_dict", "layout", "bytecode", "bytecode_runtime"),
            settings=settings, no_bytecode_metadata=True)
        deploy = result["bytecode"].removeprefix("0x").lower()
        runtime = result["bytecode_runtime"].removeprefix("0x").lower()
        files[f"oracle/{source.stem}.hex"] = f"deploy={deploy}\nruntime={runtime}\n"
        merged = sanitizer.rewrite(
            result["annotated_ast_dict"] | dict(result["layout"]), [])
        if any(marker in text for text in sanitizer.string_values(merged)
               for marker in sanitizer.DEFAULT_FORBIDDEN):
            raise RuntimeError("absolute path in annotated AST")
        files[f"ast/{source.stem}.json"] = json.dumps(
            merged, separators=(",", ":"), sort_keys=True) + "\n"
        fixtures[source.stem] = {
            "source": f"sources/{source.name}",
            "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "deploy_sha256": hashlib.sha256(bytes.fromhex(deploy)).hexdigest(),
            "runtime_sha256": hashlib.sha256(bytes.fromhex(runtime)).hexdigest(),
        }
    files["provenance.json"] = json.dumps({
        "vyper_commit": pin, "vyper_version": vyper.__version__,
        "python_version": platform.python_version(),
        "settings": {"experimental_codegen": True, "optimization_level": "NONE",
                     "venom_ir_pipeline": "O1", "evm_version": "prague",
                     "bytecode_metadata": False},
        "fixtures": fixtures,
        "validation_dependencies": {
            "rr_nr": [567], "c28_const_in_default_arg": [565],
            "g37_pub_nonreentrancy_pragma": [565],
            "dflt_effectful_constant_index": [565]},
    }, indent=2, sort_keys=True) + "\n"
    return here, files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--emit-json", action="store_true")
    args = parser.parse_args()
    here, files = artifacts()
    if args.emit_json:
        print(json.dumps(files))
        return
    for name, content in files.items():
        path = here / name
        if args.check:
            if not path.exists() or path.read_text() != content:
                raise RuntimeError(f"fixture differs: {name}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print(f"{'Checked' if args.check else 'Generated'} {len(files)} external-entry artifacts")


if __name__ == "__main__":
    main()
