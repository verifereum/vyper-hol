#!/usr/bin/env python3
"""Fresh, pin-authoritative evidence for the opt-in source module frontend.

Run from the repository root. Results live in .agent-files/source-module-parity;
no expected bytecode or source implementation is rewritten. Any oracle drift,
valid-source rejection, residual evaluation or byte mismatch remains a failure.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "lowering/defs/bytecode"
OUT = ROOT / ".agent-files/source-module-parity"
ENVROOT = ROOT / ".agent-files/folded-value-validation"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dump(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


def run(label, argv, env=None):
    argv = list(map(str, argv))
    log = OUT / "commands" / (label + ".log")
    log.parent.mkdir(parents=True, exist_ok=True)
    start = time.time()
    with log.open("w") as stream:
        status = subprocess.run(argv, cwd=ROOT, env=env, stdout=stream,
                                stderr=subprocess.STDOUT).returncode
    dump(log.with_suffix(".json"), {"argv": argv, "exit": status,
         "elapsed_seconds": time.time() - start, "log_sha256": sha(log)})
    print(label, "exit=" + str(status), flush=True)
    return status


def names():
    result = (BASE / "folded-value-witnesses.txt").read_text().split()
    assert len(result) == 37 and len(set(result)) == 37
    return result


def oracle():
    pin = (ROOT / "VYPER_PIN").read_text().strip()
    checkout = ENVROOT / "vyper-src"
    assert subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip() == pin
    assert not subprocess.check_output(["git", "-C", checkout, "status", "--porcelain"])
    env = dict(os.environ)
    for k in ("PYTHONPATH", "PYTHONHOME", "PYTHONSTARTUP"):
        env.pop(k, None)
    python = ENVROOT / "venv/bin/python"
    # Do not trust a version/commit label alone: compare the imported compiler's
    # actual Python implementation files against the clean authoritative pin.
    verify = '''import hashlib,json,pathlib,subprocess,sys,vyper
checkout=pathlib.Path(sys.argv[1]); output=pathlib.Path(sys.argv[2])
package=pathlib.Path(vyper.__file__).resolve().parent
files={}; mismatches=[]
for path in sorted(package.rglob("*.py")):
    rel=path.relative_to(package); reference=checkout/"vyper"/rel
    digest=hashlib.sha256(path.read_bytes()).hexdigest()
    files[str(rel)]=digest
    if reference.exists() and path.read_bytes()!=reference.read_bytes(): mismatches.append(str(rel))
    elif not reference.exists() and str(rel)!="version.py": mismatches.append(str(rel))
result={"package":str(package),"commit":vyper.__commit__,"version":vyper.__version__,"files":files,"mismatches":mismatches}
output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\\n")
assert not mismatches,mismatches
'''
    assert run("verify-installed-pin", [python, "-I", "-c", verify, checkout, OUT / "installed-pin.json"], env=env) == 0
    rows = {}
    for name in names():
        single = OUT / "single" / name
        single.mkdir(parents=True, exist_ok=True)
        src = BASE / "folded-value-sources" / (name + ".vy")
        (single / src.name).write_bytes(src.read_bytes())
        manifest = single / "manifest.txt"
        manifest.write_text(name + "\n")
        status = run("oracle-" + name, [python, "-I", BASE / "python_o1_bytecode_oracle.py",
            "--expected-commit", pin, "--expected-python", "3.11.11",
            "--generator-uv", "0.10.11", "--expected-install-root", ENVROOT / "venv",
            "--sources", single, "--fixture-manifest", manifest, "--output", single / "generated"], env=env)
        row = {"source_sha256": sha(src), "exit": status, "expected_accept": name != "method_id_var"}
        if status == 0:
            generated = single / "generated" / (name + ".hex")
            retained = BASE / "folded-value-oracle" / (name + ".hex")
            row.update(generated_sha256=sha(generated), retained_sha256=sha(retained),
                       retained_bytes_reproduced=generated.read_bytes() == retained.read_bytes())
        else:
            row["diagnostic"] = (OUT / "commands" / ("oracle-" + name + ".log")).read_text()
        rows[name] = row
    dump(OUT / "oracle.json", {"pin": pin, "rows": rows})
    # Check original pre-erasure syntax with the same pinned parser, independently
    # of the installed compiler's post-erasure annotated_ast.
    # Retained fixtures use Python 3.12 AST fields (notably type_params=[]).
    # Bytecode generation above remains isolated CPython 3.11.11 exactly.
    syntax_python = OUT / "syntax-venv/bin/python"
    uv = ENVROOT / "bootstrap/bin/uv"
    if not syntax_python.exists():
        assert run("syntax-venv", [uv, "venv", "--python", "/usr/bin/python3", OUT / "syntax-venv"], env=env) == 0
        install_env = dict(env, UV_CONSTRAINT=str(BASE / "python-o1-oracle-constraints.txt"),
            UV_BUILD_CONSTRAINT=str(BASE / "python-o1-oracle-constraints.txt"),
            SETUPTOOLS_SCM_PRETEND_VERSION_FOR_VYPER="0.5.0a4+cd74ce4f")
        assert run("syntax-install", [uv, "pip", "install", "--python", syntax_python, checkout], env=install_env) == 0
    syntax_env = dict(env, PYTHONPATH=str(checkout))
    syntax = run("retained-syntax", [syntax_python, ROOT / "tests/fixtures/check_contract/source_syntax/generate.py", "--check"], env=syntax_env)
    assert syntax == 0
    assert all((r["exit"] == 0 and r.get("retained_bytes_reproduced")) if r["expected_accept"]
               else (r["exit"] != 0 and "method_id" in r["diagnostic"]) for r in rows.values())


def execute():
    # This mode must run under the isolated py-evm environment.
    from eth.chains.base import MiningChain
    from eth.db.atomic import AtomicDB
    from eth.vm.forks.prague import PragueVM
    from eth.exceptions import Revert
    from eth_abi import encode
    from eth_utils import keccak
    from importlib.metadata import version
    chain_type = MiningChain.configure(__name__="SourceModuleParityChain", vm_configuration=((0, PragueVM),))
    rows = []
    for name, typ, value in [("pow_folded_exp", "uint256", 2**90), ("pow_negfold_base", "int256", 256)]:
        data = keccak(text="f(" + typ + ")")[:4] + encode([typ], [value])
        for label, path in [("Python-pin", OUT / "single" / name / "generated" / (name + ".hex")),
                            ("HOL-source-module-wrapper", OUT / "hol" / (name + ".hex"))]:
            fields = dict(line.split("=", 1) for line in path.read_text().splitlines())
            code = bytes.fromhex(fields["runtime"])
            chain = chain_type.from_genesis(AtomicDB(), {"difficulty": 0, "gas_limit": 10_000_000, "timestamp": 1}, {})
            result = chain.get_vm().execute_bytecode(origin=b"\x01"*20, sender=b"\x01"*20,
                to=b"\x02"*20, gas_price=0, gas=1_000_000, value=0, data=data, code=code)
            rows.append({"name": name, "producer": label, "argument_type": typ, "argument": str(value),
                "calldata": data.hex(), "runtime_sha256": hashlib.sha256(code).hexdigest(),
                "bytecode_file_sha256": sha(path), "runtime_bytes": len(code), "gas_limit": 1_000_000,
                "gas_used": result.get_gas_used(), "is_error": result.is_error,
                "error_type": type(result.error).__name__ if result.is_error else None,
                "output": result.output.hex(), "reverted": result.is_error and isinstance(result.error, Revert)})
            print(json.dumps(rows[-1]), flush=True)
    dump(OUT / "executions.json", {"engine": "py-evm", "version": version("py-evm"),
         "vm": "PragueVM", "python": platform.python_version(), "executions": rows})
    assert len(rows) == 4 and all(r["reverted"] for r in rows)


def summarize():
    oracle_data = json.loads((OUT / "oracle.json").read_text())
    rows = {}
    abi_owners = {"fold_not": "frontend/sourceExprElaborate: source_expr_boolean_runtime canonicalization",
                  "boolop_and3": "frontend/sourceExprElaborate: source_expr_boolean_runtime canonicalization",
                  "ctl03_abi_method_id": "#551 ABI dispatch/lowering",
                  "enc_ensT_uint_mid": "#551 ABI dispatch/lowering",
                  "rc09_abi_encode_data": "#554/#551 raw_call ABI data encoding/lowering",
                  "rr03_abi": "#567/#551 raw_revert ABI data encoding/lowering"}
    for name in names():
        status = (OUT / "hol" / (name + ".status")).read_text().strip()
        row = dict(oracle_data["rows"][name], hol_status=status,
                   source_elaborate_check="ACCEPT" if name != "method_id_var" else "PIN_INVALID_REJECT")
        if status.startswith("BACKEND_NONE"):
            row["failure_owner"] = "#563 immutable backend compilation"
        elif status.startswith("BYTE_MISMATCH"):
            row["failure_owner"] = abi_owners.get(name, "lowering/compiler bytecode parity")
        elif status.startswith("VALIDATION_FAILURE") or status.startswith("BACKEND_RESIDUAL"):
            row["failure_owner"] = "compiler evaluation/harness (not passing parity)"
        path = OUT / "hol" / (name + ".hex")
        if path.exists():
            row["hol_hex_sha256"] = sha(path)
            row["independent_pin_equal"] = path.read_bytes() == (OUT / "single" / name / "generated" / path.name).read_bytes()
        for suffix in (".wrapper", ".audit", ".compiler"):
            path = OUT / "hol" / (name + suffix)
            if path.exists():
                row[suffix[1:] + "_sha256"] = sha(path)
        rows[name] = row
    commands = {p.stem: json.loads(p.read_text()) for p in (OUT / "commands").glob("*.json")}
    result = {"pin": oracle_data["pin"], "rows": rows, "commands": commands,
              "match_count": sum(r["hol_status"].startswith("MATCH") for r in rows.values()),
              "failure_count": sum("failure_owner" in r for r in rows.values()),
              "expected_pin_rejections": [n for n,r in rows.items() if not r["expected_accept"]]}
    dump(OUT / "results.json", result)
    print(json.dumps({k: result[k] for k in ("match_count", "failure_count", "expected_pin_rejections")}))
    # A completed diagnostic probe is not a passing parity run.
    return 1 if result["failure_count"] else 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["oracle", "execute", "summarize"])
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    sys.exit(globals()[args.mode]() or 0)
