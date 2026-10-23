#!/usr/bin/env python3
"""Export actual HOL evaluation output and compare it with the pinned oracle."""

import argparse
import hashlib
import json
import re
from pathlib import Path


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_hex(path):
    return {key: bytes.fromhex(value) for key, value in
            (line.split("=", 1) for line in path.read_text().splitlines()
             if line and not line.startswith("#"))}


def comparison(actual, expected):
    first = next((i for i, (a, b) in enumerate(zip(actual, expected)) if a != b), None)
    if first is None and len(actual) != len(expected):
        first = min(len(actual), len(expected))
    return {"match": actual == expected, "first_difference": first,
            "hol_length": len(actual), "oracle_length": len(expected),
            "hol_sha256": digest(actual), "oracle_sha256": digest(expected)}


def main():
    fixture_dir = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log", type=Path, default=fixture_dir.parents[3] /
                        ".holbuild/logs/current/vyper-hol/"
                        "evalCompilerAssignmentEffectsTheory/build.log")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    log_bytes = args.log.read_bytes()
    log = log_bytes.decode()
    if 'Exporting theory "evalCompilerAssignmentEffects" ... done.' not in log:
        raise ValueError("the HOL theory did not finish successfully")
    outputs = {}
    for name, kind, data in re.findall(
            r"^HOL_BYTECODE (\S+) (deploy|runtime)=([0-9A-Fa-f]*)$", log, re.M):
        value = bytes.fromhex(data)
        previous = outputs.setdefault(name, {}).setdefault(kind, value)
        if previous != value:
            raise ValueError(f"conflicting HOL output for {name}/{kind}")
    names = [line.strip() for line in (fixture_dir / "fixtures.txt").read_text().splitlines()
             if line.strip() and not line.startswith("#")]
    if set(outputs) != set(names) or any(set(outputs[name]) != {"deploy", "runtime"}
                                         for name in names):
        raise ValueError("the HOL output does not cover the complete fixture manifest")
    required = {"c08_storage_arr_assign_computed_rhs", "c09_storage_map_assign_computed_rhs",
                "g6_write_order_side", "x04_assign_sideeffect_order",
                "s11_storage_map_assign_extcall_rhs", "g19_aug_rhs_modifies_target"}
    rows = []
    for name in names:
        oracle = read_hex(fixture_dir / "oracle" / (name + ".hex"))
        stats = {kind: comparison(outputs[name][kind], oracle[kind])
                 for kind in ("deploy", "runtime")}
        same = all(part["match"] for part in stats.values())
        if name in required and not same:
            raise ValueError(f"required bytecode comparison failed: {name}")
        rows.append({"name": name, "verdict": "MATCH" if same else "PARITY_DEFECT",
                     "theorem": "evalCompilerAssignmentEffects$" + name +
                     ("_matches_python" if same else "_compiled"), **stats})
    args.output.mkdir(parents=True, exist_ok=True)
    for name in names:
        # These bytes come only from HOL_BYTECODE lines, never from the oracle.
        (args.output / (name + ".hex")).write_text(
            "# Actual HOL evaluation output; independent oracle bytes are stored separately.\n" +
            "".join(f"{kind}={outputs[name][kind].hex()}\n" for kind in ("deploy", "runtime")))
    (args.output / "comparisons.json").write_text(json.dumps(
        {"theory": "evalCompilerAssignmentEffects", "build_log_sha256": digest(log_bytes),
         "oracle_provenance_sha256": digest((fixture_dir / "oracle/provenance.json").read_bytes()),
         "results": rows}, indent=2, sort_keys=True) + "\n")
    for row in rows:
        print(f"{row['name']}: {row['verdict']}")


if __name__ == "__main__":
    main()
