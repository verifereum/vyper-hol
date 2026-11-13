#!/usr/bin/env python3
"""Emit the existing run_test CV translation and compile it with MLton."""

import argparse
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--smoke", action="store_true",
        help="compare compiled deployment/call cases against kernel-checked results",
    )
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    targets = ["vyperTestEmitTheory"]
    if args.smoke:
        targets.append("vyperTestEmitSmokeTheory")
    subprocess.run(
        ["holbuild", "build", *targets], cwd=root, check=True,
    )
    binary = root / "tests/.emit/run-test"
    subprocess.run(
        ["mlton", "-output", str(binary), "tests/emit/run-test.mlb"],
        cwd=root, check=True,
    )
    print(f"Emitted executable: {binary}", flush=True)
    if args.smoke:
        expected = {}
        for line in (root / "tests/.emit/json-smoke.expected").read_text().splitlines():
            name, passed, encoded_input, encoded_result = line.split("\t")
            expected[name] = (passed == "true", encoded_input, encoded_result)
        result = subprocess.run(
            [str(binary), "--dump-input", "tests/fixtures/run_test_json/basic.json"],
            cwd=root, capture_output=True, text=True,
        )
        actual = [json.loads(line) for line in result.stdout.splitlines()]
        if [case["name"] for case in actual] != list(expected):
            raise SystemExit(f"Unexpected JSON cases: {actual!r}\n{result.stderr}")
        for case in actual:
            passed, encoded_input, encoded_result = expected[case["name"]]
            for key, wanted in [
                ("status", "passed" if passed else "failed"),
                ("input", encoded_input), ("result", encoded_result),
            ]:
                if case.get(key) != wanted:
                    raise SystemExit(f"Compiled/HOL mismatch: {case['name']} {key}")
        wanted_exit = 0 if all(case[0] for case in expected.values()) else 1
        if result.returncode != wanted_exit:
            raise SystemExit(f"Unexpected exit status: {result.returncode}\n{result.stderr}")
        print(f"JSON/HOL input and result parity: {len(expected)} deployment/call cases")
        fixture = json.loads(
            (root / "tests/fixtures/run_test_json/basic.json").read_text()
        )
        traces = fixture["setup"]["traces"] + fixture["test_basic_code"]["traces"]
        stdin_result = subprocess.run(
            [str(binary), "--dump-input"], cwd=root,
            input=json.dumps(traces), capture_output=True, text=True,
        )
        stdin_cases = [json.loads(line) for line in stdin_result.stdout.splitlines()]
        passed, encoded_input, encoded_result = expected["test_basic_code"]
        if stdin_result.returncode != 0 or len(stdin_cases) != 1:
            raise SystemExit(
                f"Unexpected stdin result: {stdin_result.stdout}\n{stdin_result.stderr}"
            )
        for key, wanted in [
            ("status", "passed" if passed else "failed"),
            ("input", encoded_input), ("result", encoded_result),
        ]:
            if stdin_cases[0].get(key) != wanted:
                raise SystemExit(f"Compiled/HOL mismatch: stdin {key}")
        print("JSON/HOL input and result parity: stdin deployment/call case")


if __name__ == "__main__":
    main()
