"""Verify archived folded-value evidence; run the HOL audit for current proofs.

The archive is read without extraction. Historical receipts do not certify a
changed checkout; --require-current additionally enforces source freshness.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import tarfile

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[2]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def sha(path):
    return digest(path.read_bytes())


def hex_pair(data):
    return {key: bytes.fromhex(value) for key, value in
            (line.split("=", 1) for line in data.decode().splitlines())}


def differences(hashes, ignored=()):
    return sorted(name for name, expected in hashes.items()
                  if name not in ignored and
                  (not (ROOT / name).is_file() or sha(ROOT / name) != expected))


def verify(files, metadata):
    old, recent = metadata["paths"]

    def data(directory, name):
        return files[f"{directory}/{name}"]

    def read_json(directory, name):
        return json.loads(data(directory, name))

    entries = [line.split("  ", 1) for line in
               data(old, "ARTIFACTS.sha256").decode().splitlines()]
    for expected, name in entries:
        assert digest(data(old, name)) == expected, name
    snapshot = read_json(recent, "verification.json")
    for name, expected in snapshot["current_logs_sha256"].items():
        assert digest(data(recent, "logs/" + name)) == expected, name
    for name, expected in snapshot["verification_scripts_sha256"].items():
        assert digest(data(recent, name)) == expected, name
    assert b"AUDIT PASS:" in data(recent, "logs/current-audit.log")
    for name in ("current-parity-clean.log", "current-frontend-regressions.log",
                 "current-type-proof-regressions.log", "current-supported-regressions.log"):
        log = data(recent, "logs/" + name)
        assert b"holbuild finished" in log and b"CHEAT" not in log, name

    report = read_json(old, "results.json")
    rows = {row["stem"]: row for row in report["witnesses"]}
    assert set(rows) == set((BASE / "folded-value-witnesses.txt").read_text().split())
    assert len(rows) == len(report["witnesses"]) == 37
    for stem, row in rows.items():
        assert sha(BASE / "folded-value-sources" / (stem + ".vy")) == row["source_sha256"]
        if stem == "method_id_var":
            assert row["python_ast_exit"] != 0
            assert row["verdict"] == "EXPECTED_PYTHON_REJECTION"
            continue
        assert row["check_runtime"] == row["check_deploy"] == "ACCEPT"
        assert row["python_ast_exit"] == row["python_bytecode_exit"] == 0
        assert sha(BASE / "folded-value-oracle" / (stem + ".json")) == row["ast_sha256"]
        oracle = BASE / "folded-value-oracle" / (stem + ".hex")
        assert sha(oracle) == row["oracle_sha256"]
        if row["compile"] == "NONE":
            assert row["verdict"] == "COMPILE_NONE"
            continue
        actual = hex_pair(data(old, "hol/" + stem + ".hex"))
        expected = hex_pair(oracle.read_bytes())
        for part in ("deploy", "runtime"):
            assert digest(actual[part]) == row["hol_" + part + "_sha256"]
            assert digest(expected[part]) == row["python_" + part + "_sha256"]
            assert (actual[part] == expected[part]) == row[part + "_equal"]
        assert (actual == expected) == (row["verdict"] == "MATCH")
    assert Counter(row["verdict"] for row in rows.values()) == report["verdict_counts"]
    fixtures = (BASE / "folded-value-parity-fixtures.txt").read_text().split()
    assert len(fixtures) == 7 and all(rows[s]["verdict"] == "MATCH" for s in fixtures)

    provenance = json.loads((BASE / "folded-value-oracle/provenance.json").read_text())
    assert provenance["vyper_commit"] == (ROOT / "VYPER_PIN").read_text().strip()
    assert provenance["python_version"] == "3.11.11" and provenance["uv_version"] == "0.10.11"
    assert provenance["settings"] == {
        "experimental_codegen": True, "optimization_level": "NONE",
        "venom_ir_pipeline": "O1", "final_assembly_optimization": False,
        "evm_version": "prague", "bytecode_metadata": False,
        "outputs": ["bytecode", "bytecode_runtime"]}
    executions = read_json(old, "executions.json")
    assert executions["engine_version"] == "0.12.1b1" and executions["vm"] == "PragueVM"
    seen = set()
    for run in executions["executions"]:
        stem, producer = run["stem"], run["producer"]
        assert run["reverted"] and run["error_type"] == "Revert"
        assert int(run["argument"]) == {"pow_folded_exp": 2**90, "pow_negfold_base": 256}[stem]
        assert producer in {"Python", "HOL"}
        prefix = "python_" if producer == "Python" else "hol_"
        assert run["runtime_sha256"] == rows[stem][prefix + "runtime_sha256"]
        seen.add((stem, producer))
    assert len(executions["executions"]) == 4
    assert seen == {(s, p) for s in ("pow_folded_exp", "pow_negfold_base") for p in ("Python", "HOL")}
    assert report["corpus"]["attempted"] == report["corpus"]["expected_targets"] == 33
    assert report["corpus"]["passed"] == 28

    # Documentation consolidation is expected; semantic/proof drift is reported
    # explicitly, including files moved or changed by subsequent main merges.
    documentation = {"lowering/defs/bytecode/folded-value-validation.md"}
    source_drift = differences(read_json(old, "semantic-source-hashes.json"), documentation)
    proof_drift = differences(snapshot["current_proof_sources_sha256"], documentation)
    return {
        "status": "VERIFIED_HISTORICAL_EVIDENCE",
        "archive_files_verified": len(files),
        "historical_manifest_files_verified": len(entries),
        "historical_source_revision": report["source_revision"],
        "witness_verdicts": report["verdict_counts"],
        "genuine_dual_runtime_overflow_reverts": 4,
        "historical_corpus": {k: report["corpus"][k] for k in ("attempted", "passed")},
        "current_source_differences": source_drift,
        "current_proof_source_differences": proof_drift,
        "baseline_admissions": snapshot["baseline_admissions"],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path, help="folded-value-evidence.tar.gz")
    parser.add_argument("--require-current", action="store_true",
                        help="also fail if recorded semantic/proof sources differ from this checkout")
    args = parser.parse_args()
    metadata = json.loads((BASE / "folded-value-evidence.json").read_text())
    if not args.archive.is_file():
        parser.error("archive not found; see folded-value-validation.md for recovery instructions")
    if sha(args.archive) != metadata["archive_sha256"]:
        parser.error("archive SHA256 does not match folded-value-evidence.json")
    with tarfile.open(args.archive, "r:gz") as archive:
        files = {m.name: archive.extractfile(m).read()
                 for m in archive.getmembers() if m.isfile()}
    assert len(files) == metadata["files"]
    result = verify(files, metadata)
    print(json.dumps(result, indent=2))
    if args.require_current and (result["current_source_differences"] or
                                 result["current_proof_source_differences"]):
        parser.exit(1, "Historical evidence is stale for this checkout; rerun validation for current claims.\n")


if __name__ == "__main__":
    main()
