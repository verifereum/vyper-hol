"""Verify preserved external evidence against current sources; no oracle generation.

Run from the repository root. This supplements, rather than rewrites, the
2026-10-23 historical bundle, whose parity-script identity predates the split.
"""
from collections import Counter
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
OLD = ROOT / "notes/validation/folded-value-2026-10-23"
HERE = Path(__file__).resolve().parent
BASE = ROOT / "lowering/defs/bytecode"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def hex_pair(path):
    return {key: bytes.fromhex(value) for key, value in
            (line.split("=", 1) for line in path.read_text().splitlines())}


# The original bundle remains an immutable historical receipt.
manifest = OLD / "ARTIFACTS.sha256"
entries = [line.split("  ", 1) for line in manifest.read_text().splitlines()]
for digest, name in entries:
    assert sha(OLD / name) == digest, name
semantic = json.loads((OLD / "semantic-source-hashes.json").read_text())
updated_documentation = {"lowering/defs/bytecode/folded-value-validation.md"}
for name, digest in semantic.items():
    if name not in updated_documentation:
        assert sha(ROOT / name) == digest, ("external evidence is stale", name)

report = json.loads((OLD / "results.json").read_text())
rows = {row["stem"]: row for row in report["witnesses"]}
assert set(rows) == set((BASE / "folded-value-witnesses.txt").read_text().split())
assert len(rows) == 37
for stem, row in rows.items():
    assert sha(BASE / "folded-value-sources" / (stem + ".vy")) == row["source_sha256"]
    if stem == "method_id_var":
        assert row["python_ast_exit"] != 0
        assert row["verdict"] == "EXPECTED_PYTHON_REJECTION"
        continue
    assert row["check_runtime"] == row["check_deploy"] == "ACCEPT"
    assert row["python_ast_exit"] == row["python_bytecode_exit"] == 0
    assert sha(BASE / "folded-value-oracle" / (stem + ".json")) == row["ast_sha256"]
    oracle_path = BASE / "folded-value-oracle" / (stem + ".hex")
    assert sha(oracle_path) == row["oracle_sha256"]
    if row["compile"] == "NONE":
        assert row["verdict"] == "COMPILE_NONE"
        continue
    actual = hex_pair(OLD / "hol" / (stem + ".hex"))
    expected = hex_pair(oracle_path)
    for part in ("deploy", "runtime"):
        assert hashlib.sha256(actual[part]).hexdigest() == row["hol_" + part + "_sha256"]
        assert hashlib.sha256(expected[part]).hexdigest() == row["python_" + part + "_sha256"]
        assert (actual[part] == expected[part]) == row[part + "_equal"]
    assert (actual == expected) == (row["verdict"] == "MATCH")
assert Counter(row["verdict"] for row in rows.values()) == report["verdict_counts"]
fixtures = (BASE / "folded-value-parity-fixtures.txt").read_text().split()
assert len(fixtures) == 7 and all(rows[s]["verdict"] == "MATCH" for s in fixtures)

provenance = json.loads((BASE / "folded-value-oracle/provenance.json").read_text())
assert provenance["vyper_commit"] == (ROOT / "VYPER_PIN").read_text().strip()
assert provenance["python_version"] == "3.11.11"
assert provenance["uv_version"] == "0.10.11"
assert provenance["settings"] == {
    "experimental_codegen": True, "optimization_level": "NONE",
    "venom_ir_pipeline": "O1", "final_assembly_optimization": False,
    "evm_version": "prague", "bytecode_metadata": False,
    "outputs": ["bytecode", "bytecode_runtime"]}
executions = json.loads((OLD / "executions.json").read_text())
assert executions["engine_version"] == "0.12.1b1" and executions["vm"] == "PragueVM"
seen = set()
for run in executions["executions"]:
    stem, producer = run["stem"], run["producer"]
    assert run["reverted"] and run["error_type"] == "Revert"
    assert int(run["argument"]) == {"pow_folded_exp": 2**90, "pow_negfold_base": 256}[stem]
    prefix = "python_" if producer == "Python" else "hol_"
    assert run["runtime_sha256"] == rows[stem][prefix + "runtime_sha256"]
    seen.add((stem, producer))
assert len(executions["executions"]) == 4
assert seen == {(s, p) for s in ("pow_folded_exp", "pow_negfold_base") for p in ("Python", "HOL")}
assert report["corpus"]["attempted"] == report["corpus"]["expected_targets"] == 33
assert report["corpus"]["passed"] == 28  # Do not promote unsuccessful runs to PASS.

# Current proof identities are recorded separately from the historical script.
proofs = sorted((BASE / "eval/folded").glob("*.sml"))
proofs += sorted((BASE / "eval/folded").glob("*.sig"))
proofs += [BASE / "eval/foldedValueParityScript.sml", ROOT / "holproject.toml",
           BASE / "folded-value-validation.md"]
current_sources = {str(p.relative_to(ROOT)): sha(p) for p in proofs}
logs = HERE / "logs"
assert "AUDIT PASS:" in (logs / "current-audit.log").read_text()
for name in ("current-parity-clean.log", "current-frontend-regressions.log",
             "current-type-proof-regressions.log", "current-supported-regressions.log"):
    assert "holbuild finished" in (logs / name).read_text(), name
    assert "CHEAT" not in (logs / name).read_text(), name

print(json.dumps({
    "status": "PASS_SCOPED_CHECKS_NOT_GLOBAL_CHEAT_FREE",
    "historical_bundle_files_verified": len(entries),
    "unchanged_semantic_sources_verified": len(semantic) - len(updated_documentation),
    "documentation_only_updates": sorted(updated_documentation),
    "witness_verdicts": report["verdict_counts"],
    "genuine_dual_runtime_overflow_reverts": 4,
    "historical_corpus": report["corpus"],
    "current_proof_sources_sha256": current_sources,
    "verification_scripts_sha256": {name: sha(HERE / name)
                                    for name in ("audit.sml", "verify_current.py")},
    "current_logs_sha256": {p.name: sha(p) for p in sorted(logs.glob("*.log"))},
    "baseline_admissions": ["lower_vyper_runtime_unit_correct",
                            "lower_vyper_runtime_unit_source_unit_ok",
                            "lower_vyper_runtime_unit_memory_ok"],
}, indent=2))
