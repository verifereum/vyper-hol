"""Regression checks for stale exports and legitimate compiler overrides."""

from __future__ import annotations

import json
import shutil
import tempfile
import unittest
from pathlib import Path

from vyper_test_exports import Exports, digest, portable_paths


class ExportProvenanceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.repo = Path(self.temporary.name)
        original = Exports(Path(__file__).resolve().parents[1])
        for name in original.inputs():
            target = self.repo / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(original.repo / name, target)
        self.exports = Exports(self.repo)
        self.path = self.repo / "export.json"
        self.path.write_text(json.dumps({
            "test_backend_override": {"traces": [{
                "trace_type": "deployment", "deployment_type": "source",
                "compiler_settings": {
                    "experimental_codegen": False, "optimize": "gas",
                    "evm_version": "cancun", "enable_decimals": False,
                },
            }]},
        }))
        self.sidecar = Path(str(self.path) + ".provenance")
        self.sidecar.write_text(json.dumps({
            "schema_version": 1, "inputs": self.exports.inputs(),
            "profile": self.exports.profile, "export_sha256": digest(self.path),
            "fixture_sources": {}, "resolved_settings": self.exports.settings(self.path),
        }))

    def test_resolved_upstream_overrides_are_preserved(self) -> None:
        self.exports.check(self.path)

    def test_old_exports_without_provenance_are_rejected(self) -> None:
        self.sidecar.unlink()
        with self.assertRaisesRegex(ValueError, "missing .*provenance"):
            self.exports.check(self.path)

    def test_modified_expectations_are_rejected(self) -> None:
        self.path.write_text(self.path.read_text() + "\n")
        with self.assertRaisesRegex(ValueError, "export_sha256 differs"):
            self.exports.check(self.path)

    def test_profile_changes_invalidate_replay_and_cache(self) -> None:
        previous_key = self.exports.cache_key()
        profile_path = self.repo / "tests/semantics-profile.json"
        profile_path.write_text(profile_path.read_text().replace('"none"', '"O1"'))
        self.assertNotEqual(previous_key, self.exports.cache_key())
        with self.assertRaisesRegex(ValueError, "inputs differs"):
            self.exports.check(self.path)

    def test_changed_fixture_sources_require_regeneration(self) -> None:
        source = self.repo / "test_source.py"
        source.write_text("original")
        provenance = json.loads(self.sidecar.read_text())
        provenance["fixture_sources"] = {"test_source.py": digest(source)}
        self.sidecar.write_text(json.dumps(provenance))
        source.write_text("changed")
        with self.assertRaisesRegex(ValueError, "fixture source test_source.py differs"):
            self.exports.check(self.path)

    def test_export_paths_are_portable_without_changing_call_outputs(self) -> None:
        data = {
            "annotated_ast": {"path": "/checkout/unknown_0.vy"},
            "sources": {"/checkout/a.vy": {"content": "@external\ndef f(): pass"}},
            "deps": ["/out/functional/test_f.json/fixture"],
            "output": "000007",
        }
        result = portable_paths(data, {"/checkout/": "", "/out/": "vyper-test-exports/"})
        self.assertEqual(result["annotated_ast"]["path"], "unknown_0.vy")
        self.assertEqual(result["sources"]["a.vy"], data["sources"]["/checkout/a.vy"])
        self.assertEqual(result["deps"], ["vyper-test-exports/functional/test_f.json/fixture"])
        self.assertEqual(result["output"], data["output"])


if __name__ == "__main__":
    unittest.main()
