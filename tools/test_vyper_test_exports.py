"""Regression checks for stale exports and legitimate compiler overrides."""

from __future__ import annotations

import json
import argparse
import shutil
import tempfile
import unittest
from collections.abc import Callable
from pathlib import Path
from unittest.mock import patch

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

    def test_regression_source_changes_invalidate_replay_and_cache(self) -> None:
        source = self.repo / "tests/vyper-regression/test_regression.py"
        source.parent.mkdir(parents=True, exist_ok=True)
        previous_key = self.exports.cache_key()
        source.write_text("def test_regression():\n    assert True\n")
        self.assertNotEqual(previous_key, self.exports.cache_key())
        provenance = json.loads(self.sidecar.read_text())
        provenance["inputs"] = self.exports.inputs()
        self.sidecar.write_text(json.dumps(provenance))
        self.exports.check(self.path)
        previous_key = self.exports.cache_key()
        source.write_text("def test_regression():\n    assert False\n")
        self.assertNotEqual(previous_key, self.exports.cache_key())
        with self.assertRaisesRegex(ValueError, "inputs differs"):
            self.exports.check(self.path)
        source.unlink()
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
        trace = {
            "annotated_ast": {
                "path": "/checkout/unknown_0.vy",
                "body": [{"ast_type": "Str", "value": "/checkout/keep-this-literal"}],
            },
            "solc_json": {
                "sources": {"/checkout/a.vy": {"content": "@external\ndef f(): pass"}},
                "settings": {"outputSelection": {"/checkout/a.vy": ["*"]}},
            },
            "python_args": {"kwargs": {"name": "/checkout/keep-this-argument"}},
            "output": "000007",
        }
        data = {"test": {"deps": ["/out/functional/test_f.json/fixture"], "traces": [trace]}}
        result = portable_paths(data, {"/checkout/": "", "/out/": "vyper-test-exports/"})
        portable = result["test"]["traces"][0]
        self.assertEqual(portable["annotated_ast"]["path"], "unknown_0.vy")
        self.assertEqual(portable["annotated_ast"]["body"], trace["annotated_ast"]["body"])
        self.assertEqual(portable["python_args"], trace["python_args"])
        self.assertEqual(portable["solc_json"]["sources"]["a.vy"],
                         trace["solc_json"]["sources"]["/checkout/a.vy"])
        self.assertEqual(result["test"]["deps"], ["vyper-test-exports/functional/test_f.json/fixture"])
        self.assertEqual(portable["output"], trace["output"])

    def generate(self, output: Path, run_pytest: Callable[..., None]) -> None:
        """Run `generate` against this repo, with `run_pytest` in place of pytest."""
        versions = dict(
            line.split("==")
            for line in (self.repo / "tests/semantics-test-constraints.txt").read_text().splitlines()
        )
        versions["vyper"] = self.exports.profile["vyper_version"]
        pin = (self.repo / "VYPER_PIN").read_text().strip()
        args = argparse.Namespace(vyper_repo=self.repo, output=output, fixture=[], test=[])
        with patch("vyper_test_exports.platform.python_version",
                   return_value=self.exports.profile["python_version"]), \
             patch("vyper_test_exports.importlib.metadata.version", side_effect=versions.__getitem__), \
             patch("vyper_test_exports.subprocess.check_output", side_effect=[pin, ""]), \
             patch("vyper_test_exports.subprocess.run", side_effect=run_pytest):
            self.exports.generate(args)

    def test_edits_during_export_cannot_stamp_new_generator_identity(self) -> None:
        output = self.repo / "new-exports"

        def run_pytest(*args: object, **kwargs: object) -> None:
            output.mkdir()
            shutil.copyfile(self.path, output / self.path.name)
            script = self.repo / "tools/vyper_test_exports.py"
            script.write_text(script.read_text() + "\n# edited during export\n")

        with self.assertRaisesRegex(ValueError, "generator inputs changed during export"):
            self.generate(output, run_pytest)
        self.assertFalse(list(output.glob("*.provenance")))

    def test_copied_regressions_are_packages_so_file_names_cannot_clash(self) -> None:
        # pytest names a module outside a package by its file name, so a
        # regression test named like an upstream one would abort collection.
        output = self.repo / "new-exports"
        (self.repo / "tests/vyper-regression/area/nested").mkdir(parents=True)
        (self.repo / "tests/vyper-regression/area/nested/test_x.py").write_text("")
        not_packages: list[Path] = []

        def run_pytest(*args: object, **kwargs: object) -> None:
            root = self.repo / "tests/functional/codegen/vyper_hol_regression"
            directories = [root, *filter(Path.is_dir, root.rglob("*"))]
            self.assertIn(root / "area/nested", directories)
            not_packages.extend(d for d in directories if not (d / "__init__.py").is_file())
            output.mkdir()
            (output / "export.json").write_text("{}")

        self.generate(output, run_pytest)
        self.assertEqual(not_packages, [])

    def test_regression_directories_that_cannot_be_packages_are_refused(self) -> None:
        regressions = self.repo / "tests/vyper-regression"
        for directory, module in (("hand-written", None), ("area", "area.py")):
            with self.subTest(directory=directory):
                (regressions / directory).mkdir()
                if module:
                    (regressions / module).write_text("")

                def run_pytest(*args: object, **kwargs: object) -> None:
                    self.fail("pytest ran on a tree it can't import")

                with self.assertRaisesRegex(ValueError, f"tests/vyper-regression/{directory} must"):
                    self.generate(self.repo / "new-exports", run_pytest)
                (regressions / directory).rmdir()
                if module:
                    (regressions / module).unlink()


if __name__ == "__main__":
    unittest.main()
