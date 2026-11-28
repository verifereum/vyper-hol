"""Dependency-free regressions for ABI decoding and reference checkpoint fidelity."""

from __future__ import annotations

import tempfile
from pathlib import Path
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import bytecode_state_oracle as oracle


class JsonArgumentTests(unittest.TestCase):
    def test_bytes_arrays_and_nested_tuples_follow_the_abi(self):
        parameters = [
            {"type": "bytes2[2][]"},
            {"type": "tuple[1]", "components": [
                {"name": "label", "type": "string"},
                {"name": "payload", "type": "bytes"},
                {"name": "nested", "type": "tuple[]", "components": [
                    {"type": "bytes1[2]"}, {"type": "uint256"},
                ]},
            ]},
        ]
        values = [
            [["0x0102", "0304"], ["0000", "ffff"]],
            [["0xkeep-as-text", "0x", [[["0x01", "02"], 7]]]],
        ]
        self.assertEqual(oracle._decode_arguments(parameters, values), [
            [[b"\x01\x02", b"\x03\x04"], [b"\x00\x00", b"\xff\xff"]],
            [("0xkeep-as-text", b"", [([b"\x01", b"\x02"], 7)])],
        ])
        # Decoding must not mutate the report's JSON-safe input plan.
        self.assertEqual(values[0][0][0], "0x0102")
        self.assertEqual(values[1][0][1], "0x")

    def test_bad_container_shapes_do_not_drop_arguments(self):
        with self.assertRaises(TypeError):
            oracle._decode_arguments([{"type": "bytes"}], [])
        with self.assertRaises(TypeError):
            oracle._decode_argument({"type": "bytes[]"}, "0x00")
        with self.assertRaises(ValueError):
            oracle._decode_argument({"type": "bytes[2]"}, ["00"])
        with self.assertRaises(TypeError):
            oracle._decode_argument({"type": "tuple", "components": [{"type": "bytes"}]}, [])
        with self.assertRaises(ValueError):
            oracle._decode_argument({"type": "bytes"}, "not hex")


class ProvenanceTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.checkout = self.root / "compiler"
        self.pin = "a" * 40
        (self.root / "VYPER_PIN").write_text(self.pin)
        checkout_state = patch.object(oracle, "_CHECKOUT", None)
        checkout_state.start()
        self.addCleanup(checkout_state.stop)

    def test_wrong_commit_is_rejected_before_imports(self):
        with patch.object(oracle, "_git", return_value="b" * 40):
            with self.assertRaises(oracle.OracleError):
                oracle.verify_vyper(self.checkout, self.root)
        self.assertIsNone(oracle._CHECKOUT)

    def test_dirty_stock_checkout_is_rejected(self):
        with patch.object(oracle, "_git", side_effect=[
            self.pin, str(self.checkout), " M vyper/compiler/__init__.py",
        ]):
            with self.assertRaises(oracle.OracleError):
                oracle.verify_vyper(self.checkout, self.root)
        self.assertIsNone(oracle._CHECKOUT)

    def test_unsupported_backend_is_rejected_before_loading_compiler(self):
        with patch.object(oracle, "_git", side_effect=[self.pin, str(self.checkout), ""]), \
                patch.object(oracle.importlib.metadata, "version", return_value="0.12.0b1"):
            with self.assertRaises(oracle.OracleError):
                oracle.verify_vyper(self.checkout, self.root)
        self.assertIsNone(oracle._CHECKOUT)

    def test_external_test_namespace_is_rejected(self):
        outside = self.root / "other" / "tests"
        module = SimpleNamespace(__file__=str(outside / "__init__.py"), __path__=[str(outside)])
        with patch.dict(oracle.sys.modules, {"tests": module}):
            with self.assertRaises(oracle.OracleError):
                oracle._check_loaded_paths(self.checkout)

    def test_external_namespace_package_search_path_is_rejected(self):
        inside = self.checkout / "tests"
        module = SimpleNamespace(__file__=None, __path__=[str(inside), str(self.root / "other")])
        # Isolate the package namespace from any actual compiler modules loaded by
        # another test; no compiler import or checkout is needed for this check.
        with patch.dict(oracle.sys.modules, {"tests": module}, clear=True):
            with self.assertRaises(oracle.OracleError):
                oracle._check_loaded_paths(self.checkout)


if __name__ == "__main__":
    unittest.main()
