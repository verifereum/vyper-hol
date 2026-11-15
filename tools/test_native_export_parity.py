"""Checks of native_export_parity's corpus selection and runner verdicts."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import native_export_parity as nep


def deployment(source: str, **changes: object) -> dict:
    trace = {"trace_type": "deployment", "deployment_type": "source",
             "deployment_succeeded": True, "compiler_settings": nep.ORACLE_SETTINGS,
             "solc_json": {"sources": {"a.vy": {}}}, "source_code": source}
    return trace | changes


class CollectTests(unittest.TestCase):
    def test_keeps_one_contract_per_source_and_counts_the_rest(self) -> None:
        traces = [deployment("x: uint256"), deployment("x: uint256"),
                  deployment("y: uint256", compiler_settings={"optimize": "gas"}),
                  deployment("z: uint256", deployment_type="ir"),
                  deployment("v: uint256", deployment_succeeded=False),
                  deployment("w: uint256", solc_json={"sources": {"a.vy": {}, "b.vy": {}}}),
                  {"trace_type": "call"}]
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "t.json").write_text(json.dumps({"test_a": {"traces": traces}}))
            contracts, skipped = nep.collect(Path(d))
        self.assertEqual([(c.test, c.source) for c in contracts],
                         [("t::test_a", "x: uint256"), ("t::test_a", "v: uint256")])
        self.assertEqual(skipped, {"deployments at other compiler settings": 1,
                                   "ir deployments": 1, "deployments of several modules": 1})


class ClassifyTests(unittest.TestCase):
    def test_verdicts(self) -> None:
        self.assertEqual(nep.classify("PASS a 0.1s sp=T"), ("a", "match", ""))
        self.assertEqual(nep.classify("FAIL a 0.1s sp=T: deploy differs"),
                         ("a", "mismatch", "deploy differs"))
        self.assertEqual(nep.classify("FAIL a 0.1s sp=F: deploy differs"),
                         ("a", "outside", "deploy differs"))
        self.assertEqual(nep.classify("PASS a 0.1s sp=F"), ("a", "outside", "bytes equal"))
        self.assertEqual(nep.classify("REJECT a 0.1s: frontend"), ("a", "rejected", "frontend"))
        self.assertEqual(nep.classify("FAIL a 0.1s: exception: Bind"),
                         ("a", "error", "exception: Bind"))


class KnownTests(unittest.TestCase):
    def test_reasons_may_start_with_a_hash(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            known = Path(d) / "known.txt"
            known.write_text("# header\nabc bytes #543  # some::test\ndef none decode-guards\n")
            with patch.object(nep, "KNOWN", known):
                self.assertEqual(nep.known_mismatches(), {"abc": nep.Known("bytes", "#543"),
                                                          "def": nep.Known("none", "decode-guards")})

    def test_outcomes(self) -> None:
        self.assertEqual(nep.outcome("deploy differs at byte 3 (expected 1 bytes, got 2)"), "bytes")
        self.assertEqual(nep.outcome("runtime differs at byte 3"), "bytes")
        self.assertEqual(nep.outcome("compiler returned NONE"), "none")
        self.assertEqual(nep.outcome("stuck: FAPPLY"), "stuck")
        self.assertEqual(nep.outcome("exception: Bind"), "exception")


if __name__ == "__main__":
    unittest.main()
