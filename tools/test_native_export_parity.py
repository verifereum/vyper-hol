"""Checks of native_export_parity's corpus selection and runner verdicts."""

from __future__ import annotations

import json
from collections import Counter
import importlib.util
import tempfile
import unittest
from pathlib import Path
import unittest.mock
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
        self.assertEqual(nep.classify("PASS a 0.1s sp=F modules=2"), ("a", "outside", "bytes equal"))
        self.assertEqual(nep.classify("REJECT a 0.1s: frontend"), ("a", "rejected", "frontend"))
        self.assertEqual(nep.classify("FAIL a 0.1s: exception: Bind"),
                         ("a", "error", "exception: Bind"))

    def test_gate(self) -> None:
        self.assertEqual(nep.gate("FAIL a 0.1s sp=T: deploy differs"), "T")
        self.assertEqual(nep.gate("PASS a 0.1s sp=F"), "F")
        self.assertEqual(nep.gate("FAIL a 0.1s sp=F modules=2: deploy differs"), "unit")
        self.assertEqual(nep.gate("REJECT a 0.1s: frontend"), "-")


class CheckerTests(unittest.TestCase):
    def test_check_kind(self) -> None:
        self.assertEqual(nep.check_kind('Fail "check_contract returned NONE"'), "reject")
        self.assertEqual(nep.check_kind('Fail "check_contract returned if x then SOME a else NONE"'),
                         "undecided")
        self.assertEqual(nep.check_kind('frontend: Fail "vyperCheckContractFrontendLib: rejected"'),
                         "frontend")
        self.assertEqual(nep.check_kind("HOL_ERR"), "error")

    def test_check_contracts_reads_the_checker_output(self) -> None:
        out = ("CHECKED /w/a.json\n"
               "CHECKER-REJECT /w/b.json: Fail \"check_contract returned NONE\"\n"
               "CHECKER-REJECT /w/c.json: frontend: JSONError\n")
        done = unittest.mock.Mock(stdout=out, stderr="", returncode=0)
        with tempfile.TemporaryDirectory() as d, patch.object(nep.subprocess, "run", return_value=done):
            self.assertEqual(nep.check_contracts(Path(d), ["a", "b", "c"]),
                             {"a": "accept", "b": "reject", "c": "frontend"})
            with self.assertRaises(SystemExit):
                nep.check_contracts(Path(d), ["a", "b", "c", "d"])
            done.returncode = 1
            with self.assertRaises(SystemExit):
                nep.check_contracts(Path(d), ["a", "b", "c"])

    def test_write_fixture_drops_an_earlier_runs_files(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "x.hex").write_text("deploy=60\nruntime=00\n")
            with patch.object(nep, "compile_contract", side_effect=ImportError("boom")):
                with self.assertRaises(ImportError):
                    nep.write_fixture(nep.Contract("x", "t::x", "y: uint256"), Path(d))
            self.assertFalse((Path(d) / "x.hex").exists())

    @unittest.skipUnless(importlib.util.find_spec("vyper"), "needs the pinned Vyper")
    def test_compile_contract_ignores_earlier_compiles(self) -> None:
        sqrt = "import math\n@external\ndef f() -> decimal:\n    return math.sqrt(2.0)\n"
        isqrt = "import math\n@external\ndef f() -> uint256:\n    return math.isqrt(2)\n"
        alone = nep.compile_contract(sqrt, Path("a.vy"))
        nep.compile_contract(isqrt, Path("b.vy"))
        self.assertEqual(nep.compile_contract(sqrt, Path("a.vy")), alone)


class BytesTests(unittest.TestCase):
    def test_sameness(self) -> None:
        a = {"deploy": "60", "runtime": "00"}
        self.assertEqual(nep.sameness(a, dict(a)), "same")
        self.assertEqual(nep.sameness(a, {"deploy": "61", "runtime": "00"}), "deploy")
        self.assertEqual(nep.sameness(a, {"deploy": "60", "runtime": "01"}), "runtime")
        self.assertEqual(nep.sameness(a, {"deploy": "61", "runtime": "01"}), "both")
        self.assertEqual(nep.sameness(a, None), "n/a")

    def test_code(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "a.hex"
            self.assertIsNone(nep.code(path))
            path.write_text("deploy=60\nruntime=00\n")
            self.assertEqual(nep.code(path), {"deploy": "60", "runtime": "00"})


class ReportTests(unittest.TestCase):
    def verdicts(self) -> list:
        same = {f"{a}/{b}": "same" for a, b in nep.PAIRS}
        return [
            nep.Verdict(nep.Contract("a", "t::a", ""), "match", "", "T", "accept", same),
            nep.Verdict(nep.Contract("b", "t::b", ""), "outside", "deploy differs", "F", "reject",
                        same | {"patched/HOL": "deploy", "stock/HOL": "deploy"}),
            nep.Verdict(nep.Contract("c", "t::c", ""), "vyper-error", "StructureException: x")]

    def test_totals_and_lines(self) -> None:
        text = nep.report(self.verdicts(), Counter())
        self.assertIn("supported_program: 1 sp=T, 1 sp=F, 0 units of several modules, 1 not reached\n", text)
        self.assertIn("check_contract: 1 accept, 1 reject, 0 undecided, 0 frontend, 0 error, "
                      "1 not checked\n", text)
        self.assertIn("patched vs HOL bytes: 1 same, 1 deploy, 0 runtime, 0 both, 1 n/a\n", text)
        self.assertIn("outside     b sp=F chk=reject stock/patched=same patched/HOL=deploy "
                      "stock/HOL=deploy t::b: deploy differs\n", text)
        self.assertIn("vyper-error c sp=- chk=- t::c: StructureException: x\n", text)

    def test_cross_table(self) -> None:
        self.assertEqual(nep.cross_table(self.verdicts())[1:], [
            "             vyper-error     outside       match",
            "accept                 0           0           1",
            "reject                 0           1           0",
            "not checked            1           0           0"])

    def test_without_the_checker(self) -> None:
        verdicts = self.verdicts()
        for v in verdicts:
            v.checker = "-"
        text = nep.report(verdicts, Counter())
        self.assertNotIn("check_contract", text)
        self.assertIn("match       a sp=T stock/patched=same", text)


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
