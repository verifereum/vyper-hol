"""Behavior regressions for the built native runner's JSON input boundary.

Build tests/.emit/run-test first, then run: python3 tools/test_run_test_cli.py
"""

from __future__ import annotations

import copy
import json
import subprocess
import tempfile
import unittest
from pathlib import Path


RUNNER = Path(__file__).resolve().parents[1] / "tests/.emit/run-test"


class NativeInputTests(unittest.TestCase):
    def run_document(self, document: str, source: str) -> subprocess.CompletedProcess[str]:
        command = [str(RUNNER), "--dump-input"]
        if source == "stdin":
            return subprocess.run(command, input=document, text=True, capture_output=True,
                                  check=False)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "case.json"
            path.write_text(document)
            return subprocess.run(command + [str(path)], text=True, capture_output=True,
                                  check=False)

    def passed_input(self, traces: list[dict], source: str) -> str:
        result = self.run_document(json.dumps(traces), source)
        self.assertEqual(result.returncode, 0, result.stderr or result.stdout)
        records = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual(len(records), 1)
        self.assertEqual(records[0]["status"], "passed")
        return records[0]["input"]

    def rejected(self, document: str, source: str) -> None:
        result = self.run_document(document, source)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "", "invalid input must not execute any cases")

    @staticmethod
    def balance(address: str) -> list[dict]:
        return [{"trace_type": "set_balance", "address": address, "value": 1}]

    @staticmethod
    def empty_call() -> dict:
        # An unknown target with an expected error passes without deployment.
        # The dumped input still exposes all imported byte strings and hashes.
        return {
            "trace_type": "call",
            "call_args": {
                "is_modifying": True, "calldata": "", "value": 0, "to": "0x100",
            },
            "env": {
                "tx": {"gas_price": 0, "gas": 1000000, "origin": "0x200",
                       "blob_hashes": []},
                "block": {"block_hashes": {}, "timestamp": 1, "number": 1,
                          "blob_basefee": 1},
            },
            "output": None,
        }

    def test_single_document_and_json_whitespace(self) -> None:
        document = json.dumps([{"trace_type": "clear_transient_storage"}])
        for source in ("stdin", "file"):
            for suffix in ("", " \t\r\n", "\n" * 16384):
                with self.subTest(source=source, suffix_length=len(suffix)):
                    result = self.run_document(document + suffix, source)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    records = [json.loads(line) for line in result.stdout.splitlines()]
                    self.assertEqual(len(records), 1)
                    self.assertEqual(records[0]["status"], "passed")

    def test_trailing_content_is_rejected_before_execution(self) -> None:
        document = json.dumps([{"trace_type": "clear_transient_storage"}])
        for source in ("stdin", "file"):
            for suffix in (" NOT_JSON", " {}", " " + document,
                           "\n" * 16384 + "null", "\v", "\f", "\x00",
                           " /* not JSON whitespace */"):
                with self.subTest(source=source, suffix=suffix[-40:]):
                    self.rejected(document + suffix, source)

    def test_address_hex_scanning(self) -> None:
        for source in ("stdin", "file"):
            expected = self.passed_input(self.balance("01"), source)
            for address in ("0x01", "0X01", "1"):
                with self.subTest(source=source, address=address):
                    self.assertEqual(self.passed_input(self.balance(address), source), expected)
            for address in ("", "0x", "0X", "0x01junk", "01 "):
                with self.subTest(source=source, address=address):
                    self.rejected(json.dumps(self.balance(address)), source)

    def test_bytes32_hex_scanning_and_empty_hash_normalization(self) -> None:
        for source in ("stdin", "file"):
            for field in ("block_hashes", "blob_hashes"):
                def trace(word: str) -> dict:
                    call = self.empty_call()
                    if field == "block_hashes":
                        call["env"]["block"][field] = {"0": word}
                    else:
                        call["env"]["tx"][field] = [word]
                    return call

                expected = self.passed_input([trace("01")], source)
                for word in ("0x01", "0X01", "1"):
                    with self.subTest(source=source, field=field, word=word):
                        self.assertEqual(self.passed_input([trace(word)], source), expected)
                for word in ("0x", "0X", "01junk", "01 "):
                    with self.subTest(source=source, field=field, word=word):
                        self.rejected(json.dumps([trace(word)]), source)
                # The trace schema explicitly normalizes empty hashes to zero.
                with self.subTest(source=source, field=field, word=""):
                    self.assertEqual(self.passed_input([trace("")], source),
                                     self.passed_input([trace("0")], source))

    def test_byte_strings_keep_permissive_semantics(self) -> None:
        # Byte strings strip only lowercase 0x, permit empty/odd inputs, and
        # map invalid nibbles to zero. Word parsing must not replace this path.
        for source in ("stdin", "file"):
            for text, canonical in (("", ""), ("0x", ""), ("a", "0a"),
                                    ("abc", "ab0c"), ("0X01", "0001"),
                                    ("g1", "01"), ("1g", "10")):
                with self.subTest(source=source, text=text):
                    call = self.empty_call()
                    call["call_args"]["calldata"] = text
                    expected = copy.deepcopy(call)
                    expected["call_args"]["calldata"] = canonical
                    self.assertEqual(self.passed_input([call], source),
                                     self.passed_input([expected], source))


if __name__ == "__main__":
    unittest.main()
