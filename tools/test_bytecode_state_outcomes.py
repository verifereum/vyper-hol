"""Pinned compiler/py-evm outcome and operational-error boundary regressions.

Each scenario uses a fresh interpreter to isolate upstream compiler/test imports.
Set VYPER_STATE_VYPER to the clean checkout matching VYPER_PIN.
"""

import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import textwrap
import unittest


ROOT = Path(__file__).resolve().parents[1]
CHECKOUT = Path(os.environ.get("VYPER_STATE_VYPER", ROOT / "vyper-ref")).resolve()
NATIVE_RUNNER = Path(os.environ.get("VYPER_STATE_RUNNER", ROOT / "tests/.emit/run-test")).resolve()
HAS_FIXTURE = (
    importlib.util.find_spec("eth") is not None
    and (CHECKOUT / "tests/evm_backends/pyevm_env.py").is_file()
)

PAYABLE_SOURCE = """
stored: public(uint256)

@deploy
@payable
def __init__():
    pass

@external
@payable
def put(number: uint256):
    self.stored = number
"""

INVALID_SOURCE = """
event Written:
    number: uint256

stored: public(uint256)
scratch: transient(uint256)

@external
@payable
def put(number: uint256, fail: bool):
    self.stored = number
    self.scratch = number
    log Written(number=number)
    assert not fail, UNREACHABLE
"""

INVALID_CONSTRUCTOR = """
event Written:
    number: uint256

stored: uint256
scratch: transient(uint256)

@deploy
@payable
def __init__():
    self.stored = 77
    self.scratch = 88
    log Written(number=99)
    raise UNREACHABLE
"""

PRELUDE = f'''
import sys
import json
import subprocess
from pathlib import Path
from unittest.mock import patch
sys.dont_write_bytecode = True
sys.path.insert(0, {str(ROOT / "tools")!r})
import bytecode_state_oracle as oracle
import bytecode_state_snapshot as snapshot
oracle.verify_vyper(Path({str(CHECKOUT)!r}), Path({str(ROOT)!r}))
from eth.exceptions import InsufficientFunds, InvalidInstruction, OutOfGas
from eth.codecs.abi.exceptions import EncodeError
from tests.evm_backends import base_env
from tests.evm_backends.base_env import EvmError, ExecutionReverted

PAYABLE_SOURCE = {PAYABLE_SOURCE!r}
INVALID_SOURCE = {INVALID_SOURCE!r}
INVALID_CONSTRUCTOR = {INVALID_CONSTRUCTOR!r}


def reference(source=PAYABLE_SOURCE, **kwargs):
    return oracle.ReferenceRun(source, name="outcome", source_dir=Path({str(ROOT)!r}), **kwargs)


def expect(kind, action):
    try:
        action()
    except kind as error:
        return error
    raise AssertionError("expected " + kind.__name__)


def checkpoints(run):
    return [row for row in run.traces if row["trace_type"] == "state_checkpoint"]


def world(checkpoint):
    return {{key: checkpoint[key] for key in ("accounts", "transient_storage", "logs")}}


def calls(run):
    return [row for row in run.traces if row["trace_type"] == "call"]
'''


@unittest.skipUnless(HAS_FIXTURE, "requires pinned Vyper checkout via VYPER_STATE_VYPER and py-evm")
class ExecutionOutcomeTests(unittest.TestCase):
    def execute(self, body):
        result = subprocess.run(
            [sys.executable, "-c", PRELUDE + textwrap.dedent(body)],
            cwd=ROOT, capture_output=True, text=True, timeout=90,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_invalid_call_exports_failure_and_complete_rollback_checkpoint(self):
        self.execute('''
            run = reference(INVALID_SOURCE)
            run.call({"function": "put", "args": [17, False], "value": 3})
            before = checkpoints(run)[-1]
            run.call({"function": "put", "args": [91, True], "value": 5})
            after = checkpoints(run)[-1]
            assert len(checkpoints(run)) == 3
            assert after["boundary"] == "call" and after["call_index"] == 1
            assert calls(run)[-1]["call_succeeded"] is False
            assert isinstance(run.env._last_computation.error, InvalidInstruction)
            assert after["accounts"] == before["accounts"]
            assert after["logs"] == before["logs"] and len(after["logs"]) == 1
            # ReferenceRun clears transient state before each attempted call;
            # rollback restores that cleared state, not the preceding call's.
            assert before["transient_storage"] and after["transient_storage"] == []
            run.call({"function": "put", "args": [23, False]})
            assert calls(run)[-1]["call_succeeded"] is True
            assert checkpoints(run)[-1]["call_index"] == 2
        ''')

    def test_invalid_constructor_checkpoints_rollback_and_keeps_sender_nonce(self):
        self.execute('''
            run = reference(INVALID_CONSTRUCTOR, value=9)
            assert run.contract is None
            deployment = run.traces[-2]
            checkpoint = checkpoints(run)[-1]
            assert deployment["deployment_succeeded"] is False
            assert deployment["runtime_bytecode"] == ""
            assert isinstance(run.env._last_computation.error, InvalidInstruction)
            assert checkpoint["boundary"] == "deployment" and checkpoint["call_index"] == 0
            assert checkpoint["logs"] == [] and checkpoint["transient_storage"] == []
            assert len(checkpoint["accounts"]) == 10
            for account in checkpoint["accounts"]:
                assert account["balance"] == 10**30
                assert account["storage"] == [] and account["code"] == ""
                assert account["nonce"] == (account["address"] == run.env.deployer.lower())
            expect(ValueError, lambda: run.call({"function": "put", "args": []}))
        ''')

    def test_insufficient_call_funds_does_not_reuse_previous_success(self):
        self.execute('''
            run = reference()
            run.call({"function": "put", "args": [17]})
            previous = run.env._last_computation
            before = checkpoints(run)[-1]
            run.call({"function": "put", "args": [91], "value": 10**30 + 1})
            assert run.env._last_computation is previous
            assert run.env.last_result.is_success  # deliberately stale fixture result
            assert calls(run)[-1]["call_succeeded"] is False
            assert world(checkpoints(run)[-1]) == world(before)
            assert len(checkpoints(run)) == 3
            error = expect(EvmError, lambda: run.env.message_call(run.contract.address, value=10**30 + 1))
            assert type(error) is EvmError and isinstance(error.__cause__, InsufficientFunds)
            assert run.env.is_execution_failure(error)
            assert not run.env.is_execution_failure(EvmError("unrelated harness failure"))
        ''')

    def test_insufficient_deployment_funds_and_stale_backend_computation(self):
        self.execute('''
            run = reference(value=10**30 + 1)
            assert run.contract is None
            assert run.traces[-2]["deployment_succeeded"] is False
            assert len(checkpoints(run)) == 1
            assert checkpoints(run)[0]["logs"] == []
            assert all(account["balance"] == 10**30 for account in checkpoints(run)[0]["accounts"])

            successful = reference()
            previous = successful.env._last_computation
            error = expect(EvmError, lambda: successful.env.deploy([], b"\\x00", value=10**30 + 1))
            assert type(error) is EvmError and isinstance(error.__cause__, InsufficientFunds)
            assert successful.env._last_computation is previous
            assert successful.env.last_result.is_success
            assert successful.env.is_execution_failure(error)
        ''')

    def test_fixture_keeps_invalid_and_revert_exception_classes(self):
        self.execute('''
            run = reference()
            invalid = expect(EvmError, lambda: run.env.deploy([], b"\\xfe"))
            assert type(invalid) is EvmError
            assert isinstance(invalid.__cause__, InvalidInstruction)
            assert run.env.is_execution_failure(invalid)
            reverted = expect(ExecutionReverted, lambda: run.env.deploy([], bytes.fromhex("60006000fd")))
            assert type(reverted) is ExecutionReverted
            assert run.env.is_execution_failure(reverted)
            assert not run.env.is_execution_failure(invalid)
            expect(ValueError, lambda: run.env.message_call("not-an-address"))
            assert not run.env.is_execution_failure(reverted)
        ''')

    def test_out_of_gas_call_and_constructor_remain_operational(self):
        self.execute('''
            run = reference()
            run.call({"function": "put", "args": [17]})
            count = len(checkpoints(run))
            run.env.gas_limit = 1
            error = expect(EvmError, lambda: run.call({"function": "put", "args": [91]}))
            assert type(error) is EvmError and isinstance(error.__cause__, OutOfGas)
            assert not run.env.is_execution_failure(error)
            assert len(checkpoints(run)) == count

            class LowGas(snapshot.env_class()):
                def __init__(self, *args, **kwargs):
                    super().__init__(*args, **kwargs)
                    self.gas_limit = 1

            with patch.object(snapshot, "env_class", return_value=LowGas):
                error = expect(EvmError, reference)
            assert type(error) is EvmError and isinstance(error.__cause__, OutOfGas)
        ''')

    def test_setup_compiler_abi_backend_and_snapshot_errors_are_not_execution(self):
        self.execute('''
            with patch.object(oracle, "_CHECKOUT", None):
                expect(oracle.OracleError, reference)
            expect(oracle.CompilerRejected, lambda: reference("not valid Vyper"))
            with patch.object(base_env, "_compile", side_effect=EvmError("compiler setup")):
                expect(EvmError, reference)
            expect(TypeError, lambda: reference(constructor_args=[123]))

            run = reference(INVALID_SOURCE)
            run.call({"function": "put", "args": [17, True]})
            count = len(checkpoints(run))
            expect(ValueError, lambda: run.call({"function": "missing"}))
            expect(EncodeError, lambda: run.call({"function": "put", "args": ["wrong", True]}))
            assert len(checkpoints(run)) == count
            with patch.object(run.env._state, "computation_class") as computation:
                computation.apply_message.side_effect = EvmError("backend setup")
                error = expect(EvmError, lambda: run.call({"function": "put", "args": [1, False]}))
            assert not run.env.is_execution_failure(error)
            assert len(checkpoints(run)) == count
            with patch.object(run.env, "full_state_snapshot", side_effect=RuntimeError("snapshot failed")):
                expect(RuntimeError, lambda: run.call({"function": "put", "args": [1, True]}))
            assert len(checkpoints(run)) == count
        ''')

    @unittest.skipUnless(NATIVE_RUNNER.is_file(), "requires the emitted native runner")
    def test_exceptional_call_and_deployment_checkpoints_replay_through_native(self):
        self.execute(f'''
            from bytecode_state_fuzz import native_outcome
            run = reference(INVALID_SOURCE)
            run.call({{"function": "put", "args": [17, False], "value": 3}})
            run.call({{"function": "put", "args": [91, True], "value": 5}})
            run.call({{"function": "put", "args": [23, False], "value": 10**30 + 1}})
            runs = [run, reference(INVALID_CONSTRUCTOR, value=9),
                    reference(value=10**30 + 1)]
            for case in runs:
                result = subprocess.run(
                    [{str(NATIVE_RUNNER)!r}], input=json.dumps(case.traces),
                    capture_output=True, text=True, timeout=30,
                )
                assert native_outcome(result.returncode, result.stdout, result.stderr) == "passed", (
                    result.stdout, result.stderr
                )
        ''')


if __name__ == "__main__":
    unittest.main()
