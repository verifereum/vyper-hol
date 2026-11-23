"""Real py-evm trie, journal, execution and pinned-fixture lifecycle regressions.

Direct state checks require the pinned py-evm dependencies. Fixture checks also
require VYPER_STATE_VYPER (default: the repository's vyper-ref), verified in isolated
processes so compiler/test-package globals cannot leak between unittest modules.
"""

import copy
import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import textwrap
import unittest


HAS_PYEVM = importlib.util.find_spec("eth") is not None
if HAS_PYEVM:
    import rlp
    from eth.constants import BLANK_ROOT_HASH
    from eth.db.account import AccountDB
    from eth.db.atomic import AtomicDB
    from eth.db.backends.memory import MemoryDB
    from eth.rlp.accounts import Account
    from eth.vm.execution_context import ExecutionContext
    from eth.vm.forks.prague.state import PragueState
    from eth.vm.message import Message
    from eth_hash.auto import keccak
    from lru import LRU
    from trie import HexaryTrie

    from bytecode_state_snapshot import SnapshotAccountDB, capture

    STATE = PragueState.configure(account_db_class=SnapshotAccountDB)

A = bytes.fromhex("11" * 20)
B = bytes.fromhex("22" * 20)
C = bytes.fromhex("33" * 20)
ROOT = Path(__file__).resolve().parents[1]
CHECKOUT = Path(os.environ.get("VYPER_STATE_VYPER", ROOT / "vyper-ref")).resolve()
HAS_FIXTURE = HAS_PYEVM and (CHECKOUT / "tests/evm_backends/pyevm_env.py").is_file()


def address(value):
    return "0x" + value.hex()


def frozen(value):
    """Fingerprint caches, access logs, roots and rollback data without DB reads."""
    if value is None or type(value) in (bytes, int, str, bool):
        return value
    if callable(value):
        return id(value)
    if isinstance(value, dict):
        return tuple((frozen(k), frozen(v)) for k, v in value.items())
    if isinstance(value, (tuple, list)):
        return tuple(frozen(v) for v in value)
    if isinstance(value, (set, frozenset)):
        return frozenset(frozen(v) for v in value)
    if isinstance(value, LRU):
        return tuple(value.items())
    fields = dict(getattr(value, "__dict__", {}))
    for cls in type(value).__mro__:
        for name in getattr(cls, "__slots__", ()):
            if hasattr(value, name):
                fields[name] = getattr(value, name)
    return (type(value), frozen(fields)) if fields else (type(value), id(value))


@unittest.skipUnless(HAS_PYEVM, "requires pinned py-evm dependencies")
class SnapshotStateTests(unittest.TestCase):
    def setUp(self):
        context = ExecutionContext(
            coinbase=b"\x00" * 20, timestamp=1, block_number=1, difficulty=0,
            mix_hash=b"\x00" * 32, gas_limit=30_000_000, prev_hashes=(),
            chain_id=1, base_fee_per_gas=0, excess_blob_gas=0,
        )
        self.raw = AtomicDB()
        self.state = STATE(self.raw, context, BLANK_ROOT_HASH)
        self.db = self.state._account_db
        self.logs = []

    def snapshot(self):
        return capture(self.state, self.logs)

    def account(self, target=A):
        return next(row for row in self.snapshot()["accounts"]
                    if row["address"] == address(target))

    def install(self, code, target=A):
        self.state.set_nonce(target, 1)
        self.state.set_code(target, bytes.fromhex(code))

    def execute(self, target=A):
        computation = self.state.computation_class.apply_message(
            self.state,
            Message(to=target, sender=B, value=0, data=b"", gas=1_000_000,
                    code=self.state.get_code(target)),
            self.state.transaction_context_class(origin=B, gas_price=0),
        )
        if not computation.is_error:
            self.logs.extend(computation.get_log_entries())
        return computation

    def fingerprint(self):
        return frozen((self.db, getattr(self.state, "_transient_storage", None)))

    def assert_capture_fails_readonly(self):
        before = self.fingerprint()
        with self.assertRaises(RuntimeError):
            self.snapshot()
        self.assertEqual(self.fingerprint(), before)

    def test_empty_world_and_read_caches_are_not_support(self):
        empty = {"schema_version": 1, "accounts": [], "transient_storage": [], "logs": []}
        self.assertIsNone(self.state._transient_storage)
        before = self.fingerprint()
        self.assertEqual(self.snapshot(), empty)
        self.assertEqual(self.fingerprint(), before)
        self.assertIsNone(self.state._transient_storage)
        self.state.get_balance(A)
        self.state.get_storage(B, 2**255)
        self.assertIn(B, self.db._account_stores)
        before = self.fingerprint()
        self.assertEqual(self.snapshot(), empty)
        self.assertEqual(self.fingerprint(), before)

    def test_backing_locked_and_live_storage_are_complete(self):
        self.install("00")
        self.state.set_storage(A, 2**255, 17)
        self.state.set_storage(A, 99, 23)
        self.state.persist()
        self.assertEqual(self.db._account_stores, {})
        self.state.set_storage(A, 3, 41)
        self.state.lock_changes()
        self.state.set_storage(A, 99, 0)
        self.state.set_storage(A, 0, 12)
        self.assertEqual(self.account()["storage"], [
            {"slot": 0, "value": 12}, {"slot": 3, "value": 41},
            {"slot": 2**255, "value": 17},
        ])
        before = self.snapshot()
        self.state.make_state_root()
        self.assertEqual(self.snapshot(), before)
        self.state.persist()
        self.assertEqual(self.snapshot(), before)
        self.assertEqual(self.db._account_stores, {})

    def test_persisted_and_live_accounts_and_deletions(self):
        self.state.set_balance(A, 7)
        self.state.set_balance(B, 9)
        self.state.persist()
        self.state.set_balance(A, 11)
        self.state.set_balance(C, 13)
        self.state.delete_account(B)
        self.assertEqual([(row["address"], row["balance"]) for row in
                          self.snapshot()["accounts"]], [(address(A), 11), (address(C), 13)])
        before = self.snapshot()
        self.state.persist()
        self.assertEqual(self.snapshot(), before)

    def test_storage_only_accounts_and_zero_normalization(self):
        self.state.set_storage(C, 9, 1)
        self.state.set_balance(B, 4)
        self.state.set_balance(A, 0)
        self.assertEqual([row["address"] for row in self.snapshot()["accounts"]],
                         [address(B), address(C)])
        self.assertEqual(self.account(C), {
            "address": address(C), "balance": 0, "nonce": 0, "code": "",
            "storage": [{"slot": 9, "value": 1}],
        })
        before = self.snapshot()
        self.state.persist()
        self.assertEqual(self.snapshot(), before)
        self.state.set_storage(C, 9, 0)
        self.assertEqual([row["address"] for row in self.snapshot()["accounts"]], [address(B)])
        self.state.persist()
        self.assertEqual([row["address"] for row in self.snapshot()["accounts"]], [address(B)])

    def test_original_and_detached_code_retains_trailing_stops(self):
        self.install("60000000")
        self.assertFalse(self.execute().is_error)
        code_hash = self.state.get_code_hash(A)
        self.db._set_account(B, Account(nonce=2, code_hash=code_hash))
        for target in (A, B):
            self.assertEqual(self.account(target)["code"], "60000000")
        self.state.persist()
        for target in (A, B):
            self.assertEqual(self.account(target)["code"], "60000000")
        self.state.get_code(B)
        self.assertEqual(self.account(B)["code"], "60000000")

    def test_snapshots_are_readonly_and_detached_with_live_checkpoints(self):
        self.install("602a60075500")
        self.state.set_storage(A, 2**255, 17)
        self.state.persist()
        checkpoint = self.state.snapshot()
        self.assertFalse(self.execute().is_error)
        self.state.get_storage(A, 19)
        self.state.mark_storage_warm(A, 7)
        self.state.set_transient_storage(C, 8, b"\x2b")
        before = self.fingerprint()
        snapshot = self.snapshot()
        saved = copy.deepcopy(snapshot)
        self.assertEqual(self.fingerprint(), before)
        self.assertEqual(self.snapshot(), saved)
        self.assertEqual(self.fingerprint(), before)
        snapshot["accounts"][0]["storage"][0]["value"] = 999
        snapshot["transient_storage"][0]["value"] = 999
        self.assertEqual(self.snapshot(), saved)
        self.state.set_storage(A, 7, 88)
        self.assertEqual(saved["accounts"][0]["storage"][0], {"slot": 7, "value": 42})
        self.state.revert(checkpoint)
        self.assertEqual(self.account()["storage"], [{"slot": 2**255, "value": 17}])
        self.assertEqual(self.snapshot()["transient_storage"], [])

    def test_missing_and_corrupt_bytecode_fail_without_mutation(self):
        self.db._set_account(A, Account(nonce=1, code_hash=b"\x99" * 32))
        self.assert_capture_fails_readonly()
        self.state.persist()
        self.assert_capture_fails_readonly()
        self.install("00")
        self.db._journaldb[self.state.get_code_hash(A)] = b"\x01"
        self.assert_capture_fails_readonly()

    def test_account_deletion_and_storage_clear_are_revertible(self):
        self.install("00")
        self.state.set_storage(A, 1, 12)
        self.state.persist()
        self.state.set_storage(A, 2, 13)
        self.state.lock_changes()
        self.state.set_storage(A, 3, 14)
        before = self.snapshot()
        checkpoint = self.state.snapshot()
        self.state.delete_account(A)
        self.assertEqual(self.snapshot()["accounts"], [])
        self.state.revert(checkpoint)
        self.assertEqual(self.snapshot(), before)
        checkpoint = self.state.snapshot()
        self.state.delete_storage(A)
        self.state.set_storage(A, 9, 42)
        self.assertEqual(self.account()["storage"], [{"slot": 9, "value": 42}])
        self.state.revert(checkpoint)
        self.assertEqual(self.snapshot(), before)

    def test_deleted_account_can_gain_storage_only_support(self):
        self.install("00")
        self.state.set_storage(A, 1, 12)
        self.state.persist()
        self.state.delete_account(A)
        self.state.set_storage(A, 2, 13)
        self.assertEqual(self.account(), {
            "address": address(A), "balance": 0, "nonce": 0, "code": "",
            "storage": [{"slot": 2, "value": 13}],
        })
        before = self.snapshot()
        self.state.persist()
        self.assertEqual(self.snapshot(), before)

    def test_reverted_storage_transient_and_logs_then_explicit_reset(self):
        self.install("602a600755602b60095d6001600052600260206000a100")
        self.assertFalse(self.execute().is_error)
        snapshot = self.snapshot()
        self.assertEqual(snapshot["transient_storage"], [
            {"address": address(A), "slot": 9, "value": 43},
        ])
        self.assertEqual(snapshot["logs"], [
            {"address": address(A), "topics": [f"{2:064x}"], "data": f"{1:064x}"},
        ])
        self.install("6063600755606460095d6001600052600360206000a160006000fd")
        before = self.snapshot()
        self.assertTrue(self.execute().is_error)
        self.assertEqual(self.snapshot(), before)
        self.state.clear_transient_storage()
        self.assertEqual(self.snapshot()["transient_storage"], [])
        self.assertEqual(self.snapshot()["logs"], snapshot["logs"])
        self.assertEqual(self.account()["storage"], [{"slot": 7, "value": 42}])

    def test_cumulative_ordered_logs_are_detached_and_zero_transient_is_absent(self):
        self.install("602b60095d600060095d60006000a000")
        self.assertFalse(self.execute().is_error)
        self.install("6001600052600360206000a100", C)
        self.assertFalse(self.execute(C).is_error)
        self.assertFalse(self.execute().is_error)
        snapshot = self.snapshot()
        self.assertEqual(snapshot["transient_storage"], [])
        self.assertEqual(snapshot["logs"], [
            {"address": address(A), "topics": [], "data": ""},
            {"address": address(C), "topics": [f"{3:064x}"], "data": f"{1:064x}"},
            {"address": address(A), "topics": [], "data": ""},
        ])
        snapshot["logs"][1]["topics"].append("ff")
        self.assertEqual(len(self.snapshot()["logs"][1]["topics"]), 1)

    def test_transient_clear_rollback_and_numeric_order(self):
        self.state.set_transient_storage(C, 2**255, b"\x12")
        self.state.set_transient_storage(A, 256, b"\x0b")
        self.state.set_transient_storage(A, 2, b"\x0c")
        self.state.set_transient_storage(B, 0, b"\x00")
        self.assertEqual(self.snapshot()["transient_storage"], [
            {"address": address(A), "slot": 2, "value": 12},
            {"address": address(A), "slot": 256, "value": 11},
            {"address": address(C), "slot": 2**255, "value": 18},
        ])
        before = self.snapshot()
        checkpoint = self.state.snapshot()
        self.state.clear_transient_storage()
        self.state.set_transient_storage(B, 0, b"\x63")
        self.assertEqual(self.snapshot()["transient_storage"], [
            {"address": address(B), "slot": 0, "value": 99},
        ])
        self.state.revert(checkpoint)
        self.assertEqual(self.snapshot(), before)

    def test_nonempty_initial_root_and_untracked_account_db_are_rejected(self):
        self.state.set_balance(A, 1)
        self.state.persist()
        with self.assertRaises(RuntimeError):
            SnapshotAccountDB(self.raw, self.state.state_root)
        self.state._account_db = AccountDB(AtomicDB())
        self.assert_capture_fails_readonly()

    def test_remote_or_custom_database_is_rejected_even_for_empty_world(self):
        class RemoteDB(MemoryDB):
            pass

        with self.assertRaises(RuntimeError):
            SnapshotAccountDB(AtomicDB(RemoteDB()))
        self.raw.wrapped_db = RemoteDB()
        self.assert_capture_fails_readonly()

    def test_unknown_account_preimage_fails_closed_without_mutation(self):
        # An untracked complete trie must be discovered, not skipped because its
        # address was never supplied to the tracking API.
        trie = HexaryTrie(self.raw)
        trie[keccak(C)] = rlp.encode(Account(balance=17))
        self.db.state_root = trie.root_hash
        self.assert_capture_fails_readonly()

    def test_unknown_storage_preimage_fails_closed_without_mutation(self):
        trie = HexaryTrie(self.raw)
        trie[keccak((2**255).to_bytes(32, "big"))] = rlp.encode(17)
        self.db._set_account(A, Account(storage_root=trie.root_hash))
        self.assert_capture_fails_readonly()

    def test_incomplete_account_and_storage_tries_fail_closed_without_mutation(self):
        self.db.state_root = b"\x99" * 32
        self.assert_capture_fails_readonly()
        self.db.state_root = BLANK_ROOT_HASH
        self.db._set_account(A, Account(storage_root=b"\x99" * 32))
        self.assert_capture_fails_readonly()


# Each scenario verifies compiler identity before importing upstream fixtures.
# No runtime dependency on the external fuzzer's oracle or backend is involved.
PRELUDE = '''
import sys
from pathlib import Path
from random import Random
sys.dont_write_bytecode = True
sys.path.insert(0, {tools!r})
from bytecode_state_oracle import verify_vyper
verify_vyper(Path({checkout!r}), Path({root!r}))
from bytecode_state_snapshot import env_class
from eth_keys.datatypes import PrivateKey
from tests.evm_backends.base_env import EvmError, ExecutionReverted

A = "0x" + "11" * 20
B = "0x" + "22" * 20
C = "0x" + "33" * 20

def make_env(version="prague"):
    random = Random(b"vyper")
    return env_class()(
        gas_limit=10**8,
        account_keys=tuple(PrivateKey(random.randbytes(32)) for _ in range(10)),
        tracing=False, block_number=1, evm_version=version, exporter=None,
    )

def install(env, code, address=A):
    raw = bytes.fromhex(address[2:])
    env._state.set_code(raw, bytes.fromhex(code))
    env._state.set_nonce(raw, 1)

def accounts(env):
    return {{entry["address"]: entry for entry in env.full_state_snapshot()["accounts"]}}

def expect(error_type, action):
    try:
        action()
    except error_type as error:
        return error
    raise AssertionError("expected " + error_type.__name__)
'''.format(tools=str(ROOT / "tools"), checkout=str(CHECKOUT), root=str(ROOT))


@unittest.skipUnless(HAS_FIXTURE, "requires pinned Vyper checkout via VYPER_STATE_VYPER and py-evm")
class SnapshotFixtureTests(unittest.TestCase):
    def execute(self, body):
        result = subprocess.run([sys.executable, "-c", PRELUDE + textwrap.dedent(body)],
                                cwd=ROOT, capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_constructor_installs_tracking_before_any_fixture_writes(self):
        self.execute('''
            env = make_env()
            assert env.full_state_snapshot() == {
                "schema_version": 1, "accounts": [], "transient_storage": [], "logs": [],
            }
            env.set_balance(B, 13)
            env._state.set_storage(bytes.fromhex(C[2:]), 2**255, 17)
            install(env, "60000000")
            world = accounts(env)
            assert sorted(world) == [A, B, C]
            assert world[A]["code"] == "60000000"
            assert world[B]["balance"] == 13
            assert world[C]["storage"] == [{"slot": 2**255, "value": 17}]
        ''')

    def test_reverts_keep_committed_logs_storage_and_explicit_transient_lifecycle(self):
        self.execute('''
            env = make_env()
            install(env, "602a600755602b60095d6001600052600260206000a100")
            env.message_call(A)
            env.message_call(A)
            before = env.full_state_snapshot()
            assert before["transient_storage"] == [{"address": A, "slot": 9, "value": 43}]
            assert before["logs"] == [
                {"address": A, "topics": [f"{2:064x}"], "data": f"{1:064x}"},
                {"address": A, "topics": [f"{2:064x}"], "data": f"{1:064x}"},
            ]
            install(env, "6063600755606460095d6001600052600360206000a160006000fd")
            before_revert = env.full_state_snapshot()
            expect(ExecutionReverted, lambda: env.message_call(A))
            assert not env.last_result.is_success
            assert env.full_state_snapshot() == before_revert
            env.clear_transient_storage()
            after = env.full_state_snapshot()
            assert after["transient_storage"] == []
            assert after["logs"] == before["logs"]
            assert accounts(env)[A]["storage"] == [{"slot": 7, "value": 42}]
        ''')

    def test_nested_anchor_retains_branch_until_exit_and_restores_context_and_reset(self):
        self.execute('''
            env = make_env()
            install(env, "602a600755602b60095d60006000a000")
            env.message_call(A)
            env.timestamp = 123
            baseline = env.full_state_snapshot()
            with env.anchor():
                env.timestamp = 456
                env.clear_transient_storage()
                install(env, "6063600755606460095d60006000a000")
                env.message_call(A)
                branch = env.full_state_snapshot()
                assert len(branch["logs"]) == 2
                assert branch["transient_storage"] == [{"address": A, "slot": 9, "value": 100}]
                try:
                    with env.anchor():
                        env.timestamp = 789
                        env.clear_transient_storage()
                        env.message_call(A)
                        assert len(env.full_state_snapshot()["logs"]) == 3
                        raise LookupError("rollback branch")
                except LookupError:
                    pass
                assert env.timestamp == 456
                assert env.full_state_snapshot() == branch
            assert env.timestamp == 123
            assert env.full_state_snapshot() == baseline
        ''')

    def test_nested_call_log_order_and_reverted_child_logs(self):
        self.execute('''
            env = make_env()
            emit = lambda topic: f"60{topic:02x}60006000a1"
            invoke = "6000600060006000600073" + C[2:] + "61fffff150"
            install(env, emit(3) + "00", C)
            install(env, emit(1) + invoke + emit(2) + "00")
            env.message_call(A)
            logs = env.full_state_snapshot()["logs"]
            assert [(log["address"], int(log["topics"][0], 16)) for log in logs] == [
                (A, 1), (C, 3), (A, 2),
            ]
            install(env, emit(3) + "60006000fd", C)
            env.message_call(A)
            logs = env.full_state_snapshot()["logs"]
            assert [(log["address"], int(log["topics"][0], 16)) for log in logs[3:]] == [
                (A, 1), (A, 2),
            ]
        ''')

    def test_successful_selfdestruct_finalizes_deletion_and_anchor_restores_it(self):
        self.execute('''
            env = make_env("shanghai")
            install(env, "73" + B[2:] + "ff")
            env.set_balance(A, 13)
            env._state.set_storage(bytes.fromhex(A[2:]), 7, 42)
            baseline = env.full_state_snapshot()
            with env.anchor():
                env.message_call(A)
                assert env.last_result.is_success
                assert env.full_state_snapshot()["accounts"] == [{
                    "address": B, "balance": 13, "nonce": 0, "code": "", "storage": [],
                }]
            assert env.full_state_snapshot() == baseline
        ''')

    def test_prague_preserves_existing_selfdestruct_but_deletes_created_child(self):
        self.execute('''
            env = make_env()
            code = "73" + B[2:] + "ff"
            install(env, code)
            env.set_balance(A, 13)
            env._state.set_storage(bytes.fromhex(A[2:]), 7, 42)
            env.message_call(A)
            assert accounts(env)[A] == {
                "address": A, "balance": 0, "nonce": 1, "code": code,
                "storage": [{"slot": 7, "value": 42}],
            }
            assert accounts(env)[B]["balance"] == 13

            env = make_env()
            initcode = bytes.fromhex("602a60075573" + B[2:] + "ff")
            factory = (b"\\x7f" + initcode.ljust(32, b"\\x00") + bytes.fromhex("600052")
                       + bytes.fromhex(f"60{len(initcode):02x}6000600df060005260206000f3"))
            install(env, factory.hex())
            env.set_balance(A, 13)
            child = "0x" + env.message_call(A)[-20:].hex()
            assert int(child, 16) != 0
            world = accounts(env)
            assert sorted(world) == [A, B]
            assert child not in world
            assert world[B]["balance"] == 13
            assert world[A]["nonce"] == 2
        ''')

    def test_deployment_logs_and_real_errors_retain_upstream_interface(self):
        self.execute('''
            env = make_env()
            initcode = bytes.fromhex("6001600052600760206000a160006000f3")
            contract = env.deploy([], initcode)
            address = contract.address.lower()
            assert env.last_result.is_success
            assert env.get_code(contract.address) == b""
            assert accounts(env)[address]["nonce"] == 1
            committed = env.full_state_snapshot()["logs"]
            assert committed == [{
                "address": address, "topics": [f"{7:064x}"], "data": f"{1:064x}",
            }]
            expect(ExecutionReverted, lambda: env.deploy([], bytes.fromhex("60006000fd")))
            assert env.full_state_snapshot()["logs"] == committed
            invalid = expect(EvmError, lambda: env.deploy([], bytes.fromhex("fe")))
            assert not isinstance(invalid, ExecutionReverted)
            unfunded = expect(EvmError, lambda: env.message_call(B, value=1))
            assert not isinstance(unfunded, ExecutionReverted)
            expect(ValueError, lambda: env.message_call("not-an-address"))
            assert env.full_state_snapshot()["logs"] == committed
        ''')


if __name__ == "__main__":
    unittest.main()
