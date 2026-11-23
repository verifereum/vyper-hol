"""Read-only full-world-state-v1 capture for the pinned py-evm 0.12.1b1.

Trie keys are hashes, not enumerable original addresses/slots. Keep write preimages
from an empty local world, and validate every enumerated trie leaf against them.
Private DB layouts below are deliberately version-specific and fail closed.

The upstream Vyper fixture is imported only by env_class(), which callers must
invoke after bytecode_state_oracle.verify_vyper establishes checkout provenance.
"""

from contextlib import contextmanager
from functools import cached_property

import rlp
from eth.constants import BLANK_ROOT_HASH, EMPTY_SHA3
from eth.db.accesslog import KeyAccessLoggerAtomicDB, KeyAccessLoggerDB
from eth.db.account import AccountDB
from eth.db.atomic import AtomicDB
from eth.db.backends.memory import MemoryDB
from eth.db.batch import BatchDB
from eth.db.diff import DiffMissingError
from eth.db.journal import DELETE_WRAPPED, REVERT_TO_WRAPPED, JournalDB
from eth.db.storage import AccountStorageDB
from eth.rlp.accounts import Account
from eth.vm.transient_storage import TransientStorage
from eth_hash.auto import keccak
from trie import HexaryTrie
from trie.iter import NodeIterator


class _ReadDB:
    """A read-only view that never enters caches, access loggers or remote DBs."""

    def __init__(self, db):
        self.db = db
        kind = type(db)
        if kind is MemoryDB:
            if type(db.kv_store) is not dict:
                raise RuntimeError("Complete state snapshots require a finite in-memory dictionary")
            self.parent = None
        elif kind in (AtomicDB, KeyAccessLoggerAtomicDB, KeyAccessLoggerDB, BatchDB):
            self.parent = _ReadDB(db.wrapped_db)
        elif kind is JournalDB:
            self.parent = _ReadDB(db._wrapped_db)
        else:
            raise RuntimeError(
                f"Complete state snapshots require a finite in-memory backend; "
                f"unsupported database {kind.__name__}"
            )

    def __getitem__(self, key):
        db = self.db
        kind = type(db)
        if kind is MemoryDB:
            return db.kv_store[key]
        if kind is BatchDB:
            try:
                return db._track_diff[key]
            except DiffMissingError as missing:
                if missing.is_deleted and not db._read_through_deletes:
                    raise KeyError(key) from missing
        elif kind is JournalDB:
            journal = db._journal
            value = journal._current_values.get(key)
            if value is DELETE_WRAPPED or value is REVERT_TO_WRAPPED:
                raise KeyError(key)
            if value is not None:
                return value
            if journal._ignore_wrapped_db:
                raise KeyError(key)
        return self.parent[key]


def _overlay(values, db):
    """Apply the entire logical journal, including clear and local deletions."""
    if type(db) is not JournalDB:
        raise RuntimeError("Unsupported py-evm journal layout")
    journal = db._journal
    if journal._ignore_wrapped_db:
        values.clear()
    for key, value in journal._current_values.items():
        if value is DELETE_WRAPPED or value is REVERT_TO_WRAPPED:
            values.pop(key, None)
        elif type(value) is bytes:
            values[key] = value
        else:
            raise RuntimeError("Unsupported py-evm journal value")


def _leaves(db, root):
    # A fresh trie owns its traversal state. Its reads bypass every source wrapper
    # with read-side effects; neither roots nor journals are flushed to enumerate.
    try:
        yield from NodeIterator(HexaryTrie(_ReadDB(db), root_hash=root)).items()
    except KeyError as exc:
        raise RuntimeError("Incomplete backing trie; cannot export complete state") from exc
    except RuntimeError:
        raise
    except Exception as exc:
        raise RuntimeError("Incomplete or invalid backing trie; cannot export complete state") from exc


class SnapshotAccountDB(AccountDB):
    """AccountDB with monotone write preimages, retained across persist and revert."""

    def __init__(self, db, state_root=BLANK_ROOT_HASH):
        if state_root != BLANK_ROOT_HASH:
            raise RuntimeError("Complete state tracking must start from an empty state root")
        _ReadDB(db)  # Reject a remote/custom backing store before any writes.
        self._snapshot_addresses = {}
        self._snapshot_slots = {}
        super().__init__(db, state_root)

    def _remember_address(self, address):
        self._snapshot_addresses[keccak(address)] = address

    def _set_account(self, address, account):
        super()._set_account(address, account)
        self._remember_address(address)

    def set_storage(self, address, slot, value):
        super().set_storage(address, slot, value)
        self._remember_address(address)
        self._snapshot_slots.setdefault(address, {})[keccak(slot.to_bytes(32, "big"))] = slot

    def delete_account(self, address):
        super().delete_account(address)
        self._remember_address(address)


def _storage(account_db, address, account):
    store = account_db._account_stores.get(address)
    if store is None:
        db = account_db._raw_store_db
        root = account.storage_root
    else:
        if type(store) is not AccountStorageDB:
            raise RuntimeError("Unsupported py-evm storage layout")
        lookup = store._storage_lookup
        if lookup._write_trie is None:
            db, root = lookup._db, lookup._starting_root_hash
        else:
            db, root = lookup._write_trie.db, lookup._write_trie.root_hash

    preimages = account_db._snapshot_slots.get(address, {})
    values = {}
    for hashed, encoded in _leaves(db, root):
        if hashed not in preimages:
            raise RuntimeError("Unknown storage preimage; cannot export complete state")
        slot = preimages[hashed]
        values[slot.to_bytes(max(1, (slot.bit_length() + 7) // 8), "big")] = encoded
    if store is not None:
        _overlay(values, store._locked_changes)
        _overlay(values, store._journal_storage)

    result = []
    for key, encoded in values.items():
        slot = int.from_bytes(key, "big")
        if not 0 <= slot < 2**256:
            raise RuntimeError("Invalid storage slot")
        value = rlp.decode(encoded, sedes=rlp.sedes.big_endian_int) if encoded else 0
        if value:
            result.append({"slot": slot, "value": value})
    return sorted(result, key=lambda entry: entry["slot"])


def _transient(state):
    # Do not access state.transient_storage: that property initializes it on read.
    transient = getattr(state, "_transient_storage", None)
    if transient is None:
        return []
    if type(transient) is not TransientStorage:
        raise RuntimeError("Unsupported py-evm transient storage layout")
    db = transient._db
    if type(db) is not JournalDB or type(db._wrapped_db) is not MemoryDB:
        raise RuntimeError("Unsupported py-evm transient database")
    _ReadDB(db)
    values = dict(db._wrapped_db.kv_store)
    _overlay(values, db)
    result = []
    for key, encoded in sorted(values.items()):
        if not 21 <= len(key) <= 52:
            raise RuntimeError("Invalid transient storage key")
        value = int.from_bytes(encoded, "big")
        if value:
            result.append({
                "address": "0x" + key[:20].hex(),
                "slot": int.from_bytes(key[20:], "big"),
                "value": value,
            })
    return sorted(result, key=lambda entry: (entry["address"], entry["slot"]))


def capture(state, logs):
    """Export detached canonical state and cumulative committed raw EVM log triples."""
    account_db = state._account_db
    if type(account_db) is not SnapshotAccountDB:
        raise RuntimeError("SnapshotAccountDB must be installed before state writes")
    # Validate the backing store even for a blank world and bytecode-free state.
    code_db = _ReadDB(account_db._journaldb)
    values = {}
    for hashed, encoded in _leaves(account_db._trie._db.db, account_db.state_root):
        if hashed not in account_db._snapshot_addresses:
            raise RuntimeError("Unknown account preimage; cannot export complete state")
        values[account_db._snapshot_addresses[hashed]] = encoded
    _overlay(values, account_db._journaltrie)

    accounts = []
    # A storage write need not create an encoded account until make_state_root().
    for address in sorted(values.keys() | account_db._account_stores.keys()):
        encoded = values.get(address)
        account = rlp.decode(encoded, sedes=Account) if encoded else Account()
        storage = _storage(account_db, address, account)
        if account.code_hash == EMPTY_SHA3 or account.code_hash == b"\x00" * 32:
            code = b""
        else:
            try:
                code = code_db[account.code_hash]
            except KeyError as exc:
                raise RuntimeError(
                    f"Missing bytecode for local account 0x{address.hex()}; "
                    "cannot export complete state"
                ) from exc
            if keccak(code) != account.code_hash:
                raise RuntimeError("Bytecode hash mismatch; cannot export complete state")
        if account.balance or account.nonce or code or storage:
            accounts.append({
                "address": "0x" + address.hex(),
                "balance": account.balance,
                "nonce": account.nonce,
                "code": code.hex(),
                "storage": storage,
            })
    return {
        "schema_version": 1,
        "accounts": accounts,
        "transient_storage": _transient(state),
        "logs": [
            {"address": "0x" + address.hex(),
             "topics": [f"{topic:064x}" for topic in topics], "data": data.hex()}
            for address, topics, data in logs
        ],
    }


def env_class():
    """Return the pinned fixture with finite-state capture and message finalization.

    Call only after verify_vyper succeeds; no upstream fixture is imported while
    importing this module or using capture directly on a local py-evm state.
    """
    from tests.evm_backends.pyevm_env import PyEvmEnv
    from eth.exceptions import InsufficientFunds, OutOfGas
    from tests.evm_backends.base_env import EvmError

    class SnapshotPyEvmEnv(PyEvmEnv):
        def __init__(self, gas_limit, account_keys, tracing, block_number, evm_version, exporter):
            self._logs = []
            self._operation_computation = None
            self._operation_exception = None
            self._operation_checkpoint = None
            super().__init__(gas_limit, account_keys, tracing, block_number, evm_version, exporter)

        @cached_property
        def _vm(self):
            # Upstream creates the empty genesis chain in __init__, but builds
            # this VM's state lazily. Configure its class before even the first
            # balance, code, storage or fork-initialization write can occur.
            vm = self._chain.get_vm()
            state_class = vm.get_state_class().configure(account_db_class=SnapshotAccountDB)
            vm_class = type(vm).configure(_state_class=state_class)
            return vm_class(
                header=vm.get_header(),
                chaindb=vm.chaindb,
                chain_context=vm.chain_context,
                consensus_context=vm.consensus_context,
            )

        def full_state_snapshot(self):
            return capture(self._state, self._logs)

        def is_execution_failure(self, error):
            """Recognize only this operation's non-resource EVM failure.

            last_result intentionally retains the upstream fixture semantics: it
            can still describe an earlier operation when apply_message rejects
            insufficient funds before returning any computation.
            """
            return (
                error is self._operation_exception
                and not isinstance(error.__cause__, OutOfGas)
            )

        @contextmanager
        def _execution_operation(self):
            self._operation_computation = None
            self._operation_exception = None
            self._operation_checkpoint = self._state.snapshot()
            try:
                yield
            except BaseException as error:
                # apply_message/create_message can raise before returning a
                # computation, leaving their own journal checkpoint open.
                self._state.revert(self._operation_checkpoint)
                computation = self._operation_computation
                if isinstance(error, EvmError) and (
                    (computation is not None
                     and computation.is_error
                     and error.__cause__ is computation.error)
                    or (computation is None
                        and isinstance(error.__cause__, InsufficientFunds))
                ):
                    self._operation_exception = error
                raise
            else:
                self._state.commit(self._operation_checkpoint)
            finally:
                self._operation_checkpoint = None

        def _message_call(self, *args, **kwargs):
            with self._execution_operation():
                return super()._message_call(*args, **kwargs)

        def _deploy(self, *args, **kwargs):
            with self._execution_operation():
                return super()._deploy(*args, **kwargs)

        def _generate_contract_address(self, sender):
            address = super()._generate_contract_address(sender)
            # The fixture consumes this nonce before attempting CREATE. Keep it
            # on failure, but roll back the new account's nonce and all init writes.
            if self._operation_checkpoint is not None:
                self._state.commit(self._operation_checkpoint)
                self._operation_checkpoint = self._state.snapshot()
            return address

        def _check_computation(self, computation):
            self._operation_computation = computation
            if not computation.is_error:
                # Direct message helpers commit writes but leave SELFDESTRUCT
                # deletion to the transaction executor. Apply only that missing
                # transition, using py-evm's fork-specific deletion list (including
                # EIP-6780). Do not charge fees or reset transient storage here.
                for address in computation.get_accounts_for_deletion():
                    self._state.delete_account(address)
                self._logs.extend(computation.get_log_entries())
            # Retain pinned error/revert parsing and last_result. Infrastructure
            # and ABI/compiler errors must never be converted to EVM reverts.
            super()._check_computation(computation)

        @contextmanager
        def anchor(self):
            length = len(self._logs)
            try:
                with super().anchor():
                    # Branch state and cumulative logs remain visible until exit.
                    yield
            finally:
                del self._logs[length:]

    return SnapshotPyEvmEnv
