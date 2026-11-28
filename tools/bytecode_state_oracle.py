"""Pinned upstream Vyper compilation and complete py-evm execution traces.

The upstream test exporter remains the source/ABI/AST and call-trace producer;
only full-world checkpoints and JSON argument decoding are added here.
"""

from __future__ import annotations

import importlib
import importlib.metadata
from functools import cache
from itertools import count
from pathlib import Path
from random import Random
import re
import subprocess
import sys
from threading import RLock
from unittest.mock import patch


class OracleError(RuntimeError):
    """Reference configuration/provenance failure, not an EVM outcome."""


class CompilerRejected(Exception):
    """The stock compiler rejected the input, rather than failing internally."""


_CHECKOUT: Path | None = None
_LOCK = RLock()
_BACKEND_VERSION = "0.12.1b1"


@cache
def _account_keys():
    """Cache deterministic identities, never chain state or execution results."""
    from eth_keys.datatypes import PrivateKey

    random = Random(b"vyper")
    return tuple(PrivateKey(random.randbytes(32)) for _ in range(10))


def _git(checkout: Path, *args: str) -> str:
    try:
        result = subprocess.run(
            ["git", "--no-optional-locks", "-C", str(checkout), *args],
            check=True,
            capture_output=True,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        detail = exc.stderr if isinstance(exc, subprocess.CalledProcessError) else str(exc)
        raise OracleError(f"Cannot inspect Vyper checkout {checkout}: {detail}") from exc
    return result.stdout.strip()


def _check_loaded_paths(checkout: Path) -> None:
    for name, module in tuple(sys.modules.items()):
        if name not in ("vyper", "tests") and not name.startswith(("vyper.", "tests.")):
            continue
        if module is None:
            continue
        origin = getattr(module, "__file__", None)
        expected = checkout / name.split(".")[0]
        package_paths = tuple(getattr(module, "__path__", ()))
        if ((origin is None and not package_paths) or
                (origin is not None and not Path(origin).resolve().is_relative_to(expected))):
            raise OracleError(
                f"Module {name!r} is already loaded from {origin!r}; expected {expected}. "
                "Run the oracle in a fresh Python process with the pinned checkout."
            )
        for package_path in package_paths:
            if not Path(package_path).resolve().is_relative_to(expected):
                raise OracleError(f"Module {name!r} has an external package path: {package_path}")


def verify_vyper(checkout: Path, hol_root: Path) -> dict:
    """Require the clean authoritative compiler pin and supported backend version.

    A checkout may live anywhere. Imported compiler and upstream test modules must
    all come from that checkout; changing compiler identity needs a fresh process.
    """
    global _CHECKOUT
    with _LOCK:
        _CHECKOUT = None
        checkout = checkout.resolve()
        pin = (hol_root / "VYPER_PIN").read_text().strip()
        commit = _git(checkout, "rev-parse", "HEAD")
        if commit != pin:
            raise OracleError(f"Vyper HEAD {commit} does not match VYPER_PIN {pin}")
        if _git(checkout, "rev-parse", "--show-toplevel") != str(checkout):
            raise OracleError(f"Not a standalone Vyper checkout: {checkout}")
        dirty = _git(checkout, "status", "--porcelain", "--untracked-files=no")
        if dirty:
            raise OracleError(f"Vyper tracked working tree is not clean:\n{dirty}")
        versions = {}
        for distribution in ("py-evm", "eth-keys", "eth-utils", "eth-abi", "trie", "rlp"):
            try:
                versions[distribution] = importlib.metadata.version(distribution)
            except importlib.metadata.PackageNotFoundError:
                versions[distribution] = None
        if versions["py-evm"] != _BACKEND_VERSION:
            raise OracleError(
                f"Full-state capture requires py-evm=={_BACKEND_VERSION}; "
                f"found {versions['py-evm']!r}"
            )
        _check_loaded_paths(checkout)
        # In particular, the HOL repository's tests directory must not supply the
        # upstream exporter/backend, even when the compiler itself is pinned.
        sys.path.insert(0, str(checkout))
        importlib.invalidate_caches()
        old_bytecode = sys.dont_write_bytecode
        sys.dont_write_bytecode = True
        modules = {}
        try:
            for name in (
                "vyper",
                "tests.exports",
                "tests.evm_backends.base_env",
                "tests.evm_backends.pyevm_env",
                "tests.evm_backends.abi_contract",
                "vyper.compiler.input_bundle",
                "vyper.compiler.settings",
                "vyper.exceptions",
                "eth",
                "eth.db.account",
                "eth.vm.forks.prague",
            ):
                module = importlib.import_module(name)
                modules[name] = str(Path(module.__file__).resolve())
        except ImportError as exc:
            raise OracleError(f"Cannot load pinned Vyper/backend dependencies: {exc}") from exc
        finally:
            sys.dont_write_bytecode = old_bytecode
        _check_loaded_paths(checkout)
        _CHECKOUT = checkout
        return {
            "commit": commit,
            "compiler_version": sys.modules["vyper"].__version__,
            "checkout": str(checkout),
            "compiler_module": modules["vyper"],
            "modules": modules,
            "backend": "PyEvmEnv",
            "evm_version": "prague",
            "state_comparison": "full-world-state-v1",
            "backend_versions": versions,
        }


def _decode_argument(parameter: dict, value):
    """Decode JSON bytes only where the ABI calls for bytes, including containers."""
    kind = parameter["type"]
    if kind.endswith("]"):
        base, _, dimension = kind.rpartition("[")
        if not isinstance(value, (list, tuple)):
            raise TypeError(f"Expected an array for ABI type {kind}")
        length = dimension[:-1]
        if length and len(value) != int(length):
            raise ValueError(f"Expected {length} elements for ABI type {kind}")
        element = {**parameter, "type": base}
        return [_decode_argument(element, item) for item in value]
    if kind == "tuple":
        components = parameter["components"]
        if not isinstance(value, (list, tuple)):
            raise TypeError("Expected a positional sequence for ABI tuple")
        return tuple(_decode_arguments(components, value))
    if re.fullmatch(r"bytes(?:[0-9]+)?", kind) and isinstance(value, str):
        return bytes.fromhex(value.removeprefix("0x"))
    return value


def _decode_arguments(parameters: list[dict], values) -> list:
    if len(parameters) != len(values):
        raise TypeError(f"Expected {len(parameters)} ABI arguments, got {len(values)}")
    return [_decode_argument(parameter, value) for parameter, value in zip(parameters, values)]


def _record_checkpoint(env, traces: list[dict], boundary: str, call_index: int) -> None:
    """Keep original deployment code and complete state from the same observation."""
    capture = getattr(env, "full_state_snapshot", None)
    if not callable(capture):
        raise OracleError("Complete reference state requires the local py-evm adapter")
    snapshot = capture()
    if snapshot.pop("schema_version", None) != 1:
        raise OracleError("Unsupported py-evm complete-state snapshot schema")
    if boundary == "deployment":
        deployment = traces[-1]
        address = deployment["deployed_address"].lower()
        deployment["runtime_bytecode"] = next(
            (account["code"] for account in snapshot["accounts"]
             if account["address"] == address), "")
    traces.append({
        "trace_type": "state_checkpoint",
        "boundary": boundary,
        "call_index": call_index,
        **snapshot,
    })


class ReferenceRun:
    """One deterministic deployment followed by explicitly planned messages."""

    def __init__(
        self,
        source: str,
        *,
        name: str,
        source_dir: Path,
        constructor_args=(),
        value=0,
        optimize="none",
        experimental_codegen=True,
    ):
        with _LOCK:
            if _CHECKOUT is None:
                raise OracleError("verify_vyper(checkout, hol_root) must succeed before ReferenceRun")
            from tests.evm_backends import base_env
            from tests.exports import TestExporter, TracedItem
            from vyper.compiler.input_bundle import FilesystemInputBundle
            from vyper.compiler.settings import OptimizationLevel, Settings
            from vyper.exceptions import ParserException, VyperException
            from bytecode_state_snapshot import env_class

            source_dir = source_dir.resolve()
            checkout = _CHECKOUT

            class MemoryExporter(TestExporter):
                def __init__(self):
                    super().__init__(source_dir, checkout / "tests")
                    self.item = TracedItem(name, [], [], "test")

                @property
                def current_item(self):
                    return self.item

            exporter = MemoryExporter()
            self.traces = exporter.item.traces
            self.env = env_class()(
                gas_limit=10**10,
                account_keys=_account_keys(),
                tracing=False,
                block_number=1,
                evm_version="prague",
                exporter=exporter,
            )
            self.env.timestamp = 1_700_000_000
            self.env.blob_hashes = []
            for account in self.env.accounts:
                self.env.set_balance(account, 10**30)
            settings = Settings(
                optimize=OptimizationLevel.from_string(optimize),
                experimental_codegen=experimental_codegen,
                evm_version="prague",
                enable_decimals=True,
                debug=False,
            )
            formats = dict.fromkeys(("abi", "bytecode", "annotated_ast_dict", "metadata"), True)
            compile_source = base_env._compile
            deploy = self.env.deploy

            def checked_compile(*args, **kwargs):
                # VyperInternalException (including CompilerPanic) deliberately is
                # not a VyperException. Limit classification to compilation, not
                # ABI encoding, deployment, or execution errors.
                try:
                    return compile_source(*args, **kwargs)
                except (VyperException, ParserException) as exc:
                    raise CompilerRejected(str(exc)) from exc

            def deploy_with_json_args(abi, bytecode, *args, **kwargs):
                constructor = next((item for item in abi if item["type"] == "constructor"), None)
                decoded = _decode_arguments(constructor["inputs"] if constructor else [], args)
                return deploy(abi, bytecode, *decoded, **kwargs)

            # Keep upstream source naming reproducible independently of earlier
            # cases, and reuse deploy_source's single compilation/export pipeline.
            try:
                with patch.object(base_env, "_path_index", count()), \
                        patch.object(base_env, "_compile", checked_compile), \
                        patch.object(self.env, "deploy", deploy_with_json_args):
                    self.contract = self.env.deploy_source(
                        source,
                        formats,
                        *constructor_args,
                        value=value,
                        compiler_settings=settings,
                        input_bundle=FilesystemInputBundle([source_dir]),
                    )
            except base_env.EvmError as error:
                if not self.env.is_execution_failure(error):
                    raise
                self.contract = None
            self.abi = (self.contract.abi if self.contract is not None
                        else self.traces[-1]["contract_abi"])
            self.addresses = tuple(self.env.accounts) + (
                (self.contract.address,) if self.contract is not None else ()
            )
            self._call_index = 0
            _record_checkpoint(self.env, self.traces, "deployment", 0)

    def call(self, plan: dict) -> None:
        """Checkpoint non-resource EVM failures, never setup or backend errors."""
        with _LOCK:
            from tests.evm_backends.base_env import EvmError
            if self.contract is None:
                raise ValueError("Cannot call a contract whose deployment failed")

            function_name = plan["function"]
            arguments = plan.get("args", [])
            candidates = [
                item for item in self.abi
                if item["type"] == "function" and item["name"] == function_name
                and len(item["inputs"]) == len(arguments)
            ]
            if len(candidates) != 1:
                raise ValueError(f"Expected one ABI entry for {function_name!r} with {len(arguments)} arguments")
            decoded = _decode_arguments(candidates[0]["inputs"], arguments)
            function = getattr(self.contract, function_name)
            self.env.clear_transient_storage()
            try:
                function(*decoded, value=plan.get("value", 0))
            except EvmError as error:
                if not self.env.is_execution_failure(error):
                    raise
                # Upstream BaseEnv already exported call_succeeded=False.
            _record_checkpoint(self.env, self.traces, "call", self._call_index)
            self._call_index += 1
