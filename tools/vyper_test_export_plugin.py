"""Preserve exact revm runtime bytes in upstream deployment exports."""

from __future__ import annotations

from collections.abc import Generator
from typing import Any

import pytest
from eth_hash.auto import keccak
from tests.evm_backends.base_env import BaseEnv
from tests.evm_backends.revm_env import RevmEnv
from tests.exports import TestExporter
from vyper.evm.opcodes import EVM_VERSIONS

# deployment_type values the replay decoder reads as raw deployments.
RAW_DEPLOYMENT_TYPES = {"raw_bytecode", "ir"}


def pytest_configure(config: pytest.Config) -> None:
    latest = max(EVM_VERSIONS, key=EVM_VERSIONS.__getitem__)
    selected = config.getoption("evm_version")
    if selected != latest:
        raise pytest.UsageError(
            f"semantics EVM target {selected!r}, expected latest supported by VYPER_PIN: "
            f"{latest!r}; update tests/semantics-profile.json and regenerate exports"
        )


def original_code(code: bytes, code_hash: bytes) -> bytes:
    """Remove revm analysis padding using the account's original code hash."""
    for end in range(len(code), len(code.rstrip(b"\0")) - 1, -1):
        candidate = code[:end]
        if keccak(candidate) == code_hash:
            return candidate
    raise ValueError("revm bytecode does not match the account code hash")


@pytest.hookimpl(wrapper=True)
def pytest_fixture_setup(fixturedef: pytest.FixtureDef, request: pytest.FixtureRequest
                         ) -> Generator[None, Any, Any]:
    env = yield
    if fixturedef.argname != "env" or not isinstance(env, BaseEnv) or env.exporter is None:
        return env
    exporter = env.exporter
    # The module-scoped env keeps the deployer's nonce across tests, so a raw
    # fixture can be created at a nonce its own trace doesn't account for.
    # Record the nonce each deployment starts from; replay derives the CREATE
    # address from it.
    deploy = env._deploy
    deployer_nonce: int | None = None

    def nonce_recording_deploy(*args: Any, **kwargs: Any) -> str:
        nonlocal deployer_nonce
        deployer_nonce = env._evm.basic(env.deployer).nonce
        return deploy(*args, **kwargs)

    def trace_deployment(**kwargs: Any) -> None:
        nonlocal deployer_nonce
        if isinstance(env, RevmEnv) and kwargs["deployment_succeeded"]:
            account = env._evm.basic(kwargs["deployed_address"])
            # basic().code includes analysis padding; upstream get_code strips
            # every trailing zero, including real STOP/data bytes.
            kwargs["runtime_bytecode"] = original_code(account.code, account.code_hash).hex()
        if kwargs["deployment_type"] in RAW_DEPLOYMENT_TYPES:
            kwargs["deployer_nonce"] = deployer_nonce
        deployer_nonce = None
        TestExporter.trace_deployment(exporter, **kwargs)

    if isinstance(env, RevmEnv):
        env._deploy = nonce_recording_deploy
    exporter.trace_deployment = trace_deployment
    return env
