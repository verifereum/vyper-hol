"""Preserve exact revm runtime bytes in upstream deployment exports."""

from __future__ import annotations

from collections.abc import Generator
from typing import Any

import pytest
from eth_hash.auto import keccak
from tests.evm_backends.base_env import BaseEnv
from tests.evm_backends.revm_env import RevmEnv
from tests.exports import TestExporter


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

    def trace_deployment(**kwargs: Any) -> None:
        if isinstance(env, RevmEnv) and kwargs["deployment_succeeded"]:
            account = env._evm.basic(kwargs["deployed_address"])
            # basic().code includes analysis padding; upstream get_code strips
            # every trailing zero, including real STOP/data bytes.
            kwargs["runtime_bytecode"] = original_code(account.code, account.code_hash).hex()
        TestExporter.trace_deployment(exporter, **kwargs)

    exporter.trace_deployment = trace_deployment
    return env
