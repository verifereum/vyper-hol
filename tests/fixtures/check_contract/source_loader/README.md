# Pre-erasure source-loader fixtures

These captures are made by `tools/source_module_loader.py` at `VYPER_PIN`,
before `get_node`, without semantic analysis, expression translation or
constant folding. Source identities come from canonical keys and an explicit
inherited ID map, not potentially colliding parser IDs or diagnostic paths.

## Fixture provenance

Paths are relative to the repository root; parenthesized names are canonical
keys, in manifest order:

- `multimodule_storage.json`:
  `tests/fixtures/check_contract/multimodule_storage/main.vy` (`main`),
  `tests/fixtures/check_contract/multimodule_storage/lib.vy` (`lib`).
  `frontend/sourceModuleLoaderTestScript.sml` loads and elaborates it.
- `imported_interface.json`:
  `tests/fixtures/check_contract/imported_interface/main.vy` (`main`),
  `tests/fixtures/check_contract/imported_interface/oracle.vyi` (`oracle`).
- `imported_deploy.json`:
  `tests/fixtures/check_contract/imported_deploy/main.vy` (`main`),
  `tests/fixtures/check_contract/imported_deploy/lib.vy` (`lib`).
- `interface_struct_return.json`:
  `tests/fixtures/check_contract/source_loader/interface_struct_return/main.vy`
  (`main`),
  `tests/fixtures/check_contract/source_loader/interface_struct_return/manager.vyi`
  (`manager`).
- `interface_override.json`:
  `tests/fixtures/check_contract/source_loader/interface_override/main.vy`
  (`main`),
  `tests/fixtures/check_contract/source_loader/interface_override/oracle.vyi`
  (`oracle`),
  `tests/fixtures/check_contract/source_loader/interface_override/lib.vy`
  (`lib`).
- `nonreentrant.json`:
  `tests/fixtures/check_contract/source_loader/nonreentrant/main.vy` (`main`).

The struct-return declarations match the older `interface_struct_return/`
fixture, but these sources omit its obsolete `0.5.0a3` pragma. Bodies, defaults
and annotations are not reconstructed from annotated JSON; adapted acceptance
is not original-source acceptance.

`frontend/sourceModulePolicyTestScript.sml` checks the last five captures
through `Source.check_loaded_contract_result`, including exact runtime ASTs and
retained syntax. It rejects erased/misaligned policies, fabricated interface
bodies and invented nominal field names. Nonreentrancy uses the explicit
inherited transient lock entry `(NONE,"$.nonreentrant_key") -> 0`, checked
against pinned compiler layout output; source loading does not infer layout.

## Reproduction

Create a JSON manifest of `{ "key": [key], "path": source_path }` entries in the
order above. From the repository root, with a checkout of the pinned compiler
and a Python it supports:

```sh
PYTHONPATH=/path/to/pinned-vyper /path/to/venv/bin/python \
  tools/source_module_loader.py /path/to/manifest.json /path/to/capture.json
```

The loader checks the compiler revision and records the given source paths and
their hashes. Its capture protocol is a syntax/namespace trust boundary, not a
compiler acceptance oracle.
