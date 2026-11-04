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
