# Pre-erasure source-loader fixtures

These policy regressions are captured by `tools/source_module_loader.py` at
`VYPER_PIN`, before `get_node`, without semantic analysis, expression translation
or constant folding. Source identities come from canonical keys and an explicit
inherited ID map, not potentially colliding parser IDs or diagnostic paths.

## Fixture provenance

Paths below are relative to this directory; parenthesized names are canonical
keys, in manifest order:

- `imported_interface.json`: `../imported_interface/main.vy` (`main`),
  `../imported_interface/oracle.vyi` (`oracle`).
- `imported_deploy.json`: `../imported_deploy/main.vy` (`main`),
  `../imported_deploy/lib.vy` (`lib`).
- `interface_struct_return.json`: `interface_struct_return/main.vy` (`main`),
  `interface_struct_return/manager.vyi` (`manager`).
- `interface_override.json`: `interface_override/main.vy` (`main`),
  `interface_override/oracle.vyi` (`oracle`),
  `interface_override/lib.vy` (`lib`).
- `nonreentrant.json`: `nonreentrant/main.vy` (`main`).

The struct-return declarations match the older `../interface_struct_return/`
fixture, but these explicitly supplied sources omit its obsolete `0.5.0a3`
pragma for the a4 pin. Bodies, defaults and annotations are not reconstructed
from annotated JSON; adapted acceptance is not original-source acceptance.

`frontend/sourceModulePolicyTestScript.sml` checks these captures through
`Source.check_loaded_contract_result`, including exact runtime ASTs and retained
syntax. It rejects erased/misaligned policies, fabricated interface bodies and
invented nominal field names. Nonreentrancy uses the explicit inherited
transient lock entry `(NONE,"$.nonreentrant_key") -> 0`, checked against pinned
compiler layout output; source loading does not infer layout.

## Reproduction

Create a JSON manifest of `{ "key": [key], "path": source_path }` entries in the
order above. Paths must resolve from the invocation directory. From the
repository root, use the pinned checkout and its supported Python:

```sh
PYTHONPATH=/path/to/pinned-vyper /path/to/venv/bin/python \
  tools/source_module_loader.py /path/to/manifest.json /path/to/capture.json
holbuild build sourceModulePolicyTestTheory --tactic-timeout 2.5
```

The loader checks the compiler revision and records source hashes. Its capture
protocol is a syntax/namespace trust boundary, not a compiler acceptance oracle.
