# Name-collision witnesses (#557)

These sources use identifiers that the HOL lowering used to keep in the same
`compile_env.ce_vars` table as compiler-internal entries. Each has an exact
bytecode comparison in `eval/evalCompilerNameCollisionsScript.sml`, included in
the default lowering rollup.

| Source | Fix | Checks |
|---|---|---|
| `nm_arg_return_pc` | a04-04 | an internal argument named `__return_pc__` is the user's value, not the return address |
| `nm_ext_arg_return_pc` | a04-04 | an external argument named `__return_pc__` keeps `return` on the external (ABI `RETURN`) path |

`oracle/` holds the annotated AST/layout JSON and deployment/runtime bytecode
from the pinned Python Vyper (`VYPER_PIN`), with the same settings as the
memory-store witnesses: experimental codegen, `-O none`, `evm_version=prague`,
no bytecode metadata. Run from `sources/` so recorded paths are bare file
names:

```sh
cd lowering/defs/bytecode/name-collisions/sources
vyper -f annotated_ast,layout NAME.vy > NAME.raw.json
python3 ../../../../../tests/sanitize_check_contract_json.py \
  NAME.raw.json ../oracle/NAME.json --replace "$PWD/="
vyper --experimental-codegen --evm-version prague -O none \
  --disable-bytecode-metadata -f bytecode,bytecode_runtime NAME.vy
```

The `.hex` file holds the two lines of that last command as `deploy=...` and
`runtime=...`, without `0x`.
