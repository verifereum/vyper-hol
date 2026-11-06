# Internal-call default arguments

Each source calls an internal function and leaves out one or more of its
keyword arguments. Python Vyper's `_lower_internal_call` appends the omitted
parameters' default expressions to the supplied arguments, compiles them in
the caller after the supplied ones, and stages them like any other argument.
The HOL lowering does the same (`omitted_defaults` in `compile_call`).

| Source | What it checks |
|---|---|
| `d01_int_default_word` | one word default, omitted and supplied |
| `d02_int_default_partial` | two defaults: both omitted, and only the last |
| `d03_int_default_env` | defaults reading `msg.sender` and `block.timestamp + 1` |
| `d04_int_default_string` | a memory-passed `String` default |

`parity-fixtures.txt` selects all four; each has an exact deployment and
runtime bytecode comparison in `eval/evalCompilerInternalDefaultsScript.sml`,
included in `evalCompilerWitnesses`.

`oracle/` holds the annotated AST/layout JSON and the deployment/runtime
bytecode from the pinned Python Vyper (`VYPER_PIN`) and its provenance. With
the canonical oracle environment described in the parent README first on
`PATH`, from the repository root:

```sh
python lowering/defs/bytecode/memory_store_witnesses.py prepare \
  --corpus internal-defaults --fixtures /tmp/internal-defaults-oracle --check
holbuild -j4 build evalCompilerInternalDefaultsTheory
```
