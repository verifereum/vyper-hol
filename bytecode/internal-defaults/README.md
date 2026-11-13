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
| `d05_int_default_nested` | an omitted-default call inside another one's arguments |

`parity-fixtures.txt` selects all five; the native parity runner
(`../native/`) compares each one's deployment and runtime bytecode exactly.

`oracle/` holds the annotated AST/layout JSON and the deployment/runtime
bytecode from the pinned Python Vyper (`VYPER_PIN`) and its provenance. With
the canonical oracle environment described in the parent README first on
`PATH`, from the repository root:

```sh
python bytecode/memory_store_witnesses.py prepare \
  --corpus internal-defaults --fixtures /tmp/internal-defaults-oracle --check
```

`d05_int_default_nested` declares its functions in the order pinned Python
emits them: with the order swapped, the HOL bytecode also differs when every
argument is supplied, since HOL lays internal functions out in source order.
