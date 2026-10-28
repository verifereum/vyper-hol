# #551 ABI dispatch repair and remaining semantic blocker

Reference inspected: Vyper `cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c`,
`vyper/codegen_venom/builtins/abi.py`, `expr.py:lower_Name`,
`context.py:unwrap`, and `codegen/core.py:calculate_type_for_external_return`.

## Dispatch changes

- Evaluate **and unwrap** every argument left-to-right, before allocating the
  staging tuple. This is not `compile_make_tuple`, which interleaves child
  evaluation and stores.
- A single argument uses its own ABI type only with `ensure_tuple=False`;
  otherwise encode a tuple of **all** argument types. Stage primitive words
  with MSTORE and complex pointers with MCOPY, including ADD at offset zero.
- Decode uses `calculate_type_for_external_return`'s wrapping rule when
  `unwrap_tuple=True`: all types except tuples with more than one element are
  wrapped. Descriptor, ABI size bounds, and allocation use that wrapped type;
  the returned value retains the requested type (element zero has offset zero).
- Preserve selector-before-payload instruction order. Output Bytes allocation
  rounds the selector-plus-payload capacity to a word boundary.
- The raw checker additionally accepts fixed-byte decode inputs, unlike the
  pinned source builtin. Materialize their left-aligned word as a length/data
  buffer instead of treating the word as a memory address.

The checker and ABI whitelist are unchanged. No frontend-normalization premise
was introduced.

## Regressions

`lowering/abiBuiltinDispatchTestScript.sml` covers type selection, dynamic bounds,
formal runtime bytes, raw checker acceptance, arbitrary child-effect/unwrap
ordering, primitive/complex staging, selector allocation/order, fixed-byte
inputs, and decode dispatch's use of the flag. `tests/fixtures/abi_dispatch.vy`
is accepted by the pinned compiler with experimental codegen and no optimization.

`lowering/abiAliasRegressionScript.sml` and `tests/fixtures/abi_alias.vy` retain
the following blocker independently of any JSON frontend:

```vyper
@external
def alias() -> Bytes[160]:
    a: DynArray[bool, 2] = [True, False]
    return abi_encode(a, a.pop(), ensure_tuple=False)
```

The raw checker admits the corresponding Name/Pop argument AST. The interpreter
materialises arguments before evaluating the next child (`eval_exprs`), so its
argument values are `([True, False], False)`. Pinned Vyper accepts the source,
but returns ABI encoding of `([True], False)`: its first argument is a memory
pointer, and staging copies it only after the pop changes the length. This was
confirmed by executing its runtime bytecode in py-evm 0.12.1b1 PragueVM (not merely
by comparing source IR). Local receipts: `.agent-files/stage6-abi-alias.log` and
`.agent-files/stage6-abi-alias-execution.log`.

Thus the repaired pinned staging is **not** an unrestricted raw-AST simulation
proof. Removing the ABI whitelist is unsafe. Resolving the witness requires an
explicit semantic decision: snapshot complex arguments before later effects
(departing from the pin), or change the interpreter's argument meaning and prove
that change, or establish a genuine language-domain alias/effect rule in both
source acceptance and the raw checker. A blanket implementation restriction or
an assumed frontend invariant does not resolve it.

## Proof boundary

The existing instruction-monotonicity and lowering-shape arguments are updated;
these establish generated-code shape, not ABI semantic equivalence. Existing
`exprLoweringPropsScript.sml` admissions (`compile_expr_correct`,
`compile_binop_correct`, `compile_neg_correct`) are outside this ABI-only task
and must not be mistaken for verified simulation evidence. No new admissions
are introduced by this repair.

## Validation receipts

Using `.agent-files/.holbuild-toolchain/bin/holbuild`:

- Forced rebuild of `abiBuiltinDispatchTestScript.sml` and
  `abiAliasRegressionScript.sml`: passes, 26.591s, no CHEAT warnings.
- `builtinAbi`, `exprLowering`, `exprLoweringProps`, and `loweringShapeProps`:
  build/recheck passes. The cold dependency rebuild was long; final cached
  recheck was 0.212s. New ABI shape obligations are proved, not admitted.
- All five reference fixture functions execute successfully in pinned Vyper's
  bytecode under PragueVM, with expected multi-argument and wrapped/unwrapped
  bytes. Receipt: `.agent-files/stage6-abi-reference-execution.log`.
- The alias witness executes successfully but returns the conflicting result
  recorded above; it is a blocker, not a passing semantic-parity test.

Build logs: `.agent-files/stage6-abi-final-tests.log`,
`.agent-files/stage6-abi-final-shape.log`, and
`.agent-files/stage6-abi-shape.log`. This is scoped validation, not a full
project build or an unrestricted ABI correctness certificate.
