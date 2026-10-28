# Opt-in recursive source expression elaboration

`sourceExprDefs`, `sourceExprElaborate` and `sourceExprProps` implement the
source-preserving expression path. `sourceExprWitnessDefs` holds the 37 retained
expression inputs; `sourceExprTest` checks their exact outcomes and additional
boundary cases. This API never calls the old JSON translator, reads folded
metadata, or retries a failed expression through the legacy frontend.

## API and validation

`source_expr_elaborate fuel env scopes declarations constants bindings ty e`
returns `SC_Value runtime_expr`, `SC_Invalid error`, or `SC_Unsupported reason`.
The shared result datatype also contains `SC_NotConstant`; required constant
consumers reject it. Fuel exhaustion is explicit Unsupported.

* `e` is original `sourceSyntax` syntax, with operators, operands and keywords.
* `sourceResolve` resolves declaration/callee identities. A shadowed builtin
  spelling does not acquire builtin behavior.
* `constants` is an independently constructed resolved constant environment.
  `bindings` maps resolved identities to runtime code, types, intrinsics and
  source-derived function/interface signatures. Runtime bindings preserve local `Name`, storage or
  immutable `TopLevelName`, and environment `Builtin` distinctions; correctness
  of these independently supplied bindings is not inferred from typing.
* `env` is the runtime typing environment; `ty` is a contextual expected type.
  `source_expr_annotated` obtains it through `source_type_resolve`, rejecting
  qualifiers and HashMap value types in expression positions.

Every successful public result has `expr_type result = ty` and
`well_typed_expr env result`, with **no readiness/checker-success premise**.
Original constant trees are validated by `source_expr_original` before
reification, not by constructing a runtime AST for every mathematical child.
Executable children remain range/type bounded; annotation bounds (including
`method_id` output bounds) use mathematical source arithmetic. Integer `/`,
unsigned negation except zero, narrow shifts, inappropriate literal classes,
and illegal builtin operands cannot disappear just because a final value fits.
Errors are eager even below False Boolean heads or beside dynamic operands.

## Implemented recursive fragment

* Scalar literals, resolved constants and dynamic names/module paths; unary and
  binary operators, nonmembership comparisons and conditional expressions.
* Boolean chains with at least two operands. Short-circuit runtime `IfExp`
  nodes retain order; the singleton recursion tail is the operand itself,
  **not** `IfExp e True False`. Thus `fold_not` emits `IfExp x False False`,
  and `boolop_and3` emits `IfExp (IfExp a b False) True c`. Singleton/pair
  equations are proved in `sourceExprProps`; no operand is duplicated.
* Lists and tuples with contextual element types; subscripts with inferred
  receiver types. Tuple indices must be original constants and in bounds;
  ordinary array indices may remain dynamic.
* Len/Keccak256/Abs/Min/Max/PowMod256/AddMod/MulMod; constant-only `method_id`
  with original string and resolved `output_type` validation.
* Resolved `SE_AbiEncode`/`SE_AbiDecode` intrinsics, original constant
  `ensure_tuple`/`unwrap_tuple` flags, four-byte `method_id` prefixes, duplicate
  and unknown keyword rejection, and independently resolved decode type operands.
  Tuple operands are not flattened and argument order is preserved.
* The currently supported no-keyword `raw_call(target,data)` (zero output,
  nondelegate, nonstatic, revert-on-failure, zero value) and `raw_revert(data)`.
  This is not general raw-call keyword coverage.
* `sourceExprCall` additionally constructs internal calls and interface-based
  external/static calls from resolved source signatures, including original
  `skip_contract_check` constants and typed external-call keywords. This newer
  call path is not covered by the 37-expression inventory below.

`source_expr_flag`, `source_expr_index`, and `source_expr_range_bound` share
original resolution/evaluation evidence. Indices check the supplied count;
range bounds require `0 < n < 2^256`. Present invalid/dynamic flags never become
defaults. These helpers are not complete statement/range elaborators.

## Exact retained coverage and limits

`source_expr_all_retained_witness_bodies` proves exact original-body/initializer
outcomes for **all 37** retained #543 witnesses, with a separate exact name
inventory theorem. **36 succeed**; `method_id_var` returns the intended domain
error, matching the authoritative pin
`cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c`. Additional theorems cover constructor
assignments, tuple initializers, environment reads, ABI invalid-present flags,
resolved aliases/shadowing, storage argument order, and dynamic array indices.
Power witnesses retain literal exponent 3 for `x ** (1 + 2)` and literal base
-2 for `(0 - 2) ** y`.

This is a contextual fragment, not a complete source typer. Mixed-sign
comparisons, context-polymorphic negative boundaries, structs, many builtin/call
forms and general inference remain incomplete. Wide executable intermediates
such as `(1 << 256) >> 255` are rejected by the pin and this API; the same
arithmetic can be accepted in a mathematical annotation bound. Unsupported is
not a claim of language rejection, and no compiler replacement is a fallback.

Expression AST/typing witnesses are not whole-program parity certificates.
The separate opt-in `sourceModule` path now consumes this API; ordinary public
frontend integration is **not** claimed complete. See
[the source-module results](../docs/SOURCE_MODULE_PARITY_RESULTS.md) for actual
whole-program checks, byte comparisons and remaining backend failures.

`sourceExprProps` proves runtime typing, original constant/operator validation,
required-constant provenance and local constant replacement with represented
values and unchanged states. It does not prove a universal structural
source-to-runtime simulation. [sourceMeaning](sourceMeaning.md) supplies an
independent staged semantic bridge for a smaller fragment (not dynamic Boolean
chains, ABI encode/decode, or general calls). Declaration/type/environment
transport, effects and module/compiler composition are separate obligations;
no supported-program restriction is removed here.

## Validation

From the repository root:

```sh
.agent-files/.holbuild-toolchain/bin/holbuild sourceExprTestTheory \
  sourceMeaningTestTheory --tactic-timeout 2.5 --allow-cache-timeout-discrepancy
```

The final expression kernel audit covers the expression implementation,
call-construction dependency and split test theories, rejecting open
hypotheses, axioms and non-`DISK_THM` oracle tags. The new witness-input theory
keeps each expression source file at approximately 500 lines or fewer.
Cache timeout discrepancy is for unchanged dependencies; changed proofs are
checked freshly at 2.5 seconds. Whole-module byte probes are separate tests,
not a consequence of the expression audit.
