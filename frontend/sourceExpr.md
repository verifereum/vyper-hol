# Recursive source expression elaboration

`sourceExprDefs`, `sourceExprElaborate` and `sourceExprProps` implement the
source-preserving expression path. This API never calls the old JSON translator,
reads folded metadata, or retries a failed expression through the legacy frontend.
See [constant evaluation](constant-evaluation.md) for pipeline and trust boundaries.

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
  source-derived function/interface signatures. Runtime bindings preserve local
  `Name`, storage or immutable `TopLevelName`, and environment `Builtin`
  distinctions; correctness of these independently supplied bindings is not
  inferred from typing.
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
  `skip_contract_check` constants and typed external-call keywords. This
  call path shares signature/context infrastructure with the ordinary frontend;
  independent full-Source body tests are extracted with that optional feature.

`source_expr_flag`, `source_expr_index`, and `source_expr_range_bound` share
original resolution/evaluation evidence. Indices check the supplied count;
range bounds require `0 < n < 2^256`. Present invalid/dynamic flags never become
defaults. These helpers are not complete statement/range elaborators.

## Theorem contracts and limits

`sourceExprProps` proves runtime typing, original constant/operator validation,
required-constant provenance and local constant replacement with represented
values and unchanged states. It does not prove a universal structural
source-to-runtime simulation. Independent staged program/call/location Meaning
relations are not included in this base; no claim that every accepted expression
has an independent semantic derivation is made here.

This is a contextual fragment, not a complete source typer. Mixed-sign
comparisons, context-polymorphic negative boundaries, structs, many builtin/call
forms and general inference remain incomplete. Wide executable intermediates
such as `(1 << 256) >> 255` are rejected by the pin and this API; the same
arithmetic can be accepted in a mathematical annotation bound. Unsupported is
not a claim of language rejection, and no compiler replacement is a fallback.

Expression AST/typing witnesses are not whole-program parity certificates.
[Shared module signatures](sourceModule.md) and ordinary folding consume this
API; retained-source/checking/backend equations have separate contracts.
No supported-program restriction is removed here.

## Regressions

[sourceExprWitnessDefsScript.sml](sourceExprWitnessDefsScript.sml) holds original
expression inputs; [sourceExprTestScript.sml](sourceExprTestScript.sml) proves their
exact body/initializer outcomes with `source_expr_all_retained_witness_bodies`.
Regressions include rejection of dynamic `method_id` inputs, constructor
assignments, tuple initializers, environment reads, ABI invalid-present flags,
resolved aliases/shadowing, storage argument order and dynamic array indices.
Power witnesses retain literal exponent 3 for `x ** (1 + 2)` and literal base
-2 for `(0 - 2) ** y`.
