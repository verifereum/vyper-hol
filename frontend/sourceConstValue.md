# Local typed source-value / runtime bridge

`sourceConstValueTheory`, `sourceConstValuePropsTheory`, and
`sourceConstValueTestTheory` are opt-in. Their regression/audit theories are
registered as build roots. No public frontend, checker, lowering rule or ABI
whitelist is changed by this local bridge.

## Interface

`source_const_reify tenv ty sv : expr option` takes a mathematical
`source_const_value` and an **explicit expected runtime type**. It does not
infer a source type. Success produces `Literal ty lit` only after checking
both `well_formed_type tenv ty` and `well_typed_literal ty lit`.

Supported values:

- `SCV_Int`: mathematical integer, checked against the expected signed or
  unsigned width. There is no wrapping, truncation, or implicit bool conversion.
- `SCV_Bool`: runtime Boolean literal.
- `SCV_Decimal`: the already-scaled coefficient, unchanged (scale `10^10`),
  checked against `decimal_bound`. There is no host floating-point conversion
  or second scaling step.
- `SCV_String`: ASCII validation, then the runtime string length check.
- `SCV_Bytes`: validate every natural octet is below 256 **before** `n2w`,
  then apply the runtime byte bound check.
- `SCV_Hex`: validate the existing source hexadecimal token predicate, decode
  pairs of digits preserving leading zeroes, then apply the byte bound check.
  Hex and Bytes remain distinct source constructors but may represent the same
  runtime byte value. Mixed-case hex tokens are decoded numerically.

The runtime literal checker admits byte literals at fixed bytes, dynamic
bytes, and Address (exactly 20 bytes). The bridge follows that checker; it does
not claim that the original source notation is legal for every such target.
Type well-formedness is a separate, essential check: for example, the literal
range check accepts zero at `uint0`, but the bridge rejects that type.

`SCV_BytesType` is a **type descriptor**, not data: reification always returns
`NONE` and the representation relation is false, independently of its bound.

Aggregates (`SCV_List`, `SCV_Tuple`, `SCV_Struct`) are explicitly rejected in
this primitive bridge. They are not encoded as opaque byte literals or erased
to an untyped payload. The separate structured API below supplies structured
`MakeArray` / `StructLit` expressions and recursive certificates. No nominal
correspondence is guessed from spelling.

## Certificates

`source_const_represents sv v` is independent of elaboration: it relates
source constructors directly to `IntV`, `BoolV`, `DecimalV`, `StringV`, and
`BytesV`, with source payload validation. It is not defined by successful
`source_const_reify` output. Representation is single-valued.

`source_const_reify_correct` proves that successful reification gives:

1. an expression with exactly the requested type, satisfying
   `well_typed_expr env e`;
2. an evaluated runtime type and a value satisfying `value_has_type`;
3. the independent `source_const_represents` relation;
4. `eval_expr cx e st = (INL (Value v), st)` for **every** context and state.

Runtime value typing uses the existing `well_typed_literal_sound` theorem.
The state equality covers the entire evaluation state, not just storage or
locals. No well-formed-state or context/environment agreement assumption is
needed because literal evaluation reads neither context nor state.
`source_const_reify_iff` states the exact executable success condition.

## Structured API (separate namespace)

`sourceConstValueStructured$source_const_reify nominal tenv ty sv` supports
primitive values, homogeneous `SCV_List` arrays, heterogeneous `SCV_Tuple`
values, and `SCV_Struct` values, recursively. The original three-argument
`sourceConstValue$source_const_reify` and its context-free theorem API remain
unchanged for `sourceExpr`. `source_const_reify_primitive_agrees` proves that
primitive success also succeeds in the structured API; the original stronger
soundness theorem is re-exported as `source_const_reify_primitive_sound`.

The structured bridge checks source-value validity, expected-type
well-formedness, exact tuple arity, child types/ranges, and fixed/dynamic array
bounds. Fixed-array bounds concern **logical source length**, not the number
of non-default entries in `SArrayV`. Thus three zero elements can produce an
empty sparse entry list while still having logical length three.

`nominal : (string list, nsid) fmap` is the actual path-to-identity map supplied
by resolution. Struct success requires a map lookup equal to the expected
`StructT` identity, the corresponding `StructArgs` in `tenv`, and exactly the
declared field names/order. It never synthesizes an identity from spelling.

`source_const_structured_represents nominal sv v` is an independent recursive
relation over runtime constructors, child representations, and logical array
bounds; it does not mention reification or evaluation of generated syntax.
Unlike primitive representation, it is intentionally not single-valued: the
same source list can represent a fixed sparse or a dynamic array.

`sourceConstValueStructuredProps$source_const_reify_correct` proves static
expression typing, evaluated runtime value typing, independent representation,
and whole-state-preserving evaluation. Its runtime clause explicitly requires
`get_tenv cx = env.type_defs`; arrays consult that context when evaluating
their element type. No runtime state invariant is assumed. The corresponding
`source_const_reify_sound` theorem accepts a standalone `tenv` and explicitly
requires `get_tenv cx = tenv`.

These theories remain opt-in and do not extend source-expression acceptance.
The structured regression theory is imported by the existing value-test root;
it also audits all new exported definitions/theorems for hypotheses, axioms,
and non-kernel oracle tags.

## Exact scope / non-claims

This is a theorem about an already-computed mathematical source **value** and
an independently supplied runtime type. It is **not** a theorem that the
original source expression is legal, well typed, compiler accepted, or
semantically equivalent to the literal in every context. Original expression
syntax, provenance, decimal-token precision, address checksum rules, operator
legality, and context-sensitive source conversion rules are not recovered
from a value. Successful source constant evaluation alone is not a source
legality certificate; successful reification does not change that boundary.

There is no compiler/Venom simulation theorem here. In particular the ABI
alias/effect blocker in `docs/ISSUE_551_ABI_DISPATCH.md` remains unchanged.
These theories do not remove a whitelist or introduce an assumed frontend
invariant to bypass it.

## Validation

From the project root:

```sh
.agent-files/.holbuild-toolchain/bin/holbuild frontend/sourceConstValueTestScript.sml
```

The test theory imports both definitions and proofs. Kernel computation tests
cover all six primitive constructors, signed/unsigned/decimal endpoints,
ill-formed widths, type mismatch, ASCII rejection, byte/octet and length
bounds, leading-zero and mixed-case hex decoding, malformed hex, Address
length, descriptor rejection, aggregate rejection, and unchanged-state
literal execution. The imported `sourceConstValueStructuredTestTheory` adds
nested tuple/array construction, sparse logical length, bound/arity/child
rejection, resolved nominal aliases and module identity, field order,
duplicate fields, and missing definitions. These are local bridge regressions,
not source-acceptance or ABI parity tests.
