# Constant evaluation

The legacy JSON frontend consumes compiler-provided `folded_value` in several
places, including annotation bounds. `jsonConstASTLib` and `jsonConstEvalTheory`
provide a strict first-stage frontend for an integer fragment: they retain the
original bound expressions and evaluate constants before resolving types.
This is a first milestone for [#135](https://github.com/verifereum/vyper-hol/issues/135).

## Example

```vyper
N: constant(uint256) = 1 + 2

@external
@pure
def power(x: uint256, values: uint256[N]) -> uint256:
    return x ** N
```

The frontend produces an array parameter of length 3 and an exponent expression
`Literal (BaseT (UintT 256)) (IntL 3)`. The constant declaration retains its
elaborated addition initializer.

From a HOL script with `jsonConstEval` as an ancestor and
`vyperCheckContractFrontendLib` as a library:

```sml
val checked = vyperCheckContractFrontendLib.check_constant_contract_file
  {address = ``0w : address``, path = "constant_bound.json"};
```

The input is Vyper's `-f annotated_ast` output. The returned theorem certifies
`check_contract` success for the translated module. For translation alone,
decode with `jsonConstASTLib.annotated_ast` and evaluate
`translate_constant_module` on the resulting declaration list.

## Evaluation order

1. Decode source integer expressions and annotations into `jsonConstAST`.
   `CA_Array` contains a bound expression, not a folded number. The decoder never
   reads `folded_value` or inferred `type` fields.
2. Process declarations in order. Elaborate each constant's integer expression
   using its declared type and previously evaluated constants. Check literal
   ranges and evaluate the closed expression with `eval_pure_expr`. Before
   accepting a closed shift, check that its count lies in 0–256 and that a
   left shift's unwrapped result fits the result type. This prevents runtime
   wrapping from changing a source constant's value.
3. Evaluate array bounds in the same environment, require positive results,
   and construct the resolved parameter/result types. Elaborate function
   expressions with parameter types and literal constant substitutions.
4. Run the existing contract checker on the resulting module.

## Correctness

`eval_integer_constant_sound` proves that every successful evaluation agrees
with `eval_expr` in **any** runtime context and state, leaving that state
unchanged. Its proof establishes context independence for the supported closed
integer expressions, then uses `eval_pure_expr_to_eval_expr_some`.

`evaluate_constant_sound` applies this result to source-expression elaboration.
`evaluate_constant_literal_equivalent` proves equivalence of the elaborated
initializer and its replacement literal. `resolved_array_bound_sound` connects
each resolved array bound to a positive integer computed by runtime semantics.
These are local evaluation guarantees; they do not assert correctness of the
JSON decoder or a whole-program frontend transformation.

## Supported fragment

The decoder accepts non-public integer constants and external pure functions
with one return statement. Annotations support signed/unsigned integers of
width 8, 16, …, 256 and nested static arrays. Expressions support integer
literals, names, and integer
binary operators. Constant references must name an earlier declaration;
function expressions can additionally use parameters. Shift counts have their
own unsigned type, inferred from local operands when present, otherwise
`uint256`. For example, `x: int256` can be shifted by `n: uint8` or `n: uint256`;
`x >> (1 + n)` uses the type of `n` for the count expression.

Imports, other statements, calls, unary expressions, defaults, public getters,
and default nonreentrancy are rejected by the decoder. Unresolved names, duplicate
declarations/parameters, invalid widths, nonpositive bounds, and unsuccessful
arithmetic return `NONE` during formal translation. Arithmetic uses the existing
bounded runtime operations, so an overflowing intermediate result is rejected
even if a compiler's unbounded constant folder could simplify the full expression.
In particular, `uint256[((1 << 256) >> 255) + 1]` is rejected: the pinned compiler
resolves it to length 3, but runtime shifts would produce length 1. Supporting
that expression requires evaluation beyond this bounded fragment. Runtime
shifts with nonconstant operands retain their existing wrapping semantics.

The legacy `jsonASTLib` / `translate_annotated_ast` entry point is unchanged.
The strict entry point never falls back to it. Broader expression and module
support, range bounds, and the other legacy uses of folded metadata remain work
for #135.

## Validation

`jsonConstEvalWitnessTheory` imports a fixture produced at `VYPER_PIN`, checks the
exact array-bound/exponent translation, and proves contract-checker success.
It repeats decoding with folding/type metadata deleted and with invalid strings
in every such field, and requires identical source terms. It also checks failure
on arithmetic errors, unsupported expressions, invalid bounds, and invalid
constant dependencies. Two additional pinned fixtures check rejection of the
overflowing shift bound and acceptance of signed shifts with unsigned counts,
including a count expression and an array bound from a safe constant shift.
Those fixtures are also decoded with metadata removed and poisoned. Width
tests include nonmultiples of 8 and the supported endpoints.
The witness is a default build root.

The implementation introduces two datatypes (`const_annotation` and
`const_declaration`) and ten definitions: `closed_integer`,
`eval_integer_constant`, `integer_local_type`, `constant_shift_ok`,
`elaborate_integer`, `evaluate_constant`,
`resolve_constant_annotation`, `resolve_constant_args`,
`translate_constant_declarations`, and `translate_constant_module`.
There are no new axioms or cheats and no changes to existing theorem statements.
