# Constant evaluation

Vyper programs use values that must be known at compile time: array and string
bounds in type annotations, `range` bounds, tuple indices, the length of a
`msg.data` slice, `raw_call` flags and `max_outsize`, a `method_id` selector,
the `ensure_tuple`/`unwrap_tuple` flags of ABI calls, and constant exponents.
The compiler's annotated AST also records its own folded result at many nodes
(`folded_value`). Taking those results on trust would make every translated
program depend on an unverified folder. The frontend therefore computes each
of these values itself from the source expression, with the interpreter's own
operations, and never reads `folded_value`.

## Example

```vyper
N: constant(uint256) = 1 + 2

@external
@pure
def power(x: uint256, values: uint256[N]) -> uint256:
    return x ** N
```

`values` gets type `ArrayT (BaseT (UintT 256)) (Fixed 3)` and the return
expression becomes `Builtin _ (Bop Exp) [Name _ "x"; Literal _ (IntL 3)]`.

## The evaluator

`eval_constant` (`vyperConstEvalScript.sml`) computes the value of a closed
expression of the Vyper AST: a literal, `max_value`/`min_value` of an integer
type, or a builtin applied to closed expressions, where the builtin is a binary
operator other than `in`/`not in`, `not`, unary minus, or `method_id`. It
applies the interpreter's `evaluate_literal`, `evaluate_max_value`,
`evaluate_min_value` and `evaluate_builtin` directly, in an empty context. Any
other expression, a decimal, or an operation the interpreter rejects (division
by zero, overflow) has no value (`NONE`).

`eval_constant_sound` states that a computed value is what the interpreter
returns for the expression in any context and state, leaving the state
unchanged:

```
eval_constant e = SOME v ==> eval_expr cx e st = (INL (Value v), st)
```

So replacing such an expression by its value never changes what a program
does. `eval_constant` is translated to `cv_compute`, and `vyperConstEvalLib`
makes `EVAL` compute it with `cv_eval`, which is what makes `method_id`'s
Keccak hash fast enough to translate with; theories that translate contracts
load that library. Arithmetic is bounded, with the result type's wrapping where
the interpreter wraps (shifts).

Compile-time translation uses `pin_fold_expr` and its scalar projection
`pin_fold_value`. This folder preserves operations the pin does not fold,
including unsafe arithmetic and conversions. It also covers the pin's decimal,
modular-arithmetic and literal-selection operations. The separate
`eval_constant_sound` law remains about runtime-safe evaluation; it does not
justify replacing every expression the compiler folds at runtime.

## Translation

Constant evaluation happens on the translated expression, after `translate_expr`
has given every name and operator its meaning, so the evaluator sees exactly
what the interpreter would run.

1. Constants are evaluated in passes over every module, imported modules
   first (`annotated_constants`). Each pass evaluates the initializers not yet
   evaluated, using the constants evaluated so far, and records the value of
   each one that evaluates under its `(module, name)` key. Passes repeat until
   one evaluates nothing new, since a constant may refer to one declared after
   it. Initializers without a scalar folded value stay top-level names for the
   semantics to evaluate at runtime.
2. A reference to an evaluated constant, bare or through a module, translates
   to its value as a literal of the type the compiler gives the reference,
   which is the type its position expects (`top_level_ref`): with
   `B: constant(Bytes[5]) = b"abc"`, the reference `B` in
   `A: constant(Bytes[10]) = B` is a `Bytes[10]`.
3. Each compile-time position evaluates its translated expression: annotation
   bounds (`annotation_bound`), `range` counts (`get_iter_bound`), the
   endpoints of a `range` without `bound=` (`translate_iter`), keyword
   flags (`kwarg_bool`, `kwarg_num`, `kwarg_method_id`), the slice length,
   tuple indices and `method_id` (`fold_pin_constant`). Exponents use
   `pin_fold_expr`, which preserves operations the compiler does not fold,
   including unsafe arithmetic. Boolean operators fold their literal children
   before translation to conditional expressions.
4. A position whose value must be known at compile time but does not
   evaluate is rejected, never given a default: a declaration with such an
   annotation bound or `range` bound fails validation (`bound_resolved`,
   `iter_bound_resolved`), and a call with such a keyword or slice length
   translates to an expression the type checker rejects (`kwargs_checked`,
   `rejected_expr`). A `range` count defined by `uint256_addmod` and a closed
   Boolean flag such as `True or False` are folded and accepted.

The patched pin type-checks annotation sizes before exporting their annotated
ASTs. `T[expr]`, `Bytes[expr]`, `String[expr]` and `DynArray[T, expr]` therefore
use the same typed expression translation and bounded folder as other constant
positions. No separate mathematical annotation evaluator is used. The patch
rejects overflowing and incompatible intermediate expressions without changing
accepted sizes. HOL matches sizes in accepted compiler exports; it does not
duplicate the compiler's rejection pass over arbitrary JSON.

For legacy exports and imported functions the compiler leaves untyped,
`jsonASTLib.count_expr` still supplies `uint256` where a type is missing and
gives integer `max_value(T)`/`min_value(T)` their argument type. It preserves
types present in a patched annotation.
A module path
in them (`uint256[lib.N]`, `uint256[outer.inner.N + 1]`) is resolved through
the import maps of the modules it passes (`resolve_module_expr`). An
annotation that is present but does not decode fails the decoding; reading it
as absent would trust the compiler's inferred type. The one exception is an
interface stub's `String[...]` or `Bytes[...]`, which states no bound, so the
compiler's inferred type (unbounded) says no more than it does.

The original `.vy` source is not needed: the annotated AST keeps the original
expression under every node that also carries a `folded_value`.

## Validation

`vyperConstEvalWitnessTheory` (default build) translates the fixtures
`constant_bound`, `constant_shifts`, `constant_shift_bound`, `constant_refs`
(a forward reference and a module constant in a bound), `constant_nested`
(constants of an imported module's import in bounds), `constant_widened`
(a `Bytes[5]` constant referenced as a `Bytes[10]`), `constant_minmax_bound`
(`int8[max_value(int8)]` and a `min_value` constant), `constant_interface_stub`
(the builtin `IERC20Detailed` interface's `String[...]`), the two
`constant_unevaluated_*` fixtures, `constant_undecodable_bound` and
`constant_undecodable_import` (legacy names for now-typed `len(b"abc")`
annotations in the main or an imported module) from
`tests/fixtures/check_contract`. It decodes each one again with every
`folded_value` deleted, and again with every one replaced by junk, and requires
identical terms. The patch rejects the old overflowing shift annotation
`uint256[((1 << 256) >> 255) + 1]`; its accepted replacement uses shifts
255 and 254 and still has size 3. Compiler rejection regressions are carried
in the backport patch.

`constant_typed_sizes` covers all four sized annotation forms, narrow and
forward constants, decimal arithmetic, literal and named-container selection,
closed shifts, and a struct bound referring to a later imported constant.
Its witness checks each declared bound and successful contract checking.

`frontendConstantParityTheory` is an opt-in check, outside the default build
and run by its own CI job. Over every checked-in annotated-AST fixture, it
evaluates each non-literal node that has a `folded_value` and requires the
computed value to equal the compiler's. It reports how many nodes the
evaluator leaves alone, by kind (lists, tuples, comparisons). Every compared
value must match, with no exception list. Build it with

```sh
holbuild build frontendConstantParityTheory
```
