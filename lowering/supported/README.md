# Supported-subset whitelist (TASK_019/020/021)

Progress: **TASK_019, TASK_020 and TASK_021 complete**. Implements all
PLAN §5.6 type, declaration, name, expression, statement and function-body
rows. `supportedProgramTheory` assembles the total computable predicate
`supported_program tops`. This is a syntactic boundary, not source typing
(PLAN D10), a compiler/evaluator change, or a correctness theorem.
The 101 individual fixture membership proofs remain TASK_022.

## Exported API

### `supportedTypesTheory`

- `supported_int_width`: 8, 16, …, 256; `supported_integer_type`.
- `supported_word_type`: those integers, bool, decimal, address, and fixed bytes
  1–32 **excluding bytes20**.
- `supported_full_word_type`: uint256, int256, bytes32 only.
- `supported_string_type`: String[n], Bytes[n] (dynamic bytes).
- `supported_scalar_type`: word or string; `supported_tuple_type`: nonempty,
  shallow tuple of these scalar types.
- `supported_value_type tops`: scalar, nonempty shallow tuple, word-element
  fixed array of positive length, word-element dynamic array, or main-module
  declared struct with word fields.
- `supported_storage_type tops`: full word, full-word-element arrays (fixed
  length positive), or main-module declared struct with full-word fields.
- `supported_hashmap_key_type`: supported integers, bool, address.
- `supported_return_type tops`: NoneT or a value type.
- `supported_main_nsid`; `supported_struct_fields tops id` (first type declaration
  wins, and a matching interface/flag blocks a later struct).

No unlisted nested tuple/array/struct depth is admitted. Zero string/dynamic-array
bounds are not excluded by this whitelist; typing and allocation are separate.

### `supportedDeclsTheory`

- `supported_declaration_header tops top`, `supported_declaration_headers tops`:
  function flags false, no defaults, value arguments and NoneT/value return;
  private explicitly slotted storage of storage types; private explicitly slotted
  transient full words; private non-transient non-nested maps with permitted
  keys and full-word values; value-typed struct/interface fields; word/string
  event fields (thus no indexed aggregates or bytes20); no flags, constants,
  immutables, public storage, or missing slots.
- `supported_interface_signature tops (name,args,ret,mut)` checks types only.
- `supported_variable_decl tops id`: option of `(visibility,mutability,type,slot)`.
- `supported_hashmap_decl tops id`: option of `(visibility,transient,key,value,slot)`.
- `supported_function_decl tops id visibility`: option of
  `(mutability,nonreentrant,raw_return,args,defaults,return_type,body)`.
- `supported_event_fields tops id`: option of declared `(argument,indexed)` list.

These are **raw syntactic lookups**, not admission predicates: inspect their
results and combine them with the declaration/type checks. All namespace-bearing
lookups reject `SOME module_id`, including `SOME 0`.

`FunctionDecl` header checks deliberately ignore the body, as their name and
`supported_header_body_independent` contract state. There is no body predicate
or placeholder. A header theorem is not a program/body acceptance theorem.

### `supportedNamesTheory`

- `supported_module_names`, `supported_function_names`, `supported_event_names`
  collect only the corresponding top-level names.
- `supported_internal_name`: excludes `revert`, `code_end`, and the prefixes
  `return_label_`, `reachable_` (uses forward `isPREFIX`).
- **`supported_function_bindings tops args locals loops`**: ALL_DISTINCT
  on `MAP FST args ++ locals ++ loops`. Locals may shadow module variables
  (`compile_env` keys those as `"self." ++ name`) and may use the names
  `__return_buf__`/`__return_pc__` (dedicated `ce_return_*` fields). TASK_021 must supply
  **all** AnnAssign and For names across all branches/nesting, as lists rather
  than deduplicated sets. This rejects duplicates within and across each class.
- `supported_function_header_names tops top`: argument-name checks, internal
  label restrictions, no-argument `__default__`.
- `supported_struct_field_names tops top`: no field/module-variable/map collision.
- `supported_selectors_distinct tops`: uses **the actual compiler**
  `build_selectors (type_env tops) (FST (classify_functions tops))`; excludes
  fallback, Internal, Deploy; does not approximate selector uniqueness by names.
- `supported_declaration_names tops`: distinct function/event names plus the
  header, field-collision, and selector checks. It does not inspect locals/loops:
  TASK_021 must additionally call `supported_function_bindings` on its collected
  names and enforce the internal-function/loop body restrictions.

## Permanent contracts and validation

Each foundation exports symbolic boundary contracts. `supportedTypeProps`,
`supportedDeclProps`, and `supportedNameProps` provide plain-EVAL positive and
negative examples covering every assigned table row, declaration/namespace
resolution order, repeated/cross-class bindings, reserved labels/locals,
struct-field/module collisions, duplicate function/event names, and fallback
arguments. The general selector-pair contract checks actual selector equality,
including differently named functions; a repeated-selector rejection is proved
without spending time recomputing identical Keccak hashes. Predicates are all
computable by plain EVAL; two full hash evaluations can exceed the 10s tactic
limit, so the symbolic pair contract avoids that unnecessary test cost.

Build from the worktree root:

```sh
timeout 120s holbuild --max-heap 16384 -j1 --tactic-timeout 10 \
  supportedTypePropsTheory supportedDeclPropsTheory supportedNamePropsTheory
```

For an individual target use `timeout 30s` with the same flags (initial dependency
loading is infrastructure and can use 120s). These additive theories and their
contracts contain no cheats or axioms. Existing proofs/definitions are untouched;
cheat delta is zero.

## Expression API (TASK_020)

### `supportedExprFormsTheory`

- `supported_binop op operand_type rhs_type literal_base nonnegative_exponent`
  is the exact operator table. Comparison restrictions use the **operand** type,
  not their bool result. TASK_021 can reuse it for AugAssign with literal_base=F.
- `supported_unsigned_type`, `supported_signed_type`,
  `supported_fixed_bytes_type`, `supported_numeric_type`,
  `supported_short_bytes_type`, `supported_integer_literal`,
  `supported_nonnegative_literal`; widths/bytes20 reuse the foundation limits.
- `supported_conversion src dst` is the directed conversion whitelist, not the
  source type system's broader conversion relation. Signed decimal inputs must
  have N <= 134 (thus the largest supported byte-aligned width is 128).
- `supported_builtin_form tops ty builtin args` and
  `supported_type_builtin_form ty builtin target args` encode exact forms and
  arities, including the ABI flags/method-id/single-argument restrictions.
- `supported_storage_scalar tops id ty`, `supported_storage_array tops id`,
  `supported_storage_dynamic_array tops id`, `supported_subscript_base tops id`,
  `supported_storage_fields tops id`, `supported_storage_field_read tops id field`.
  These inspect TASK_019 lookups; require private slotted admitted storage/map
  declarations, reject modules, and distinguish aggregate places from values.
  Storage-field **reads** require the first field; TASK_021 can use the exported
  field list for arbitrary-field writes.
- `supported_external_return_type tops ty`: any `supported_value_type tops ty`
  (W, strings/bytes, tuples of scalars, arrays of W, word structs); no NoneT.

### `supportedExprsTheory`

- `supported_pure_expr tops e` (P), `supported_pure_exprs tops es`,
  `supported_pure_fields tops fields`: structural recursion, with every AST
  constructor explicit. Calls/Pop are never P. Aggregate storage bases of
  Subscript/Attribute are specially checked places, not standalone P values.
- `supported_effect_expr tops e` (E): only root IntCall, ExtCall, Send, or Pop.
  All call arguments, including external target/value, must be P. Internal
  lookup requires Internal/NONE. ExtCall requires exact count, W arguments and
  a supported value return. No declaration is consulted: the selector is
  hashed from the call-site signature, as the source semantics does
  ([#555](https://github.com/verifereum/vyper-hol/issues/555)).
  Keyword operands (`value=`, `gas=`, `default_return_value=`) follow the
  positional arguments in source order, each kind at most once, and no
  `value=` on a staticcall. They are pure like every other operand, and both
  the lowering and the semantics evaluate them before the call.
- `supported_expr tops e`: P or E, for later statement expression positions.
  No statement or whole-program placeholder is provided.
- Symbolic contracts: pure Call/Pop rejection, external-call inversion,
  rejection of every call with a `default` field, and
  list/field EVERY equivalences.

### `supportedExprTraverseTheory`

- `supported_expr_exists p e` is a reusable occurrence traversal, with exported
  target/list/option/named-field variants `supported_target_exists`,
  `supported_exprs_exists`, `supported_opt_exists`, `supported_fields_exists`.
  It traverses **unsupported syntax too**, including default returns, nested
  assignment-target indices, both subscript operands and all conditional arms.
- `expr_has_effect` detects Call/Pop occurrence; `expr_has_internal_call` and
  `target_has_internal_call` detect IntCall occurrence.
- `expr_has_dynamic_decode tops e`, `target_has_dynamic_decode tops target`
  detect any AbiDecode target with dynamic ABI encoding, independently of
  whitelist/unwrap flags. They reuse `vyper_is_dynamic (type_env tops)` rather
  than implementing another ABI type evaluator; this supports PLAN D9.
- Contracts prove occurrence monotonicity/root inclusion, list/field EXISTS
  equivalences, P has no effects/internal calls, internal calls are effects,
  E has an effect, and `supported_expr /\ expr_has_effect <=> E`.

## Permanent expression table coverage

Proof paths: `lowering/supported/supportedExprFormPropsScript.sml` (F below)
 and `lowering/supported/supportedExprPropsScript.sml` (X below). All concrete
 coverage theorems use **plain EVAL_TAC**; standard `intLib` installs integer
 reductions for literal exponent checks. They require no custom evaluation
 library, axioms, assumptions, or cheats.

| PLAN §5.6 row/exclusion | Permanent coverage theorem(s) |
|---|---|
| Name, Literal, TopLevelName, IfExp, StructLit, tuple construction, Subscript, Attribute | X `supported_pure_expression_rows`, `supported_storage_base_exclusions`, `supported_bad_storage_declarations_excluded` |
| Every Bop constructor, integer/decimal/word restrictions | F `supported_arithmetic_operator_coverage`, `supported_bitwise_comparison_operator_coverage`, `supported_power_shift_counterexamples` |
| Not, Neg, Abs, AsWeiValue, AddMod, MulMod, PowMod256 | F `supported_unary_modular_builtin_coverage` |
| Every Env/Acc item; BlockHash, BlobHash, ECRecover, ECAdd, ECMul | F `supported_environment_crypto_builtin_coverage` |
| Empty, MaxValue, MinValue, Epsilon, Extract32 exclusion | F `supported_type_builtin_coverage` |
| Every admitted conversion family; out-of-list, width, bytes20, N>=135 exclusions | F `supported_conversion_whitelist_coverage`, `supported_conversion_exclusion_coverage` |
| ABI encode/decode exact flags, method-id size, tuple depth/length, arity | F `supported_abi_forms_coverage` |
| Len, hashes, Concat, Slice, Uint2Str, typed/dynamic MakeArray, Ceil, Floor, MethodId; wrong arities | F `supported_builtin_exclusion_coverage` |
| IntCall, Send, storage dynamic Pop; namespace/visibility/base exclusions | X `supported_internal_send_pop_rows` |
| ExtCall counts, keyword operands, pure vs effectful defaults, value/NoneT returns, nonword args | X `supported_external_expression_row`, `supported_external_nonword_arguments_rejected` |
| ExtCall admission does not depend on declarations of the same name | X `supported_external_declaration_independent` |
| F22/ordering: nested effects in P, internal args, external target/value/args | X `supported_effect_nesting_counterexamples` |
| RawCallTarget, RawLog, RawRevert, SelfDestructTarget, every CreateTarget kind | X `supported_raw_call_forms_excluded` |
| Internal-call/effect occurrence through every recursive container | X `supported_occurrence_traversal_coverage` |
| Dynamic decode in expressions/targets/defaults; static negatives; source ABI type reuse | X `supported_dynamic_decode_traversal_coverage` |

Validation from the worktree root:

```sh
timeout 120s holbuild --max-heap 16384 -j1 --tactic-timeout 10 \
  supportedTypePropsTheory supportedDeclPropsTheory supportedNamePropsTheory \
  supportedExprFormsTheory supportedExprsTheory supportedExprTraverseTheory \
  supportedExprFormPropsTheory supportedExprPropsTheory
```

Individual expression targets also pass with `timeout 30s` and the same flags.
All TASK_020 additions are within this directory; existing theory source and
all `.agent-files` inputs are untouched. Source/proof cheat delta: **zero**.

## Statement/program API (TASK_021)

- `supportedStmtTraverseTheory`: `supported_stmt_expr_exists` and its list,
  assignment/tuple-target, iterator and reason variants traverse **all** AST
  forms, not only admitted ones. They reuse TASK_020's expression traversal,
  including defaults, Pop targets and nested unsupported expressions.
- `supported_stmt_bindings locals stmt`, `supported_stmts_bindings locals ss`
  retain declared `(name,type)` pairs and **duplicates** across all branches
  and nesting. `locals=T` collects AnnAssign; `locals=F` collects For variables.
  The append contract supports consumers without unfolding the traversal.
- `supported_internal_stmt_shape`/list variant exclude AnnAssign and For
  recursively. `supported_internal_shape_bindings` proves this is exactly
  emptiness of both binding lists.
- `supported_type_namespace` recursively checks **only** module components in
  type annotations, independently of the W/value/storage classes. Together
  with `expr_nonmain_type_root` and the statement traversal, this enforces the
  global main-module requirement even in Name/Subscript annotations and loop
  types; it does not invoke or reproduce source typing.
- `supportedStmtsTheory`: `supported_stmt tops bindings`, `supported_stmts`
  enumerate every constructor. The only E positions are Expr, Return,
  AnnAssign, and a word-typed local Assign. Storage writes and indices,
  augmentation, append arguments, conditions and event arguments must be P.
  Tuple assignment and all other target shapes are rejected.
- `supported_assignment`, `supported_aug_target`, `supported_append_target`
  reuse TASK_020's storage-base lookups. Writes may use **any declared field**
  of a full-word storage struct; the first-field restriction remains read-only.
- `supported_iterator tops ty iter bound`: two IntL endpoints require integer
  loop type, start <= end, and exact `Num(end-start)` (including zero); other
  ranges require two P expressions and a positive bound; arrays require the
  exact Name/Fixed element-type and bound shape. Nonliteral endpoint typing is
  a separate source-typing check, not an added restriction here.
- `supported_assert_reason`, `supported_raise_reason`: only bare,
  UNREACHABLE or StringL. `supported_log` checks declared event existence,
  module NONE, exact argument count/types and P arguments.
- `supportedProgramTheory`: `supported_function_body` combines complete
  binding/name checks, statement checks, annotation namespaces and the
  Internal no-AnnAssign/no-For/no-IntCall restriction. Every For body excludes
  IntCall through its entire recursive subtree. Send/ExtCall/Pop are **not**
  prohibited merely because they are effects in an Internal/For body.
- `supported_declaration_body` explicitly handles all declarations;
  `supported_program` conjoins TASK_019 headers and actual selector/name
  checks with all function bodies. Fallback arguments, defaults,
  nonreentrancy, raw returns, immutables and module exclusions are enforced.
- `occurs_abi_decode_target target tops` is the exact PLAN §5.5/D9 API:
  some **function body** contains TypeBuiltin _ (AbiDecode _) target _.
  It traverses targets/reasons/iterators/unsupported bodies and is independent
  of admission, flags or dynamicity. Defaults/constants alone do not count.
  Consumers can conjoin the source ABI dynamic-type test for the exemption;
  no dependency on future e2e theories is introduced.

Permanent plain-EVAL checks:

| Boundary | Theory and checks |
|---|---|
| Every statement row, E root positions, targets, pure storage ordering, augmentation, append, reasons, exact logs | `supportedStmtProps`: `supported_simple_statement_rows`, `supported_all_effect_root_positions`, `supported_storage_statement_rows`, `supported_target_exclusions`, `supported_storage_effects_rejected`, `supported_augmented_statement_row`, `supported_control_reason_rows`, `supported_log_statement_row` |
| Literal/checked ranges, fixed-array shape/type/bound | `supportedStmtProps`: `supported_literal_range_statement_row`, `supported_checked_range_statement_row`, `supported_fixed_array_iteration_row` |
| Whole-program acceptance, Internal/loop restrictions, name/type environments, all header/name exclusions, fallback, annotations; typing separate | `supportedProgramProps`: all theorems |
| Every statement/target occurrence position, exact/dynamic decode API, duplicate-preserving recursive binding collection | `supportedStmtTraverseProps`: all theorems |

Build the new checks with the ordinary 10s tactic contract:

```sh
timeout 30s holbuild --max-heap 16384 -j1 --tactic-timeout 10 \
  supportedStmtTraversePropsTheory supportedStmtPropsTheory supportedProgramPropsTheory
```

Cold dependency/heap loading is infrastructure and may use `timeout 600s`;
no EVAL check is given a larger tactic limit. Existing actual bytecode-parity
checks use their independent Python oracle, the prescribed 600s tactic limit
and a 3600s outer timeout. No TASK_022 fixture membership proofs are added.
All TASK_021 source changes stay here; `.agent-files` records are read-only.
No cheats or axioms were added or substituted.
