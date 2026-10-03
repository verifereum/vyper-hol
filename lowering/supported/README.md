# Supported-subset foundations and expressions (TASK_019/020)

Progress: **TASK_019 and TASK_020 complete**. Implements the type,
body-independent declaration, name, and expression rows of PLAN §5.6.
Statement/body traversal remains TASK_021. These theories do not define
`supported_program`, accept function bodies, change the compiler/evaluator,
or perform source typing (PLAN D10 keeps typing separate).

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
- `supported_interface_method tops name`: option of
  `(from_interface,args,return_type,mutability)`. Follows the first matching
  External function or interface method, just like `build_method_id_map`.
- `supported_external_call_signature tops name arg_types`: requires interface
  origin and exact argument types; a preceding matching External declaration
  blocks it. Other external-call restrictions remain TASK_020's responsibility.

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
- `supported_local_name tops`: excludes all variable/map names and
  `__return_buf__`, `__return_pc__`.
- **`supported_function_bindings tops args locals loops`**: ALL_DISTINCT and
  name restrictions on `MAP FST args ++ locals ++ loops`. TASK_021 must supply
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
- `supported_external_return_type`: W or a nonempty tuple of W; no NoneT,
  dynamic returns, nested tuples, or arrays.

### `supportedExprsTheory`

- `supported_pure_expr tops e` (P), `supported_pure_exprs tops es`,
  `supported_pure_fields tops fields`: structural recursion, with every AST
  constructor explicit. Calls/Pop are never P. Aggregate storage bases of
  Subscript/Attribute are specially checked places, not standalone P values.
- `supported_effect_expr tops e` (E): only root IntCall, ExtCall, Send, or Pop.
  All call arguments, including external target/value, must be P. Internal
  lookup requires Internal/NONE. ExtCall requires exact count, W arguments,
  static W/tuple-W return, no default, and TASK_019's **first-by-name interface**
  signature rule (parameter types only, exactly as PLAN §5.6 specifies).
- `supported_expr tops e`: P or E, for later statement expression positions.
  No statement or whole-program placeholder is provided.
- Symbolic contracts: pure Call/Pop rejection, external-call inversion,
  default-return rejection, and list/field EVERY equivalences.

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
| ExtCall counts, defaults, NoneT/dynamic/nonword returns, nonword args | X `supported_external_expression_row`, `supported_external_nonword_arguments_rejected` |
| First matching External/interface/duplicate interface entry blocks later matches | X `supported_external_first_declaration_rule` |
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
