# Supported-subset whitelist

`supportedProgramTheory` assembles the total computable predicate
`supported_program tops`, the subset of Vyper the staged compiler-correctness
results cover. It is a syntactic boundary, not source typing, a compiler or
evaluator change, or a correctness theorem.

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
  no raw return, defaults only on external functions, value arguments and
  NoneT/value return (nonreentrant guards and external defaults are admitted;
  `check_contract` separately validates their headers);
  private explicitly slotted storage of storage types; private explicitly slotted
  transient full words; private non-transient non-nested maps with permitted
  keys and full-word values; value-typed struct/interface fields; word/string
  event fields (thus no indexed aggregates or bytes20), at most three of them
  indexed; no flags, constants,
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
- **`supported_function_bindings tops args locals loops`**: ALL_DISTINCT
  on `MAP FST args ++ locals ++ loops`. Locals may shadow module variables
  (`compile_env` keeps those in `ce_module_vars`) and may use the names
  `__return_buf__`/`__return_pc__` (dedicated `ce_return_*` fields). The statement checks supply
  **all** AnnAssign and For names across all branches/nesting, as lists rather
  than deduplicated sets. This rejects duplicates within and across each class.
- `supported_function_header_names tops top`: argument-name checks.
  Internal function names are unrestricted: their Venom labels come from
  `internal_fn_label`, which no other label can equal. External fallback
  argument checks belong to `function_header_ok` in `check_contract`.
- `supported_selectors_distinct tops`: uses **the actual compiler**
  `build_selectors (type_env tops) (FST (classify_functions tops))`; excludes
  fallback, Internal, Deploy; does not approximate selector uniqueness by names.
- `supported_declaration_names tops`: distinct event names plus argument-name
  checks. Struct fields may share names with module variables or maps.
  `check_contract` separately checks external
  names and all ABI-prefix/public-getter selectors; the selector helper above
  is not a whitelist precondition. It does not inspect locals/loops:
  the statement checks additionally call `supported_function_bindings` on its collected
  names and enforce the internal-function/loop body restrictions.

## Expression API

### `supportedExprFormsTheory`

- `supported_binop op operand_type rhs_type literal_base nonnegative_exponent`
  is the exact operator table. Comparison restrictions use the **operand** type,
  not their bool result. AugAssign reuses it with literal_base=F.
- `supported_unsigned_type`, `supported_signed_type`,
  `supported_numeric_type`, `supported_integer_literal`,
  `supported_nonnegative_literal`; widths reuse the foundation limits.
- Conversion forms use the source type system's width-aware
  `valid_conversion src dst` relation directly; there is no separate conversion
  whitelist.
- `supported_builtin_form tops ty builtin args` and
  `supported_type_builtin_form ty builtin target args` encode exact forms and
  arities, including the ABI flags/method-id/single-argument restrictions.
- `supported_storage_scalar tops id ty`, `supported_storage_array tops id`,
  `supported_storage_dynamic_array tops id`, `supported_subscript_base tops id`,
  `supported_storage_fields tops id`, `supported_storage_field_read tops id field`.
  These inspect the declaration lookups; require private slotted admitted storage/map
  declarations, reject modules, and distinguish aggregate places from values.
  Storage-field **reads** require the first field; writes may use any field
  in the exported field list.
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
  The interpreter captures internal argument results before reading them after
  defaults; external positional arguments are read after keyword evaluation.
  This deferred-read behavior does not remove the whitelist's pure-operand
  restriction. Builtin and log arguments remain eager.
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

Proof paths: `supportedExprFormPropsScript.sml` (F below) and
 `supportedExprPropsScript.sml` (X below). All concrete
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
| Checker conversion domain and accepted/rejected width boundaries | F `supported_convert_checker_domain`, `conversion_width_boundary_acceptance`, `conversion_width_boundary_rejection` |
| ABI encode/decode exact flags, method-id size, tuple depth/length, arity | F `supported_abi_forms_coverage` |
| Uint2Str (unsigned argument), CalldataSlice; Len, hashes, Concat, Slice, typed/dynamic MakeArray, Ceil, Floor, MethodId and wrong arities excluded | F `supported_builtin_exclusion_coverage` |
| IntCall, Send, storage dynamic Pop; namespace/visibility/base exclusions | X `supported_internal_send_pop_rows` |
| ExtCall counts, keyword operands, pure vs effectful defaults, value/NoneT returns, nonword args | X `supported_external_expression_row`, `supported_external_nonword_arguments_rejected` |
| ExtCall admission does not depend on declarations of the same name | X `supported_external_declaration_independent` |
| F22/ordering: nested effects in P, internal args, external target/value/args | X `supported_effect_nesting_counterexamples` |
| RawCallTarget, RawLog, RawRevert, SelfDestructTarget, every CreateTarget kind | X `supported_raw_call_forms_excluded` |
| Internal-call/effect occurrence through every recursive container | X `supported_occurrence_traversal_coverage` |
| Dynamic decode in expressions/targets/defaults; static negatives; source ABI type reuse | X `supported_dynamic_decode_traversal_coverage` |

## Statement/program API

- `supportedStmtTraverseTheory`: `supported_stmt_expr_exists` and its list,
  assignment/tuple-target, iterator and reason variants traverse **all** AST
  forms, not only admitted ones. They reuse the expression traversal,
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
  enumerate every constructor. E is admitted at Expr, Return, AnnAssign,
  Assign/AugAssign RHSs and supported subscript-target indices. Nested effects
  inside P expressions remain excluded; append values, conditions and event
  arguments must be P.
- `supported_assignment`, `supported_target`, `supported_append_target`
  reuse the storage-base lookups. Assignment targets include locals of
  supported value types, slotted scalar storage/transient variables, one-level
  storage/map subscripts, and **any declared field** of a full-word storage
  struct. Flat tuple assignment uses these same targets, including repeats;
  nested tuple targets remain rejected. The first-field restriction remains
  read-only. RHS/target type compatibility is a separate typing obligation.
  Single-target assignment captures the RHS, resolves the target, then reads
  and stores the RHS; augmentation reads the target before its RHS. These are
  implemented evaluation orders, not an assignment simulation theorem:
  [stmtSim](../stmtSimScript.sml) still lists Assign/AugAssign as unproved.
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
  `supported_program` conjoins the declaration headers and actual selector/name
  checks with all function bodies. Fallback arguments, defaults,
  nonreentrancy, raw returns, immutables and module exclusions are enforced.
- `occurs_abi_decode_target target tops` is the exact PLAN §5.5/D9 API:
  some **function body** contains TypeBuiltin _ (AbiDecode _) target _.
  It traverses targets/reasons/iterators/unsupported bodies and is independent
  of admission, flags or dynamicity. Defaults/constants alone do not count.
  Consumers can conjoin the source ABI dynamic-type test for the exemption;
  no dependency on future e2e theories is introduced.

Whole-program acceptance, the Internal/loop restrictions, name/type
environments, every header/name exclusion, fallback and annotations are
checked by plain EVAL in `supportedProgramProps`.
