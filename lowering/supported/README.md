# Supported-subset foundations (TASK_019)

Status: complete. Implements the **type, body-independent declaration, and
name rows of PLAN §5.6**; expression and statement/body traversal are deliberately
left to TASK_020/021. These theories do not define `supported_program`, accept
function bodies, change the compiler, or perform source typing.

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
cheat delta is zero. No TASK_020 work has been started.
