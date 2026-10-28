# Opt-in source annotation resolution

## API

- `sourceTypeDefs`: resolved identities, errors, required-constant bounds.
- `sourceTypeResolve`: `source_type_resolve tenv names constants annotation`
  consumes the common `source_const_annotation` AST and returns
  `ST_Ok (SourceTypeResolution vtype qualifiers bounds)` or an explicit error.
- `sourceTypeProps`: runtime wellformedness and exact bound-value provenance.
- `sourceTypeProvenance`: the recorded expressions are **exactly all original
  annotation bounds**, in structural left-to-right/postorder, not replacements.
- `sourceTypeFrontendLib`: opt-in kernel-certified annotation gate. `resolve`
  returns the equation, wellformedness, bound-value and original-bound theorems.
  `check_claim` additionally rejects a disagreeing inferred `value_type` claim.
  No existing frontend entry point or ordinary path is changed.

`tenv` is the independently elaborated nominal type environment. `names` maps
resolved paths to `source_type_identity`; `constants` is the common
`source_const_eval` environment (e.g. a successful `source_const_resolve` output).
There is deliberately no spelling-based primitive fallback. Aliases may map to
identical identities; shadowed names need not. Integer identities carry signedness
and source width; fixed-byte identities carry the source byte width.

The common annotation AST uses dedicated tags for `String`, `Bytes`, `DynArray`,
`HashMap` and qualifiers. These tags alone do **not** establish builtin identity:
resolution also requires the matching `STI_Constructor` binding at the constructor's
canonical path. A `Bytes` spelling bound to `STI_Bool`, for example, is rejected.
The current common syntax cannot represent an alias of a parameterized builtin
constructor; this layer does not invent that missing identity information.

A stricter frontend can pass retained original annotations and independently
resolved environments to `sourceTypeFrontendLib.resolve`, or `check_claim` when
checking an imported inferred-type assertion. The library computes HOL terms with
proved computation rules, never performs source arithmetic in ML, and fails
closed on errors/nonclosed/noncomputable input. It does not decode JSON or
reify source syntax; use the common source syntax/annotation decoder upstream.

## Validation and errors

Integer widths must be multiples of eight in `[8,256]`; fixed bytes are `[1,32]`.
Original bound expressions are evaluated using **common `source_const_eval`**.
Only `SC_Value (SCV_Int i)` with `0 < i < 2^256` is accepted. Naturals are
constructed only after this check, never by unsigned wrapping. Booleans and
scaled decimals are not integers for this purpose. All common outcomes remain
distinct:

| Common outcome | Annotation error |
|---|---|
| `SC_NotConstant` | `STE_RequiredConstant` |
| `SC_Invalid e` | `STE_ConstantInvalid e` |
| `SC_Unsupported u` | `STE_ConstantUnsupported u` |
| noninteger `SC_Value` | `STE_IntegerBound` |
| nonpositive/too-large integer | `STE_BoundRange` |

Each constructed type is additionally checked by `well_formed_vtype`, including
aggregate slot-size overflow and nominal declaration validity. HashMaps retain
`HashMapT key value` separately from ordinary `Type ty` and may nest as values;
they never masquerade as `NoneT`. HashMap keys obey `hashmap_key_type`. Arrays
and tuples require ordinary runtime element types and reject nested qualifiers.
Empty tuples, duplicate qualifiers and mutually exclusive constant/immutable/
transient qualifiers are rejected. Root qualifiers are retained, not silently
translated away. Resolution reports the first failing structural child; each
individual constant expression uses the common evaluator's eager error algebra.

## Proof boundary

`source_type_resolve_well_formed` proves a successful output's `value_type` is
wellformed. `source_type_resolve_runtime_well_formed` specializes this to ordinary
runtime `Type ty`. `source_type_resolve_bound_provenance` gives the exact common
evaluation and positive, source-range-checked natural for every recorded bound.
`source_type_resolve_original_bounds` shows there are no omitted, inserted or
substituted bound expressions. `source_type_claim_is_only_a_check` proves that
success with an inferred claim is precisely independent resolution success plus
claim equality: inferred metadata cannot select meanings.

These facts are not whole-program source acceptance, import provenance, cycle
checking for nominal definitions, qualifier **placement** checking (e.g. indexed
only on event fields), storage-layout correctness or compiler equivalence.
Those obligations remain with the stricter frontend/caller. Environments must be
resolved independently, not copied from unchecked compiler inferred metadata.

## Validation

Use holbuild **0.11.7**:

```
.agent-files/.holbuild-toolchain/bin/holbuild sourceTypeFrontendLibTestTheory
```

For isolated artifacts while another agent builds this worktree:

```
mkdir -p .source-type-build
cd .source-type-build
../.agent-files/.holbuild-toolchain/bin/holbuild --source-dir .. \
  sourceTypeTestTheory sourceTypeProvenanceTheory sourceTypeFrontendLibTestTheory
```

The test theories cover primitives, source-width rejection, arithmetic/name
bounds, nested arrays, nested HashMap value types, tuple/qualifier handling,
common outcome distinctions, slot overflow, no wrapping, shadowed constructors,
and inferred-claim rejection. Returned frontend certificates are saved as HOL
theorems in `sourceTypeFrontendLibTest`.
