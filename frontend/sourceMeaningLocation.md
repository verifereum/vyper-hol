# Original-source, location-sensitive meaning

This opt-in relation defines location-sensitive source meaning without emitted
expressions. It is separate from the pure staged relation in
[sourceMeaning.md](sourceMeaning.md) and does not redirect ordinary frontend
entry points. See [constant-evaluation.md](constant-evaluation.md) for the
cross-cutting design and trust boundary.

## Interfaces and contracts

* `sourceMeaningLocationDefs` defines semantic terms, source references and
  ordinary/ABI computations. Terms contain no runtime `expr`; constants embed
  independent mathematical meanings. Names read scoped/global cells, and
  assignment targets distinguish immutables using the runtime module context.
  Errors and complete state are retained.
* `sourceMeaningLocationSource` gives recursive original-syntax rules for
  constants, resolved references, `msg.sender`, unary/binary operations,
  comparisons, Boolean chains, conditionals, tuples/arrays, subscripts, mapped
  builtins (including location-sensitive `len`), ABI encode/decode, `raw_revert`
  and ordinary `raw_call`. Type operands, Boolean options and four-byte
  selectors resolve independently from original syntax and mathematical values.
  Missing options differ from invalid present options. These rules mention
  neither elaboration nor an interpreter AST evaluator.
* `sourceMeaningLocationCode` is a separate structural compilation relation.
  `source_location_code_evaluates` simultaneously equates ordinary expressions,
  ABI operands and both argument-list computations, including complete state.
  It covers every constructor/type-builtin branch and relates source metadata
  to actual `Name`/`TopLevelName` representations.
* `sourceMeaningLocationBody` gives independent body rules/store computations
  for declarations, assignments, returns, expression statements, branches and
  sequencing. `source_location_body_code_evaluates` preserves the entire result
  and final state. `source_location_global_metadata` derives global
  identity/type/reference metadata from original annotations, preserving the
  constant/dynamic distinction imposed by resolution.

## ABI staging

ABI evaluation has **two phases**. Local/global operands capture runtime cell
**types and locations**. Primitive/storage/immutable operands unwrap at their
prescribed point; complex memory remains a live pointer until every argument
has been evaluated. Projection indices and conditions are evaluated once when
forming/selecting the location, not replayed during staging. Fresh captures are
released on success and failure. Ordinary builtin arguments instead retain
their own left-to-right materialisation behavior.

Local and immutable captures use separate token arenas. Complex immutable
operands snapshot on unwrap; complex local-memory operands retain aliases until
staging. Projection bounds are checked when capturing the location. A later pop
does not invalidate an already captured cell merely by shortening the logical
array length. Cleanup removes fresh capture suffixes, not logical mutations or
writes to surviving backing cells.

Runtime operands are defined in
[vyperAbiOperandScript.sml](../semantics/vyperAbiOperandScript.sml). The typing
predicate `abi_operand_valid` establishes type/tag/token validity, not future
decoding success. `read_abi_operand_valid_typed` derives result typing when decoding
succeeds; `unwrap_abi_immutable_valid_snapshot` specifies immutable snapshots.
The frame theorem `abi_operand_valid_memory_frame` requires both arena lengths
to be nondecreasing. These contracts are in
[vyperAbiReadTypingScript.sml](../semantics/prop/vyperAbiReadTypingScript.sml).

The scalar/operator algebra, source type resolver, state/capture primitives,
ABI value operation and external-call primitive are shared with the interpreter.
This is not independent hashing, ABI byte semantics, EVM-call semantics or source
type checking. `raw_revert` preserves `RuntimeError "raw_revert"`, not a stronger
revert-payload model.

## Scope and assumptions

The fixed regression contract in
`tests/sourceMeaningLocationWitnessTestScript.sml` requires freshly decoded
original syntax from the 37-source manifest, 36 accepted finite constant
dependency derivations, rejection of `method_id_var`, and independent meanings
for all 40 function/constructor bodies. It checks structural certificates against
actual retained declarations and all-initial-state result/state equality, with
explicit primitive-only context condition `get_tenv cx = FEMPTY`.

Semantic terms derive from source syntax and source declaration/type/reference
metadata **before** runtime code is inspected; a separate recursion checks those
terms against phase output. Kernel-computed Keccak equations accelerate
computation, not compiler selectors, expected bytecode or folding metadata. The
fixture helper has no compiler/lowering-correctness dependency.

This suite includes tuple/ABI handling, source options/selectors, comparisons,
storage reads/assignment, immutable constructor assignment, environment reads
and staged call/revert arguments. The pure `sourceMeaningWitnessTest` tests the
smaller relation separately. Body/dependency certificates are **not whole-program
deployment, dispatch or bytecode proofs**. Layout/module inputs remain explicit.
Full callee derivations, external lowering correctness, general deployment,
getters, nominal structures, loops, dynamic shifts and general source typing are
outside this contract. No backend preconditions are weakened.

## Reproduction

```sh
holbuild build sourceMeaningLocationDefsTheory sourceMeaningLocationCodeTheory \
  sourceMeaningLocationSourceTheory sourceMeaningLocationBodyTheory \
  sourceMeaningLocationTestTheory sourceMeaningLocationWitnessTestTheory \
  --force=theory --no-cache --skip-checkpoints --tactic-timeout 2.5
```

`sourceMeaningLocationTest` exercises original derivations and all-state
ordinary/ABI transport for dynamic `len`/Keccak, tuple indexing, conditional
array indexing and ABI projection. State regressions require runtime cell-type
capture, delayed reads after mutation, capture release on error, and once-only
index/condition evaluation while observing later writes to the selected cell.
The witness root checks exact inventory and kernel closure: no open hypotheses,
axioms, cheats or oracle tags except `DISK_THM` bookkeeping. Artifact tag auditing
does not certify a fresh build of the backend dependency closure.
