# Original-source, location-sensitive meaning

This opt-in extension leaves `sourceExpr*`, `sourceModule*`, and the existing
`sourceMeaning*` mathematical/pure frontend unchanged. It extends that frontier
without using emitted expressions to define source meaning.

## Interfaces

* `sourceMeaningLocationDefs`: separate semantic terms, source references, and
  ordinary/ABI computations. The terms contain no runtime `expr`. Constants
  embed the existing independent mathematical meanings. Names read actual
  scoped/global cells; assignment targets distinguish immutables using the
  runtime module context. Runtime errors and complete state are retained.
* `sourceMeaningLocationSource`: recursive original-syntax rules for constants,
  resolved references and `msg.sender`, unary/binary operations, ordinary
  comparisons, Boolean chains, conditionals, tuples/arrays and subscripts,
  mapped runtime builtins (including special location-sensitive `len`), ABI
  encode/decode, `raw_revert`, and ordinary `raw_call`. Source type operands,
  Boolean options and four-byte selectors are independently resolved from
  original syntax and mathematical values. Missing options and invalid present
  options are not conflated. These rules mention neither elaboration nor an
  interpreter AST evaluator.
* `sourceMeaningLocationCode`: a separate structural compilation relation.
  `source_location_code_evaluates` simultaneously proves ordinary expression,
  ABI operand, ordinary argument-list and ABI argument-list agreement. Equality
  is of complete state computations, not only returned values. Every constructor
  and type-builtin branch is covered. Source metadata is related to actual
  `Name`/`TopLevelName` representations here, not assumed to denote emitted code.
* `sourceMeaningLocationBody`: independent original body rules and store
  computations for declarations, assignments, returns, expression statements,
  branches and sequencing. `source_location_body_code_evaluates` preserves the
  entire result and final state. `source_location_global_metadata` derives
  global identity/type/reference metadata from original declaration annotations,
  preserving the constant/dynamic distinction enforced by source resolution.

ABI evaluation has **two distinct phases**. Local/global operands capture
runtime cell types and locations. Primitive/storage/immutable operands unwrap
at their prescribed point; complex memory remains a live pointer until all
arguments have been evaluated. Projection indices and conditions are evaluated
once, when forming/selecting the location. Staging does not replay syntax.
Fresh representation captures are released on success and failure. Ordinary
builtin arguments retain their separate left-to-right materialisation behavior.

The scalar/operator algebra, source type resolver, state/capture primitives,
ABI value operation and external-call primitive are shared with the existing
semantics. This is not a second implementation of hashing, ABI bytes, EVM calls
or source type checking. In particular `raw_revert` preserves the interpreter's
existing `RuntimeError "raw_revert"`, not a stronger revert-payload semantics.

## Fixed #543 inventory

`tests/sourceMeaningLocationWitnessTestScript.sml` uses the unchanged 37-source
manifest and freshly decoded original syntax. It requires:

* 36 accepted source constant-dependency environments, with finite independent
  dependency derivations and initializer values;
* the pinned rejection of `method_id_var`;
* independent derivations for all **40 original function/constructor bodies**;
* structural code certificates against the actual retained declarations and
  all-initial-state body result/state equality for every one of those bodies
  (with the explicit primitive-only context condition `get_tenv cx = FEMPTY`);
* kernel-closed exports: no open hypotheses, axioms, cheats or oracle tags other
  than `DISK_THM` bookkeeping.

The proof-producing recursion derives semantic terms from original syntax and
source declaration/type/reference metadata **before** examining runtime code.
A separate recursion checks those already-derived terms against the actual
phase output. Kernel-computed Keccak equations accelerate evaluation; compiler
selectors, expected bytecode and folding metadata are not rewrite rules.
The fixture helper deliberately has no compiler/lowering-correctness dependency.

This closes the former 19-body gap, including local tuple/ABI handling, source
constant options/selectors, dynamic comparison, storage assignment/reads,
immutable constructor assignments, environment reads and staged raw-call/revert
arguments. The older frozen `sourceMeaningWitnessTest` remains the unchanged
21-body regression for its smaller pure expression relation.

These are **body execution** and source dependency results, not 36 new whole-
program deployment/dispatch/bytecode proofs. Inherited layout/module inputs
remain explicit. External lowering failures (#551/#554/#563/#567), full callee
source derivations, general deployment simulation, getters, nominal structures,
loops, dynamic shifts and general #135 completeness remain separate obligations.
No backend precondition or whitelist is weakened.

## Regressions and validation

`sourceMeaningLocationTest` constructs original derivations plus all-state
ordinary/ABI code transport for dynamic `len`/Keccak, folded tuple indexing,
conditional local-array indexing and ABI projection. Concrete state regressions
check actual cell-type capture, delayed reads after mutation, release on error,
and an index/condition captured once despite later changes to both, while still
observing a later write to the selected backing cell.

```sh
holbuild build sourceMeaningLocationDefsTheory sourceMeaningLocationCodeTheory \
  sourceMeaningLocationSourceTheory sourceMeaningLocationBodyTheory \
  sourceMeaningLocationTestTheory sourceMeaningLocationWitnessTestTheory \
  --force=theory --no-cache --skip-checkpoints --tactic-timeout 2.5
```

For concurrent agents, run in an isolated source snapshot. Current receipt:
`.agent-files/source-meaning-location-verified.log` and the corresponding theory
logs under `.agent-files/source-meaning-location-check/.holbuild/logs/current/`.
Verified receipt: all six targets force-built successfully at **2.5 seconds**
in 389.455 seconds total. The actual inventory output is
`constant_dependencies=36 original_bodies=40 remaining=0`. The focused root was
also force-rebuilt after adding audit-count output (2.1 seconds).

The six new theories have **376 audited exports**. In addition,
`tests/sourceMeaningLocationAudit.sml` reopened every unchanged legacy
`sourceMeaning` theory in the existing aggregate validation snapshot: **31
legacy theories / 452 exports**. Their source scripts and the checked core
runtime/frontend dependencies match the working copy. This is an artifact tag
audit, not a claim to force-rebuild the legacy backend dependency closure.
Together these audit **all 37 sourceMeaning theories / 828 exports**, with empty
hypotheses and axioms and only `DISK_THM` bookkeeping tags. The separate legacy
audit receipt is `.agent-files/source-meaning-location-legacy-audit.log`.

The inventory intentionally exceeds the small-proof 30-second target because
it recomputes original-source derivations across all fixtures; individual
instrumented proof tactics use the 2.5-second timeout.
