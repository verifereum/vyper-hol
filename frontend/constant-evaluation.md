# Source evaluation and public frontend integration (#135)

## Public source path and compatibility boundary

`vyperCheckContractFrontendLib.Source.check_contract` (also
`check_source_contract`) is the general source-facing checker. Its required
input is `{fuel, trust, keys, program, layouts, address}`:

* `program` is ORIGINAL **pre-erasure** `sourceSyntax` syntax. Constants,
  qualifier calls, annotation bounds, defaults and executable children remain
  intact. Ordinary compiler annotated JSON has already erased qualifiers and
  is not an adequate substitute. No flags reconstruct them in this API.
* `trust` supplies the inherited canonical module IDs, nominal identities,
  nominal environment and storage slots; `keys` supplies the corresponding
  source registry. `layouts` and `address` are explicit inherited checker
  inputs. Neither a constant value nor a resolved bound comes from trust.
* This policy-free record API calls `sourceModuleFrontendLib.check_simple`,
  and therefore `source_module_elaborate_simple` / `source_module_check_simple`, checking constructors with
  `check_contract T`. An error, Unsupported, exhausted fuel, unresolved name or
  failed checker is terminal: **no old translator/evaluator retry**.

`Source.check_contract_result` / `check_source_contract_result` returns the
retained source, exact executable modules, phase equation, original-retention
and linking equations, actual checker input, artifact, checker equation and
composition equation. `check_source_contract_file` decodes a caller-supplied
pre-erasure syntax file with explicit keys/trust/layouts; it does not authenticate
that file's origin or infer erased qualifiers. The public
`Source.check_contract_file_result` / `Source.check_contract_file` instead load
**the genuine pre-erasure capture protocol**, produced by
`tools/source_module_loader.py` before `get_node`. They preserve captured keys
and pass captured nonreentrancy/declaration-only policies explicitly to HOL.
The policy-free record API uses the preserved `_simple` equations. Already loaded
captures use `Source.check_loaded_contract_result` (also
`check_loaded_source_contract_result`). Ordinary post-erasure JSON is rejected,
not retried or reconstructed. Protocol labels, hashes and parsing correctness
remain explicit loader trust, not HOL authenticity proofs.
See [the loader protocol](sourceModuleLoader.md).

```sml
val checked = vyperCheckContractFrontendLib.Source.check_contract_result
  {fuel = ``80:num``, trust = inherited_source_trust, keys = canonical_keys,
   program = original_source_program, layouts = inherited_layouts,
   address = ``0w:address``};
val phase = #equation (#elaboration checked);
val checker = #checking checked;
val composition = #composition checked;
```

The old successful top-level names `prepare_check_input`, `check_contract`,
`check_contract_result` and `check_contract_file` are deliberately **unchanged**.
Their explicit `_legacy` aliases label the metadata-consuming frontend; local
ordinary fixture callers use those aliases. They are compatibility entry points,
not a source API with fallback. Changing their input type or routing them to an
incomplete source evaluator would regress currently valid contracts.

**The ordinary switch is NOT achieved by adding this source API.** The gate is
full ordinary acceptance coverage, not just opt-in witnesses. Before making the
short top-level names source-facing, supply pre-erasure captures and explicit
trust/layouts for every successful ordinary caller/fixture, close the gaps below,
and require exact emitted-module/checker-artifact equations (plus backend parity
where compilation is claimed). Then migrate callers explicitly and leave the
old path under `_legacy`; never use success/error-based automatic routing.

## Strict integer-bound compatibility adapter

`prepare_constant_source_file` decodes the original integer syntax accepted by
`jsonConstASTLib` and constructs a `SourceProgram`; it performs **no arithmetic
or type evaluation**. `Source.check_constant_contract_file` (also
`check_constant_source_contract_file`) feeds that program into the very same
source checker above. For supported strict #135 bound cases this is one pipeline,
not a second evaluator. A constant such as `N = 1 + 2` gives array bound 3 and a
literal exponent 3; the original addition remains in `retained_source` even
though the emitted constant initializer is a literal 3.

This adapter is explicitly a **legacy JSON syntax compatibility boundary**:
`jsonConstASTLib` reads `is_constant`/`is_public` to identify its restricted
non-public constant declarations, because those fixtures are post-erasure.
Those qualifier assertions are trusted, not recovered source or a source parsing
proof. Original expressions/bounds never use `folded_value` or inferred `type`.
General source callers must supply actual pre-erasure syntax instead.

The preserved `check_constant_contract_file_legacy` alone uses
`translate_constant_module` and bounded runtime integer evaluation. The top-level
`check_constant_contract_file` is now an alias of the same source route as
`Source.check_constant_contract_file`: both existing pin-valid strict fixtures,
`constant_bound.json` and `constant_shifts.json`, pass. Signed shifted operands,
unsigned/narrow dynamic counts and source-validated canonical literal arithmetic
are covered by [the shift regressions](../tests/sourceShiftCount.md). Signed
runtime count names remain rejected, as at the pin. There is no per-input retry.

Tests preserve explicit legacy acceptance and its checker artifact, and compare
exact function ASTs. Whole legacy/source module ASTs are deliberately **not**
asserted equal: the old constant initializer remains an unfurled runtime
expression, whereas Source reifies its mathematical value. Strict-adapter Source
and true pre-erasure Source must give exactly the same checked module/artifact.
This gate is not complete #135 typing or authorization for the ordinary switch.

The source route also intentionally improves mathematical annotation arithmetic:
`((1 << 256) >> 255) + 1` resolves to 3 in a bound. The bounded legacy evaluator
rejects that expression rather than wrapping it to length 1. These are different
specified frontends, not interchangeable implementations; tests/documentation
must not present changed behavior as exact legacy equivalence.

## Ordinary integration prerequisite inventory

This compares current implementations, including **extended** `sourceExprCall`,
`sourceModuleLink` and `sourceModuleOverride`, rather than the older expression-only
inventory. "Implemented" does not mean the entire legacy family has parity.

| Ordinary legacy surface | Current source path / remaining switch requirement |
| --- | --- |
| Original constants, bounds, defaults, local annotations, constructor bodies | Implemented recursively; forward/imported dependencies, duplicates, cycles and unresolved names handled independently of folded fields. All retained pin-valid whole-source witnesses check, but this is not the ordinary fixture corpus. |
| Internal/self/imported calls and omitted internal defaults | Source-derived signatures and canonical linked IDs now implemented; imported-call/public export witness checks exact AST. Do not list *all calls* as missing. General inference/nominal operands still constrain these calls. |
| External/static calls, inline interface constructors, interface-typed locals/parameters | Implemented with source signatures, receiver/argument/keyword order, typed gas/value/default-return operands, independently constant skip flag and mutability checks. Genuine imported `.vyi` policies and nominal struct field reads now have public-path captures. Omitted external default arguments remain a gap. |
| Exports, transitive `__interface__`, initializes/uses, abstract overrides | Source linkage now implemented, with initialized targets, unique links/cycles, canonical original structural defaults, and abstract-body removal. `implements` linkage is not independent full interface-obligation checking. |
| Ordinary multi-module storage | Public loader capture checks with inherited canonical IDs/layout and an independently specified complete Source AST. Source explicitly annotates imported storage slot SOME 0; legacy leaves that declaration's slot NONE. Checker artifacts agree; whole AST equality is not claimed. This one fixture is not broad ordinary coverage. |
| Imported `.vyi` / JSON ABI and repeated/builtin interface identities | Genuine source-loader `.vyi` policies now elaborate signature-only call bindings, retain nominal declarations and emit no executable stubs. `sourceModulePolicyTest` covers imported interfaces/struct returns/deployment and nonreentrancy through public Source. JSON ABI, repeated/builtin interface identities and unbounded ABI callsite bounds remain broader legacy coverage gaps. |
| Nonreentrancy-by-default and explicit decorators | Captured policy now reaches signatures and bodies: non-pure external functions default to nonreentrant, `@reentrant` opts out, and internal/deploy functions retain explicit policy. The genuine pragma regression pins all these cases through public Source. |
| Storage/transient/immutable/HashMap declarations, nominal structs/flags/events | Source declaration/signature support exists with inherited nominal definitions and slots. Runtime struct construction/ordinary field access, flag members and their general call/assignment use do not have full legacy coverage. Nominal identity/duplicate normalization behavior must remain tested. |
| Basic control flow, ranges, array iteration, nested assignment | Pass/break/continue/return/if/assert/raise/local/for/log and basic assignment paths exist. Tuple/destructuring assignment, append/pop, general attribute targets/inference, and `UNREACHABLE` assert/raise markers remain gaps. Range bounds require original constant evidence; check legacy zero/dynamic endpoint cases explicitly. |
| Operators and literal inference | Dynamic Boolean chains/IfExp, contextual lists/tuples, ordinary array and constant tuple indices, basic arithmetic/comparisons exist. Mixed-sign/context-polymorphic boundaries, membership, fixed-byte operations, address literals/checksums remain incomplete. Signed shifted operands and unsigned/narrow counts now have explicit pin-valid regressions; signed runtime count names reject. Executable intermediates remain bounded; annotation math is separate. |
| ABI encode/decode/method ID and selected builtins | Implemented with original constant flags, duplicate/unknown keyword rejection, independent type operands and selectors. Len/Keccak/Abs/Min/Max/PowMod/AddMod/MulMod are present. This does **not** cover legacy concat/slice/sha256/floor/ceil/convert/empty/min/max-value/epsilon/unsafe ops/extract32/uint2str/as_wei_value/EC/chain builtins. |
| Raw calls and chain interaction | Only no-keyword `raw_call(target,data)` zero-output and `raw_revert(data)` subset is implemented. General raw-call flags/output/gas/value, raw_log, send, selfdestruct, creation builtins and dedicated calldata len/slice/raw-call forms remain gaps. Environment bindings are not general account-attribute coverage. |
| Backend compilation | Module checking is distinct from compilation. `source_module_compile` currently rejects multi-module backend linking and has known single-module backend failures; exact phase/check equations alone are not byte parity or source/runtime simulation. |

The ordinary regression list in `vyperCheckContractFrontendLibTestScript.sml`
continues to run explicitly through `_legacy`: scoped locals, simple/address,
storage/transient, imported struct/flag/interface, duplicate interfaces,
multi-module storage, defaults/control, nonreentrancy, deployment/imported deploy,
third-party flex/daddy, interface struct returns and ABI encode. No claim is made
that this list has all been ported to pre-erasure source. In particular the
import/interface, nominal-expression, policy and builtin rows above prevent a
safe ordinary switch today.

An additional **actual pre-erasure ordinary-source** probe uses the pinned
loader and public `Source.check_contract_file_result`, not post-erasure flags:
`simple`, `storage`, `deployment`, `defaults_control`, explicit `nonreentrant`
and `transient_storage` pass the full checker and have identical legacy ASTs.
`address_bytes20` rejects with `SME_Constant SCErr_Type`; this is a concrete
remaining ordinary coverage failure, not a legacy fallback. The `abi_encode`
source capture itself rejects its stale `#pragma version 0.5.0a3` at the current
0.5.0a4 pin; that is not counted as HOL source rejection or acceptance.
Reproducible scripts/receipts are `.agent-files/public-source-ordinary-generate.py`,
`.agent-files/.public-source-ordinary.sml` and
`.agent-files/public-source-ordinary-{capture,results}.log`.
See [module coverage](sourceModule.md),
[expression coverage](sourceExpr.md) and
[whole-program parity results](../docs/SOURCE_MODULE_PARITY_RESULTS.md).

## Guarantees and validation

The source pipeline retains originals, resolves source declarations and constants,
elaborates/checks modules and exports exact computation equations. Its local
source expression/type/constant theorems are documented in the linked phase docs.
`Source.artifact_semantics checked` extracts a kernel theorem using
`source_meaning_compile_program` for the **same checked single-main-module
artifact**. Its universally quantified raw `compile_vyper` success remains an
antecedent; it does not assert compilation exists. The independent original-source
module derivation and equality with the inherited nominal environment remain
explicit for complete interpreter call/load transport, including defaults and
constructor installation. Imported backend modules reject rather than being
flattened. See [independent source meaning](sourceMeaning.md) for exact coverage.
This is not universal accepted-program semantics, parsing authenticity, bytecode
execution correctness, or removal of backend hypotheses. Inherited parser/loader,
nominal/layout trust remains explicit.

`vyperCheckContractFrontendLibTestTheory` checks the public phase, original,
linking, checking and composition equations (including the exact artifact),
metadata deletion/poison invariance, exact array/exponent AST, imported/exported
and external calls, genuine public loader/policy rejection, and ordinary
multi-module Source AST/checker artifacts. It exercises **all 37 retained whole
source programs through the public full deployment checker**: all 36 pin-valid
programs must pass; only pin-invalid `method_id_var` proves the exact source domain
rejection. Resource failures are not acceptance. The same checked original
`N=1+2; f(x=N): return x+N` artifact supplies the semantic extraction regression;
actual full runtime dispatch returns 6. Source failures stay failures. New equation
receipts are audited for hypotheses, axioms and non-`DISK_THM` oracle tags.

`jsonConstEvalWitnessTheory` remains the separate legacy bounded-evaluator
regression: exact old initializer ASTs, arithmetic/width/shift failures, metadata
independence and successful signed shifts. `eval_integer_constant_sound`,
`evaluate_constant_sound`, `evaluate_constant_literal_equivalent` and
`resolved_array_bound_sound` describe that old evaluator, not all sourceModule
arithmetic.

```sh
holbuild vyperCheckContractFrontendLibTestTheory sourceShiftCountFrontendTestTheory \
  jsonConstEvalWitnessTheory sourceModuleParityInputTheory \
  --tactic-timeout 2.5 --skip-checkpoints --allow-cache-timeout-discrepancy
```

Current integration validation **passes at 2.5 seconds**, after the shared
pure-expression ancestor repair. The isolated `/tmp/public-source-check` build
has byte-identical public frontend, source shift/module and sourceMeaningCompile
inputs to the working tree. All four targets above pass. The public frontend
script's full legacy-plus-source computation matrix took 379.463 seconds;
the final incremental four-root recheck took 0.264 seconds. Receipts:
`.agent-files/public-source-validation3.log` and
`.agent-files/public-source-final.log`.

The independent exported-object audit accepts **391 theorems** across the public,
strict-shift, legacy, source-matrix and call/compile transport frontiers, with no
open hypotheses, axioms or non-`DISK_THM` oracles and no CHEAT warnings:
`.agent-files/public-source-exported-audit.log`. Fresh pin checks reproduce all
13 shift acceptance rows and seven Prague executions, including narrow-count
intermediate-overflow revert (`.agent-files/public-source-pin.log`). The strict
constant alias is switched; ordinary switching remains gated by the concrete
coverage inventory above.
