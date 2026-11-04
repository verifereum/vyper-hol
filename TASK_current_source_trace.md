# TASK: Port storage-observation proofs to the current live entry pipeline

## Meta
Status: approved for proof repair; independent statement and executable audits complete
Created: 2026-11-04
Location: project root
Candidate anchor: 90e3e8f12, based on 92bea34aa

## Theorem Statement (FROZEN)
Every existing theorem statement and definition in semantics/ and frontend/
is frozen exactly as supplied, including local helpers. The principal current
statements are copied below. Do not modify this statement. Prove it as-is, or
produce a counterexample. No additional premise is authorized.

```sml
Theorem storage_trace_frame_precompile_call_success:
  storage_trace_frame (precompile_call_success bt)

Theorem evaluate_storage_trace_frame:
  (!cx s. storage_trace_frame (eval_stmt cx s)) /\
  (!cx ss. storage_trace_frame (eval_stmts cx ss)) /\
  (!cx it. storage_trace_frame (eval_iterator cx it)) /\
  (!cx tyv nm body vs. storage_trace_frame (eval_for cx tyv nm body vs)) /\
  (!cx e. storage_trace_frame (eval_expr cx e)) /\
  (!cx es. storage_trace_frame (eval_exprs cx es)) /\
  (!cx t. storage_trace_frame (eval_base_place cx t)) /\
  (!cx t. storage_trace_frame (eval_target_place cx t)) /\
  (!cx t v. storage_trace_frame (assign_tuple_targets cx t v)) /\
  (!cx ts vs. storage_trace_frame (assign_tuple_target_list cx ts vs)) /\
  (!cx es. storage_trace_frame (eval_expr_results cx es))

Theorem call_external_function_no_loop_control_c53[local]:
  stmts_no_control_escape body /\
  call_external_function orc gobs am cx nr mut ts mods args dflts vals body ret =
    (INR exc,am',rqs) ==>
  exc <> BreakException /\ exc <> ContinueException

Theorem call_external_function_exact_selected_no_type_error_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  call_external_function orc gobs am cx nr mut ts mods args dflts vals body ret = (res,am',rqs) ==>
  no_type_error_result res

Theorem call_external_function_nondeploy_failure_rolls_back:
  ~cx.in_deploy /\
  call_external_function orc gobs am cx nr mut ts mods args dflts vals body ret =
    (INR exc,am',rqs) ==>
  am' = am

Theorem call_external_function_initial_failure_rolls_back:
  call_external_function orc gobs am
    (initial_evaluation_context am.sources am.layouts tx src)
    nr mut ts mods args dflts vals body ret = (INR exc,am',rqs) ==>
  am' = am

Theorem call_external_function_selected_explicit_success_machine_well_typed[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  LENGTH vals <= LENGTH args /\ LENGTH args - LENGTH vals <= LENGTH dflts /\
  call_external_function orc gobs am cx nr mut ts mods args dflts vals body ret =
    (INL v,am',rqs) ==>
  machine_well_typed am'

Theorem call_external_function_success_log_extends:
  call_external_function orc gobs am cx nr mut ts all_mods args dflts vals body ret =
    (INL v,am',rqs) ==>
  machine_log_extends am am'
```

## Completion Criteria
- The default-budget build below passes with no CHEAT or parser warnings.
- Preserve all supplied definitions and theorem statements byte for byte.
- Proof-body-only repairs are permitted in semantics/prop, in the proof
  sections of semantics/vyperInterpreterScript.sml, and in
  frontend/vyperConstEvalScript.sml. Test proofs may be repaired without
  changing test statements. No lowering or Venom edits are in scope.
- Add a helper only after searching for an existing result. Put reusable
  helpers beside their definitions, export existing local results when needed,
  and reuse them. Existing statements cannot be restated even when local.
- Report a counterexample and stop if a frozen statement is false.
- Commit only scoped source files and this task file. Never push. Each commit
  ends with Bot: sol (OpenAI GPT-6.1 Sol).

## Build
`holbuild -j4 build vyperConstEvalTheory vyperCallOutcomeBranchesTheory vyperCallOutcomeFrameTheory vyperCallOutcomePropsTheory vyperCallTheory vyperCreateFrameTheory vyperEvalExprPreservesScopesDomTheory vyperEvalMiscTheory vyperEvalOutcomeSuffixTheory vyperEvalPreservesImmutablesDomTheory vyperEvalPreservesScopesTheory vyperEvalPureExprTheory vyperExprNoControlTheory vyperHashMapPreservationTheory vyperHashMapTheory vyperHashMapStorageTheory vyperImmutableMetadataFrameTheory vyperImmutablesPreservationTheory vyperLookupStorageScopesTheory vyperLookupStorageTheory vyperMachineFrameTheory vyperPlaceFramesTheory vyperPlaceResultTypingTheory vyperPlaceTypingTheory vyperPureExprTheory vyperReadOnlyTargetsTheory vyperScopePreservationTheory vyperStatePreservationTheory vyperStorageBackendTheory vyperStorageFrameTheory vyperStoragePlaceProvenanceTheory vyperStorageReadSoundnessTheory vyperStorageTraceTheory vyperStorageWritePreservationTheory vyperTargetPlaceWriteTheory vyperTypeCallOutcomeTheory vyperTypeConstantFoldTheory vyperTypeContractGetterTheory vyperTypeEnvPreservationTheory vyperTypeEvalSoundnessTheory vyperTypeEvalStoragePreservationTheory vyperTypeExprSoundnessTheory vyperTypeExtCallSoundnessTheory vyperTypeGlobalLookupSoundnessTheory vyperTypeInitialStateTheory vyperTypeInvariantsTheory vyperTypeStatePreservationTheory vyperTypeStoragePreservationTheory vyperCallOutcomeTheory vyperCreateTheory vyperInterpreterTheory vyperStateTheory vyperStorageTraceTestTheory vyperTypeContractSoundnessTheory vyperTypeExternalCallMachineTheory vyperTypeEntryReadinessTheory vyperLogPreservationTheory`

The current-base definitions and statements have been independently inspected:
the eleven-family trace-frame and unchanged physical soundness statements were
judged PROVABLE; the executable definition audit also approved this exact port.
There is no kernel validation on this base yet. The complete batch
has not parsed because ancestors require this same ghost-field migration.
Keep the existing proofs; do not replace them with temporary admissions.

## Background
Storage observations are ghost bookkeeping on the actual source execution.
The current interpreter evaluates external defaults in the live entry state,
after value transfer and before argument binding, locking and body evaluation.
Constant evaluation contributes a trace prefix; entry failures and rollback
retain the observations already made. The producer definitions are supplied
and frozen; this task repairs their physical-property consumers.

## Domain Constraints
- Default tactic budget, checkpoints and proof steps remain enabled.
- No TRY/ORELSE around search, new admissions, axioms, timeout changes or
  strengthened hypotheses. Never call holbuild run/repl or Holmake.
- Do not restore the retired fresh-state evaluate_defaults API. Preserve live
  eval_external_defaults and current getter metadata/precompile semantics.
- Do not change oracle consumption, payload adoption, concrete execution or
  ghost event definitions. Generic proof transport must use the supplied
  result-side trace-insensitive relations, not new public assumptions.
- Finite storage preservation and compiler contracts are separate owner work.

## Available Resources
- semantics/prop/vyperStorageTraceScript.sml: frame/prefix/erasure algebra,
  shared unprefix and send_call_value helpers, all evaluator families.
- semantics/vyperInterpreterScript.sml: actual current traced external entry,
  live defaults, constants and load_contract projections.
- semantics/prop/vyperPlaceFramesScript.sml and
  semantics/prop/vyperStatePreservationScript.sml: ghost-aware physical frames.
- semantics/prop/vyperStorageBackendScript.sml: ghost-invariant storage reads
  and backend actions.
- semantics/prop/vyperTypeExprSoundnessScript.sml: runtime_consistent trace
  closure. TypeInvariants/TypeEnvPreservation contain other shared closures.
- semantics/prop/vyperCallOutcomeFrameScript.sml and Branches: approved
  trace-insensitive generic relation transport.
- semantics/prop/vyperTypeEntryReadinessScript.sml,
  vyperTypeContractSoundnessScript.sml, vyperTypeExternalCallMachineScript.sml
  and vyperLogPreservationScript.sml: current-base entry consumers.
- semantics/prop/vyperTypeEvalStoragePreservationScript.sml: independently
  meaningful legacy global-storage theorem; preserve its statements.

## Notes
The owner will check all frozen declarations, logs and exports after completion.
Do not edit owner tracking files or Alan state by hand.
