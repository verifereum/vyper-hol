# Issue #570: event proof scope and pre-existing limitations

## Result

The event/type endpoints and the two Log branch theorems below are kernel-closed.
The public compiler call theorem has pre-existing admissions. Closing unrelated
S1–S7 or deployment admissions is outside #570 and is not a completion requirement
for this issue.

The owner's scope clarification is authoritative: correct typed event topics,
enforce event declarations and Log checking, prove affected Log lowering,
remove the specified event whitelist restrictions, and run affected proof and
parity/mutation checks. Additional helpers need a concrete use in the Log proof.
Argument expression correctness may appear as an induction hypothesis in that
proof; #570 does not require a general expression-verification campaign.

Reproduce: build `eventEndpointAuditTheory` (tests/eventEndpointAuditScript.sml).
It prints `Tag.dest_tag (Thm.tag th)` plus axiom/hypothesis counts from actual
saved theorem objects, including cached dependencies. DISK_THM is bookkeeping;
`cheat` is an admission. The check asserts clean tags for selected event/type
theories, but deliberately only REPORTS the unresolved compiler endpoints.
This is an inventory, not a proof alias or admission-hiding certification.

## Endpoint selection

Rebuild the affected e2e and type-soundness proofs, and prove the affected Log
obligations without supported_log or new admissions. The inventory below also
records unrelated, pre-existing admissions; those are limitations, not extra work.

* `e2eDefs`: all saved theorems, including typed topic characterization and
  `log_entry_equiv_concrete_event`. All inspected tags: DISK_THM only, no axioms
  or hypotheses. Target `e2eDefsTheory`.
* `vyperEventSoundness.checked_log_encoding_success` and its four boundary
  theorems: clean, target `vyperEventSoundnessTheory`.
* `vyperTypeEvalSoundness.eval_all_type_sound_mutual`: clean. It includes the
  changed Log branch. Target `vyperTypeEvalSoundnessTheory`.
* All saved objects in `vyperTypeSoundness`, `vyperTypeContractSoundness`,
  `vyperTypeInitialState`, `vyperTypeStmtSoundness`, `vyperTypeCallSoundness`:
  clean tags, zero axioms/hypotheses. These include public
  `typed_stmts_no_type_error`, `typed_expr_success_preserves_type`, and
  `checked_call_external_no_type_error`. Respective `...Theory` targets.
* `e2eCorrectness.e2e_vyper_to_evm` (ACTIVE declaration at lines 208-240): clean
  composition theorem, but its premises explicitly assume source execution,
  context transformation and codegen simulation. It does not discharge those
  premises from successful compilation. Cannot replace the next endpoint.
* `e2eCorrectness.vyper_call_correct` (ACTIVE lines 727-780): public compilation
  to execution endpoint, tagged cheat. Its statement assumes successful
  compile_vyper, supported_program, source_typing_ok, source_storage_ok,
  call_state_rel, valid_vyper_call and call_outcomes_ok; concludes actual run_call
  with resource/precompile starvation or call_result_rel. Target
  `e2eCorrectnessTheory`.
* `e2eCorrectness.e2e_deploy_correctness` (ACTIVE lines 859-894): independently
  directly admitted, tagged cheat. This is a pre-existing limitation outside
  #570, not an ancestor of vyper_call_correct.

The same files retain large INACTIVE commented legacy theorem archives. Grep
hits there are not extra saved endpoints/admissions. Tag checks select saved
objects, not archive text. The uncompiled legacy names must not drive scope.

## Pre-existing admitted frontier of public call correctness

Each row is a direct logical use in the ACTIVE vyper_call_correct proof, not
merely a theory import. Every root's saved tag includes cheat, with no axioms
or hypotheses. Statements are retained verbatim at the cited source ranges;
notation below summarizes them, not a proposed weakening.

| Root | Statement location; admission | Use in endpoint | Classification |
|---|---|---|---|
| S1 `vyperLoweringCorrect.lower_vyper_runtime_unit_correct` | lowering/vyperLoweringCorrectScript.sml:165-179; cheat:178 | e2eCorrectnessScript.sml:763-765 | required endpoint prerequisite; includes direct Log simulation |
| S2 `vyperLoweringCorrect.lower_vyper_runtime_unit_source_unit_ok` | same:183-189; cheat:188 | :747 | required endpoint structural prerequisite |
| S3 `vyperLoweringCorrect.lower_vyper_runtime_unit_memory_ok` | same:194-208; cheat:207 | :772 | required endpoint memory prerequisite |
| S4 `o1PipelineCorrect.run_venom_pipeline_correct` | venom/compiler/o1PipelineCorrectScript.sml:28-37; cheat:36 | :773 | required endpoint optimizer simulation prerequisite |
| S5 `o1PipelineCorrect.o1_pipeline_memory_obligations` | same:48-60; cheat:59 | :774 | required endpoint transformed memory/reachability prerequisite |
| S6 `o1PipelineCorrect.run_venom_pipeline_output_shape` | same:70-76; cheat:75 | :748 | required endpoint output shape prerequisite |
| S7 `codegenCorrectness.codegen_correct` | venom/codegen/codegenCorrectnessScript.sml:370-385; cheat:384 | :778 | required endpoint EVM/codegen prerequisite |

S1 asserts source_unit_execution_correct from successful runtime lowering,
supported_program, source typing/storage/deployment relations, a valid call,
initial_venom_state_rel and the actual outcome supply. Its conclusion means an
existential fuel yielding external_call_result_rel, including logs, accounts,
transient storage, returndata and requests (same file:137-158).

S2 asserts o1_source_unit_ok from successful lowering and supported_program.
S3 adds the S1 entry hypotheses and non-source-exemption and concludes
raw_unit_memory_ok. S4 transports this raw context through the actual O1 hook
under source-unit/initial-state/memory obligations. S5 uses those obligations
plus generated context plan and matching initial FMP to construct Inv satisfying
codegen_memory_obligations and codegen_reachability_package. S6 produces
unit_shape_ok of the pipeline output. S7 converts a run_context result at any
fuel to an actual run_call result with the stated starvation alternatives or
venom_frame_rel, under codegen shape, context, reachability and entry relations.

These seven are the first admitted frontier, not seven proved subresults.
Their direct cheats terminate the *current* logical dependency trace: it would
be incorrect to report every imported expression/ABI/pass admission as an
additional actual ancestor of S1/S4. Proving these stages will expose new
strict prerequisites, which then require their own inventory/decomposition.

Deployment's independent root states agreement of compiled creation with
load_contract NONE on [(NONE,tops)], installation of runtime_bc, accounts,
transient storage and logs, with explicit failure/starvation/strictness cases;
see the complete statement at e2eCorrectnessScript.sml:859-891. No replacement
from just runtime Log simulation is apparent.

## Direct Log infrastructure versus actual current admitted ancestors

E0007/E0008's negative interface diagnosis is confirmed by source and saved tags:

* `exprLoweringProps.compile_expr_correct`, lowering/exprLoweringPropsScript.sml
  :106-128 (cheat:127), concludes eval_operand = val_to_w256 v and run_inst_seq,
  same_blocks, frame/freshness. This untyped scalar representation is NOT the
  typed bytes20/aggregate-pointer representation required by Log. Its current
  admission is not consumed by S1's `cheat`; a proved typed replacement can avoid
  using this theorem altogether. Do not prove its wrong-shaped interface merely
  because the theory is imported.
* `stmtLoweringProps.compile_stmt_correct` :87-96 (cheat:95), and
  `compile_stmts_correct` :99-108 (cheat:107), claim successful source evaluation
  yields frag_exec preserving state_rel. These pre-existing general statement
  admissions remain. The new checked Log branch proofs below establish the
  affected local simulation separately; they do not discharge S1 or certify the
  public call endpoint.
* `abiEncoderProps.compile_abi_encode_to_buf_correct`,
  lowering/abiEncoderPropsScript.sml:412ff, has saved cheat provenance; unresolved
  Resume cases:708-736. It requires single_block_enc_info, typed val_in_memory,
  memory bounds, freshness and non-overlap/layout hypotheses. Dynamic-element
  arrays are excluded by single_block_enc_info (:382-389). It is therefore not
  the complete Log ABI boundary for the required dynamic aggregates. A framed,
  control-flow-aware replacement is now used by the Log proofs: recursive
  `abiNativeEncoding` and `typedCopyComplete` prove the actual encoder and
  widening copies, including arrays, tuples, structs and byte/string values.
  The Log proof does not use the admitted encoder theorem.
* The new argument-code, split, topic and data-packing proofs execute the actual
  `compile_log_eval_all`, `split_log_ops`, `compile_log_topic_ops` and
  `compile_log_store_data` definitions.

## Proved Log branches

* `checkedLogEmptyExecution.checked_compile_log_empty_execution` proves the
  indexed-only branch, including real argument evaluation, topic production,
  native LOG execution, authoritative source event encoding and the complete
  `state_rel` after the source log append.
* `checkedLogDataExecution.checked_compile_log_data_execution` proves the
  nonempty-data branch, including real argument evaluation, both actual buffers,
  compatible recursive packing, ABI encoding, topics, LOG and the source append.

Both are local statement-simulation theorems. Their premises state the checked
single-module contract and Log typing, actual compiler cuts and function code,
source/native entry relations, allocation/profile bounds, and the per-expression
`log_argument_lowering` induction contract. They assume neither whole-Log native
execution nor successful execution of the saved argument prefix. They do not use
`supported_log`. They retain the explicit resource and code-embedding invariants
needed to execute a compiled fragment; establishing a whole function's entry and
expression invariants belongs to the pre-existing S1 frontier.

The supporting bridges have specific Log obligations:

* `checkedLogMetadata` derives actual lowered argument compatibility and indexed
  field admissibility from the checker.
* `checkedLogValues` transports existing source type soundness to declared event
  field values; `checkedLogDataEncoding` derives conversion success and the
  actual compiler buffer's ABI length bound.
* `logArgumentCodeExecution` derives and executes the real argument plan using
  the expression induction contract. The list and snapshot proofs establish the
  saved argument prefix rather than assuming it.
* `logArgumentLogSafety` proves that source-backed or snapshot-backed arguments
  cannot overlap the actual payload allocation, and bounds indexed-only reads.
  `logArgumentLogResources` obtains the buffer and encoder-scratch budget from
  the argument evaluator's concrete reservation profile.
* `checkedLogEmpty` and `checkedLogData` connect the saved-argument suffix to the
  checker-resolved source event and complete source state.

Every new theory checks its saved theorem tags for `DISK_THM` only, zero axioms
and zero hypotheses. `eventEndpointAuditTheory` imports and repeats that check
for both complete Log branch theories, while retaining report-only diagnostics
for the unrelated compiler admissions above.

Only infrastructure actually consumed by the focused Log theorem belongs in
the #570 proof change. Whole-runtime dispatch, decoding, returns, internal calls,
non-Log statements, S2–S7 and creation correctness remain outside this issue.

## Scope boundary

Unrelated pass theorems, retired codegen_correct_legacy, S1–S7 and deployment
admissions do not become #570 obligations by appearing in an import or endpoint
dependency graph. Do not expand this task to close them.

Retain typed representation, argument snapshot, split, topic and recursive ABI
helpers only where the Log proof concretely needs them. Compose expression-level
induction hypotheses with actual Log evaluation, encoding and emission; do not
prove every expression constructor as an additional task. Report the pre-existing
admissions separately from the affected Log proof and required test results.

The unrelated `Empty` construction and zero-word ordering changes from the
earlier expression campaign were removed; their original files and proof code
are preserved in the scope-cleanup archive. The #560 validation dependencies
remain outside this fix.

The fixed-array widening parity fixture requires the corrected deep-DUP restore
order, which current main already contains. The remaining schedule factoring is
behavior-preserving. The unique input/reorder/block and LOG simulation proofs
are retained: they have no equivalent fallback. Duplicated allocator and prefix
proofs derive from their stronger shared lemmas instead. These proofs do not
close the pre-existing S7 admission.

After integrating #551, native Log and shared encoder proofs reuse the same raw
leaf execution and generative member recursion; see
`lowering/ABI_ENCODER_REUSE_PROPOSAL.md`. The native static and mixed traversals
and the shared member spine retain their existing statements. Their distinct
resource, frame and execution-path guarantees are not discarded to force an
endpoint alias. Unconsumed deployment, optimizer and representation probes and
unused expression/name/store extensions were removed; concrete codegen
regressions and unique correctness lemmas remain.

## Focused validation

The complete focused run passed in 2836.673 seconds with normal caches and
checkpoints enabled:

```sh
holbuild -j1 --maxheap=16384 build --tactic-timeout 2.5 \
  eventEndpointAuditTheory evalCompilerEventParityTheory \
  eventEncodingPropsTheory eventTopicPropsTheory eventTopicExecPropsTheory \
  eventBytecodeEvalChecksTheory vyperEventWhitelistTheory \
  supportedProgramPropsTheory deepDupChecksTheory
```

The endpoint audit reported 150 saved endpoints. Both complete Log branch
theorems and `eval_all_type_sound_mutual` have `DISK_THM` only, no axioms and no
hypotheses. The 13 cheat-tagged entries are the pre-existing compiler, general
statement/expression and encoder limitations inventoried above.

All seven exact deployment/runtime bytecode fixtures passed: indexed bytes20,
storage bytes20, dynamic-array widening, nested-string widening, tuple widening,
fixed arrays of dynamic arrays, and the forward-declared nested struct. The
rollup also checks actual argument-lifetime and forward-struct LOG execution and
audits every saved event fixture theorem for admissions.

The certified checker rejects e11, `DUP_EVENT`, `MISMATCH`, `UNDECLARED` and `ARITY`
in both deployment modes. The e62, m14 and m49 imported-event projections are
rejected on the single-module input in both modes. The specified accepted corpus,
including `IDX4`, `DUP_FIELD`, `LOG_VIEW` and `LOG_PURE`, retains its planned
acceptance. Event whitelist regressions, evaluator-certificate checks and the
deep-DUP physical assembly checks also pass.

The provided `~/vyper` checkout was verified at VYPER_PIN
`cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c`, including all 204 installed compiler
Python/interface sources. Its provided Python 3.14.4 binary reproduced all seven
frozen deployment/runtime bytecode pairs. Eight sanitized AST/layout inputs were
identical; the two builtin-interface inputs differed only in Python installation
path strings. Frozen fixtures and their Python 3.11 provenance were not
regenerated, and exact reproduction of that legacy dependency environment is not
claimed.

## Post-merge consolidation validation

After integrating #551, the following build passed with no CHEAT warnings.
The full dependency rebuild finished in 3702.686 seconds; the final cached
recheck, including the explicit codegen and trimmed-helper targets below,
finished in 2.417 seconds. The 10-second tactic contract accommodates the
existing dependency cache; no proof-step or goal-fragment checks were skipped.

```sh
holbuild -j4 --maxheap=8192 build --tactic-timeout 10 \
  abiEncoderPathPropsTheory abiNativeEncodingTheory abiEncoderReuseAuditTheory \
  eventEndpointAuditTheory evalCompilerEventParityTheory \
  eventBytecodeEvalChecksTheory vyperEventWhitelistTheory \
  supportedProgramPropsTheory deepDupChecksTheory logFrameChecksTheory \
  doSwapSimTheory operandInventoryTheory reorderSimTheory genBlockSimTheory \
  allocationSpillChecksTheory nameLoweringPropsTheory nameValueCodeTheory \
  localValueStorePropsTheory loweringShapePropsTheory
```

The merge had left the shape proof using the pre-snapshot Log evaluator and
pre-declared-layout data-store APIs; their proofs now compose the actual
compiler actions without changing their statements. The retained concrete LOG
trace regression converts its byte-list memory to the current EVM buffer type
at the state-construction boundary. The member-phase global frame derives from
the existing stronger leaf frame rather than unfolding instruction semantics.

## Whitelist validation baseline

The focused `vyperEventWhitelistTheory` regressions pass after removing the
event guards. The checker mutation and single-module imported-event regressions
also pass. `supportedStmtPropsTheory` stops earlier at the unchanged
`supported_target_exclusions` row: it rejects tuple/array local assignments even
though the unchanged `supported_assignment` predicate admits supported value
types there. This non-event baseline failure is recorded separately; assignment
semantics are outside #570. The affected Log row has the new checker-owned
expectations, and the focused event theory tests those expectations independently.

Evidence: successful audit builds TO_TASK-L0008-20261023T125855020112Z_m0022_t001
and TO_TASK-L0008-20261023T125855020112Z_m0035_t001; exact initial tag report
TO_TASK-L0008-20261023T125855020112Z_m0025_t001; additional representation/ABI
tag report TO_TASK-L0008-20261023T125855020112Z_m0036_t001.
