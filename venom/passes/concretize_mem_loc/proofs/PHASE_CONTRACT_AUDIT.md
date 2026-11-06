# Concrete phase / generic contract audit

Checkpoint C0.exception.contractaudit; source inspection, not a proved contract.
Baseline: account-reader certificates committed as 7b3d93630.

## Scope and proposed arguments

`framePhaseSimulationScript.sml:5-17` has **15** conjuncts. Its generic
finite induction is already implemented; it must not be duplicated.
Write E = `layout_phase_entry D lo vs0 C C' q0 es qs q` and
Q0 = `layout_phase_ok_abort D lo vs0 C C' q0 es qs q`.
The immediate entry candidate is A = `(\g s. T)`, R = E, hence
`indexed_entry A R g s t <=> E g s t`. This is an exact candidate,
not a theorem that all certificates hold.

Candidate BlockPair: corresponding source/target blocks of the selected
source function and its concretization, with identical label, instruction
index and PHI prefix correspondence. Candidate InstPair: selected source
instruction and the instruction fetched at the same target index (ALLOCA
rewritten, other opcodes unchanged). Existing concretizeStepStructure,
StepShape, StepRetpc and StepCallChecks are the canonical frozen owners of
rewrite facts. A fully quantified BlockPair must carry the selected function
witness, not accidentally relate arbitrary equal-label blocks.

Run cannot be E. It must be a separate function-entry relation (ordinary
mode only) carrying pre-PHI parameter roots, selected function pair and the
trace segment leading to the post-PHI point. PushRel must retain the paired
saved callers, actual invocation/argument/setup witnesses, ids/annotations,
return cursor and saved variable/control relations. Neither predicate has
been concretely assembled for these phase records.

## Contract coverage matrix

Names below are exact predicate arguments in phase_contract_def. All
unqualified layout_* names are in concretizeLayoutPhase*Script.sml under
this directory. A candidate theorem is not a proof of the whole row.

| Required predicate | Existing evidence / candidate instantiation | Residual hypotheses / missing integration | Owner |
|---|---|---|---|
| indexed_outcome_shape Q | Q0 has only OK/OK and Abort/Abort branches (PhaseOrigin:108-115). | Full Q must add paired Halt and paired IntRet and reject Error/mixed constructors. | C0.exception / frames.instantiate |
| indexed_ok_exit A R Q | layout_phase_ok_origin gives E h s t from Q0 g h (OK s) (OK t). | Retain this implication in full Q; normalized ready state is not the unnormalized pending state. | C0.exception |
| indexed_base A R InstPair Q | layout_calldata_reader_trace_step (PhaseReaders), layout_returncopy_trace_step (PhaseTrace), layout_state_read_trace_step and layout_state_write_trace_step (PhaseStorage), layout_returndatasize_trace_step, layout_balance_reader_trace_step, layout_extcodesize_trace_step. layout_stop_sink_halt returns dead_result_rel directly. | These require ready ordinary entry, selected config/trace event, source shape, source success and lookup. Need dispatch from arbitrary indexed_entry, all non-Error source constructors, ALLOCA pairing and all opcodes. Exempt-copy whole-block Abort is NOT a base-step certificate. | local.owneddispatch; local.externalowned; local.observationexit; local.returndatacopyowned.exempt.certificate |
| phase_push C C' A R Run InstPair PushRel | disciplined_invoke_setup_roots (LayoutCalleeRoots), parameter_roots_setup_callee (LayoutParameterRoots), paired_setup_control (LayoutCallControl), relocation_environment_setup_callee (LayoutFrameEnvironment); activation_lookup_push. | Target argument evaluation/setup, callee trace/id/annotation advancement, local memory/Obs0/supplement preservation, saved target caller witness, actual Run entry. Joint call edge includes enters_block; generic phase_push requires pre-PHI setup state cs/ct, so an intermediate run-entry interface is essential. | frames.instantiate |
| indexed_pop A R Q PushRel | paired_return_values, return_binding_control, paired_return_next_control (LayoutCallControl); relocation_environment_return_plumbing (LayoutFrameEnvironment). | Given Q c d (IntRet ret post) (IntRet ret' post'), target bind_outputs must succeed and restored callers must satisfy full OK relation. Must carry return values/length, NONE adopted FMP (DRET excluded), saved variables and future memory demand, merged Obs0/supplement, OriginResume cursor, restored ids/annotations. Existing plumbing only proves environments/control, not these obligations. | frames.instantiate |
| indexed_call_exit A R Q PushRel | Abort Q0 ignores ghosts; direct Halt observation can also ignore ghosts. | Reindex terminal outcomes from callee c to caller g. Cannot impose callee/caller origin equality for Halt/Abort. | frames.instantiate |
| indexed_lookup A R BlockPair InstPair | canonical StepStructure and StepShape correspondence facts. | Discharge selected-function/block/index alignment and terminator equality for both ordinary and terminal modes; E alone does not identify the externally quantified bb unless BlockPair supplies the right witness. | frames.instantiate / local.owneddispatch |
| indexed_admin_entry A R Admin | layout_phase_ready_entry, layout_ordinary_administrative (PhaseCompose), layout_terminal_administrative (PhaseOrigin). | Candidate Admin is identity OR h-to-layout_phase_ready h with state normalization by old pending flag. Need explicit predicate and universal certificate; entry normalization alone does not define Admin. | C0.exception / frames.instantiate |
| indexed_admin_refl Admin | Include identity branch in candidate Admin. | State this branch for *all* ghosts/states, not only pending entries. | C0.exception |
| indexed_splice Q Admin | layout_phase_ok_abort_splice and layout_phase_ready_begins (PhaseCompose); layout_phase_ok_origin (PhaseOrigin). | Existing splice is unnormalized Q0 composition. Need normalized middle-entry transport plus full-Q splice including IntRet. No target-execution induction is needed here. | C0.exception / frames.instantiate |
| indexed_halted Q | Current ordinary E includes Obs0 through local_rel; Obs0 compares vs_halted. | Q0 OK also permits terminal entry, which only gives domains/labels/corridor, not halted equality. Need derive/exclude terminal OK cases or strengthen the future terminal interface consistently. | C0.exception |
| indexed_halt Q | layout_stop_sink_halt and concretize_supplement_halt_exit (LayoutHaltExit). | Certificate applies to *any* Q OK with source halted, not just an explicit STOP premise. Requires final_taint evidence or proof halted OK unreachable. Existing Q0 has no Halt branch at all. | local.observationexit / C0.exception |
| indexed_increment A R BlockPair InstPair Q Admin | PhaseCompose ready normalization, with pending post index increment; PhaseSuccess constructs pending ordinary successor. | Show pending flag and post.idx=source.idx at all nonterminating base/call producers; terminal corridor uses its own progress. Candidate identity branch handles cases without administrative change only when actual cursor update agrees. | C0.exception / frames.instantiate |
| phase_phi_prefix Run A R BlockPair Q | resolved_parameter_segment (LayoutParameterSegments), resolved_call_parameter_step (LayoutParameterSteps); frameRelocationPhi parallel-PHI boundaries; source origin initialization (PhaseOrigin). | Need actual target PHI execution, annotations and trace selection, Run-to-post-PHI E, and universal Q prefix transport. Origin reset and full-Q prefix transport are NOT discharged by an ordinary local producer. | frames.instantiate |
| phase_block_return C C' Run BlockPair Q | layout_phase_terminal_origins and layout_terminal_origin_exclusion (PhaseOrigin), generic phase_terminal_origins interfaces; source call-prefix no-normal evidence. | Restore ordinary function Run only after completed finite_block OK; must not infer Run from every intermediate E. Need jump/next-block trace/PHI boundary. Endpoint terminal exclusion relies on begins/origin matching actual block entry. | frames.instantiate / C0.exception |

Abbreviated owner prefix `local` = C0.relocation.consumers.producers.local;
`frames` = C0.relocation.consumers.producers.frames.

## Outcome constructors actually provided

| Outcome | Checked producer | What it establishes; what it does not |
|---|---|---|
| OK | PhaseReaders (CALLDATALOAD/CALLDATASIZE), PhaseStorage (SLOAD/TLOAD/SSTORE/TSTORE), PhaseReturndataSize, PhaseAccountReaders (BALANCE/SELFBALANCE/EXTCODESIZE), PhaseTrace (ordinary nonexempt RETURNDATACOPY) | Actual target base success and Q0 pending successor; current guarded values, demand, Obs0, supplement and environments. Not full indexed_base dispatch. |
| Abort | layout_returncopy_phase_block_abort (PhaseExceptional), layout_pending_returncopy_block_abort (PhaseCompose) | Actual target **exec_block** Abort and Q0 on whole-block outcomes. Not step_inst_base matching with a successor entry. |
| Abort | concretize_invalid_complete, concretize_revert_complete, concretize_static_write_abort_complete (LayoutLocalTerminals), concretize_returncopy_bounds_abort_complete (LayoutLocalReturnCopy) | Local target execution/dead_result_rel. Need phase dispatch and equal Abort tag packaging. |
| Halt | layout_stop_sink_halt (PhaseHalt) | Target step_inst and task-mask dead_result_rel from final_taint + supplement. Does not add a Halt constructor to Q0. |
| Halt/OK SELFDESTRUCT | existing LayoutLocalSelfdestruct boundaries | Existing semantic facts must be adapted through final/request observation; no full phase certificate is claimed. |
| IntRet | paired_return_values (LayoutCallControl), opaque_return_token_step (frameRelocationOpaque) | Paired RET execution if front values are already LIST_REL Rel; excludes final return-PC token; iret_adopt_fmp=NONE. Does not prove the front relation or saved-caller restoration. |
| RETURN / external CALL/STATICCALL/DELEGATECALL/CREATE/CREATE2 | Search in task proof theories found no owned LayoutLocal* complete producer for these families. | Old concretizeMemLocProofs return/call lemmas use its older invariant; not a proof of current Obs0/supplement/trace contracts. Their integration remains the existing owners' task, not this audit's implementation authority. |

## Proposed full outcome interface (specification only)

Use a **separate** Q, not an edit to the checked partial relation. Its exact
constructor schema should be:

```
Q g h (OK s) (OK t)       <=> OKScope g h /\ Efull h s t
Q g h (Abort a s) (Abort b t) <=> a = b /\ dead_result_rel D (Abort a s) (Abort b t)
Q g h (Halt s) (Halt t)   <=> dead_result_rel D (Halt s) (Halt t)
Q g h (IntRet ir s) (IntRet jr t) <=> RetState h ir jr s t
Q g h r r'               <=> F          [all remaining constructor pairs]
```

Here OKScope, Efull and RetState are explicit **unimplemented interface
parameters**, not established invariants or new assumptions available to
proofs. Required embedding:
`Q0 g h r r' ==> Q g h r r'`. For ordinary OK, Efull must include E;
for a corridor extension it must instead give a valid exceptional entry
which survives ASSIGN progress. RetState must supply a ready ordinary
callee endpoint and local memory/Obs0/supplement/environment facts, matching
source trace and saved-frame annotations, equal-length returned value
lists related strongly enough to bind caller outputs, and adopted-FMP
compatibility. A likely specialization is ir.iret_values=jr.iret_values
and both adopted FMPs NONE: fn_ptr_ok excludes DRET and ptr_use_ok/taint_ok
exclude pointer/tainted RET operands. That specialization is **not proved**
by paired_return_values, which takes LIST_REL as a premise. Opaque final
return-PC tokens must never be compared as returned values.

RetState's required consuming law is exactly indexed_pop_def: with a
PushRel witness and a successful source bind into adopt_return_fmp of
merge_callee_state, obtain a successful target bind and Q OK on restored
callers. Giving only dead_result_rel on IntRet is both insufficient and
literally false under dead_result_rel_def's wildcard branch. No proposed
RetState law may simply assume its final caller OK conclusion as data.

## Architectural mismatches to settle before implementation

1. **Exempt-copy granularity.** indexed_base is an instruction boundary;
   current exempt integration consumes a whole block atomically. Successful
   exempt copy need not preserve ordinary memory demand. Existing terminal
   entry additionally requires revert_forward_at at its normalized cursor;
   an intermediate ASSIGN cursor need not satisfy it. Therefore the checked
   atomic consumer cannot close indexed_base. No number of additional
   ordinary opcode adapters repairs this. Need a validated corridor entry
   that survives intermediate steps, or a separately justified block-level
   integration design. Do not infer a stronger driver from the current one.
2. **Origin and run prefix.** Setting OKScope to origin equality embeds Q0,
   but phase_phi_prefix requires `!d r r'. Q h d r r' ==> Q g d r r'`.
   Resetting h's origin for a new block while keeping g's old origin makes
   that universal OK clause unavailable. Conversely retaining the old
   origin cannot be used as evidence that a terminal suffix originated at
   the new block's PHI-prepared state. The run/block scope interface needs
   a definition probe, not blind reuse of Q0's equality in a full Q.
3. **Halted OK.** terminal_entry only contains corridor/domain/label facts;
   unlike ordinary E, it does not compare vs_halted. Full indexed_halted
   and indexed_halt need actual invariants, not constructor case-splitting
   on Q0 alone. This is an interface gap, not a counterexample to the TASK.
4. **RET is not RETURN.** paired_return_values concerns internal RET and
   requires an input value relation. RETURN is a memory-reading Halt and
   needs final dead-return-mask conversion. Neither gives the other's case.
5. **Source trace is post-PHI.** joint_transition_call has enters_block,
   whereas phase_push concludes Run at setup_callee states. OriginResume
   similarly includes caller increment/next active instruction. These
   mismatches require explicit pre/post administrative boundaries.

Recommended next bounded semantic/interface checkpoint: validate a terminal
corridor mode with source-origin no-normal evidence preserved through an
ASSIGN step and its administrative increment, and expose how it supplies
instruction-level indexed_base/ok_exit without asserting revert_forward_at
at intermediate cursors. In the same architectural review settle whether
the full Q needs separate run/block scope metadata for PHI prefix transport.
Do not implement this proposal until the strategist assigns its owner and
approach. RETURN/external producers remain with observationexit/externalowned;
IntRet/pop and Run initialization remain with frames.instantiate.

## Checked builds

`holbuild` succeeded for framePhaseSimulationTheory,
concretizeLayoutPhaseComposeTheory, concretizeLayoutPhaseHaltTheory,
concretizeLayoutPhaseStorageTheory, concretizeLayoutPhaseAccountReadersTheory,
concretizeLayoutPhaseReturndataSizeTheory and concretizeLayoutPhaseReadersTheory.
Evidence: TO_concretize_sim-20261105T171004Z_m14069_t001; revalidated in
TO_concretize_sim-20261105T171004Z_m14097_t001 (all seven requested roots clean).

Signature checks: frameIndexedCertificatesScript.sml:10-29,47-63 for
shape/exit/base/pop/call-exit; framePhaseCertificatesScript.sml:42-90 for
PHI prefix, push and block return; framePhaseSimulationScript.sml:5-17 for
the complete matrix. Concrete Q0 and entry checked at
concretizeLayoutPhaseOriginScript.sml:70-115. Storage write export verified
by source theorem search (TO_concretize_sim-20261105T171004Z_m14100_t001).
The proposed schema is intentionally not a completed instantiation: the
universal prefix, intermediate corridor and halted-OK obligations above
remain unvalidated design gates. This diagnostic establishes coverage and
missing interfaces, not impossibility of the generic driver or the TASK.

No frozen source modified, no new proof axioms/cheats, no final assembly attempted.
