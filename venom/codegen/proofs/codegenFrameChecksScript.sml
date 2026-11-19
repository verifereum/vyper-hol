(* Focused frame API checks, independent of S7 and the legacy admission.
 * TOP-LEVEL: constructor/observation checks and a concrete fresh entry witness.
 * These do not claim that the witness program/context/plan were generated. *)
Theory codegenFrameChecks
Ancestors
  codegenCorrectness frameOutcome frameGas callTrace observableOracle stateEquiv
  stateFrame venomState venomInst venomExecSemantics codegenRel contextCodegenRel
  asmSem asmIR symbolResolve asmOracleRegression asmFrameCallStep stackPlanTypes stackPlanGen
  vfmExecution vfmExecutionProp vfmContext vfmState vfmConstants vfmOperation
  list finite_map words
Libs
  wordsLib

val _ = Parse.hide "cp";

(* Reuse the existing observable contract, rather than inventing another
   field-by-field frame relation. Abort contracts do not inspect state effects. *)
Theorem venom_frame_rel_observable_transport:
  observable_equiv s1 s2 ==>
  (venom_frame_rel es r es' (Halt s1) <=>
   venom_frame_rel es r es' (Halt s2)) /\
  (venom_frame_rel es r es' (Abort a s1) <=>
   venom_frame_rel es r es' (Abort a s2))
Proof
  Cases_on `a` >> simp[observable_equiv_def, venom_frame_rel_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem venom_frame_rel_constructor_cases:
  venom_frame_rel es r es' (Error msg) /\
  ~venom_frame_rel es r es' (OK vs) /\
  ~venom_frame_rel es r es' (IntRet ret vs) /\
  (venom_frame_rel es r es' (Abort Revert_abort vs) <=>
   (?lgs. frame_outcome es r es' (SOME Reverted) vs.vs_returndata lgs) /\
   frame_inst_raises es Reverted Revert) /\
  (venom_frame_rel es r es' (Abort ExHalt_abort vs) <=>
   ?exc lgs. exc <> Reverted /\ frame_outcome es r es' (SOME exc) [] lgs)
Proof
  simp[venom_frame_rel_def]
QED

Theorem venom_frame_rel_oracle_freedom:
  (venom_frame_rel es r es' (Halt (vs with vs_outcomes := os)) <=>
   venom_frame_rel es r es' (Halt vs)) /\
  (venom_frame_rel es r es'
     (Abort a (vs with <| vs_outcomes := os; vs_requests := rqs;
                         vs_logs := lgs; vs_accounts := accts;
                         vs_transient := ts |>)) <=>
   venom_frame_rel es r es' (Abort a vs))
Proof
  Cases_on `a` >> simp[venom_frame_rel_def]
QED

(* Single-frame constructor witnesses with arbitrary logs/output and the exact
   traced requests. The Revert witness requires an instruction raising Revert. *)
Theorem venom_frame_rel_single_constructor_witnesses:
  let start = es with contexts := [(ctxt with logs := [], rb)];
      post = es with contexts :=
        [(ctxt with <| returnData := out; logs := lgs |>, rb)];
      vs' = vs with <| vs_returndata := out; vs_logs := lgs;
                      vs_accounts := es.rollback.accounts;
                      vs_transient := es.rollback.tStorage;
                      vs_pending_deletions := es.rollback.toDelete;
                      vs_requests := call_requests start |>
  in
    venom_frame_rel start (INR NONE) post (Halt vs') /\
    (frame_inst_raises start Reverted Revert ==>
     venom_frame_rel start (INR (SOME Reverted)) post (Abort Revert_abort vs')) /\
    venom_frame_rel start (INR (SOME InvalidOpcode))
      (es with contexts := [(ctxt with returnData := [], rb)])
      (Abort ExHalt_abort vs')
Proof
  simp[LET_THM, venom_frame_rel_def, frame_outcome_def] >>
  qexists_tac `InvalidOpcode` >> simp[]
QED

Theorem venom_frame_rel_success_requests_and_logs:
  venom_frame_rel es r es' (Halt vs) ==>
  vs.vs_requests = call_requests es /\
  frame_outcome es r es' NONE vs.vs_returndata vs.vs_logs /\
  ~venom_frame_rel es r es'
    (Halt (vs with vs_requests := call_requests es ++ [rq]))
Proof
  simp[venom_frame_rel_def] >> rpt strip_tac >> simp[]
QED

Theorem venom_frame_rel_single_nonempty_logs_checked:
  es.contexts = [(ctxt, rb)] /\ ctxt.logs = [] /\
  es'.contexts = [(ctxt', rb')] /\ ctxt'.logs = [ev] ==>
  ~venom_frame_rel es (INR NONE) es' (Halt (vs with vs_logs := []))
Proof
  simp[venom_frame_rel_def, frame_outcome_def] >> rpt strip_tac >> gvs[]
QED

(* The opaque request/outcome lists are those from call_trace es; changing
   cc_gas is free. No ordinary Venom GAS = observed EVM reading equation. *)
Theorem initial_ctx_rel_trace_and_gas_boundary:
  initial_ctx_rel cp prog ctx vs es ==>
  vs.vs_outcomes = MAP SND (call_trace es) /\ vs.vs_requests = [] /\
  initial_ctx_rel cp prog ctx
    (vs with vs_call_ctx := vs.vs_call_ctx with cc_gas := gas) es /\
  ~initial_ctx_rel cp prog ctx (vs with vs_requests := [rq]) es /\
  ~initial_ctx_rel cp prog ctx
    (vs with vs_outcomes := MAP SND (call_trace es) ++ [outcome]) es
Proof
  simp[initial_ctx_rel_def, initial_state_rel_def, msg_ctx_rel_def,
       blockhash_rel_def, initial_codegen_state_rel_def, stack_params_rel_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* Saved snapshots cannot stand in for the live accounts (F5). This is a
   negative boundary check, not another selector-projection API. *)
Theorem saved_snapshot_cannot_replace_live_state:
  es.contexts = (ctxt, rb) :: rest /\
  (rb.accounts = vs.vs_accounts /\ es.rollback.accounts <> vs.vs_accounts \/
   rb.tStorage = vs.vs_transient /\ es.rollback.tStorage <> vs.vs_transient)
  ==> ~initial_ctx_rel cp prog ctx vs es
Proof
  simp[initial_ctx_rel_def, initial_state_rel_def] >> rpt strip_tac >> gvs[]
QED

Theorem initial_ctx_rel_empty_rejected:
  ~initial_ctx_rel cp prog (ctx with ctx_functions := []) vs es /\
  ~initial_ctx_rel cp prog ctx vs (es with contexts := [])
Proof
  simp[initial_ctx_rel_def]
QED

(* Concrete nonempty label map with a zero-sized trailing data header. *)
Definition frame_probe_prog_def:
  frame_probe_prog = [AsmOp "STOP"; AsmDataHeader "code_end"]
End

Definition frame_probe_fn_def:
  frame_probe_fn = mk_raw_function "entry"
    [<| bb_label := "entry";
        bb_instructions := [mk_inst 0 STOP [] []] |>]
End

Definition frame_probe_es_def:
  frame_probe_es = make_asm_call_state asm_oracle_initial 0w 100 0 []
                    (assemble frame_probe_prog) F
End

Definition frame_probe_vs_def:
  frame_probe_vs = init_venom_state "entry" with <|
    vs_code := assemble frame_probe_prog;
    vs_call_ctx := empty_call_context with cc_created_in_tx := T;
    vs_labels := FEMPTY |+ ("code_end", 1w) |>
End

Theorem frame_probe_encoding:
  assemble frame_probe_prog = [0w] /\
  SND (compute_label_offsets frame_probe_prog) = FEMPTY |+ ("code_end", 1) /\
  parse_code 0 FEMPTY [0w] = FEMPTY |+ (0, Stop)
Proof
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def]
QED

Theorem frame_probe_terminal_step:
  FST (step frame_probe_es) = INR NONE
Proof
  simp[frame_probe_es_def, frame_probe_encoding, make_asm_call_state_def,
       asm_oracle_initial_def, empty_call_context_def, make_sub_tx_def,
       vfmContextTheory.initial_context_def, initial_msg_params_def,
       step_def, handle_def, get_current_context_def, bind_def, return_def,
       step_inst_def, step_context_def, set_return_data_def,
       finish_def, fail_def, ignore_bind_def, handle_step_def,
       handle_exception_def, get_tx_params_def, set_current_context_def,
       reraise_def, FLOOKUP_UPDATE, vfm_abort_def, handle_create_def,
       get_return_data_def, get_output_to_def, get_num_contexts_def,
       empty_return_destination_def]
QED

Theorem frame_probe_trace:
  call_trace frame_probe_es = [] /\ gas_readings frame_probe_es = []
Proof
  mp_tac frame_probe_terminal_step >> Cases_on `step frame_probe_es` >>
  simp[] >> strip_tac >>
  simp[call_trace_def, gas_readings_def, frame_obs_def] >>
  conj_tac >> simp[Once frame_obs_tr_def, observe_def]
QED

Theorem initial_ctx_rel_fresh_nonvacuity:
  initial_ctx_rel (cp with <| cp_initial_fmp := 0; cp_regions := [] |>)
    frame_probe_prog (mk_venom_context [frame_probe_fn] (SOME "entry"))
    frame_probe_vs frame_probe_es
Proof
  simp[initial_ctx_rel_def, frame_probe_fn_def, mk_venom_context_def,
       frame_probe_vs_def, frame_probe_es_def, make_asm_call_state_def,
       asm_oracle_initial_def, frame_probe_encoding, frame_probe_trace,
       initial_state_rel_def, initial_codegen_state_rel_def,
       stack_params_rel_def, mk_raw_function_def, get_params_def,
       is_param_opcode_def, mk_inst_def, init_venom_state_def,
       context_memory_rel_def, context_spill_byte_def,
       msg_ctx_rel_def, tx_ctx_rel_def, block_ctx_rel_def, blockhash_rel_def,
       empty_call_context_def, empty_tx_context_def, empty_block_context_def,
       asm_to_tx_params_def, make_sub_tx_def, make_rollback_def,
       initial_msg_params_def, vfmContextTheory.initial_context_def,
       empty_return_destination_def, transfer_value_def, asm_pc_to_offset_def,
       wf_state_def, wf_context_def, all_accounts_def, wf_accounts_def,
       stack_room_ok_def, gas_stack_ok_def, outputTo_consistent_stack_def,
       outputTo_consistent_ctx_def, empty_accounts_def, stack_limit_def,
       context_limit_def, FLOOKUP_UPDATE, lookup_account_def,
       account_empty_def, empty_account_state_def, wf_account_state_def] >>
  simp[dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  gen_tac >> IF_CASES_TAC >> simp[]
QED

(* REVERT at entry, with an empty output slice and enough stack and gas. *)
Definition frame_revert_probe_prog_def:
  frame_revert_probe_prog = [AsmOp "REVERT"]
End

Definition frame_revert_probe_es_def:
  frame_revert_probe_es =
    (make_asm_call_state asm_oracle_initial 0w 100 0 []
       (assemble frame_revert_probe_prog) F) with contexts updated_by
      MAP (\(ctxt, rb). (ctxt with stack := [0w; 0w], rb))
End

Theorem frame_revert_probe_encoding:
  assemble frame_revert_probe_prog = [0xfdw] /\
  parse_code 0 FEMPTY [0xfdw] = FEMPTY |+ (0, Revert)
Proof
  conj_tac >- EVAL_TAC >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def]
QED

Theorem frame_revert_probe_step:
  step_inst Revert frame_revert_probe_es =
    (INR (SOME Reverted), frame_revert_probe_es with contexts updated_by
      MAP (\(ctxt, rb). (ctxt with stack := [], rb)))
Proof
  simp[frame_revert_probe_es_def,
       frame_revert_probe_encoding, make_asm_call_state_def,
       asm_oracle_initial_def, empty_call_context_def, make_sub_tx_def,
       vfmContextTheory.initial_context_def, initial_msg_params_def] >>
  simp[step_inst_def, step_return_def, pop_stack_def,
       memory_expansion_info_def, memory_expansion_cost_def,
       consume_gas_def, expand_memory_def, read_memory_def,
       set_return_data_def, revert_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def, return_def,
       assert_def, static_gas_def, FLOOKUP_UPDATE] >>
  simp[vfmBufferTheory.buffer_take_to_list]
QED

Theorem frame_revert_probe_raises:
  frame_inst_raises frame_revert_probe_es Reverted Revert
Proof
  rw[frame_inst_raises_def] >>
  qexistsl_tac [`frame_revert_probe_es`,
               `SND (step_inst Revert frame_revert_probe_es)`] >>
  simp[frame_revert_probe_step, frame_inst_at_step,
       frame_revert_probe_es_def, frame_revert_probe_encoding,
       make_asm_call_state_def, vfmContextTheory.initial_context_def,
       initial_msg_params_def,
       FLOOKUP_UPDATE]
QED

Theorem frame_revert_probe_run_frame:
  frame_raises frame_revert_probe_es Reverted
Proof
  irule frame_inst_raises_frame_raises >> simp[vfm_abort_def] >>
  qexists_tac `Revert` >> simp[frame_revert_probe_raises]
QED

Theorem venom_frame_rel_revert_nonvacuity:
  venom_frame_rel frame_revert_probe_es (INR (SOME Reverted))
    frame_revert_probe_es
    (Abort Revert_abort (init_venom_state "entry"))
Proof
  simp[venom_frame_rel_def, frame_revert_probe_raises,
       frame_outcome_def, frame_revert_probe_es_def,
       make_asm_call_state_def, vfmContextTheory.initial_context_def,
       init_venom_state_def]
QED

(* The caller has reserved the child's gas and has room for its result word. *)
Definition nested_frame_probe_def:
  nested_frame_probe reverting =
    let es = make_asm_call_state asm_oracle_initial 0w 100 0 []
      [if reverting then 0xfdw else 0xf3w] F in
    let (c,rb) = HD es.contexts in
      es with contexts :=
        [(c with stack := [0w; 0w], rb); (c with gasUsed := 100, rb)]
End

Theorem frame_return_probe_encoding[local]:
  parse_code 0 FEMPTY [0xf3w] = FEMPTY |+ (0, Return)
Proof
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def]
QED

Theorem nested_frame_probe_outcome:
  !reverting. ?pre es'.
    run_frame (nested_frame_probe reverting) =
      SOME (INR (if reverting then SOME Reverted else NONE),pre) /\
    LENGTH pre.contexts = 2 /\
    frame_outcome (nested_frame_probe reverting) (INL ()) es'
      (if reverting then SOME Reverted else NONE) [] [] /\
    LENGTH es'.contexts = 1 /\
    HD (FST (HD es'.contexts)).stack = b2w (~reverting)
Proof
  gen_tac >>
  qabbrev_tac `start = nested_frame_probe reverting` >>
  qabbrev_tac `exc = if reverting then SOME Reverted else NONE` >>
  qabbrev_tac `c = initial_context 0w [if reverting then 0xfdw else 0xf3w] F
    empty_return_destination
    (make_sub_tx asm_oracle_initial.as_call_ctx.cc_address 0w 0 100 [])` >>
  qabbrev_tac `rb = start.rollback` >>
  qabbrev_tac `parent = c with gasUsed := 100` >>
  `start.contexts = [(c with stack := [0w; 0w],rb); (parent,rb)]` by
    simp[Abbr `start`, Abbr `c`, Abbr `parent`, Abbr `rb`,
         nested_frame_probe_def, make_asm_call_state_def, LET_THM] >>
  qabbrev_tac `pre = start with contexts := [(c,rb); (parent,rb)]` >>
  `pre.contexts = [(c,rb); (parent,rb)]` by simp[Abbr `pre`] >>
  `?mr. empty_return_destination = Memory mr` by
    simp[empty_return_destination_def] >>
  pop_assum strip_assume_tac >>
  `c.msgParams.outputTo = Memory mr /\ c.returnData = [] /\
   c.gasUsed = 0 /\ c.msgParams.gasLimit = 100 /\ c.logs = [] /\
   c.stack = [] /\ c.pc = 0` by
    simp[Abbr `c`, vfmContextTheory.initial_context_def, initial_msg_params_def,
         make_sub_tx_def] >>
  `run_frame start = SOME (INR exc,pre)` by
    (irule run_frame_terminal_call >> simp[Abbr `exc`, vfm_abort_def] >>
     Cases_on `reverting` >>
     simp[Abbr `pre`, step_inner_def, get_current_context_def, bind_def, return_def] >>
     simp[Abbr `c`, vfmContextTheory.initial_context_def, initial_msg_params_def,
          frame_return_probe_encoding, frame_revert_probe_encoding, FLOOKUP_UPDATE] >>
     simp[step_inst_def, step_return_def, pop_stack_def,
          memory_expansion_info_def, memory_expansion_cost_def,
          consume_gas_def, expand_memory_def, read_memory_def, set_return_data_def,
          revert_def, finish_def, get_current_context_def, set_current_context_def,
          bind_def, ignore_bind_def, return_def, assert_def, static_gas_def] >>
     simp[vfmBufferTheory.buffer_take_to_list,
          vfmContextTheory.execution_state_component_equality,
          vfmContextTheory.initial_context_def, initial_msg_params_def,
          frame_return_probe_encoding, frame_revert_probe_encoding]) >>
  qabbrev_tac `settled = handle_exception exc pre` >>
  `FST settled = INL () /\ LENGTH (SND settled).contexts = 1 /\
   HD (FST (HD (SND settled).contexts)).stack = b2w (~reverting) /\
   (SND settled).txParams = start.txParams /\
   (reverting ==> (SND settled).rollback = rb)` by
    (Cases_on `reverting` >>
     simp[Abbr `settled`, Abbr `exc`, handle_exception_def,
          get_num_contexts_def, get_return_data_def, get_output_to_def,
          pop_and_incorporate_context_def, get_gas_left_def, pop_context_def,
          unuse_gas_def, push_logs_def, update_gas_refund_def, set_rollback_def,
          inc_pc_def, set_return_data_def, push_stack_def, write_memory_def,
          get_current_context_def, set_current_context_def, bind_def,
          ignore_bind_def, return_def, assert_def] >>
     simp[Abbr `pre`, Abbr `parent`, stack_limit_def]) >>
  `handle_exception exc pre = (INL (), SND settled)` by
    (Cases_on `settled` >>
     qpat_x_assum `Abbrev ((_,_) = _)`
       (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >> gvs[]) >>
  qexistsl_tac [`pre`, `SND settled`] >>
  simp[frame_outcome_def] >>
  Cases_on `reverting` >> gvs[Abbr `exc`, vfm_abort_def]
QED

(* A child can fail after an ordinary call pushes its frame, or during a
   precompile call that pushes and settles it in the same step. In both
   cases an ordinary continuation at the original depth stays in the run. *)
Theorem frame_probe_child_failure_continues:
  start.contexts <> [] /\
  RTC (\a b. LENGTH a.contexts >= LENGTH start.contexts /\
              step a = (INL (),b)) start current /\
  LENGTH start.contexts <= LENGTH current.contexts /\
  step_inner current = (INR (SOME exc),child_end) /\
  LENGTH start.contexts < LENGTH child_end.contexts /\
  handle_step (SOME exc) child_end = (INL (),next) /\
  LENGTH next.contexts = LENGTH start.contexts ==>
  run_frame start = run_frame next
Proof
  strip_tac >>
  `step current = (INL (),next)` by
    simp[step_eq_handle_step_inner, handle_def] >>
  irule run_frame_prefix >> simp[] >>
  `(\a b. LENGTH a.contexts >= LENGTH start.contexts /\
          step a = (INL (),b))^* current next` by
    (irule relationTheory.RTC_SINGLE >> simp[arithmeticTheory.GREATER_EQ]) >>
  metis_tac[relationTheory.RTC_TRANS]
QED

(* The identity precompile runs out of gas in the child created by the
   caller's instruction. The frame handler settles it and resumes the caller. *)
Theorem frame_probe_identity_precompile_failure:
  s.contexts = (child,rb)::(parent,prb)::rest /\
  child.msgParams.outputTo = Memory mr /\
  child.gasUsed = child.msgParams.gasLimit /\
  LENGTH parent.stack < stack_limit ==>
  dispatch_precompiles 4w s = (INR (SOME OutOfGas),s) /\
  ?t. handle_step_frame (SUC (LENGTH rest)) (SOME OutOfGas) s = (INL (),t) /\
      LENGTH t.contexts = SUC (LENGTH rest) /\
      HD (FST (HD t.contexts)).stack = 0w /\ t.rollback = rb
Proof
  strip_tac >> conj_tac
  >- simp[dispatch_precompiles_def, precompile_identity_def, get_call_data_def,
          consume_gas_def, get_current_context_def, bind_def, ignore_bind_def,
          return_def, assert_def, fail_def] >>
  `handle_step_frame (SUC (LENGTH rest)) (SOME OutOfGas) s =
   handle_step (SOME OutOfGas) s` by
    simp[handle_step_frame_def, handle_step_def, vfm_abort_def,
         get_num_contexts_def, bind_def, return_def] >>
  `handle_step (SOME OutOfGas) s = handle_exception (SOME OutOfGas) s` by
    (mp_tac (Q.INST [`e` |-> `SOME OutOfGas`, `t` |-> `s`,
      `child` |-> `child`, `child_rb` |-> `rb`, `tail` |-> `(parent,prb)::rest`]
      asm_handle_step_memory) >> simp[vfm_abort_def]) >>
  mp_tac (Q.INST [`exc` |-> `OutOfGas`, `s` |-> `s`, `child` |-> `child`,
    `child_rb` |-> `rb`, `parent` |-> `parent`, `parent_rb` |-> `prb`,
    `rest` |-> `rest`, `r` |-> `mr`] asm_handle_exception_memory_exception) >>
  simp[]
QED
