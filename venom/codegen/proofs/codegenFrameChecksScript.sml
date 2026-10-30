(* Focused frame API checks, independent of S7 and the legacy admission.
 * TOP-LEVEL: constructor/observation checks and a concrete fresh entry witness.
 * These do not claim that the witness program/context/plan were generated. *)
Theory codegenFrameChecks
Ancestors
  codegenCorrectness frameOutcome callTrace observableOracle stateEquiv
  stateFrame venomState venomInst venomExecSemantics codegenRel contextCodegenRel
  asmSem asmIR symbolResolve asmOracleRegression stackPlanTypes stackPlanGen
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
   ?lgs. frame_outcome es r es' (SOME Reverted) vs.vs_returndata lgs) /\
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

(* Nonvacuity for all three terminal constructors, with arbitrary nonempty
   emitted logs/output and the EXACT traced requests, not a fabricated oracle. *)
Theorem venom_frame_rel_single_constructor_witnesses:
  let start = es with contexts := [(ctxt with logs := [], rb)];
      post = es with contexts :=
        [(ctxt with <| returnData := out; logs := lgs |>, rb)];
      vs' = vs with <| vs_returndata := out; vs_logs := lgs;
                      vs_accounts := es.rollback.accounts;
                      vs_transient := es.rollback.tStorage;
                      vs_toDelete := es.rollback.toDelete;
                      vs_requests := MAP FST (call_trace start) |>
  in
    venom_frame_rel start (INR NONE) post (Halt vs') /\
    venom_frame_rel start (INR (SOME Reverted)) post (Abort Revert_abort vs') /\
    venom_frame_rel start (INR (SOME InvalidOpcode))
      (es with contexts := [(ctxt with returnData := [], rb)])
      (Abort ExHalt_abort vs')
Proof
  simp[LET_THM, venom_frame_rel_def, frame_outcome_def] >>
  qexists_tac `InvalidOpcode` >> simp[]
QED

Theorem venom_frame_rel_success_requests_and_logs:
  venom_frame_rel es r es' (Halt vs) ==>
  vs.vs_requests = MAP FST (call_trace es) /\
  frame_outcome es r es' NONE vs.vs_returndata vs.vs_logs /\
  ~venom_frame_rel es r es'
    (Halt (vs with vs_requests := MAP FST (call_trace es) ++ [rq]))
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

Theorem initial_ctx_rel_empty_and_static_rejected:
  ~initial_ctx_rel cp prog (ctx with ctx_functions := []) vs es /\
  ~initial_ctx_rel cp prog ctx vs (es with contexts := []) /\
  ~initial_ctx_rel cp prog ctx vs
    (es with contexts :=
      [(ctxt with msgParams := ctxt.msgParams with static := T, rb)])
Proof
  simp[initial_ctx_rel_def]
QED

(* Nested success returns to the parent, with short-write splice and combined
   logs. Failure restores the child's saved rollback and leaves parent logs.
   No run_call correctness is assumed to construct these relation witnesses. *)
Theorem venom_frame_rel_nested_constructor_witnesses:
  let child = ctxt with msgParams := ctxt.msgParams with outputTo := Memory mr;
      start = es with contexts := [(child, rb); (parent, prb)];
      ok = parent with <|
        returnData := out; stack := 1w :: parent.stack; pc := SUC parent.pc;
        logs := parent.logs ++ (child.logs ++ lgs);
        memory := buffer_write mr.offset (TAKE mr.size out) parent.memory |>;
      bad = parent with <|
        returnData := out; stack := 0w :: parent.stack; pc := SUC parent.pc;
        memory := buffer_write mr.offset (TAKE mr.size out) parent.memory |>;
      vs' = vs with <| vs_returndata := out; vs_logs := lgs;
        vs_accounts := es.rollback.accounts; vs_transient := es.rollback.tStorage;
        vs_toDelete := es.rollback.toDelete;
        vs_requests := MAP FST (call_trace start) |>
  in
    venom_frame_rel start (INL ()) (es with contexts := [(ok, prb)]) (Halt vs') /\
    venom_frame_rel start (INL ())
      (es with <| contexts := [(bad, prb)]; rollback := rb |>)
      (Abort Revert_abort vs')
Proof
  simp[LET_THM] >> conj_tac >>
  simp[venom_frame_rel_def, frame_outcome_def, b2w_def]
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
  simp[call_trace_def, full_call_trace_def, gas_readings_def, frame_obs_def] >>
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
       context_limit_def, FLOOKUP_UPDATE] >>
  simp[dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  gen_tac >> IF_CASES_TAC >> simp[]
QED
