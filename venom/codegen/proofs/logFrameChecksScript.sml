(* Live generated LOG probe. Independent of the admitted correctness root. *)
Theory logFrameChecks
Ancestors
  codegen stackPlanGenCompute stackPlanTypes planExec symbolResolve
  codegenRel asmSem venomExecSemantics venomInst venomState
  frameOutcome callTrace vfmExecution vfmExecutionProp vfmContext vfmState vfmOperation vfmConstants
  list finite_map words
Libs wordsLib finite_mapLib

val () = computeLib.upd_compset add_finite_map_compset;
val () = computeLib.add_funs [byteTheory.set_byte_def];

Definition log_probe_fn_def:
  log_probe_fn = (mk_raw_function "main"
    [<| bb_label := "entry"; bb_instructions :=
      [instruction 0 MSTORE [Lit 0w; Lit 7w] [];
       instruction 1 LOG [Lit 1w; Lit 9w; Lit 32w; Lit 0w] [];
       instruction 2 STOP [] []] |>]) with fn_eom := SOME 32
End
Definition log_probe_ctx_def:
  log_probe_ctx = mk_venom_context [log_probe_fn] (SOME "main")
End
Theorem log_probe_plan:
  ?cp. generate_context_plan log_probe_ctx = SOME cp
Proof
  EVAL_TAC >> simp[stackModelTheory.stack_find_def] >> EVAL_TAC >>
  simp[listTheory.SET_TO_LIST_THM] >> EVAL_TAC
QED

Definition log_probe_prog_def:
  log_probe_prog = [AsmLabel "entry"; AsmPush [7w]; AsmPush [];
    AsmOp "MSTORE"; AsmPush [9w]; AsmPush [32w]; AsmPush [];
    AsmOp "LOG1"; AsmOp "STOP"; AsmLabel "revert"; AsmPush [];
    AsmOp "DUP1"; AsmOp "REVERT"]
End
Theorem log_probe_generated:
  OPTION_MAP (\cp. execute_plan cp.cp_initial_fmp (context_plan_ops cp))
    (generate_context_plan log_probe_ctx) = SOME log_probe_prog
Proof
  EVAL_TAC >> simp[stackModelTheory.stack_find_def] >> EVAL_TAC >>
  simp[listTheory.SET_TO_LIST_THM] >> EVAL_TAC
QED

Definition log_probe_asm_def:
  log_probe_asm = <| as_stack := []; as_memory := []; as_accounts := empty_accounts;
    as_transient := empty_transient_storage; as_returndata := [];
    as_logs := []; as_pc := 0; as_call_ctx := empty_call_context;
    as_tx_ctx := empty_tx_context; as_block_ctx := empty_block_context;
    as_code := []; as_prev_hashes := []; as_outcomes := [];
    as_requests := []; as_gas_readings := [] |>
End
Definition log_probe_es_def:
  log_probe_es = make_asm_call_state log_probe_asm 0w 10000 0 []
    (assemble log_probe_prog) F
End

Theorem log_probe_code:
  assemble log_probe_prog =
    [0x5bw;0x60w;7w;0x5fw;0x52w;0x60w;9w;0x60w;32w;0x5fw;
     0xa1w;0w;0x5bw;0x5fw;0x80w;0xfdw]
Proof
  EVAL_TAC
QED

Theorem log_probe_parsed:
  parse_code 0 FEMPTY (assemble log_probe_prog) =
    FEMPTY |+ (0, JumpDest) |+ (1, Push 1 [7w]) |+ (3, Push 0 []) |+
    (4, MStore) |+ (5, Push 1 [9w]) |+ (7, Push 1 [32w]) |+ (9, Push 0 []) |+
    (10, Log 1) |+ (11, Stop) |+ (12, JumpDest) |+ (13, Push 0 []) |+
    (14, Dup 0) |+ (15, Revert)
Proof
  simp[log_probe_code] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def] >> EVAL_TAC
QED
val () = computeLib.add_funs [log_probe_code, log_probe_parsed];

Definition log_probe_at_def:
  log_probe_at used pc stk mem lgs =
    log_probe_es with contexts :=
      [((FST (HD log_probe_es.contexts)) with
         <| gasUsed := used; pc := pc; stack := stk; memory := mem; logs := lgs |>,
        SND (HD log_probe_es.contexts))]
End
Theorem log_probe_initial:
  log_probe_at 0 0 [] [] [] = log_probe_es
Proof
  simp[log_probe_at_def, log_probe_es_def, make_asm_call_state_def,
       vfmContextTheory.initial_context_def]
QED
Theorem log_probe_jumpdest:
  step (log_probe_at 0 0 [] [] []) =
    (INL (), log_probe_at 1 1 [] [] [])
Proof
  simp[log_probe_at_def, log_probe_es_def, make_asm_call_state_def,
       vfmContextTheory.initial_context_def, initial_msg_params_def,
       log_probe_code, log_probe_parsed, make_sub_tx_def] >>
  simp[step_def, handle_def, get_current_context_def, bind_def, return_def,
       step_inst_def, step_context_def, push_stack_def, consume_gas_def,
       assert_def, inc_pc_or_jump_def, is_call_def, opcode_def, static_gas_def,
       ignore_bind_def, set_current_context_def, FLOOKUP_UPDATE]
QED

val log_step_setup =
  simp[log_probe_at_def, log_probe_es_def, make_asm_call_state_def,
       vfmContextTheory.initial_context_def, initial_msg_params_def,
       log_probe_code, log_probe_parsed, make_sub_tx_def];
val log_scalar_step =
  simp[step_def, handle_def, get_current_context_def, bind_def, return_def,
       step_inst_def, step_context_def, push_stack_def, consume_gas_def,
       assert_def, inc_pc_or_jump_def, is_call_def, opcode_def, static_gas_def,
       ignore_bind_def, set_current_context_def, FLOOKUP_UPDATE];

Theorem log_probe_push7:
  step (log_probe_at 1 1 [] [] []) =
    (INL (), log_probe_at 4 3 [7w] [] [])
Proof
  log_step_setup >> log_scalar_step >> EVAL_TAC
QED

Theorem log_probe_push0:
  step (log_probe_at 4 3 [7w] [] []) =
    (INL (), log_probe_at 6 4 [0w;7w] [] [])
Proof
  log_step_setup >> log_scalar_step >> EVAL_TAC
QED

Definition log_probe_data_def:
  log_probe_data = REPLICATE 31 (0w:word8) ++ [7w]
End
Definition log_probe_event_def:
  log_probe_event = <| logger := 0w; topics := [9w]; data := log_probe_data |>
End

Theorem log_probe_store:
  step (log_probe_at 6 4 [0w;7w] [] []) =
    (INL (), log_probe_at 12 5 [] log_probe_data [])
Proof
  log_step_setup >>
  simp[step_def, handle_def, bind_def, ignore_bind_def, return_def,
       get_current_context_def, set_current_context_def, step_inst_def,
       step_mstore_def, pop_stack_def, consume_gas_def, assert_def,
       memory_expansion_info_def, expand_memory_def, write_memory_def,
       inc_pc_or_jump_def, is_call_def, opcode_def, static_gas_def,
       FLOOKUP_UPDATE] >>
  EVAL_TAC
QED

Theorem log_probe_push_topic:
  step (log_probe_at 12 5 [] log_probe_data []) =
    (INL (), log_probe_at 15 7 [9w] log_probe_data [])
Proof
  log_step_setup >> log_scalar_step >> EVAL_TAC
QED
Theorem log_probe_push_size:
  step (log_probe_at 15 7 [9w] log_probe_data []) =
    (INL (), log_probe_at 18 9 [32w;9w] log_probe_data [])
Proof
  log_step_setup >> log_scalar_step >> EVAL_TAC
QED
Theorem log_probe_push_offset:
  step (log_probe_at 18 9 [32w;9w] log_probe_data []) =
    (INL (), log_probe_at 20 10 [0w;32w;9w] log_probe_data [])
Proof
  log_step_setup >> log_scalar_step >> EVAL_TAC
QED
Theorem log_probe_log:
  step (log_probe_at 20 10 [0w;32w;9w] log_probe_data []) =
    (INL (), log_probe_at 1026 11 [] log_probe_data [log_probe_event])
Proof
  log_step_setup >>
  simp[step_def, handle_def, bind_def, ignore_bind_def, return_def,
       get_current_context_def, set_current_context_def, step_inst_def,
       step_log_def, pop_stack_def, FLOOKUP_UPDATE] >>
  simp[memory_expansion_info_def, log_probe_data_def,
       vfmConstantsTheory.word_size_def] >>
  simp[consume_gas_def, assert_def, expand_memory_def, read_memory_def,
       push_logs_def, get_callee_def, get_static_def, assert_not_static_def,
       inc_pc_or_jump_def, is_call_def, opcode_def, static_gas_def,
       bind_def, ignore_bind_def, return_def, get_current_context_def,
       set_current_context_def, log_probe_event_def, log_probe_data_def] >>
  EVAL_TAC
QED
Theorem log_probe_stop:
  step (log_probe_at 1026 11 [] log_probe_data [log_probe_event]) =
    (INR NONE, log_probe_at 1026 11 [] log_probe_data [log_probe_event])
Proof
  log_step_setup >>
  simp[step_def, handle_def, get_current_context_def, bind_def, return_def,
       step_inst_def, step_context_def, set_return_data_def,
       finish_def, fail_def, ignore_bind_def, handle_step_def,
       handle_exception_def, get_tx_params_def, set_current_context_def,
       reraise_def, FLOOKUP_UPDATE, vfm_abort_def, handle_create_def,
       get_return_data_def, get_output_to_def, get_num_contexts_def,
       empty_return_destination_def]
QED
Definition log_probe_s0_def: log_probe_s0 = log_probe_at 0 0 [] [] []
End
Definition log_probe_s1_def: log_probe_s1 = log_probe_at 1 1 [] [] []
End
Definition log_probe_s2_def: log_probe_s2 = log_probe_at 4 3 [7w] [] []
End
Definition log_probe_s3_def: log_probe_s3 = log_probe_at 6 4 [0w;7w] [] []
End
Definition log_probe_s4_def: log_probe_s4 = log_probe_at 12 5 [] log_probe_data []
End
Definition log_probe_s5_def: log_probe_s5 = log_probe_at 15 7 [9w] log_probe_data []
End
Definition log_probe_s6_def: log_probe_s6 = log_probe_at 18 9 [32w;9w] log_probe_data []
End
Definition log_probe_s7_def: log_probe_s7 = log_probe_at 20 10 [0w;32w;9w] log_probe_data []
End
Definition log_probe_s8_def: log_probe_s8 = log_probe_at 1026 11 [] log_probe_data [log_probe_event]
End
Definition log_probe_s9_def: log_probe_s9 = log_probe_at 1026 11 [] log_probe_data [log_probe_event]
End

Theorem log_probe_states:
  (log_probe_s0 = log_probe_at 0 0 [] [] []) /\
  (log_probe_s1 = log_probe_at 1 1 [] [] []) /\
  (log_probe_s2 = log_probe_at 4 3 [7w] [] []) /\
  (log_probe_s3 = log_probe_at 6 4 [0w;7w] [] []) /\
  (log_probe_s4 = log_probe_at 12 5 [] log_probe_data []) /\
  (log_probe_s5 = log_probe_at 15 7 [9w] log_probe_data []) /\
  (log_probe_s6 = log_probe_at 18 9 [32w;9w] log_probe_data []) /\
  (log_probe_s7 = log_probe_at 20 10 [0w;32w;9w] log_probe_data []) /\
  (log_probe_s8 = log_probe_at 1026 11 [] log_probe_data [log_probe_event]) /\
  (log_probe_s9 = log_probe_at 1026 11 [] log_probe_data [log_probe_event])
Proof
  simp[log_probe_s0_def, log_probe_s1_def, log_probe_s2_def, log_probe_s3_def,
       log_probe_s4_def, log_probe_s5_def, log_probe_s6_def, log_probe_s7_def,
       log_probe_s8_def, log_probe_s9_def]
QED
Theorem log_probe_steps:
  log_probe_s0 = log_probe_es /\
  step log_probe_s0 = (INL (), log_probe_s1) /\
  step log_probe_s1 = (INL (), log_probe_s2) /\
  step log_probe_s2 = (INL (), log_probe_s3) /\
  step log_probe_s3 = (INL (), log_probe_s4) /\
  step log_probe_s4 = (INL (), log_probe_s5) /\
  step log_probe_s5 = (INL (), log_probe_s6) /\
  step log_probe_s6 = (INL (), log_probe_s7) /\
  step log_probe_s7 = (INL (), log_probe_s8) /\
  step log_probe_s8 = (INR NONE, log_probe_s9)
Proof
  conj_tac >- simp[log_probe_states, log_probe_initial] >>
  simp[log_probe_states, log_probe_jumpdest,
       log_probe_push7, log_probe_push0, log_probe_store, log_probe_push_topic,
       log_probe_push_size, log_probe_push_offset, log_probe_log, log_probe_stop]
QED

Theorem log_probe_at_projections[simp]:
  LENGTH (log_probe_at used pc stk mem lgs).contexts = 1 /\
  (FST (HD (log_probe_at used pc stk mem lgs).contexts)).pc = pc /\
  (FST (HD (log_probe_at used pc stk mem lgs).contexts)).logs = lgs /\
  (FST (HD (log_probe_at used pc stk mem lgs).contexts)).stack = stk /\
  (FST (HD (log_probe_at used pc stk mem lgs).contexts)).memory = mem /\
  (FST (HD (log_probe_at used pc stk mem lgs).contexts)).returnData = [] /\
  (log_probe_at used pc stk mem lgs).txParams = log_probe_es.txParams /\
  (log_probe_at used pc stk mem lgs).rollback = log_probe_es.rollback
Proof
  simp[log_probe_at_def, log_probe_es_def, make_asm_call_state_def,
       vfmContextTheory.initial_context_def]
QED

Theorem log_probe_at_next_opcode:
  next_opcode (FST (HD (log_probe_at used pc stk mem lgs).contexts)) =
    if 16 <= pc then SOME Stop
    else FLOOKUP (parse_code 0 FEMPTY (assemble log_probe_prog)) pc
Proof
  simp[log_probe_at_def, log_probe_es_def, make_asm_call_state_def,
       vfmContextTheory.initial_context_def, initial_msg_params_def,
       next_opcode_def, log_probe_code]
QED
Theorem log_probe_fresh:
  wf_state log_probe_es /\
  (?d. log_probe_es.msdomain = Collect d) /\
  LENGTH log_probe_es.contexts = 1 /\
  (FST (HD log_probe_es.contexts)).logs = [] /\
  (FST (HD log_probe_es.contexts)).memory = [] /\
  ~(FST (HD log_probe_es.contexts)).msgParams.static
Proof
  simp[log_probe_es_def, log_probe_asm_def, make_asm_call_state_def,
       vfmContextTheory.initial_context_def, initial_msg_params_def,
       make_sub_tx_def, empty_call_context_def, make_rollback_def,
       asm_to_tx_params_def, empty_tx_context_def, empty_block_context_def,
       transfer_value_def, empty_return_destination_def,
       wf_state_def, wf_context_def, all_accounts_def, wf_accounts_def,
       stack_room_ok_def, gas_stack_ok_def, outputTo_consistent_stack_def,
       outputTo_consistent_ctx_def, empty_accounts_def, stack_limit_def,
       context_limit_def]
QED

Theorem log_probe_depths[simp]:
  LENGTH log_probe_s0.contexts = 1 /\
  LENGTH log_probe_s1.contexts = 1 /\
  LENGTH log_probe_s2.contexts = 1 /\
  LENGTH log_probe_s3.contexts = 1 /\
  LENGTH log_probe_s4.contexts = 1 /\
  LENGTH log_probe_s5.contexts = 1 /\
  LENGTH log_probe_s6.contexts = 1 /\
  LENGTH log_probe_s7.contexts = 1 /\
  LENGTH log_probe_s8.contexts = 1 /\
  LENGTH log_probe_s9.contexts = 1
Proof
  simp[log_probe_states]
QED

val log_cert_steps = tl (CONJUNCTS log_probe_steps);

Theorem log_probe_run:
  run_call log_probe_es = SOME (INR NONE, log_probe_s9)
Proof
  rewrite_tac[GSYM (cj 1 log_probe_steps), run_call_def] >>
  ntac 10 (once_rewrite_tac[WhileTheory.OWHILE_THM] >>
    simp (combinTheory.o_DEF :: log_cert_steps))
QED

Theorem log_probe_observations:
  observe 1 log_probe_s0 (INL (),log_probe_s1) obs = obs /\
  observe 1 log_probe_s1 (INL (),log_probe_s2) obs = obs /\
  observe 1 log_probe_s2 (INL (),log_probe_s3) obs = obs /\
  observe 1 log_probe_s3 (INL (),log_probe_s4) obs = obs /\
  observe 1 log_probe_s4 (INL (),log_probe_s5) obs = obs /\
  observe 1 log_probe_s5 (INL (),log_probe_s6) obs = obs /\
  observe 1 log_probe_s6 (INL (),log_probe_s7) obs = obs /\
  observe 1 log_probe_s7 (INL (),log_probe_s8) obs = obs /\
  observe 1 log_probe_s8 (INR NONE,log_probe_s9) obs = obs
Proof
  simp[observe_def, observable_call_def, log_probe_states,
       log_probe_at_next_opcode, log_probe_parsed, FLOOKUP_UPDATE]
QED

Theorem log_probe_frame_obs:
  frame_obs log_probe_es =
    <| entries := []; readings := []; pending := NONE |>
Proof
  rewrite_tac[GSYM (cj 1 log_probe_steps), frame_obs_def] >>
  simp log_cert_steps >>
  ntac 9 (once_rewrite_tac[frame_obs_tr_def] >>
    simp (log_probe_observations :: log_cert_steps))
QED

Theorem log_probe_trace:
  call_trace log_probe_es = [] /\ gas_readings log_probe_es = []
Proof
  simp[call_trace_def, full_call_trace_def, gas_readings_def,
       log_probe_frame_obs]
QED

Theorem log_probe_frame_outcome:
  frame_outcome log_probe_es (INR NONE) log_probe_s9 NONE [] [log_probe_event]
Proof
  rewrite_tac[GSYM (cj 1 log_probe_steps)] >>
  simp[frame_outcome_def, log_probe_states, log_probe_at_def,
       log_probe_es_def, make_asm_call_state_def,
       vfmContextTheory.initial_context_def]
QED



val _ = List.app (fn (name,th) =>
  if null (List.filter (fn s => s <> "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("oracle dependency in " ^ name)) (DB.thms "logFrameChecks");
