(* Actual pure address operations with fixed-limit frames. *)
Theory entryRegistrationAddressFrame
Ancestors
  entryRegistrationPrefixFrame calldataRegistrationExec successfulSequenceEndpoint loweringStateRelDefs
  entryDecoderStateFrame entryDecoderHistoryFrame abiDecoderLoopRegisters
  abiDecoderVarSequence abiDecoderReentryAddress abiDecoderReentry
  venomMemDefs emitHelperProps fragExecMem abiDecoderContract fragExec
  unitTransformDefs contextCodegenRel codegenRel venomExecSemantics venomState
  venomInst compileEnv emitHelper exprLoweringProps finite_map words list rich_list arithmetic

Theorem registration_pure_operation_frame[local]:
  emit_op opc args st = (out,last) /\ (opc = ADD \/ opc = CALLDATALOAD) /\
  step_inst_base (mk_inst st.cs_next_id opc args
    [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) w s) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  alloca_history fn s /\ alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  fresh_vars_wrt limit_st s /\ last.cs_next_var <= limit_st.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    eval_operand out t = SOME w /\
    abi_decoder_operand_live last.cs_next_var out /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    entry_decoder_obs s t /\ alloca_history fn t /\ fresh_vars_wrt limit_st t /\
    ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s) /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  `run_inst_seq (emitted_insts st last) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) w s)` by
    simp[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st last)` by
    (qpat_x_assum `opc = ADD \/ _` strip_assume_tac >>
     simp[mk_inst_def, is_terminator_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st last) s` by
    (qpat_x_assum `opc = ADD \/ _` strip_assume_tac >>
     simp[run_inst_seq_mem_ok_def, inst_mem_below_frontier_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       memSafeRunTheory.inst_dload_in_section_def, mk_inst_def] >>
     CASE_TAC >> simp[]) >>
  `last.cs_current_bb = st.cs_current_bb` by gvs[same_blocks_def] >>
  `entry_decoder_obs s (update_var (STRING #"%" (toString st.cs_next_var)) w s)` by simp[] >>
  `alloca_history fn ((update_var (STRING #"%" (toString st.cs_next_var)) w s)
    with vs_inst_idx := LENGTH last.cs_current_insts)` by
    (irule entry_straight_line_alloca_history >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`s`, `st`] >> simp[inst_extends_def, is_terminator_def, mk_inst_def] >>
     gvs[inst_extends_def]) >>
  suspend "package"
QED

Resume registration_pure_operation_frame[package]:
  `fresh_vars_wrt limit_st
    (update_var (STRING #"%" (toString st.cs_next_var)) w s)` by
    (irule abi_decoder_generated_update_fresh >> simp[] >> decide_tac) >>
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`P` |-> `\s:venom_state. T`] successful_sequence_endpoint)) >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qexists `(update_var (STRING #"%" (toString st.cs_next_var)) w s)
    with vs_inst_idx := LENGTH last.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    ASCIInumbersTheory.toString_inj, alloca_inv_def,
    venomMemDefsTheory.allocas_non_overlapping_def,
    venomMemDefsTheory.alloca_next_valid_def,
    allocaFrontierBoundTheory.alloca_frontier_inv_def,
    allocaBudgetPropsTheory.remaining_alloca_budget_def,
    fresh_vars_wrt_def] >>
  conj_tac
  >- (Cases >> simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> first_x_assum (qspec_then `st.cs_next_var` mp_tac) >> simp[]) >>
  gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
    fresh_vars_wrt_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise registration_pure_operation_frame

Theorem registration_add_frame[local]:
  emit_op ADD [lhs;rhs] st = (out,last) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  alloca_history fn s /\ alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  fresh_vars_wrt limit_st s /\ last.cs_next_var <= limit_st.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    eval_operand out t = SOME (a+b) /\
    abi_decoder_operand_live last.cs_next_var out /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    entry_decoder_obs s t /\ alloca_history fn t /\ fresh_vars_wrt limit_st t /\
    ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s) /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s))
Proof
  strip_tac >> irule registration_pure_operation_frame >> simp[] >>
  qexistsl [`[lhs;rhs]`, `ADD`] >> simp[] >>
  irule step_ADD >> simp[]
QED

Theorem registration_read_frame[local]:
  emit_op CALLDATALOAD [src] st = (out,last) /\
  eval_operand src s = SOME p /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  alloca_history fn s /\ alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  fresh_vars_wrt limit_st s /\ last.cs_next_var <= limit_st.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    eval_operand out t = SOME (abi_decode_load CALLDATALOAD p s) /\
    abi_decoder_operand_live last.cs_next_var out /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    entry_decoder_obs s t /\ alloca_history fn t /\ fresh_vars_wrt limit_st t /\
    ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s) /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s))
Proof
  strip_tac >> irule registration_pure_operation_frame >> simp[] >>
  qexistsl [`[src]`, `CALLDATALOAD`] >> simp[] >>
  irule abi_decode_read_step >> simp[abi_decode_source_opcode_def]
QED

Theorem entry_registration_address_frame:
  emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] st = (head,after_head) /\
  (if dyn then
    ?offset after_load.
      emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
      emit_op ADD [Lit (n2w 4); offset] after_load = (src,first)
   else src = head /\ first = after_head) /\
  fn_has_code st first fn /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  fn_inst_ids_distinct fn /\ alloca_history fn s /\
  fresh_vars_wrt limit_st s /\ first.cs_next_var <= limit_st.cs_next_var ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = first.cs_current_bb /\
    t.vs_inst_idx = LENGTH first.cs_current_insts /\
    eval_operand src t = SOME
      (if dyn then n2w 4 + abi_decode_load CALLDATALOAD
         (n2w 4 + n2w (off-4):bytes32) s else n2w 4 + n2w (off-4)) /\
    abi_decoder_operand_live first.cs_next_var src /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    entry_decoder_obs s t /\ alloca_history fn t /\ fresh_vars_wrt limit_st t /\
    ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s) /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  reverse (Cases_on `dyn`)
  >- (gvs[] >>
      `eval_operand (Lit (n2w 4)) s = SOME (n2w 4) /\
       eval_operand (Lit (n2w (off-4))) s = SOME (n2w (off-4))` by
        simp[eval_operand_def] >>
      drule_all registration_add_frame >> simp[]) >>
  gvs[] >> suspend "dynamic"
QED

Resume entry_registration_address_frame[dynamic]:
  `cs_extends st after_head /\ cs_extends after_head after_load /\
   cs_extends after_load first` by
    (imp_res_tac emit_op_extends >> rpt conj_tac >>
     irule cs_extends_same_block >>
     gvs[same_blocks_def, IS_PREFIX_APPEND]) >>
  `cs_extends after_head first` by metis_tac[cs_extends_trans] >>
  `fn_has_code st after_head fn /\ fn_has_code after_head after_load fn /\
   fn_has_code after_load first fn` by metis_tac[fn_has_code_split] >>
  `after_head.cs_next_var <= after_load.cs_next_var /\
   after_load.cs_next_var <= first.cs_next_var` by
    metis_tac[emitted_insts_emit_op, LESS_EQ_ADD] >>
  `after_head.cs_next_var <= limit_st.cs_next_var /\
   after_load.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `eval_operand (Lit (n2w 4)) s = SOME (n2w 4) /\
   eval_operand (Lit (n2w (off-4))) s = SOME (n2w (off-4))` by
    simp[eval_operand_def] >>
  drule_all registration_add_frame >> strip_tac >>
  drule_all registration_read_frame >> strip_tac >>
  `eval_operand (Lit (n2w 4)) t' = SOME (n2w 4)` by simp[eval_operand_def] >>
  drule_all registration_add_frame >> strip_tac >>
  suspend "compose"
QED

Resume entry_registration_address_frame[compose]:
  `st.cs_next_var <= after_head.cs_next_var` by
    metis_tac[emitted_insts_emit_op, LESS_EQ_ADD] >>
  `abi_decode_load CALLDATALOAD (n2w 4 + n2w (off-4):bytes32) t =
   abi_decode_load CALLDATALOAD (n2w 4 + n2w (off-4):bytes32) s` by
    simp[abi_decode_load_def, abi_decode_source_def] >>
  qexists `t''` >> simp[] >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      `abi_decoder_operand_live after_head.cs_next_var op /\
       abi_decoder_operand_live after_load.cs_next_var op` by
        metis_tac[abi_decoder_operand_live_mono, LESS_EQ_TRANS] >>
      simp[]) >>
  conj_tac >- metis_tac[entry_decoder_obs_trans] >>
  qpat_x_assum `!fuel r. run_from fuel ctx fn t = r /\ _ ==> _` mp_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx fn t' = r /\ _ ==> _` mp_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx fn t'' = r /\ _ ==> _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]
QED

Finalise entry_registration_address_frame

val () =
  List.app (fn th =>
    let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
    in if null axioms andalso null (Thm.hyp th) andalso
          List.all (fn name => name = "DISK_THM") oracles
       then ()
       else raise Fail "registration address frame inherited admission"
    end)
    [registration_pure_operation_frame, registration_add_frame,
     registration_read_frame, entry_registration_address_frame];
val () = print "ENTRY_REGISTRATION_ADDRESS_FRAME_AUDIT OK\n";
