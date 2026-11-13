(* Same-witness machine frames for positional registration prefixes. *)
Theory entryRegistrationPrefixFrame
Ancestors
  actualAllocExec entryDecoderStateFrame entryDecoderHistoryFrame abiAllocationHistory loweringStateRelDefs
  emitHelperProps abiDecoderVarSequence
  successfulSequenceEndpoint abiDecoderLoopRegisters fragExecMem loweringHalt
  abiDecoderReentry unitTransformDefs contextCodegenRel codegenRel
  venomExecSemantics venomState venomInst venomMemDefs compileEnv
  emitHelper exprLoweringProps finite_map words list rich_list arithmetic

Theorem entry_registration_alloc_buffer_frame:
  compile_alloc_buffer n st = (buf,last) /\ fn_has_code st last fn /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  n < dimword (:256) /\ unit_alloca_budget ctx < dimword (:256) /\
  (!entry. FLOOKUP initial.vs_allocas st.cs_next_id = SOME entry ==>
    ?p. entry = (p,n) /\ p+n < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  fn_inst_ids_distinct fn /\ alloca_history fn initial /\
  fresh_vars_wrt limit_st initial /\ last.cs_next_var <= limit_st.cs_next_var ==>
  ?v p. ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
    v.vs_inst_idx = LENGTH last.cs_current_insts /\
    eval_operand buf.buf_operand v = SOME (n2w p) /\
    abi_decoder_operand_live last.cs_next_var buf.buf_operand /\
    FLOOKUP v.vs_allocas st.cs_next_id = SOME (p,n) /\
    p+n < dimword (:256) /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    initial.vs_alloca_next <= v.vs_alloca_next /\
    v.vs_memory = initial.vs_memory /\ v.vs_call_ctx = initial.vs_call_ctx /\
    v.vs_data_section = initial.vs_data_section /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op v = eval_operand op initial) /\
    (!id entry. FLOOKUP initial.vs_allocas id = SOME entry ==>
      FLOOKUP v.vs_allocas id = SOME entry) /\
    (!id. id <> st.cs_next_id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial)) /\
    entry_decoder_obs initial v /\ alloca_history fn v /\
    (abi_alloca_history (fn_insts fn) initial ==> abi_alloca_history (fn_insts fn) v) /\
    fresh_vars_wrt limit_st v /\
    ((!fuel. mem_safe_run fuel ctx fn v) ==> !fuel. mem_safe_run fuel ctx fn initial)
Proof
  strip_tac >> drule_all actual_alloc_buffer_site >> strip_tac >>
  qmatch_asmsub_abbrev_tac `MEM ins (fn_insts fn)` >>
  `ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit (n2w n)] /\
    ins.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
    ins.inst_id = st.cs_next_id` by simp[Abbr `ins`, mk_inst_def] >>
  `!entry. FLOOKUP initial.vs_allocas ins.inst_id = SOME entry ==>
    ?p. entry = (p,n) /\ p+n < dimword (:256)` by metis_tac[] >>
  drule_all actual_literal_alloca_owned_step >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `emitted_insts st last = [ins]` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND, Abbr `ins`] >>
  `run_inst_seq (emitted_insts st last) initial = OK t` by
    simp[run_inst_seq_def] >>
  suspend "frames"
QED

Resume entry_registration_alloc_buffer_frame[frames]:
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st last)` by simp[is_terminator_def] >>
  `run_inst_seq_mem_ok (emitted_insts st last) initial` by
    simp[run_inst_seq_mem_ok_def, inst_mem_below_frontier_def,
      source_memory_read_ranges_def, source_memory_write_ranges_def,
      memSafeRunTheory.inst_dload_in_section_def] >>
  `inst_extends st last` by
    simp[inst_extends_def, IS_PREFIX_APPEND, Abbr `ins`] >>
  `entry_decoder_obs initial t` by
    (irule entry_decoder_step_obs >> goal_assum (drule_at Any) >>
     simp[abi_decoder_reentry_opcode_def]) >>
  `alloca_history fn (t with vs_inst_idx := LENGTH last.cs_current_insts)` by
    (irule entry_straight_line_alloca_history >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`initial`, `st`] >> simp[IS_PREFIX_APPEND, is_terminator_def]) >>
  suspend "fresh"
QED

Resume entry_registration_alloc_buffer_frame[fresh]:
  `fresh_vars_wrt limit_st t` by
    (qpat_x_assum `exec_alloca _ _ _ = OK t` mp_tac >>
     qpat_x_assum `fresh_vars_wrt limit_st initial` mp_tac >>
     `st.cs_next_var < limit_st.cs_next_var` by decide_tac >>
     qpat_x_assum `st.cs_next_var < limit_st.cs_next_var` mp_tac >>
     qpat_x_assum `ins.inst_outputs = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
     irule abi_decoder_generated_update_fresh >>
     gvs[fresh_vars_wrt_def]) >>
  `abi_alloca_history (fn_insts fn) initial ==>
    abi_alloca_history (fn_insts fn) t` by
    (strip_tac >> irule abi_alloca_history_alloca >>
     goal_assum (drule_at (Pat `exec_alloca _ _ _ = OK _`)) >> simp[]) >>
  qpat_x_assum `!entry. FLOOKUP initial.vs_allocas st.cs_next_id = SOME entry ==> _` kall_tac >>
  qpat_x_assum `!entry. FLOOKUP initial.vs_allocas ins.inst_id = SOME entry ==> _` kall_tac >>
  qpat_x_assum `MEM ins _` kall_tac >>
  qpat_x_assum `ALL_DISTINCT _` kall_tac >>
  qpat_x_assum `!y. not_fresh_at _ _ ==> _` kall_tac >>
  suspend "package"
QED

Resume entry_registration_alloc_buffer_frame[package]:
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`P` |-> `\s:venom_state. T`] successful_sequence_endpoint)) >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule actual_alloc_buffer_live >> strip_tac >>
  `FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,n)` by metis_tac[] >>
  `fresh_vars_wrt limit_st (t with vs_inst_idx := LENGTH last.cs_current_insts)` by
    gvs[fresh_vars_wrt_def] >>
  qexistsl [`t with vs_inst_idx := LENGTH last.cs_current_insts`, `p`] >>
  simp[eval_operand_def] >> strip_tac >>
  irule abi_alloca_history_frame >> qexists_tac `t` >> simp[]
QED

Finalise entry_registration_alloc_buffer_frame

val () =
  let val th = entry_registration_alloc_buffer_frame
      val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "ENTRY_REGISTRATION_ALLOCATION_FRAME_AUDIT OK\n"
     else raise Fail "registration allocation frame inherited admission"
  end;
