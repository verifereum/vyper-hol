(* Execute a supplied keyword's location calculation before its ABI decoder. *)
Theory groupedKeywordAddress
Ancestors abiEncoder abiDecoderReentryPointer abiDecoderReservation abiDecoderContract
  decoderMemberPrefixPtr fragGasOriginPtr fragExec ptrDiscipline ptrSafeRun
  compileEnv venomState venomInst emitHelperProps emitHelper context
  decoderWorldFramePtr venomInstProofs1 exprLoweringProps loweringStateRelDefs list words

Theorem grouped_keyword_source_address:
  compile_getelemptr_abi (Lit 4w) dyn off CALLDATALOAD (Lit 0w) (Lit 0w)
    sa = (src,se) /\
  fn_has_code sa se fn /\
  (dyn ==> abi_decode_load CALLDATALOAD (n2w (4+off) : bytes32) s = n2w delta /\
    4+delta < dimword (:256)) /\
  fresh_vars_wrt sa s /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G' tn'.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) /\
    ~t.vs_halted /\ t.vs_current_bb = se.cs_current_bb /\
    t.vs_inst_idx = LENGTH se.cs_current_insts /\ fresh_vars_wrt se t /\
    eval_operand src t = SOME (n2w (4 + if dyn then delta else off)) /\
    abi_decoder_operand_live se.cs_next_var src /\
    op_taint tn' src = {} /\ op_prov G' src = NONE /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_memory = s.vs_memory /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_initial_fmp = s.vs_initial_fmp /\ t.vs_fmp = s.vs_fmp /\
    t.vs_code = s.vs_code /\ t.vs_data_section = s.vs_data_section /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
    t.vs_requests = s.vs_requests /\ t.vs_pending_deletions = s.vs_pending_deletions /\
    t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
    t.vs_gas_readings = s.vs_gas_readings /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\
      FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  mp_tac (Q.INST [`src` |-> `Lit 4w`, `opc` |-> `CALLDATALOAD`,
    `base_op` |-> `Lit 0w`, `hi` |-> `Lit 0w`, `sb` |-> `4`,
    `src_base` |-> `0`, `payload_off` |-> `delta`, `s` |-> `s`,
    `st` |-> `sa`, `st'` |-> `se`, `member_op` |-> `src`,
    `dyn` |-> `dyn`, `off` |-> `off`]
      (SPEC_ALL abi_decoder_member_pointer_sequence)) >>
  impl_tac >- (simp[abi_decode_source_opcode_def, eval_operand_def] >>
    strip_tac >> qpat_assum `dyn ==> _` (mp_tac o UNDISCH) >>
    simp_tac bool_ss [arithmeticTheory.ADD_COMM]) >>
  disch_then (qx_choose_then `raw` strip_assume_tac) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_pointer_code >> strip_tac >>
  `~raw.vs_halted` by
    (drule_all abi_decoder_sequence_halted >> simp[]) >>
  `sa.cs_current_bb = se.cs_current_bb` by
    (qpat_assum `compile_getelemptr_abi _ _ _ _ _ _ _ = _` mp_tac >>
     Cases_on `dyn` >>
     gvs[compile_getelemptr_abi_def, compile_abi_dec_addr_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
         fresh_var_def, fresh_id_def, emit_def]) >>
  drule abi_decoder_member_pointer_counters >> strip_tac >>
  drule abi_decode_member_pointer_allocation_shape >> simp[] >> strip_tac >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  drule_all decoder_run_world_frame >> strip_tac >>
  `raw.vs_code = s.vs_code /\ raw.vs_initial_fmp = s.vs_initial_fmp` by
    (irule (SIMP_RULE (srw_ss()) []
      (Q.ISPEC `\s:venom_state. (s.vs_code,s.vs_initial_fmp)`
        run_inst_seq_preserves_field)) >>
     qexists_tac `emitted_insts sa se` >> simp[] >> rpt strip_tac >>
     `~is_terminator i.inst_opcode` by fs[EVERY_MEM] >>
     drule_all step_inst_base_preserves_all >> simp[]) >>
  mp_tac (Q.INST [`src` |-> `Lit 4w`, `ep` |-> `src`, `s` |-> `s`,
    `t` |-> `raw`, `dyn` |-> `dyn`, `ao` |-> `off`, `sa` |-> `sa`,
    `sb` |-> `se`, `func` |-> `fn`, `lower` |-> `lo`,
    `tn` |-> `tn`, `G` |-> `G`, `ctx` |-> `ctx`, `PG` |-> `PG`]
      (SPEC_ALL member_navigation_source_origin)) >>
  impl_tac >- simp[op_taint_def, op_prov_def] >>
  disch_then (qx_choosel_then [`H`, `u`] strip_assume_tac) >>
  qexistsl_tac [`raw with vs_inst_idx := LENGTH se.cs_current_insts`, `H`, `u`] >>
  fs[eval_operand_def, lookup_var_def, fresh_vars_wrt_def] >>
  qpat_assum `s.vs_inst_idx = LENGTH sa.cs_current_insts` (fn eq =>
    fs[GSYM eq, venom_state_accfupds])
QED
