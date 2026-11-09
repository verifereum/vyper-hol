(* Actual-site allocation for the two Log buffers, including re-entry. *)
Theory stmtSimLogAllocate
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts
  stmtSimLogTrace stmtSimLogAllocResource stmtSimLogScalarPrefix
  abiBuiltinAllocation localPtrsProps abiEncoderComplexPrefix abiEncoderComplexCode
  abiEncoderMemberCode abiEncoderChildContext fragExec
  loweringSlice exprSimOperands  stmtSimLogArgs exprLoweringProps
  compileEnv loweringStateRelDefs context emitHelperProps venomExecSemantics venomInst venomState
  finite_map words list arithmetic string ASCIInumbers

Theorem log_buffer_allocate:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ cap < dimword (:256) /\
  sb.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t p. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand buf.buf_operand t = SOME (n2w p) /\ buf.buf_size = cap /\
    p + cap < dimword (:256) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (p,cap) /\
    stmt_state_rel ctx func ce cx es t /\ fresh_vars_wrt limit_st t /\
    (!op. abi_decoder_operand_live sa.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\
    abi_builtin_allocation_frame sa.cs_next_var sa.cs_next_id cap s t /\
    (!id b sz. id <> sa.cs_next_id /\ FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
      p + cap <= b \/ b + sz <= p) /\
    inst_extends sa sb
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all log_buffer_trace_code >> strip_tac >>
  qmatch_asmsub_abbrev_tac `MEM inst (fn_insts func)` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit (n2w cap)] /\
   inst.inst_outputs = [STRING #"%" (toString sa.cs_next_var)] /\
   inst.inst_id = sa.cs_next_id` by simp[Abbr `inst`, mk_inst_def] >>
  drule_all log_event_buffer_resource >>
  disch_then (qx_choose_then `p` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qpat_x_assum `_ \/ _` mp_tac >> asm_simp_tac bool_ss [] >>
  disch_then assume_tac >>
  drule_all abi_builtin_alloc_buffer >> strip_tac >>
  `abi_builtin_allocation_frame sa.cs_next_var sa.cs_next_id cap s t` by
    gvs[abi_builtin_allocation_frame_def, abi_builtin_allocate_state_def] >>
  `not_local_ptr ce es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule fresh_not_local_ptr >> qexists_tac `sa` >>
     simp[not_fresh_at_def, toString_inj]) >>
  `exec_alloca inst s (n2w cap : 256 word) = OK t` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, Abbr `inst`, mk_inst_def] >>
     Cases_on `exec_alloca
       <|inst_id := sa.cs_next_id; inst_opcode := ALLOCA;
         inst_operands := [Lit (n2w cap)];
         inst_outputs := [STRING #"%" (toString sa.cs_next_var)]|>
       s (n2w cap : 256 word)` >>
     simp[run_inst_seq_def]) >>
  drule_all stmt_state_rel_exec_alloca >> strip_tac >>
  qexistsl_tac [`t`,`p`] >>
  gvs[abi_builtin_allocation_frame_def, abi_builtin_allocate_state_def,
      FLOOKUP_UPDATE, eval_operand_def, lookup_var_def] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]
QED

(* Ownership follows the actual instruction site, including replayed sites. *)
Theorem log_buffer_clear_of_locals:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  FLOOKUP s.vs_allocas sa.cs_next_id = SOME (p,cap) /\
  local_region ce es.scopes s name lo sz ==>
  p + cap <= lo \/ lo + sz <= p
Proof
  rpt strip_tac >>
  drule_all log_buffer_trace_code >> strip_tac >>
  qmatch_asmsub_abbrev_tac `MEM inst (fn_insts func)` >>
  `inst.inst_outputs = [STRING #"%" (toString sa.cs_next_var)] /\
   inst.inst_id = sa.cs_next_id` by simp[Abbr `inst`, mk_inst_def] >>
  `not_local_ptr ce es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule fresh_not_local_ptr >> qexists_tac `sa` >>
     simp[not_fresh_at_def, toString_inj]) >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (p,cap)` by simp[] >>
  drule_all alloca_clear_of_locals >> simp[]
QED

Theorem log_buffer_clear_of_immutable:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func ce cx es s /\ ce.ce_is_ctor /\
  FLOOKUP s.vs_allocas sa.cs_next_id = SOME (p,cap) /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
  off + type_memory_size tv <= p \/ p + cap <= off
Proof
  rpt strip_tac >> drule_all log_buffer_trace_code >> strip_tac >>
  `immutable_alloca_sep func ce cx es s` by fs[stmt_state_rel_def] >>
  qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [immutable_alloca_sep_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `!inst b sz. _` drule >>
  simp[mk_inst_def, regions_disjoint_def]
QED

Theorem log_pending_alloca_locals[local]:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
  not_local_ptr ce es.scopes q /\
  ((FLOOKUP s.vs_allocas inst.inst_id = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas inst.inst_id = SOME (p,cap)) /\
  local_region ce es.scopes s name lo sz ==>
  lo + sz <= p \/ p + cap <= lo
Proof
  strip_tac
  >- (`local_ptrs_rel func ce es.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
      `s.vs_alloca_next <= p` by simp[] >>
      drule_all local_ptrs_rel_above_frontier >>
      disch_then (qspec_then `cap` mp_tac) >>
      simp[regions_disjoint_def]) >>
  drule_all alloca_clear_of_locals >> decide_tac
QED

Theorem log_pending_alloca_immutable[local]:
  stmt_state_rel ctx func ce cx es s /\ ce.ce_is_ctor /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  ((FLOOKUP s.vs_allocas inst.inst_id = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas inst.inst_id = SOME (p,cap)) /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
  off + type_memory_size tv <= p \/ p + cap <= off
Proof
  strip_tac >>
  `immutable_alloca_sep func ce cx es s` by fs[stmt_state_rel_def] >>
  qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [immutable_alloca_sep_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac
  >- simp[] >>
  qpat_x_assum `!inst b sz. _` drule >> simp[regions_disjoint_def]
QED

(* This is the prospective cursor resource consumed by the encoder, not an
   assumption that its ALLOCA is fresh.  Its site may already be recorded. *)
Theorem log_cursor_ownership:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w 32)] /\
  inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
  local_ptrs_reserved ce st ==>
  ?p. ((FLOOKUP s.vs_allocas inst.inst_id = NONE /\ p = s.vs_alloca_next) \/
       FLOOKUP s.vs_allocas inst.inst_id = SOME (p,32)) /\
    p < dimword (:256) /\
    (!id b sz. id <> inst.inst_id /\ FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
      p+32 <= b \/ b+sz <= p) /\
    (!name lo sz. local_region ce es.scopes s name lo sz ==>
      lo+sz <= p \/ p+32 <= lo) /\
    (ce.ce_is_ctor ==> !name tv v off.
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
      off+type_memory_size tv <= p \/ p+32 <= off)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all log_scalar_cursor_resource >>
  disch_then (qx_choose_then `p` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `not_local_ptr ce es.scopes (STRING #"%" (toString st.cs_next_var))` by
    (irule fresh_not_local_ptr >> qexists_tac `st` >>
     simp[not_fresh_at_def, toString_inj]) >>
  qexists_tac `p` >> asm_simp_tac bool_ss [] >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac
  >- (rpt strip_tac >> drule_all log_pending_alloca_locals >> simp[]) >>
  rpt strip_tac >> drule_all log_pending_alloca_immutable >> simp[]
QED

Theorem log_cursor_trace_code:
  abi_encode_complex_prefix infos st = (dyn_ptr,prepared) /\
  fn_has_code st prepared func ==>
  MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w 32)]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)
Proof
  rpt strip_tac >> drule abi_encoder_complex_prefix_trace >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  `cs_extends st allocation_st` by
    (irule cs_extends_same_block >> gvs[same_blocks_def]) >>
  `cs_extends allocation_st prepared` by
    (irule cs_extends_same_block >> gvs[same_blocks_def]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all log_buffer_trace_code >> simp[]
QED

Theorem log_encoder_cursor_code:
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,end_st) /\
  fn_has_code st end_st func ==>
  MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w 32)]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)
Proof
  rpt strip_tac >> drule_all abi_encoder_complex_dynamic_trace >> strip_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  drule abi_encoder_members_bounds >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  `cs_extends st prepared` by
    (irule abi_encoder_straight_extends >> asm_simp_tac bool_ss []) >>
  `cs_extends middle end_st` by
    (irule cs_extends_same_block >> gvs[same_blocks_def]) >>
  `cs_extends prepared end_st` by
    (irule cs_extends_trans >> qexists_tac `middle` >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all log_cursor_trace_code >> simp[]
QED
