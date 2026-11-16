(* The scalar saved-length store closing a dynamic sparse array. *)
Theory fullStoreSlotsArraySuffix
Ancestors
  fragGasCopyLoop fragGasSeqPtr fragGasOriginPtr
  assignBasePtrWordStore ptrDiscipline bodyPtrDefs instMemFrontier
  emitHelper emitHelperProps codegenRel contextCodegenRel unitTransformDefs
  fragExec fragExecMem exprLoweringProps arithmetic memSafeRun venomExecSemantics venomState venomInst
  finite_map pred_set list rich_list words stateFrame

Theorem store_slots_scalar_store_origin_ptr:
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id (if tr then TSTORE else SSTORE) [dst;value] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand dst s = SOME k /\ eval_operand value s = SOME w /\
  op_taint tn dst = {} /\ op_taint tn value = {} /\
  op_prov G dst = NONE /\ op_prov G value = NONE /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_call_ctx.cc_static ==>
  !D explicit PG.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK ((if tr then tstore else sstore) k w s with
        vs_inst_idx := SUC s.vs_inst_idx),G,
       if tr then tn with t_trans := key_update tn.t_trans k {}
       else tn with t_stor := key_update tn.t_stor k {})
Proof
  strip_tac >> rpt gen_tac >>
  `ptr_inst_ok D 0 0 ctx func G tn
    (mk_inst id (if tr then TSTORE else SSTORE) [dst;value] []) s` by
    (irule assign_base_ptr_inst_ok_storage_word >> Cases_on `tr` >> simp[]) >>
  `inst_seq_ptr D 0 ctx func PG G tn
    [mk_inst id (if tr then TSTORE else SSTORE) [dst;value] []] s G
    (if tr then tn with t_trans := key_update tn.t_trans k {}
     else tn with t_stor := key_update tn.t_stor k {})` by
    (Cases_on `tr` >>
     gvs[inst_seq_ptr_def,step_inst_base_opcode_eqs,mk_inst_def,exec_write2_def,
       step_prov_def,set_prov_def,out_prov_def,step_taint_def,set_var_taint_def,
       out_taint_def,mem_taint_def,store_taint_def,imm_taint_def,adopt_reset_def,
       step_writes_def,source_memory_write_ranges_def,written_taint_def,
       range_bytes_def,new_site_bytes_def,sstore_def,tstore_def,FLOOKUP_DEF,
       DRESTRICT_UNIV,SF ETA_ss,SF CONJ_ss] >> simp[taint_component_equality]) >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`) run_inst_seq_origin_ptr_lift >>
  disch_then (qspecl_then [`(if tr then tstore else sstore) k w s`,`lo`,`explicit`] mp_tac) >>
  fs[mk_inst_def,is_terminator_def] >>
  (impl_tac >- (Cases_on `tr` >>
    simp[run_inst_seq_mem_ok_def,inst_mem_below_frontier_def,
      inst_dload_in_section_def,source_memory_write_ranges_def,
      source_memory_read_ranges_def,run_inst_seq_def,step_inst_base_opcode_eqs,
      mk_inst_def,is_terminator_def,exec_write2_def,sstore_def,tstore_def])) >>
  simp[ADD1]
QED

Theorem store_slots_length_suffix_origin_ptr:
  emit_void (if tr then TSTORE else SSTORE) [dst;value] sa = ((),sb) /\
  fn_has_code sa sb func /\
  eval_operand dst s = SOME k /\ eval_operand value s = SOME w /\
  op_taint tn dst = {} /\ op_taint tn value = {} /\
  op_prov G dst = NONE /\ op_prov G value = NONE /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_call_ctx.cc_static /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u tf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,G,tf)) /\
    u = ((if tr then tstore else sstore) k w s with
      vs_inst_idx := SUC s.vs_inst_idx) /\
    tf = (if tr then tn with t_trans := key_update tn.t_trans k {}
          else tn with t_stor := key_update tn.t_stor k {}) /\
    u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    (if tr then tf.t_trans else tf.t_stor) =
      key_update (if tr then tn.t_trans else tn.t_stor) k {} /\
    (if tr then tf.t_stor else tf.t_trans) = (if tr then tn.t_stor else tn.t_trans) /\
    (!x. lookup_var x u = lookup_var x s /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_labels = s.vs_labels /\ u.vs_call_ctx = s.vs_call_ctx /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_void_extends >> simp[same_blocks_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX [mk_inst sa.cs_next_id (if tr then TSTORE else SSTORE) [dst;value] []]
      (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def,IS_PREFIX_APPEND] >>
     simp[DROP_APPEND,DROP_LENGTH_NIL]) >>
  qexistsl_tac [`(if tr then tstore else sstore) k w s with
    vs_inst_idx := SUC s.vs_inst_idx`,
    `if tr then tn with t_trans := key_update tn.t_trans k {}
     else tn with t_stor := key_update tn.t_stor k {}`] >>
  conj_tac >- (rpt gen_tac >> irule store_slots_scalar_store_origin_ptr >>
    simp[] >> qexistsl_tac [`dst`,`sa.cs_next_id`,`value`] >> simp[] >>
    qpat_x_assum `[_] ≼ _` mp_tac >> simp[]) >>
  Cases_on `tr` >> simp[sstore_def,tstore_def,lookup_var_def,op_taint_def]
QED
