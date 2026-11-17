Theory bodyFullAssignImmutableWord_L0004
Ancestors
  immutableAssignCompose immutableAssignStore immutableDeployAssignFacts
  exprPtrCtorImmStore fragGasSeqPtr fragGasOriginPtr fragExecMem
  emitHelper memSafeRun unitTransformDefs
  instMemFrontier bodyFullMemoryFrames bodyPtrDefs stateRelProj
  immutableWordExecution immutableCopyExecution emitHelperProps
  context stmtLowering compileEnv exprLoweringProps loweringStateRelDefs
  venomState venomExecSemantics venomInst finite_map list rich_list words bodyFullUnwrapRun exprSimCopy ptrDiscipline

Theorem body_assign_immutable_word_mem_ok:
  compile_imm_store_word imm (Lit (n2w off)) op sa = ((),sb) /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\
  off < dimword (:256) /\ off + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> Cases_on `imm` >>
  qpat_x_assum `compile_imm_store_word _ _ _ _ = _` mp_tac >>
  simp[compile_imm_store_word_def,emit_op_def,emit_void_def,
       fresh_id_def,fresh_var_def,emit_def,comp_bind_def,
       comp_ignore_bind_def,comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def,DROP_APPEND] >>
  simp[run_inst_seq_mem_ok_def,inst_dload_in_section_def,
       below_frontier_ISTORE,inst_mem_below_frontier_def,mk_inst_def,
       step_inst_base_opcode_eqs,exec_pure2_def,eval_operand_def,
       update_var_def,lookup_var_def,FLOOKUP_UPDATE,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       arithmeticTheory.SUB_PLUS] >>
  simp[codegenRelTheory.fixed_source_write_range_def,
       eval_operand_def,lookup_var_def,FLOOKUP_UPDATE] >>
  rpt CASE_TAC >> gvs[WORD_ADD_0,w2n_n2w]
QED

Theorem body_assign_immutable_word_execution:
  compile_assign_value ce (Lit (n2w off)) LocCode op T loc ity sty bytes su = ((),sb) /\
  fn_has_code su sb func /\ fresh_vars_wrt su s /\
  (!x. op = Var x ==> not_fresh_at su x) /\
  (!region. ce.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ op_taint tn region = {} /\ op_prov G region = NONE) /\
  eval_operand op s = SOME (typed_val_to_w256 itv v) /\ op_taint tn op = {} /\
  evaluate_type tenv ity = SOME itv /\ is_word_type ity /\ value_has_type itv v /\
  off < dimword (:256) /\ off + 32 <= lo /\ lo <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?u Gf tf.
    run_inst_seq (emitted_insts su sb) s = OK u /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf) /\
    immutable_execution_frame su s sb u /\
    tf.t_mem = tn.t_mem DIFF {j | off <= j /\ j < off + 32} /\
    tf.t_imm = key_update tn.t_imm off {} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. not_fresh_at su p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p)) /\
    (!p n. not_fresh_at su p /\ ptr_covers G tn p s n ==> ptr_covers Gf tf p u n) /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    val_in_memory itv v off u.vs_memory /\
    u.vs_memory = (mstore off (typed_val_to_w256 itv v) s).vs_memory /\
    u.vs_immutables = s.vs_immutables |+ (off,typed_val_to_w256 itv v) /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_immutables := s.vs_immutables|>) = s
Proof
  strip_tac >>
  `compile_imm_store_word ce.ce_imm_alloca (Lit (n2w off)) op su = ((),sb)` by
    fs[compile_assign_value_def,comp_bind_def,comp_return_def] >>
  `copy_old_operand su op` by fs[copy_old_operand_def] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
   op_taint tn (Lit (n2w off)) = {} /\ op_prov G (Lit (n2w off)) = NONE` by
    simp[eval_operand_def,op_taint_def,op_prov_def] >>
  `w2n (n2w off : bytes32) = off` by simp[w2n_n2w] >>
  drule code_ctor_store_word >>
  disch_then drule >>
  disch_then drule >>
  disch_then drule >>
  simp[] >>
  disch_then drule >>
  disch_then drule >>
  disch_then (qspecl_then [`func`,`ctx`,`PG`,`G`,`D`] mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  `!region. ce.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w`
    by metis_tac[] >>
  drule_all immutable_assign_word_store >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `u = t` by fs[immutable_execution_frame_def] >> gvs[] >>
  qexistsl_tac [`Gf`,`tnf`] >> simp[] >>
  irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
  simp[] >> qexistsl_tac [`emitted_insts su sb`,`su`] >>
  fs[immutable_execution_frame_def,same_blocks_def] >>
  conj_tac >- (fs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
    fs[is_terminator_def]) >>
  conj_tac >- (irule body_assign_immutable_word_mem_ok >>
    qexistsl_tac [`ce.ce_imm_alloca`,`off`,`op`] >>
    simp[] >> decide_tac) >>
  first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]
QED
