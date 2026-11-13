Theory bodyPtrTypeBuiltinsBytesWordContinue
Ancestors bodyPtrTypeBuiltinsBytesWordSuccess bodyPtrTypeBuiltinsBytesWordAbort
  bodyPtrTypeBuiltinsBytesWordActual bodyPtrTypeBuiltinsBytesWordInputs
  bodyPtrTypeBuiltinsBytesWordTypes bodyPtrSignedConvertSourceTyping
  fragGasSeqPtr gasStorage vyperStorageFootprint vyperStorageTrace freshWrites
  fragGasPathPtr bodyPtrDefs exprLowering exprLoweringProps loweringPosts
  compileEnv venomState exprSimDefs

Theorem bytes_word_nonzero_outcome_ptr:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  is_bytestring_type (expr_type e) /\ ~is_bytestring_type dst /\
  valid_conversion (expr_type e) dst /\ well_formed_type tenv dst /\
  ~((?b. dst = BaseT (IntT b)) \/ dst = BaseT DecimalT) /\
  lowered_value_type cenv e <> BaseT (BytesT (Dynamic 0)) /\
  lowered_value_type cenv e <> BaseT (StringT 0) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  compile_type_convert x (mk_convert_op (expr_type e) dst) sa = (out,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  fn_has_code sa sb fn /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx fn cenv cx e es ca sa s0 ee v x s /\
    ghost_inv H d cenv cx ee G tn s) /\
  ptr_val_ok cx (expr_type e) v x G tn s /\ ptr_buf_ok cenv e x G s /\
  ghost_kept cenv es ca G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ ca.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  gas_outcome_ptr D tops (ctx,fn) PG cx st0
    (\st. (convert_result cx (expr_type e) dst v,st)) (ee,s,G,tn)
    (\H res fin HG th u. ?vout. res = INL vout /\
      expr_post H ctx fn cenv cx (TypeBuiltin dst Convert dst [e]) es ca sb s0 fin vout out u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv H d cenv cx fin HG th u /\
      ptr_val_ok cx (post_value_type cenv (TypeBuiltin dst Convert dst [e])) vout out HG th u /\
      (~is_word_type (post_value_type cenv (TypeBuiltin dst Convert dst [e])) ==>
        ptr_buf_ok cenv (TypeBuiltin dst Convert dst [e]) out HG u) /\
      ghost_kept cenv es ca G0 tn0 s0 HG th)
    (\H res fin gt r. expr_exit res r)
Proof
  strip_tac >>
  reverse (Cases_on `?H0. valid_horizon cx st0 H0 ee.storage_trace`)
  >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gas_bad_storage_at_initial >>
      simp[storage_trace_frame_def, storage_trace_domain_def] >> metis_tac[]) >>
  pop_assum (qx_choose_then `H0` assume_tac) >> res_tac >>
  `64 <= type_memory_bytes cenv (lowered_value_type cenv e)` by
    (drule_all body_source_lowered_nonzero_capacity >> simp[]) >>
  drule_all bytes_word_child_memory_inputs >> strip_tac >>
  `eval_operand x s = SOME a` by simp[eval_operand_def] >>
  `convert_result cx (expr_type e) dst v = convert_result cx (expr_type e) dst v` by simp[] >>
  drule_all bytes_word_semantic_run_actual >>
  Cases_on `convert_result cx (expr_type e) dst v` >> simp[] >> strip_tac
  >- (`is_word_type dst` by
        (drule_all bytestring_scalar_unsigned_convert_op >> simp[]) >>
      `expr_val_rel cx dst x' out sf` by
        (simp[expr_val_rel_def] >> goal_assum (drule_at Any) >> simp[]) >>
      drule_all bytes_word_success_post_counted >>
      disch_then (qspecl_then [`PG`,`D ARB`] strip_assume_tac) >>
      simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
      simp[gas_summary_ptr_at_def] >>
      qexistsl_tac [`INL x'`,`ee`,`HG`,`th`,
        `OK (sf with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
      simp[] >> gen_tac >> strip_tac >>
      `expr_post H ctx fn cenv cx e es ca sa s0 ee v x s /\
       ghost_inv H d cenv cx ee G tn s` by metis_tac[] >>
      drule_all bytes_word_success_post_counted >>
      disch_then (qspecl_then [`PG`,`D H`] strip_assume_tac) >>
      `HG' = HG /\ th' = th` by metis_tac[inst_seq_ptr_ghost_unique] >>
      gvs[vyperASTTheory.expr_type_def]) >>
  drule_all bytes_word_abort_counted >>
  disch_then (qspecl_then [`PG`,`D ARB`] strip_assume_tac) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    inst_seq_ptr (D H) 0 ctx fn PG G tn (emitted_insts sa sb) s HG th` by
    (rpt strip_tac >>
     `expr_post H ctx fn cenv cx e es ca sa s0 ee v x s /\
      ghost_inv H d cenv cx ee G tn s` by metis_tac[] >>
     drule_all bytes_word_abort_counted >>
     disch_then (qspecl_then [`PG`,`D H`] strip_assume_tac) >>
     `HG' = HG /\ th' = th` by metis_tac[inst_seq_ptr_ghost_unique] >> gvs[]) >>
  drule_all bytes_word_unsigned_code_frame >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (fs[listTheory.EVERY_MEM] >> rpt strip_tac >> res_tac >>
     fs[fresh_write_op_def, venomInstTheory.is_terminator_def]) >>
  drule_all fn_code_emitted_prefix >> strip_tac >>
  drule_all run_inst_seq_abort_zero_path_ptr_uniform >>
  disch_then (qspec_then `ctx` (qx_choose_then `j0` assume_tac)) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR y`,`ee`,`HG`,`th`,`Abort Revert_abort (sf with vs_inst_idx := j0)`] >>
  simp[] >> gen_tac >> strip_tac >> res_tac >>
  gvs[oneline expr_exit_def, AllCaseEqs(), fragExecTheory.exit_result_def] >> metis_tac[]
QED
