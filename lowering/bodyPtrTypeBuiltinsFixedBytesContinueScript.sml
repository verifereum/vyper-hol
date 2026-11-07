(* All-length fixed byte conversions, including zero-length destinations. *)
Theory bodyPtrTypeBuiltinsFixedBytesContinue
Ancestors bodyPtrTypeBuiltinsFixedAddressContinue bodyPtrTypeBuiltinsScalarChecks
  convertScalarEncoding convertScalarBytesRun exprSimConvert exprLowering
  exprLoweringProps compileEnv vyperValue vyperValueOperation vyperTyping
  valueEncoding varsExt freshWrites venomState words byte rich_list list
  exprSimDefs exprSimHyps exprSimProps exprSimWordArgs loweringPosts
  bodyPtrDefs fragGasPathPtr ptrDiscipline emitHelperProps instIdxIndep finite_map
  vyperAST bodyPtrTypeBuiltinsUintCounted bodyPtrTypeBuiltinsUintContinue fragExec
  bodyPtrTypeBuiltinsSourceFrame emitHelper venomInst venomExecSemantics vyperTypeSystem

Theorem scalar_fixed_fixed_raw_semantic:
  LENGTH bs = m /\ m <= 32 /\ n <= 32 /\
  compile_type_convert x (ConvBytesMToBytesM m n) sa = (r,sb) /\
  eval_operand x ss = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs)) /\
  fresh_vars_wrt sa ss ==>
  case convert_result cx (BaseT (BytesT (Fixed m))) (BaseT (BytesT (Fixed n))) (BytesV bs) of
    INL out => ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed n))) out)
  | INR ex => (?msg. ex = Error (RuntimeError msg)) /\
      ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  strip_tac >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def] >>
  Cases_on `n < m` >> simp[]
  >- (Cases_on `EVERY (\b. b = 0w) (DROP n bs)` >> simp[]
      >- (drule_all scalar_bytes_narrow_run_ok >> strip_tac >>
          goal_assum (drule_at Any) >> simp[scalar_fixed_narrow]) >>
      drule_all scalar_bytes_narrow_run_abort >> simp[]) >>
  gvs[compile_type_convert_def, comp_return_def, emitted_insts_def, run_inst_seq_def] >>
  simp[scalar_fixed_widen]
QED

Theorem scalar_fixed_fixed_replay:
  compile_type_convert x (ConvBytesMToBytesM m n) sa = (r,sb) ==>
  vars_ext_result
    (run_inst_seq (emitted_insts sa sb) (drop_fresh sa ss))
    (run_inst_seq (emitted_insts sa sb) ss)
Proof
  strip_tac >> irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
  Cases_on `n < m` >>
  gvs[compile_type_convert_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >>
  simp[emitted_insts_def] >>
  rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def, is_ext_call_op_def]
QED

Theorem scalar_fixed_fixed_typed_actual:
  evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = SOME tv /\
  value_has_type tv v /\ n <= 32 /\
  compile_type_convert x (ConvBytesMToBytesM m n) sa = (r,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x ss = SOME (typed_val_to_w256 tv v) ==>
  case convert_result cx (BaseT (BytesT (Fixed m))) (BaseT (BytesT (Fixed n))) v of
    INL out => ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed n))) out) /\
      (sf with vs_vars := ss.vs_vars) = ss /\
      (!z. not_fresh_at sa z ==> lookup_var z sf = lookup_var z ss)
  | INR ex => (?msg. ex = Error (RuntimeError msg)) /\
      ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  simp[vyperValueTheory.evaluate_type_def] >> strip_tac >> gvs[] >>
  Cases_on `v` >> fs[value_has_type_def, AllCaseEqs()] >>
  `fresh_vars_wrt sa (drop_fresh sa ss)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand x (drop_fresh sa ss) = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV l))` by
    simp[eval_operand_drop_fresh] >>
  drule_all scalar_fixed_fixed_raw_semantic >>
  disch_then (qspec_then `cx` mp_tac) >>
  Cases_on `convert_result cx (BaseT (BytesT (Fixed m))) (BaseT (BytesT (Fixed n))) (BytesV l)` >>
  simp[] >> strip_tac >>
  drule scalar_fixed_fixed_replay >> disch_then (qspec_then `ss` mp_tac) >>
  simp[vars_ext_result_def] >> strip_tac >> gvs[]
  >- (rename1 `run_inst_seq (emitted_insts sa sb) ss = OK actual` >> conj_tac
      >- (fs[vars_ext_def] >>
          qpat_x_assum `actual = _ with vs_vars := _` SUBST1_TAC >>
          simp[eval_operand_vars_ext]) >>
      irule convert_bytesm_runtime_frame >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any)) >> simp[]
QED

Theorem scalar_fixed_fixed_compile_frame:
  compile_type_convert x (ConvBytesMToBytesM m n) sa = (r,sb) ==>
  inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb)
Proof
  Cases_on `n < m` >>
  simp[compile_type_convert_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def, inst_extends_def] >>
  rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem scalar_fixed_fixed_counted_success:
  compile_type_convert x (ConvBytesMToBytesM m n) s1 = (op,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts s1 sb) s = OK t /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts s1 sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  local_ptrs_reserved cenv s1 /\ sa.cs_next_var <= s1.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at s1 p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at s1 p) /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 sa G0 tn0 s0 G tn ==>
  ?H th. gas_path_ptr D 0 ctx func PG G tn s 0 H th
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts s1 sb))) /\
    op_prov H op = NONE /\ op_taint th op = {} /\
    ghost_inv d cenv cx es H th
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts s1 sb)) /\
    ghost_kept cenv es0 sa G0 tn0 s0 H th
Proof
  strip_tac >> drule_all convert_bytesm_counted_certificate >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `t = s with vs_vars := t.vs_vars /\
   (!p. not_fresh_at s1 p ==> lookup_var p t = lookup_var p s)` by
    (drule_all convert_bytesm_runtime_frame >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `ghost_inv d cenv cx es H th
    (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts s1 sb))` by
    (irule ghost_inv_readonly_frame >>
     qexistsl_tac [`G`,`not_fresh_at s1`,`s`,`tn`] >>
     qpat_x_assum `t = s with vs_vars := _` SUBST_ALL_TAC >>
     fs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]) >>
  `ghost_kept cenv es0 sa G0 tn0 s0 H th` by
    (irule ghost_kept_readonly_frame >>
     qexistsl_tac [`G`,`not_fresh_at s1`,`tn`] >> simp[] >>
     fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qexistsl_tac [`H`,`th`] >> simp[]
QED

Theorem scalar_fixed_fixed_abort_zero_counted:
  compile_type_convert x (ConvBytesMToBytesM m n) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th j. gas_path_ptr D 0 ctx fn PG G tn s 0 H th
    (Abort err (t with vs_inst_idx := j))
Proof
  strip_tac >>
  drule_all (cj 2 (PURE_REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM] convert_bytesm_fixed_certificate)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  drule convert_bytesm_instruction_filter >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
     i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  drule_all no_gas_seq_abort_counted >> metis_tac[]
QED

Theorem scalar_fixed_fixed_continuation:
  expr_post ctx func cenv cx e es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert (BaseT (BytesT (Fixed n))) [e]) es /\
  expr_type e = BaseT (BytesT (Fixed m)) /\
  compile_type_convert x (mk_convert_op (expr_type e) (BaseT (BytesT (Fixed n)))) s1 = (op,sb) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v1 /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  fn_has_code s1 sb func /\ local_ptrs_reserved cenv s1 /\
  sa.cs_next_var <= s1.cs_next_var /\ ~ctx_has_dalloca ctx /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at s1 p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at s1 p) /\
  ptr_val_ok cx (expr_type e) v1 x G tn t0 /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,func) PG []
    (\vs. (convert_result cx (expr_type e) (BaseT (BytesT (Fixed n))) v1,vs))
    (ee with gas_obs := [],t0,G,tn)
    (\res fin H th ss. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert (BaseT (BytesT (Fixed n))) [e])
        es sa sb s0 fin v op ss /\
      ss.vs_current_bb = sb.cs_current_bb /\ ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\
      ptr_val_ok cx (BaseT (BytesT (Fixed n))) v op H th ss /\
      ghost_kept cenv es sa G0 tn0 s0 H th)
    (\res fin gt out. expr_exit res out)
Proof
  strip_tac >>
  `ann = BaseT (BytesT (Fixed n))` by
    (drule expr_body_pre_convert >> simp[]) >> gvs[] >>
  `n <= 32` by
    (drule expr_body_pre_type_evaluates >>
     simp[expr_type_def, vyperValueTheory.evaluate_type_def]) >>
  `m <= 32` by fs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  `eval_operand x t0 = SOME (typed_val_to_w256 tv v1)` by
    fs[expr_post_def, expr_val_rel_def, is_word_type_def] >>
  `compile_type_convert x (ConvBytesMToBytesM m n) s1 = (op,sb)` by
    fs[mk_convert_op_def, is_bytestring_type_def] >>
  drule_all scalar_fixed_fixed_typed_actual >>
  drule_all scalar_fixed_fixed_compile_frame >> strip_tac >>
  `?bb. lookup_block t0.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts s1 sb) (DROP t0.vs_inst_idx bb.bb_instructions)` by
    (irule fn_code_emitted_prefix >> simp[] >> metis_tac[]) >>
  `op_prov G x = NONE /\ op_taint tn x = {}` by
    fs[ptr_val_ok_def, is_word_type_def] >>
  Cases_on `convert_result cx (BaseT (BytesT (Fixed m))) (BaseT (BytesT (Fixed n))) v1` >>
  simp[] >> strip_tac
  >- suspend "success"
  >> suspend "abort"
QED

Resume scalar_fixed_fixed_continuation[abort]:
  drule_all scalar_fixed_fixed_abort_zero_counted >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR y`,`ee`,`H`,`th`,`Abort Revert_abort (sf with vs_inst_idx := j)`] >>
  simp[exit_result_def, expr_exit_def]
QED

Resume scalar_fixed_fixed_continuation[success]:
  drule_all scalar_fixed_fixed_counted_success >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  `sf = t0 with vs_vars := sf.vs_vars` by fs[venom_state_component_equality] >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) sf` by
    (irule stmt_state_rel_readonly_vars_pc >>
     qexistsl_tac [`t0`,`s1`] >> simp[] >> reverse conj_tac
     >- fs[expr_post_def, stmt_state_rel_gas_obs] >>
     qpat_x_assum `sf = t0 with vs_vars := _` SUBST1_TAC >>
     simp[venom_state_component_equality]) >>
  `expr_post ctx func cenv cx
    (TypeBuiltin (BaseT (BytesT (Fixed n))) Convert (BaseT (BytesT (Fixed n))) [e])
    es sa sb s0 (ee with gas_obs := []) x' op
      (sf with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule scalar_suffix_expr_post >>
     simp[expr_type_def, is_word_type_def, stmt_state_rel_inst_idx, eval_op_inst_idx,
          vyperValueTheory.evaluate_type_def] >>
     conj_tac >- fs[stmt_state_rel_gas_obs] >>
     qexistsl_tac [`e`,`s1`,`t0`,`v1`,`x`] >> simp[lookup_var_def] >>
     conj_tac >- (fs[lookup_var_def] >> metis_tac[]) >>
     qpat_x_assum `sf = t0 with vs_vars := _` SUBST1_TAC >> simp[]) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL x'`,`ee`,`H`,`th`,
    `OK (sf with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  gvs[ptr_val_ok_def, is_word_type_def, arithmeticTheory.ADD_COMM] >>
  qpat_x_assum `sf = t0 with vs_vars := _` SUBST_ALL_TAC >>
  gvs[venom_state_component_equality]
QED

Finalise scalar_fixed_fixed_continuation
