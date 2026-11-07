(* Shared word-source Convert continuation interfaces. *)
Theory bodyPtrTypeBuiltinsScalarContinue
Ancestors bodyPtrTypeBuiltinsScalarSemantic bodyPtrTypeBuiltinsUintContinue
  exprSimConvert exprSimHyps exprSimDefs exprSimProps exprSimWordArgs
  exprLowering exprLoweringProps compileEnv loweringPosts bodyPtrDefs
  fragGasPathPtr ptrDiscipline vyperAST vyperValue valueEncoding venomState
  bodyPtrTypeBuiltinsScalarChecks bodyPtrTypeBuiltinsSourceFrame
  bodyPtrTypeBuiltinsUintCounted finite_map instIdxIndep fragExec
  bodyPtrTypeBuiltinsScalarArithmetic emitHelper emitHelperProps rich_list list

Theorem scalar_identity_continuation:
  expr_post ctx func cenv cx e es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert typ [e]) es /\
  ~is_bytestring_type (expr_type e) /\
  (case typ of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
   | _ => mk_convert_op (expr_type e) typ) = ConvIdentity /\
  compile_type_convert x ConvIdentity s1 = (op,sb) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v1 /\
  sa.cs_next_var <= s1.cs_next_var /\
  ptr_val_ok cx (expr_type e) v1 x G tn t0 /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,func) PG []
    (\vs. (convert_result cx (expr_type e) typ v1,vs))
    (ee with gas_obs := [],t0,G,tn)
    (\res fin H th ss. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert typ [e])
        es sa sb s0 fin v op ss /\
      ss.vs_current_bb = sb.cs_current_bb /\ ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\
      ptr_val_ok cx typ v op H th ss /\
      ghost_kept cenv es sa G0 tn0 s0 H th)
    (\res fin gt out. expr_exit res out)
Proof
  strip_tac >>
  drule_all scalar_source_body_word_types >> strip_tac >>
  `?tout. evaluate_type (get_tenv cx) typ = SOME tout` by
    (qpat_assum `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _`
       (mp_then Any mp_tac expr_body_pre_type_evaluates) >>
     simp[expr_type_def, optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  drule_all scalar_identity_semantic_packet >> strip_tac >>
  qpat_x_assum `ann = typ` SUBST_ALL_TAC >>
  gvs[compile_type_convert_def, comp_return_def] >>
  `eval_operand op t0 = SOME (typed_val_to_w256 tout v)` by
    (fs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `expr_post ctx func cenv cx (TypeBuiltin typ Convert typ [e])
    es sa s1 s0 (ee with gas_obs := []) v op t0` by
    (irule scalar_suffix_expr_post >> simp[expr_type_def] >>
     conj_tac >- fs[expr_post_def, stmt_state_rel_gas_obs] >>
     qexistsl_tac [`e`,`s1`,`t0`,`v1`,`op`] >>
     simp[] >> fs[expr_post_def]) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL v`,`ee`,`G`,`tn`,`OK t0`] >>
  fs[ptr_val_ok_def] >> simp[gas_path_ptr_rules]
QED

Theorem scalar_flag_counted_success:
  compile_type_convert x (ConvToFlag n) s1 = (op,sb) /\
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
  strip_tac >> drule_all convert_flag_counted_certificate >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `t = s with vs_vars := t.vs_vars /\
   (!p. not_fresh_at s1 p ==> lookup_var p t = lookup_var p s)` by
    (drule_all convert_flag_runtime_frame >>
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

Theorem scalar_flag_continuation:
  expr_post ctx func cenv cx e es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert (FlagT name) [e]) es /\
  compile_type_convert x (ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))) s1 = (op,sb) /\
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
    (\vs. (convert_result cx (expr_type e) (FlagT name) v1,vs))
    (ee with gas_obs := [],t0,G,tn)
    (\res fin H th ss. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert (FlagT name) [e])
        es sa sb s0 fin v op ss /\
      ss.vs_current_bb = sb.cs_current_bb /\ ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\
      ptr_val_ok cx (FlagT name) v op H th ss /\
      ghost_kept cenv es sa G0 tn0 s0 H th)
    (\res fin gt out. expr_exit res out)
Proof
  strip_tac >> drule_all scalar_flag_body_packet >> strip_tac >> gvs[] >>
  `eval_operand x t0 = SOME (i2w i)` by
    fs[expr_post_def, expr_val_rel_def, is_word_type_def] >>
  drule_all scalar_flag_compile_frame >> strip_tac >>
  `?bb. lookup_block t0.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts s1 sb) (DROP t0.vs_inst_idx bb.bb_instructions)` by
    (irule fn_code_emitted_prefix >> simp[] >> metis_tac[]) >>
  `op_prov G x = NONE /\ op_taint tn x = {}` by
    fs[ptr_val_ok_def, is_word_type_def] >>
  drule_all scalar_flag_semantic_actual >>
  Cases_on `convert_result cx (BaseT (UintT 256)) (FlagT name) (IntV i)` >>
  simp[] >> strip_tac
  >- suspend "success"
  >> suspend "abort"
QED

Resume scalar_flag_continuation[abort]:
  `cenv.ce_flag_n_members (nsid_to_string name) < 256` by
    (spose_not_then assume_tac >>
     gvs[compile_type_convert_def, comp_return_def, emitted_insts_refl,
         run_inst_seq_def]) >>
  `compile_int_clamp F (cenv.ce_flag_n_members (nsid_to_string name)) x s1 = (op,sb)` by
    fs[compile_type_convert_def] >>
  drule_all int_clamp_abort_zero_counted >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR y`,`ee`,`H`,`th`,`Abort Revert_abort (sf with vs_inst_idx := j)`] >>
  simp[exit_result_def, expr_exit_def]
QED

Resume scalar_flag_continuation[success]:
  drule_all scalar_flag_counted_success >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  `sf = t0 with vs_vars := sf.vs_vars` by
    fs[venom_state_component_equality] >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) sf` by
    (irule stmt_state_rel_readonly_vars_pc >>
     qexistsl_tac [`t0`,`s1`] >> simp[] >> reverse conj_tac
     >- fs[expr_post_def, stmt_state_rel_gas_obs] >>
     qpat_x_assum `sf = t0 with vs_vars := _` SUBST1_TAC >>
     simp[venom_state_component_equality]) >>
  `expr_post ctx func cenv cx (TypeBuiltin (FlagT name) Convert (FlagT name) [e])
    es sa sb s0 (ee with gas_obs := []) x' x
      (sf with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule scalar_suffix_expr_post >>
     simp[expr_type_def, is_word_type_def, stmt_state_rel_inst_idx,
          eval_op_inst_idx] >>
     conj_tac >- fs[stmt_state_rel_gas_obs] >>
     qexistsl_tac [`e`,`s1`,`t0`,`IntV i`,`x`] >> simp[lookup_var_def] >>
     conj_tac >- (fs[lookup_var_def] >> metis_tac[]) >>
     qpat_x_assum `sf = t0 with vs_vars := _` SUBST1_TAC >> simp[]) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL x'`,`ee`,`H`,`th`,
    `OK (sf with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  gvs[ptr_val_ok_def, is_word_type_def, arithmeticTheory.ADD_COMM] >>
  qpat_x_assum `sf = t0 with vs_vars := _` SUBST_ALL_TAC >>
  gvs[venom_state_component_equality]
QED

Finalise scalar_flag_continuation

Theorem scalar_fixed_int_compile_frame:
  compile_type_convert x (ConvBytesToInt m sg b) sa = (r,sb) ==>
  inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb)
Proof
  Cases_on `sg` >> Cases_on `m*8 > b` >>
  simp[compile_type_convert_def, compile_int_clamp_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def, inst_extends_def] >>
  rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem scalar_fixed_int_counted_success:
  compile_type_convert x (ConvBytesToInt m sg b) s1 = (op,sb) /\
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
  strip_tac >> drule_all convert_bytes_int_counted_certificate >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `t = s with vs_vars := t.vs_vars /\
   (!p. not_fresh_at s1 p ==> lookup_var p t = lookup_var p s)` by
    (drule_all convert_bytes_int_runtime_frame >>
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

Theorem scalar_fixed_int_abort_zero_counted:
  compile_type_convert x (ConvBytesToInt m sg b) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th j. gas_path_ptr D 0 ctx fn PG G tn s 0 H th
    (Abort err (t with vs_inst_idx := j))
Proof
  strip_tac >>
  drule_all (cj 2 (PURE_REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM] convert_bytes_int_fixed_certificate)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  drule convert_bytes_int_instruction_filter >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
     i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  drule_all no_gas_seq_abort_counted >> metis_tac[]
QED

Theorem scalar_fixed_int_continuation:
  expr_post ctx func cenv cx e es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  expr_body_pre cenv cx env
    (TypeBuiltin ann Convert (BaseT (if sg then IntT b else UintT b)) [e]) es /\
  expr_type e = BaseT (BytesT (Fixed m)) /\
  compile_type_convert x (mk_convert_op (expr_type e)
    (BaseT (if sg then IntT b else UintT b))) s1 = (op,sb) /\
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
    (\vs. (convert_result cx (expr_type e) (BaseT (if sg then IntT b else UintT b)) v1,vs))
    (ee with gas_obs := [],t0,G,tn)
    (\res fin H th ss. ?v. res = INL v /\
      expr_post ctx func cenv cx
        (TypeBuiltin ann Convert (BaseT (if sg then IntT b else UintT b)) [e])
        es sa sb s0 fin v op ss /\
      ss.vs_current_bb = sb.cs_current_bb /\ ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\
      ptr_val_ok cx (BaseT (if sg then IntT b else UintT b)) v op H th ss /\
      ghost_kept cenv es sa G0 tn0 s0 H th)
    (\res fin gt out. expr_exit res out)
Proof
  strip_tac >>
  `ann = BaseT (if sg then IntT b else UintT b)` by
    (drule expr_body_pre_convert >> simp[]) >> gvs[] >>
  `?tout. evaluate_type (get_tenv cx) (BaseT (if sg then IntT b else UintT b)) = SOME tout` by
    (qpat_assum `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _`
       (mp_then Any mp_tac expr_body_pre_type_evaluates) >>
     simp[expr_type_def, optionTheory.IS_SOME_EXISTS]) >>
  `is_word_type (BaseT (if sg then IntT b else UintT b))` by
    (Cases_on `sg` >> simp[is_word_type_def]) >>
  `m <= 32` by fs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  `eval_operand x t0 = SOME (typed_val_to_w256 tv v1)` by
    fs[expr_post_def, expr_val_rel_def, is_word_type_def] >>
  drule_all scalar_fixed_int_all_typed_actual >>
  `compile_type_convert x (ConvBytesToInt m sg b) s1 = (op,sb)` by
    (Cases_on `sg` >> fs[mk_convert_op_def, is_bytestring_type_def,
      type_bits_def, type_bounds_def, is_signed_type_def]) >>
  drule_all scalar_fixed_int_compile_frame >> strip_tac >>
  `?bb. lookup_block t0.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts s1 sb) (DROP t0.vs_inst_idx bb.bb_instructions)` by
    (irule fn_code_emitted_prefix >> simp[] >> metis_tac[]) >>
  `op_prov G x = NONE /\ op_taint tn x = {}` by
    fs[ptr_val_ok_def, is_word_type_def] >>
  Cases_on `convert_result cx (BaseT (BytesT (Fixed m)))
    (BaseT (if sg then IntT b else UintT b)) v1` >> simp[] >> strip_tac
  >- suspend "success"
  >> suspend "abort"
QED

Resume scalar_fixed_int_continuation[abort]:
  drule_all scalar_fixed_int_abort_zero_counted >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR y`,`ee`,`H`,`th`,`Abort Revert_abort (sf with vs_inst_idx := j)`] >>
  simp[exit_result_def, expr_exit_def]
QED

Resume scalar_fixed_int_continuation[success]:
  drule_all scalar_fixed_int_counted_success >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  `sf = t0 with vs_vars := sf.vs_vars` by
    fs[venom_state_component_equality] >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) sf` by
    (irule stmt_state_rel_readonly_vars_pc >>
     qexistsl_tac [`t0`,`s1`] >> simp[] >> reverse conj_tac
     >- fs[expr_post_def, stmt_state_rel_gas_obs] >>
     qpat_x_assum `sf = t0 with vs_vars := _` SUBST1_TAC >>
     simp[venom_state_component_equality]) >>
  `expr_post ctx func cenv cx
    (TypeBuiltin (BaseT (if sg then IntT b else UintT b)) Convert
      (BaseT (if sg then IntT b else UintT b)) [e])
    es sa sb s0 (ee with gas_obs := []) x' op
      (sf with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule scalar_suffix_expr_post >>
     simp[expr_type_def, is_word_type_def, stmt_state_rel_inst_idx,
          eval_op_inst_idx] >>
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

Finalise scalar_fixed_int_continuation

Theorem scalar_fixed_decimal_continuation:
  expr_post ctx func cenv cx e es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert (BaseT DecimalT) [e]) es /\
  expr_type e = BaseT (BytesT (Fixed m)) /\
  compile_type_convert x (mk_convert_op (expr_type e) (BaseT DecimalT)) s1 = (op,sb) /\
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
    (\vs. (convert_result cx (expr_type e) (BaseT DecimalT) v1,vs))
    (ee with gas_obs := [],t0,G,tn)
    (\res fin H th ss. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert (BaseT DecimalT) [e])
        es sa sb s0 fin v op ss /\
      ss.vs_current_bb = sb.cs_current_bb /\ ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\
      ptr_val_ok cx (BaseT DecimalT) v op H th ss /\
      ghost_kept cenv es sa G0 tn0 s0 H th)
    (\res fin gt out. expr_exit res out)
Proof
  strip_tac >>
  `ann = BaseT DecimalT` by (drule expr_body_pre_convert >> simp[]) >> gvs[] >>
  `evaluate_type (get_tenv cx) (BaseT DecimalT) = SOME (BaseTV DecimalT)` by
    simp[vyperValueTheory.evaluate_type_def] >>
  `m <= 32` by fs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  `eval_operand x t0 = SOME (typed_val_to_w256 tv v1)` by
    fs[expr_post_def, expr_val_rel_def, is_word_type_def] >>
  drule_all scalar_fixed_decimal_all_typed_actual >>
  `compile_type_convert x (ConvBytesToInt m T 168) s1 = (op,sb)` by
    fs[scalar_fixed_decimal_compile_eq] >>
  drule_all scalar_fixed_int_compile_frame >> strip_tac >>
  `?bb. lookup_block t0.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts s1 sb) (DROP t0.vs_inst_idx bb.bb_instructions)` by
    (irule fn_code_emitted_prefix >> simp[] >> metis_tac[]) >>
  `op_prov G x = NONE /\ op_taint tn x = {}` by
    fs[ptr_val_ok_def, is_word_type_def] >>
  Cases_on `convert_result cx (BaseT (BytesT (Fixed m))) (BaseT DecimalT) v1` >>
  simp[] >> strip_tac
  >- suspend "success"
  >> suspend "abort"
QED

Resume scalar_fixed_decimal_continuation[abort]:
  drule_all scalar_fixed_int_abort_zero_counted >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR y`,`ee`,`H`,`th`,`Abort Revert_abort (sf with vs_inst_idx := j)`] >>
  simp[exit_result_def, expr_exit_def]
QED

Resume scalar_fixed_decimal_continuation[success]:
  drule_all scalar_fixed_int_counted_success >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  `sf = t0 with vs_vars := sf.vs_vars` by fs[venom_state_component_equality] >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) sf` by
    (irule stmt_state_rel_readonly_vars_pc >>
     qexistsl_tac [`t0`,`s1`] >> simp[] >> reverse conj_tac
     >- fs[expr_post_def, stmt_state_rel_gas_obs] >>
     qpat_x_assum `sf = t0 with vs_vars := _` SUBST1_TAC >>
     simp[venom_state_component_equality]) >>
  `expr_post ctx func cenv cx (TypeBuiltin (BaseT DecimalT) Convert (BaseT DecimalT) [e])
    es sa sb s0 (ee with gas_obs := []) x' op
      (sf with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule scalar_suffix_expr_post >>
     simp[expr_type_def, is_word_type_def, stmt_state_rel_inst_idx, eval_op_inst_idx] >>
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

Finalise scalar_fixed_decimal_continuation
