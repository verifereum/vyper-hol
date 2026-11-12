Theory bodyPtrTypeBuiltinsScalarOperandContinuation
Ancestors
  bodyPtrTypeBuiltinsScalarContinuation bodyPtrTypeBuiltinsConvertOperandBoundary
  bodyPtrTypeBuiltinsScalarSemantic exprSimSource exprSimOperators exprOperandVar
  exprSimHyps exprSimHypsDefs freshWrites fragGasFresh externalEntryShape
  loweringPosts exprLoweringProps bodyPtrDefs compileEnv loweringStateRelDefs exprSimDefs vyperInterpreter vyperState
  bodyPtrPreds gasOutcomeMarkedPtr gasPathPtrExec gasSummary gasExemptCert
  exprSimConvert fragGasMode fragGasPath fragExec gasSummaryComposePtr

Theorem scalar_convert_operand_continuation:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) (es with gas_obs := gs) /\
  ~is_bytestring_type (expr_type e) /\
  ~((?a f args drv. e = Call a (IntCall f) args drv) /\
    lowered_value_type cenv e <> expr_type e) /\
  (do r <- eval_expr cx e; read_result cx r od) (es with gas_obs := gs) = (INL v,ee) /\
  lower_value compile_expr cenv (expr_type e) e ca = (x,sa) /\
  compile_type_convert x (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op (expr_type e) dst) sa = (out,sb) /\
  fn_has_code sa sb fn /\
  expr_post ctx fn cenv cx e es ca sa s0 ee v x s /\
  ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
  local_ptrs_reserved cenv ca /\ ca.cs_next_var <= sa.cs_next_var /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es ca G0 tn0 s0 G tn /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at ca p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at ca p) ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (\st. (convert_result cx (expr_type e) dst v,st)) (ee,s,G,tn)
    (\res fin H th u. ?vout. res = INL vout /\
      expr_post ctx fn cenv cx (TypeBuiltin dst Convert dst [e]) es ca sb s0 fin vout out u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th u /\
      ptr_val_ok cx (post_value_type cenv (TypeBuiltin dst Convert dst [e])) vout out H th u /\
      (~is_word_type (post_value_type cenv (TypeBuiltin dst Convert dst [e])) ==>
        ptr_buf_ok cenv (TypeBuiltin dst Convert dst [e]) out H u) /\
      ghost_kept cenv es ca G0 tn0 s0 H th)
    (\res fin gt r. expr_exit res r)
Proof
  strip_tac >> drule_all scalar_source_body_word_types >> strip_tac >>
  drule_all expr_body_pre_word_value >> strip_tac >>
  `post_value_type cenv e = expr_type e` by metis_tac[convert_operand_post_type] >>
  `straight_fresh (compile_type_convert x (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op (expr_type e) dst))` by
    metis_tac[bodyPtrTypeBuiltinsScalarRawOutcomeTheory.scalar_dispatch_straight_fresh] >>
  drule_all straight_fresh_code_prefix >> strip_tac >>
  `!name n. FLOOKUP (get_tenv cx) name = SOME (FlagArgs n) ==>
    cenv.ce_flag_n_members (nsid_to_string name) = n` by
    (fs[expr_body_pre_def, expr_sim_inv_def]) >>
  `?tout. evaluate_type (get_tenv cx) dst = SOME tout` by
    (qpat_x_assum `expr_body_pre _ _ _ e _` kall_tac >>
     drule expr_body_pre_type_evaluates >> simp[vyperASTTheory.expr_type_def] >>
     Cases_on `evaluate_type (get_tenv cx) dst` >> simp[]) >>
  `stmt_state_rel ctx fn cenv cx ee s /\
   eval_operand x s = SOME (typed_val_to_w256 tyv v) /\
   op_prov G x = NONE /\ op_taint tn x = {}` by
    (fs[expr_post_def, expr_val_rel_def, ptr_val_ok_def]) >>
  irule scalar_convert_modern_outcome_ptr >> simp[] >>
  rpt (goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (fs[straight_fresh_def] >> metis_tac[]) >>
  qexistsl_tac [`sa`,`x`] >> simp[] >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (fs[straight_fresh_def] >> metis_tac[]) >>
  simp[listTheory.LENGTH_APPEND] >>
  rpt conj_tac
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `ca` >>
      fs[local_ptrs_reserved_def] >> metis_tac[])
  >- (metis_tac[not_fresh_at_mono])
  >- (metis_tac[not_fresh_at_mono])
  >- (metis_tac[compile_lower_value_var])
  >- metis_tac[] >>
  fs[local_ptrs_reserved_def] >> rpt strip_tac >>
  metis_tac[not_fresh_at_mono]
QED

Theorem scalar_convert_expr_sim_ptr:
  body_exprs_ptr_ok cx [e] /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  ~is_bytestring_type (expr_type e) /\
  ~((?a f args drv. e = Call a (IntCall f) args drv) /\
    lowered_value_type cenv e <> expr_type e) ==>
  expr_sim_ptr d ctx PG fn cenv cx ty (TypeBuiltin ann Convert dst [e]) es
Proof
  strip_tac >> drule_all scalar_source_body_word_types >> strip_tac >>
  drule_all convert_operand_ptr_entry >>
  disch_then (qspecl_then [`fn`,`d`,`PG`] strip_assume_tac) >> gvs[] >>
  simp[expr_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule_all lower_value_convert >> strip_tac >>
  `cs_extends sa s1` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends s1 sb` by
    (qspecl_then [`x`,`case ann of FlagT name =>
      ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
      | _ => mk_convert_op (expr_type e) ann`,`s1`] mp_tac
      (cj 1 compile_type_convert_labels) >> simp[]) >>
  `fn_has_code sa s1 fn /\ fn_has_code s1 sb fn` by
    (irule fn_has_code_split >> simp[]) >>
  `gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[SRULE [SF ETA_ss] convert_operand_admissible] >>
  qpat_x_assum `expr_sim_ptr d ctx PG fn cenv cx (expr_type e) e es`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`,`s1`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  irule convert_operand_marked_bind >>
  `!res r. (?exc. res = INR exc /\ expr_exit (INR exc : value + exception) r) <=>
     expr_exit (res : value + exception) r` by
    (Cases >> simp[expr_exit_def]) >>
  simp[] >> qexists_tac `\v ee G tn t.
    expr_post ctx fn cenv cx e es sa s1 s0 ee v x t /\
    t.vs_current_bb = s1.cs_current_bb /\ t.vs_inst_idx = LENGTH s1.cs_current_insts /\
    ghost_inv d cenv cx ee G tn t /\
    ptr_val_ok cx (post_value_type cenv e) v x G tn t /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G t) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn` >>
  (reverse conj_tac >-
    (`post_value_type cenv e = expr_type e` by metis_tac[convert_operand_post_type] >> gvs[])) >>
  rpt gen_tac >> strip_tac >> gnvs[] >>
  suspend "callback"
QED

Resume scalar_convert_expr_sim_ptr[callback]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  drule gas_marked_exec_ptr_exec >>
  simp[gas_marked_exec_def] >> strip_tac >>
  `~t.vs_halted` by metis_tac[gas_marked_path_def, gas_path_normal] >>
  simp[vyperASTTheory.expr_type_def] >>
  qpat_assum `is_word_type ann` (fn th =>
    irule (SRULE [th, vyperASTTheory.expr_type_def]
      (Q.INST [`dst` |-> `ann`] scalar_convert_operand_continuation))) >>
  simp[] >> rpt (goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (qexists_tac `gas_explicit marks s0.vs_gas_readings` >>
      qpat_assum `!tail. _ = (INL v,_)` (qspec_then `[]` mp_tac) >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >>
      pure_rewrite_tac[listTheory.APPEND_NIL] >> simp[]) >>
  `sa.cs_next_var <= s1.cs_next_var` by metis_tac[cj 2 compile_expr_grows] >>
  simp[] >> metis_tac[]
QED
Finalise scalar_convert_expr_sim_ptr
