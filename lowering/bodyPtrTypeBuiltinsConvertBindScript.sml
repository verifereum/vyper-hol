Theory bodyPtrTypeBuiltinsConvertBind
Ancestors
  bodyPtrTypeBuiltinsConvertOperandBoundary exprSimSource exprSimHyps
  exprSimHypsDefs freshWrites fragGasFresh externalEntryShape
  loweringPosts exprLoweringProps bodyPtrDefs compileEnv exprSimDefs
  vyperInterpreter vyperState bodyPtrPreds gasOutcomeMarkedPtr gasPathPtrExec
  gasSummary gasExemptCert exprSimConvert fragGasMode fragGasPath fragExec
  gasSummaryComposePtr

Theorem convert_bind_expr_sim_ptr:
  body_exprs_ptr_ok cx [e] /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  ~((?a f args drv. e = Call a (IntCall f) args drv) /\
    lowered_value_type cenv e <> expr_type e) /\
  (!ca out cb.
    lower_value compile_expr cenv ty (TypeBuiltin ann Convert dst [e]) ca = (out,cb) ==>
    ?x sa. lower_value compile_expr cenv (expr_type e) e ca = (x,sa) /\
      suffix x sa out cb /\ cs_extends sa cb) /\
  (!ca x sa out cb s0 G0 tn0 gs v ee G tn s.
    suffix x sa out cb /\ lower_value compile_expr cenv (expr_type e) e ca = (x,sa) /\
    fn_has_code ca sa fn /\ fn_has_code sa cb fn /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved cenv ca /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at ca p) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at ca p) /\
    stmt_state_rel ctx fn cenv cx es s0 /\ ghost_inv d cenv cx es G0 tn0 s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = ca.cs_current_bb /\
    s0.vs_inst_idx = LENGTH ca.cs_current_insts /\
    ca.cs_next_var <= sa.cs_next_var /\
    (bind (eval_expr cx e) (read_result cx)) (es with gas_obs := gs) = (INL v,ee with gas_obs := []) /\
    expr_post ctx fn cenv cx e es ca sa s0 (ee with gas_obs := []) v x s /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~s.vs_halted /\ ghost_inv d cenv cx (ee with gas_obs := []) G tn s /\
    ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G s) /\
    ghost_kept cenv es ca G0 tn0 s0 G tn ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
      (\st. (convert_result cx (expr_type e) dst v,st)) (ee with gas_obs := [],s,G,tn)
      (\res fin H th u. ?vout. res = INL vout /\
        expr_post ctx fn cenv cx (TypeBuiltin ann Convert dst [e]) es ca cb s0 fin vout out u /\
        u.vs_current_bb = cb.cs_current_bb /\ u.vs_inst_idx = LENGTH cb.cs_current_insts /\
        ghost_inv d cenv cx fin H th u /\
        ptr_val_ok cx (post_value_type cenv (TypeBuiltin ann Convert dst [e])) vout out H th u /\
        (~is_word_type (post_value_type cenv (TypeBuiltin ann Convert dst [e])) ==>
          ptr_buf_ok cenv (TypeBuiltin ann Convert dst [e]) out H u) /\
        ghost_kept cenv es ca G0 tn0 s0 H th)
      (\res fin gt r. expr_exit res r)) ==>
  expr_sim_ptr d ctx PG fn cenv cx ty (TypeBuiltin ann Convert dst [e]) es
Proof
  strip_tac >> drule_all convert_operand_ptr_entry >>
  disch_then (qspecl_then [`fn`,`d`,`PG`] strip_assume_tac) >> gvs[] >>
  simp[expr_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!ca out cb. _` drule >> strip_tac >>
  `cs_extends sa sa'` by metis_tac[cj 2 compile_expr_grows] >>
  `fn_has_code sa sa' fn /\ fn_has_code sa' sb fn` by
    (irule fn_has_code_split >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[SRULE [SF ETA_ss] convert_operand_admissible] >>
  qpat_x_assum `expr_sim_ptr d ctx PG fn cenv cx (expr_type e) e es`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`,`sa'`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  irule convert_operand_marked_bind >>
  `!res r. (?exc. res = INR exc /\ expr_exit (INR exc : value + exception) r) <=>
     expr_exit (res : value + exception) r` by
    (Cases >> simp[expr_exit_def]) >>
  simp[] >> qexists_tac `\v ee G tn t.
    expr_post ctx fn cenv cx e es sa sa' s0 ee v x t /\
    t.vs_current_bb = sa'.cs_current_bb /\ t.vs_inst_idx = LENGTH sa'.cs_current_insts /\
    ghost_inv d cenv cx ee G tn t /\
    ptr_val_ok cx (post_value_type cenv e) v x G tn t /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G t) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn` >>
  (reverse conj_tac >-
    (`post_value_type cenv e = expr_type e` by metis_tac[convert_operand_post_type] >> gvs[])) >>
  rpt gen_tac >> strip_tac >> gnvs[] >>
  suspend "callback"
QED

Resume convert_bind_expr_sim_ptr[callback]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  drule gas_marked_exec_ptr_exec >>
  simp[gas_marked_exec_def] >> strip_tac >>
  `~t.vs_halted` by metis_tac[gas_marked_path_def, gas_path_normal] >>
  qpat_x_assum `!ca x sa out cb s0 G0 tn0 gs v ee G tn s. _` irule >>
  simp[] >> rpt (goal_assum (drule_at Any) >> simp[]) >>
  (reverse conj_tac >- metis_tac[cj 2 compile_expr_grows]) >>
  qexists_tac `gas_explicit marks s0.vs_gas_readings` >>
  qpat_assum `!tail. _ = (INL v,_)` (qspec_then `[]` mp_tac) >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  pure_rewrite_tac[listTheory.APPEND_NIL] >> simp[]
QED
Finalise convert_bind_expr_sim_ptr
