(* Linked scalar keyword operand boundary. *)
Theory bodyExtKeywordScalarMods
Ancestors
  bodyFullPostsMods gasShadowCompileHelpers gasOutcomeFullPostMods
  exprLoweringProps exprSimDefs compileEnv vyperInterpreter vyperState
  vyperTypeSystem vyperValue
  bodyPtrDefs loweringPosts gasContext allocaHistory
  bodyExtKeywordScalarTypingMods exprBopSimProps exprSimSend
Libs monadsyntax

Theorem ext_kw_scalar_head_mods:
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (ext_call_kw_type rt k) e es /\
  expr_body_pre_mods mods cenv cx env e es /\
  expr_type e = ext_call_kw_type rt k /\
  k <> EKDefault /\
  lower_value compile_expr cenv (ext_call_kw_type rt k) e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) (ext_call_kw_type rt k)
    (gas_shadow_expr e) shadow_sa = (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx))
    (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      expr_post_mods H ctx func cenv cx e es sa sb s0 ee v op t /\
      expr_store_bound cx (post_value_type cenv e) v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      (?w. eval_operand op t = SOME w /\
        dest_NumV v = SOME (w2n w) /\ op_taint tn op = {}))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  strip_tac >>
  qhdtm_x_assum `expr_sim_full_mods`
    (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
  simp[Abbr `childQ`, Abbr `childR`] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  qexists_tac `v` >> simp[ptr_val_ok_def] >>
  `expr_type e = BaseT (UintT 256)` by
    (`k <> EKDefault ==> ext_call_kw_type rt k = BaseT (UintT 256)` by
       (Cases_on `k` >> simp[NoAsms, ext_call_kw_type_def]) >>
     fs[]) >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := xs) <=>
   expr_body_pre_mods mods cenv cx env e es` by
    simp[NoAsms, exprSimHypsDefsTheory.expr_body_pre_mods_def,
         exprSimHypsDefsTheory.expr_sim_inv_mods_def] >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := xs)` by simp[] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs) =
     (INL v,ee with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [listTheory.APPEND_NIL]))) >>
  drule_all_then strip_assume_tac expr_body_pre_mods_word_value >>
  `evaluate_type (get_tenv cx) (BaseT (UintT 256)) = SOME (BaseTV (UintT 256))` by
    EVAL_TAC >>
  `tyv = BaseTV (UintT 256)` by
    (qpat_assum `expr_type e = BaseT (UintT 256)` (fn ty =>
       qpat_assum `evaluate_type _ (expr_type e) = SOME tyv`
         (mp_tac o PURE_REWRITE_RULE [ty])) >>
     qpat_assum `evaluate_type _ (BaseT (UintT 256)) = _`
       (fn ev => simp[NoAsms, ev])) >>
  qpat_x_assum `tyv = BaseTV (UintT 256)` SUBST_ALL_TAC >>
  qhdtm_assum `expr_post_mods`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def, expr_post_def]) >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_word >> first_assum ACCEPT_TAC) >>
  qpat_assum `post_value_type cenv e = expr_type e` (fn ty =>
    qpat_x_assum `expr_val_rel _ _ _ _ _`
      (assume_tac o PURE_REWRITE_RULE [ty])) >>
  drule_all_then assume_tac expr_val_rel_typed >>
  qexists_tac `typed_val_to_w256 (BaseTV (UintT 256)) v` >>
  simp[uint256_typed_dest] >>
  qhdtm_assum `ptr_val_ok`
    (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [ptr_val_ok_def])
QED
