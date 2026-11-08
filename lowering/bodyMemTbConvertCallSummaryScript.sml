(* Conversion continuations for physical internal-call return buffers. *)
Theory bodyMemTbConvertCallSummary
Ancestors
  bodyMemTbConvertCallWindow bodyMemTbConvertCallSource
  bodyMemTbConvertDynamicScalar bodyMemTbConvertDestSummary
  exprSimConvertFromBytes exprSimConvertBytes exprSimConvert
  exprSimHyps exprSimHypsDefs exprSimDefs exprSimMemDefs
  exprLowering loweringPosts compileEnv valueCopyBytes context
  gasSummary gasSummaryCompose fragGasMode vyperState vyperInterpreter
  convertScalarTyping vyperEvalExprPreservesScopesDom exprSimSource exprLoweringProps

Theorem call_read_summary_bind[local]:
  gas_marked_exec T (ctx,func) source (ee,s) [] (INL v) ee (OK s) /\
  ee.gas_obs = [] /\
  gas_summary_at T (ctx,func) [] (next v) (ee,s) Q R ==>
  gas_summary_at T (ctx,func) [] (bind source next) (ee,s) Q R
Proof
  rewrite_tac[gas_summary_at_def] >> strip_tac >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
  irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
    |> REWRITE_RULE [listTheory.APPEND_NIL]) >>
  goal_assum (drule_at Any) >> gvs[]
QED

Theorem call_dynamic_vv_convert_summary:
  e = Call a (IntCall fid) args drv /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert ann [e]) es /\
  expr_body_pre cenv cx env e es /\
  is_bytestring_type (expr_type e) /\ ~is_bytestring_type ann /\
  valid_conversion (expr_type e) ann /\ well_formed_type env.type_defs ann /\
  is_word_type ann /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
  type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  unwrap_value cenv vv sm = (x,s1) /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv vv t /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv t /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\ ee.gas_obs = [] /\
  (if lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
      lowered_value_type cenv e = BaseT (StringT 0)
   then op = Lit 0w /\ sb = s1
   else compile_type_convert x (mk_convert_op (expr_type e) ann) s1 = (op,sb)) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ fn_has_code s1 sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv s1 /\
  sa.cs_next_var <= s1.cs_next_var ==>
  gas_summary_at T (ctx,func) []
    (bind (read_result cx tv) (\v ee. (convert_result cx (expr_type e) ann v,ee)))
    (ee,t)
    (\res fin ss. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert ann [e]) es sa sb s0
        fin v op ss /\ ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func ss /\ s0.vs_alloca_next <= ss.vs_alloca_next)
    (\res fin out. expr_exit res out)
Proof
  strip_tac >> gvs[vyperASTTheory.expr_type_def] >>
  drule_all convert_call_marked_read_window >> strip_tac >> gvs[] >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `read_result cx tv ee = (INL v,ee)` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> metis_tac[]) >>
  `bind (eval_expr cx (Call a (IntCall fid) args drv)) (read_result cx)
     (es with gas_obs := gs) = (INL v,ee)` by simp[bind_def] >>
  `expr_body_pre cenv cx env (TypeBuiltin ann Convert ann
     [Call a (IntCall fid) args drv]) (es with gas_obs := gs)` by
    metis_tac[expr_body_pre_gas_obs] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) dynamic_convert_operand_typed) >>
  strip_tac >>
  `alloca_inv t` by fs[expr_post_def, stmt_state_rel_def] >>
  `((lowered_value_type cenv (Call a (IntCall fid) args drv) =
       BaseT (BytesT (Dynamic 0)) \/
     lowered_value_type cenv (Call a (IntCall fid) args drv) = BaseT (StringT 0)) ==>
     v = BytesV [] \/ v = StringV "")` by
    metis_tac[convert_call_read_zero_empty, expr_body_pre_gas_obs] >>
  irule call_read_summary_bind >> simp[] >> qexists_tac `v` >> simp[] >>
  qpat_assum `ee with gas_obs := [] = ee` (fn th =>
    drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
      (Q.INST [`t` |-> `ann`, `ee` |-> `ee`] dynamic_continuation_summary_mem
       |> REWRITE_RULE [th])) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `well_formed_type _ _`)) >>
  disch_then (qspecl_then [`sb`, `op`] mp_tac) >>
  (impl_tac >- (simp[vyperASTTheory.expr_type_def] >> metis_tac[])) >>
  simp[vyperASTTheory.expr_type_def]
QED

Theorem call_bytestring_vv_convert_summary:
  e = Call a (IntCall fid) args drv /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert ann [e]) es /\
  expr_body_pre cenv cx env e es /\
  is_bytestring_type (expr_type e) /\ is_bytestring_type ann /\
  valid_conversion (expr_type e) ann /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
  type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  unwrap_value cenv vv sm = (x,s1) /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv vv t /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv t /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\ ee.gas_obs = [] /\
  (if type_memory_bytes cenv (lowered_value_type cenv e) < type_memory_bytes cenv ann
   then compile_bytestring_widen_copy (type_memory_bytes cenv ann) x
          (type_memory_bytes cenv (lowered_value_type cenv e)) s1
   else compile_type_convert x (mk_convert_op (expr_type e) ann) s1) = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ fn_has_code s1 sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv s1 /\ sa.cs_next_var <= s1.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ stmt_state_rel ctx func cenv cx es s0 /\
  type_memory_bytes cenv ann < dimword (:256) /\
  (!v. read_result cx tv ee = (INL v,ee) ==>
       expr_res_ok (convert_result cx (expr_type e) ann v)) ==>
  gas_summary_at T (ctx,func) []
    (bind (read_result cx tv) (\v ee. (convert_result cx (expr_type e) ann v,ee)))
    (ee,t)
    (\res fin ss. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert ann [e]) es sa sb s0
        fin v op ss /\ ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func ss /\ s0.vs_alloca_next <= ss.vs_alloca_next /\
      (?w. eval_operand op ss = SOME w /\
        w2n w + type_memory_bytes cenv ann <= ss.vs_alloca_next))
    (\res fin out. expr_exit res out)
Proof
  strip_tac >> gvs[vyperASTTheory.expr_type_def] >>
  drule_all convert_call_marked_read_window >> strip_tac >> gvs[] >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `read_result cx tv ee = (INL v,ee)` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> metis_tac[]) >>
  `bind (eval_expr cx (Call a (IntCall fid) args drv)) (read_result cx)
     (es with gas_obs := gs) = (INL v,ee)` by simp[bind_def] >>
  `expr_body_pre cenv cx env (TypeBuiltin ann Convert ann
     [Call a (IntCall fid) args drv]) (es with gas_obs := gs)` by
    metis_tac[expr_body_pre_gas_obs] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) dynamic_convert_operand_typed) >>
  disch_then (qx_choose_then `tv1` strip_assume_tac) >>
  `?tv2. evaluate_type (get_tenv cx) ann = SOME tv2` by
    (drule expr_body_pre_scalar_convert >> metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  `val_footprint tv1 v <= type_memory_bytes cenv
     (lowered_value_type cenv (Call a (IntCall fid) args drv))` by
    metis_tac[convert_call_read_footprint, expr_body_pre_gas_obs,
              vyperASTTheory.expr_type_def] >>
  `is_bytestring_type (lowered_value_type cenv (Call a (IntCall fid) args drv))` by
    metis_tac[convert_call_lowered_bytestring] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `alloca_inv t` by fs[expr_post_def, stmt_state_rel_def] >>
  irule call_read_summary_bind >> simp[] >> qexists_tac `v` >> simp[] >>
  qpat_assum `ee with gas_obs := [] = ee` (fn th =>
    drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
      (Q.INST [`e1` |-> `Call a (IntCall fid) args drv`,
               `e` |-> `TypeBuiltin ann Convert ann [Call a (IntCall fid) args drv]`,
               `ee` |-> `ee`] convert_bytestring_continuation_summary_mem
       |> REWRITE_RULE [th, vyperASTTheory.expr_type_def])) >>
  disch_then (drule_at (Pat `value_has_type _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ ann = SOME _`)) >>
  disch_then (qspecl_then [`sb`, `op`] mp_tac) >>
  (impl_tac >- (fs[vyperASTTheory.expr_type_def, arithmeticTheory.ADD_COMM] >>
               metis_tac[])) >>
  rewrite_tac[gas_summary_at_def] >> strip_tac >>
  qexistsl_tac [`res`, `es_end`, `r`] >> gvs[] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED
