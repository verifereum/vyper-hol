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
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sm s0 ee tv vv t) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
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
    (\res fin ss. !H. valid_horizon cx st0 H fin.storage_trace ==>
      ?v. res = INL v /\
      expr_post H ctx func cenv cx (TypeBuiltin ann Convert ann [e]) es sa sb s0
        fin v op ss /\ ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func ss /\ s0.vs_alloca_next <= ss.vs_alloca_next)
    (\res fin out. !H. valid_horizon cx st0 H fin.storage_trace ==>
      expr_exit res out)
Proof
  strip_tac >>
  qpat_x_assum `e = Call _ _ _ _` SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (REWRITE_RULE [vyperASTTheory.expr_type_def]) >>
  rewrite_tac[vyperASTTheory.expr_type_def] >>
  rename1 `valid_horizon cx st0 H0 ee.storage_trace` >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `!w. gas_marked_exec T (ctx,func) (read_result cx tv) (ee,t) [] (INL w) ee (OK t) ==>
       read_result cx tv ee = (INL w,ee)` by
    (gen_tac >> simp[gas_marked_exec_def] >> metis_tac[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H0` assume_tac) >>
  drule_all convert_call_marked_read_window >> strip_tac >>
  qpat_x_assum `s1 = sm` SUBST_ALL_TAC >>
  `read_result cx tv ee = (INL v,ee)` by metis_tac[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post H ctx func cenv cx (Call a (IntCall fid) args drv) es sa sm s0
         ee v x t` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (drule_then assume_tac) >>
     drule_all convert_call_marked_read_window >> strip_tac >>
     metis_tac[sumTheory.INL_11, pairTheory.PAIR_EQ]) >>
  `bind (eval_expr cx (Call a (IntCall fid) args drv)) (read_result cx)
     (es with gas_obs := gs) = (INL v,ee)` by simp[bind_def] >>
  `expr_body_pre cenv cx env (TypeBuiltin ann Convert ann
     [Call a (IntCall fid) args drv]) (es with gas_obs := gs)` by
    metis_tac[expr_body_pre_gas_obs] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) dynamic_convert_operand_typed) >>
  strip_tac >>
  `alloca_inv t` by
    (qpat_assum `expr_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def, stmt_state_rel_def]) >>
     first_assum ACCEPT_TAC) >>
  `((lowered_value_type cenv (Call a (IntCall fid) args drv) =
       BaseT (BytesT (Dynamic 0)) \/
     lowered_value_type cenv (Call a (IntCall fid) args drv) = BaseT (StringT 0)) ==>
     v = BytesV [] \/ v = StringV "")` by
    metis_tac[convert_call_read_zero_empty, expr_body_pre_gas_obs] >>
  irule (Q.INST [`v` |-> `v`, `u` |-> `t`] convert_read_summary_bind) >> simp[] >>
  mp_tac (Q.INST [`e1` |-> `Call a (IntCall fid) args drv`, `t` |-> `ann`,
                  `t0` |-> `t`, `v1` |-> `v`, `s1` |-> `sm`, `x` |-> `x`,
                  `sb` |-> `sb`, `op` |-> `op`, `ee` |-> `ee`,
                  `tenv` |-> `env.type_defs`] dynamic_continuation_summary_mem
          |> REWRITE_RULE [ASSUME ``(ee:evaluation_state) with gas_obs := [] = ee``]) >>
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
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sm s0 ee tv vv t) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
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
  sa.cs_next_id <= s1.cs_next_id /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0) /\
  type_memory_bytes cenv ann < dimword (:256) /\
  (!v. read_result cx tv ee = (INL v,ee) ==>
       expr_res_ok (convert_result cx (expr_type e) ann v)) ==>
  gas_summary_at T (ctx,func) []
    (bind (read_result cx tv) (\v ee. (convert_result cx (expr_type e) ann v,ee)))
    (ee,t)
    (\res fin ss. !H. valid_horizon cx st0 H fin.storage_trace ==>
      ?v. res = INL v /\
      expr_post H ctx func cenv cx (TypeBuiltin ann Convert ann [e]) es sa sb s0
        fin v op ss /\ ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func ss /\ s0.vs_alloca_next <= ss.vs_alloca_next /\
      (?w. eval_operand op ss = SOME w /\
        w2n w + type_memory_bytes cenv ann <= ss.vs_alloca_next))
    (\res fin out. !H. valid_horizon cx st0 H fin.storage_trace ==>
      expr_exit res out)
Proof
  strip_tac >>
  qpat_x_assum `e = Call _ _ _ _` SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (REWRITE_RULE [vyperASTTheory.expr_type_def]) >>
  rewrite_tac[vyperASTTheory.expr_type_def] >>
  rename1 `valid_horizon cx st0 H0 ee.storage_trace` >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `!w. gas_marked_exec T (ctx,func) (read_result cx tv) (ee,t) [] (INL w) ee (OK t) ==>
       read_result cx tv ee = (INL w,ee)` by
    (gen_tac >> simp[gas_marked_exec_def] >> metis_tac[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H0` assume_tac) >>
  drule_all convert_call_marked_read_window >> strip_tac >>
  qpat_x_assum `s1 = sm` SUBST_ALL_TAC >>
  `read_result cx tv ee = (INL v,ee)` by metis_tac[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post H ctx func cenv cx (Call a (IntCall fid) args drv) es sa sm s0
         ee v x t` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (drule_then assume_tac) >>
     drule_all convert_call_marked_read_window >> strip_tac >>
     metis_tac[sumTheory.INL_11, pairTheory.PAIR_EQ]) >>
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
  `alloca_inv t` by
    (qpat_assum `expr_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def, stmt_state_rel_def]) >>
     first_assum ACCEPT_TAC) >>
  irule (Q.INST [`v` |-> `v`, `u` |-> `t`] convert_read_summary_bind) >> simp[] >>
  irule (Q.INST [`Q` |-> `\res fin tt. !H. valid_horizon cx st0 H fin.storage_trace ==>
      ?v'. res = INL v' /\
      expr_post H ctx func cenv cx
        (TypeBuiltin ann Convert ann [Call a (IntCall fid) args drv]) es sa sb s0
        fin v' op tt /\
      tt.vs_current_bb = sb.cs_current_bb /\
      tt.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func tt /\ t.vs_alloca_next <= tt.vs_alloca_next /\
      (?w. eval_operand op tt = SOME w /\
        w2n w + type_memory_bytes cenv ann <= tt.vs_alloca_next)`,
    `R` |-> `\res fin r. !H. valid_horizon cx st0 H fin.storage_trace ==> expr_exit res r`]
    convert_summary_post_mono) >>
  rpt conj_tac >|
  [rpt gen_tac >> CONV_TAC (DEPTH_CONV BETA_CONV) >> rpt strip_tac >>
   qpat_x_assum `!H'. valid_horizon cx st0 H' fin.storage_trace ==> _`
     (drule_then strip_assume_tac) >>
   metis_tac[arithmeticTheory.LESS_EQ_TRANS],
   rpt gen_tac >> CONV_TAC (DEPTH_CONV BETA_CONV) >> simp[],
   ALL_TAC] >>
  mp_tac (Q.INST [`e1` |-> `Call a (IntCall fid) args drv`,
                  `e` |-> `TypeBuiltin ann Convert ann [Call a (IntCall fid) args drv]`,
                  `ee` |-> `ee`, `s` |-> `t`, `sb` |-> `sb`, `op` |-> `op`,
                  `v` |-> `v`, `x` |-> `x`, `sm` |-> `sm`]
            convert_bytestring_continuation_summary_mem
          |> REWRITE_RULE [ASSUME ``(ee:evaluation_state) with gas_obs := [] = ee``,
                           vyperASTTheory.expr_type_def,
                           loweringPostsTheory.expr_has_effect_thm,
                           listTheory.EXISTS_DEF]) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                TRY (simp[vyperASTTheory.expr_type_def] >> NO_TAC) >>
                metis_tac[arithmeticTheory.ADD_COMM])) >>
  simp[]
QED
