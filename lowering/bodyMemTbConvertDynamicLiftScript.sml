(* Lowering layout for the bytestring-to-scalar memory branch. *)
Theory bodyMemTbConvertDynamicLift
Ancestors
  bodyMemTbConvertMarkedCompose bodyMemTbConvertCompose
  exprSimConvertFromBytes exprSimConvert exprLoweringProps exprOperandVar
  loweringSlice freshWrites compileEnv rich_list fragExec
  exprSimMemDefs exprSimHyps exprSimHypsDefs exprSimSource vyperAST
  stmtSimForced gasSummary gasOutcome vyperState exprLowering exprSimUnwrap
  valueCopyBytes fragGasMode fragGasPath gasSummaryCompose vyperInterpreter
  exprSimDefs loweringPosts bodyMemTbConvertDynamicScalar

Theorem dynamic_convert_mem_layout:
  lower_value compile_expr cenv ty (TypeBuiltin ann Convert dst [e]) sa = (op,sb) /\
  is_bytestring_type (expr_type e) /\ is_word_type dst /\
  valid_conversion (expr_type e) dst /\
  (!n. dst <> FlagT n) /\ fn_has_code sa sb func /\
  local_ptrs_reserved cenv sa ==>
  ?x s1.
    lower_value compile_expr cenv (expr_type e) e sa = (x,s1) /\
    (if lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
        lowered_value_type cenv e = BaseT (StringT 0)
     then op = Lit 0w /\ sb = s1
     else compile_type_convert x (mk_convert_op (expr_type e) dst) s1 = (op,sb)) /\
    cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
    sa.cs_next_id <= s1.cs_next_id /\
    cs_extends s1 sb /\ s1.cs_next_var <= sb.cs_next_var /\
    fn_has_code sa s1 func /\ fn_has_code s1 sb func /\
    local_ptrs_reserved cenv s1 /\
    (!z. x = Var z ==> not_fresh_at s1 z)
Proof
  strip_tac >> drule_all lower_value_dynamic_convert >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `!z. x = Var z ==> not_fresh_at s1 z` by
    metis_tac[compile_lower_value_var] >>
  `dynamic_straight_fresh (compile_type_convert x (mk_convert_op (expr_type e) dst))` by
    (irule dynamic_scalar_straight_read_fresh >>
     simp[] >> metis_tac[is_word_type_not_bytestring]) >>
  `cs_extends s1 sb /\ s1.cs_next_var <= sb.cs_next_var` by
    (Cases_on `lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
               lowered_value_type cenv e = BaseT (StringT 0)`
     >- gvs[cs_extends_def] >>
     fs[dynamic_straight_fresh_def, dynamic_writes_fresh_def] >>
     first_x_assum drule >> strip_tac >>
     simp[cs_extends_def, IS_PREFIX_APPEND3]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> asm_rewrite_tac[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  qexistsl_tac [`x`, `s1`] >> simp[]
QED

Theorem dynamic_read_convert_summary[local]:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert ann [e]) es /\
  expr_body_pre cenv cx env e es /\
  is_bytestring_type (expr_type e) /\ ~is_bytestring_type ann /\
  valid_conversion (expr_type e) ann /\ well_formed_type env.type_defs ann /\
  is_word_type ann /\
  (!a f args d. e = Call a (IntCall f) args d ==>
     lowered_value_type cenv e = expr_type e) /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\ ee.gas_obs = [] /\
  gas_marked_exec T (ctx,func) (read_result cx tv) (ee,t) [] (INL v) ee (OK u) /\
  expr_post ctx func cenv cx e es sa s1 s0 ee v x u /\
  alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  u.vs_current_bb = s1.cs_current_bb /\
  u.vs_inst_idx = LENGTH s1.cs_current_insts /\
  (lowered_value_type cenv e <> BaseT (BytesT (Dynamic 0)) /\
   lowered_value_type cenv e <> BaseT (StringT 0) ==>
   !sw. eval_operand x u = SOME sw ==> w2n sw + 64 <= u.vs_alloca_next) /\
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
  strip_tac >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `read_result cx tv ee = (INL v,ee)` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> metis_tac[]) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by
    simp[bind_def] >>
  `expr_body_pre cenv cx env (TypeBuiltin ann Convert ann [e])
     (es with gas_obs := gs)` by metis_tac[expr_body_pre_gas_obs] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) dynamic_convert_operand_typed) >>
  strip_tac >>
  `((lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
     lowered_value_type cenv e = BaseT (StringT 0)) ==> v = BytesV [] \/ v = StringV "")` by
    (strip_tac >>
     metis_tac[CONV_RULE (DEPTH_CONV ETA_CONV) lowered_zero_bytestring_read_empty,
               expr_body_pre_gas_obs]) >>
  `~u.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `alloca_inv u` by fs[expr_post_def, stmt_state_rel_def] >>
  qpat_assum `ee with gas_obs := [] = ee` (fn th =>
    drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
      (Q.INST [`t` |-> `ann`, `ee` |-> `ee`] dynamic_continuation_summary_mem
       |> REWRITE_RULE [th])) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `well_formed_type _ _`)) >>
  disch_then (qspecl_then [`sb`, `op`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  rewrite_tac[gas_summary_at_def] >> strip_tac >>
  qexistsl_tac [`res`,`es_end`,`r`] >>
  (conj_tac >-
    (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
            |> REWRITE_RULE [APPEND_NIL]) >>
     goal_assum (drule_at Any) >>
     simp[evaluation_state_component_equality] >> gvs[]) >> gvs[])
QED

Theorem dynamic_vv_convert_summary[local]:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert ann [e]) es /\
  expr_body_pre cenv cx env e es /\
  is_bytestring_type (expr_type e) /\ ~is_bytestring_type ann /\
  valid_conversion (expr_type e) ann /\ well_formed_type env.type_defs ann /\
  is_word_type ann /\
  (!a f args d. e = Call a (IntCall f) args d ==>
     lowered_value_type cenv e = expr_type e) /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  unwrap_value cenv vv sm = (x,s1) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm s1 func /\ fn_inst_ids_distinct func /\
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
  local_ptrs_reserved cenv s1 /\ sa.cs_next_var <= s1.cs_next_var ==>
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
  strip_tac >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_bytestring >> first_assum ACCEPT_TAC) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >>
     simp[]) >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sm z` by
    (drule_at (Pat `compile_expr _ _ _ _ = _`)
       (cj 1 exprOperandVarTheory.compiler_compile_var) >> simp[]) >>
  `!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
     type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
     type_memory_size tvt < 2 ** 64` by
    (gen_tac >> strip_tac >>
     drule_at (Pat `evaluate_type _ _ = SOME _`) expr_body_pre_copy_ok >>
     simp[] >> disch_then irule >> metis_tac[is_bytestring_word_type]) >>
  drule_at (Pat `unwrap_value _ _ _ = _`)
    bodyMemTbConvertSourceUnwrapTheory.convert_unwrap_value_marked_read_mem_window >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`) dynamic_read_convert_summary >>
  disch_then (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `well_formed_type _ _`)) >>
  disch_then (qspecl_then [`sb`, `op`, `gs`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED

Theorem dynamic_convert_branch_sim_mem:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  is_bytestring_type (expr_type e) /\ ~is_bytestring_type dst /\
  (!a f args d. e = Call a (IntCall f) args d ==>
     lowered_value_type cenv e = expr_type e) /\
  expr_vv_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_sim_mem ctx func cenv cx ty (TypeBuiltin ann Convert dst [e]) es
Proof
  strip_tac >> drule dynamic_convert_typing_boundary >> strip_tac >>
  drule_all dynamic_scalar_type >> strip_tac >>
  drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_all dynamic_convert_mem_layout >> strip_tac >>
  irule expr_sim_mem_word_outcome >>
  conj_tac >- simp[vyperASTTheory.expr_type_def] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr cenv (expr_type e) e sa = (vv,sm)` >>
  `unwrap_value cenv vv sm = (x,s1)` by
    (qpat_x_assum `lower_value _ _ (expr_type e) e _ = _` mp_tac >>
     simp[lower_value_def, comp_bind_def]) >>

  drule (cj 1 compile_expr_grows) >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm s1 func` by
    (irule fn_has_code_split >> simp[]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_mem_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rewrite_tac[eval_expr_convert_action, bind_assoc] >>
  irule forced_vv_then_outcome >>
  conj_tac >- (rpt strip_tac >> BETA_TAC >>
    metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  qexists_tac `\tv ee u.
    vv_post ctx func cenv cx e es sa sm s0 ee tv vv u /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv u /\
    u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next` >>
  reverse conj_tac >- simp[] >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>

  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) dynamic_vv_convert_summary >>
  disch_then (drule_at (Pat `well_formed_type _ _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (qspecl_then [`sb`, `op`, `gs`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  simp[gas_summary_at_def, gas_marked_exec_def] >> metis_tac[]
QED

