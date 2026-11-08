(* Lowering layout and capacity-preserving bytestring destination lifting. *)
Theory bodyMemTbConvertDestLift
Ancestors
  bodyMemTbConvertDestSummary bodyMemTbConvertDynamicLift
  exprSimConvertBytes exprLoweringProps exprOperandVar compileEnv
  exprSimMemDefs exprSimHyps exprSimHypsDefs exprSimDefs exprLowering
  loweringSlice freshWrites fragExec rich_list valueCopyBytes context
  exprOpenTerminals exprOpenMain exprSimConvert exprSimSource exprSimUnwrap
  gasSummary gasSummaryCompose fragGasMode fragGasPath vyperState
  vyperInterpreter loweringPosts

Theorem bytestring_convert_mem_layout[local]:
  lower_value compile_expr cenv ty (TypeBuiltin ann Convert dst [e]) sa = (op,sb) /\
  valid_conversion (expr_type e) dst /\
  is_bytestring_type dst /\ is_bytestring_type (expr_type e) /\
  is_bytestring_type (lowered_value_type cenv e) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa ==>
  ?x s1.
    lower_value compile_expr cenv (expr_type e) e sa = (x,s1) /\
    (if type_memory_bytes cenv (lowered_value_type cenv e) < type_memory_bytes cenv dst
     then compile_bytestring_widen_copy (type_memory_bytes cenv dst) x
            (type_memory_bytes cenv (lowered_value_type cenv e)) s1
     else compile_type_convert x (mk_convert_op (expr_type e) dst) s1) = (op,sb) /\
    cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
    sa.cs_next_id <= s1.cs_next_id /\
    cs_extends s1 sb /\ s1.cs_next_var <= sb.cs_next_var /\
    fn_has_code sa s1 func /\ fn_has_code s1 sb func /\
    local_ptrs_reserved cenv s1 /\
    (!z. x = Var z ==> not_fresh_at s1 z) /\
    (!tops ctx cx env es tv ee.
      body_inv tops ctx cenv cx /\ supported_expr tops e /\
      expr_body_pre cenv cx env e es /\
      storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
      eval_expr cx e es = (INL tv,ee) /\ ~block_is_terminated sa ==>
      ~block_is_terminated s1)
Proof
  strip_tac >> drule_all lower_value_convert_bytestring >> strip_tac >> gvs[] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `cs_extends s1 sb /\ s1.cs_next_var <= sb.cs_next_var /\
   s1.cs_next_id <= sb.cs_next_id` by
    (Cases_on `type_memory_bytes cenv (lowered_value_type cenv e) < type_memory_bytes cenv dst`
     >- (gvs[] >>
         `0 < type_memory_bytes cenv (lowered_value_type cenv e)` by
           metis_tac[bytestring_memory_bytes_positive] >>
         drule_all convert_widen_copy_parts >> strip_tac >>
         `ci_mono s1 mid` by
           metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
         `ci_mono mid sb` by
           metis_tac[ci_mono_emit_void, pairTheory.SND] >>
         gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
     gvs[] >> metis_tac[convert_bytestring_suffix_grows]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!z. x = Var z ==> not_fresh_at s1 z` by
    metis_tac[compile_lower_value_var] >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `lower_value _ _ (expr_type e) e _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  `~block_is_terminated cs'` by
    (irule compile_expr_open_general >> goal_assum (drule_at Any) >>
     metis_tac[]) >>
  metis_tac[unwrap_value_open]
QED

Theorem bytestring_read_convert_summary[local]:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert ann [e]) es /\
  is_bytestring_type ann /\ is_bytestring_type (lowered_value_type cenv e) /\
  valid_conversion (expr_type e) ann /\
  (!a f args d. e = Call a (IntCall f) args d ==>
     lowered_value_type cenv e = expr_type e) /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\ ee.gas_obs = [] /\
  gas_marked_exec T (ctx,func) (read_result cx tv) (ee,t) [] (INL v) ee (OK u) /\
  expr_post ctx func cenv cx e es sa s1 s0 ee v x u /\
  alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  u.vs_current_bb = s1.cs_current_bb /\
  u.vs_inst_idx = LENGTH s1.cs_current_insts /\
  (!sw. eval_operand x u = SOME sw ==>
    w2n sw + type_memory_bytes cenv (lowered_value_type cenv e) <= u.vs_alloca_next) /\
  (if type_memory_bytes cenv (lowered_value_type cenv e) < type_memory_bytes cenv ann
   then compile_bytestring_widen_copy (type_memory_bytes cenv ann) x
          (type_memory_bytes cenv (lowered_value_type cenv e)) s1
   else compile_type_convert x (mk_convert_op (expr_type e) ann) s1) = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ fn_has_code s1 sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv s1 /\ sa.cs_next_var <= s1.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ stmt_state_rel ctx func cenv cx es s0 /\
  type_memory_bytes cenv ann < dimword (:256) /\
  expr_res_ok (convert_result cx (expr_type e) ann v) ==>
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
  strip_tac >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `read_result cx tv ee = (INL v,ee)` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> metis_tac[]) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by
    simp[bind_def] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) convert_bytestring_operand_facts) >>
  strip_tac >>
  `~u.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `alloca_inv u` by fs[expr_post_def, stmt_state_rel_def] >>
  qpat_assum `ee with gas_obs := [] = ee` (fn th =>
    drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
      (Q.INST [`e1` |-> `e`, `e` |-> `TypeBuiltin ann Convert ann [e]`, `ee` |-> `ee`]
        convert_bytestring_continuation_summary_mem
       |> REWRITE_RULE [th, vyperASTTheory.expr_type_def])) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `value_has_type _ _`)) >>
  disch_then (qspecl_then [`sb`, `op`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  rewrite_tac[gas_summary_at_def] >> strip_tac >>
  qexistsl_tac [`res`,`es_end`,`r`] >>
  (conj_tac >-
    (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
            |> REWRITE_RULE [APPEND_NIL]) >>
     goal_assum (drule_at Any) >>
     simp[evaluation_state_component_equality] >> gvs[]) >>
   gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS])
QED

Theorem bytestring_vv_convert_summary[local]:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert ann [e]) es /\
  expr_body_pre cenv cx env e es /\
  is_bytestring_type (expr_type e) /\ is_bytestring_type ann /\
  is_bytestring_type (lowered_value_type cenv e) /\
  valid_conversion (expr_type e) ann /\
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
  (if type_memory_bytes cenv (lowered_value_type cenv e) < type_memory_bytes cenv ann
   then compile_bytestring_widen_copy (type_memory_bytes cenv ann) x
          (type_memory_bytes cenv (lowered_value_type cenv e)) s1
   else compile_type_convert x (mk_convert_op (expr_type e) ann) s1) = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ fn_has_code s1 sb func /\
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
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `read_result cx tv ee = (INL v,ee)` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> metis_tac[]) >>
  drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`) bytestring_read_convert_summary >>
  disch_then (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _`)) >>
  disch_then (qspecl_then [`sb`, `op`, `gs`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED

Theorem bytestring_convert_capacity_outcome[local]:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert ann [e]) es /\
  is_bytestring_type ann /\
  (!a f args d. e = Call a (IntCall f) args d ==>
     lowered_value_type cenv e = expr_type e) /\
  expr_vv_sim_mem ctx func cenv cx (expr_type e) e es /\
  lower_value compile_expr cenv ty (TypeBuiltin ann Convert ann [e]) sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (bind (eval_expr cx (TypeBuiltin ann Convert ann [e])) (read_result cx))
    expr_res_ok es /\ stmt_state_rel ctx func cenv cx es s0 /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (eval_expr cx (TypeBuiltin ann Convert ann [e])) (read_result cx)) (es,s0)
    (\res fin ss. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert ann [e]) es sa sb s0
        fin v op ss /\ ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func ss /\ s0.vs_alloca_next <= ss.vs_alloca_next /\
      (?w. eval_operand op ss = SOME w /\
        w2n w + type_memory_bytes cenv ann <= ss.vs_alloca_next))
    (\res fin out. expr_exit res out)
Proof
  strip_tac >> drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  `is_bytestring_type (expr_type e)` by metis_tac[valid_conversion_to_bytestring] >>
  `is_bytestring_type (lowered_value_type cenv e)` by
    metis_tac[lowered_value_type_bytestring] >>
  drule_all bytestring_convert_mem_layout >> strip_tac >>
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
  irule stmtSimForcedTheory.forced_vv_then_outcome >>
  conj_tac >- (rpt strip_tac >> BETA_TAC >>
    metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  qexists_tac `\tv ee u.
    vv_post ctx func cenv cx e es sa sm s0 ee tv vv u /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv u /\
    u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next` >>
  reverse conj_tac >- simp[] >>
  rpt gen_tac >> BETA_TAC >> strip_tac >> suspend "continuation"
QED

Resume bytestring_convert_capacity_outcome[continuation]:
  `type_memory_bytes cenv ann < dimword (:256)` by
    (`~is_word_type ann` by gvs[bytestring_type_cases, is_word_type_def] >>
     `alloc_limits_expr cenv (TypeBuiltin ann Convert ann [e])` by
       gvs[expr_body_pre_def] >>
     gvs[allocLimitsTheory.alloc_limits_expr_def,
         allocLimitsTheory.type_alloc_ok_def, vyperASTTheory.expr_type_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `!v. read_result cx tv ee = (INL v,ee) ==>
       expr_res_ok (convert_result cx (expr_type e) ann v)` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `gas_admissible (bind (eval_expr cx (TypeBuiltin _ _ _ _)) _) _ es`
       (mp_tac o REWRITE_RULE [gasContextTheory.gas_admissible_def]) >>
     disch_then (qspec_then `gs` mp_tac) >>
     rewrite_tac[eval_expr_convert_action] >>
     simp[bind_def] >> disch_then irule >> simp[]) >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) bytestring_vv_convert_summary >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (qspecl_then [`sb`, `op`, `gs`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  simp[gas_summary_at_def, gas_marked_exec_def] >> metis_tac[]
QED

Finalise bytestring_convert_capacity_outcome

Theorem bytestring_convert_capacity_posts[local]:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert ann [e]) es /\
  expr_post ctx func cenv cx (TypeBuiltin ann Convert ann [e]) es sa sb s0
    fin v op ss /\
  (?w. eval_operand op ss = SOME w /\
       w2n w + type_memory_bytes cenv ann <= ss.vs_alloca_next) ==>
  expr_store_bound cx ann v op ss /\
  vv_post ctx func cenv cx (TypeBuiltin ann Convert ann [e]) es sa sb s0
    fin (Value v) (StackValue t op) ss /\
  vv_store_bound cx ann ann fin (Value v) (StackValue t op) ss
Proof
  strip_tac >>
  `!tvt. evaluate_type (get_tenv cx) ann = SOME tvt ==>
      type_memory_bytes cenv ann = type_memory_size tvt` by
    metis_tac[expr_sim_inv_memory_size, expr_body_pre_def] >>
  `expr_store_bound cx ann v op ss` by
    (irule (Q.INST [`e` |-> `TypeBuiltin ann Convert ann [e]`]
              expr_store_bound_capacity
            |> REWRITE_RULE [vyperASTTheory.expr_type_def, post_value_type_def]) >>
     metis_tac[]) >>
  simp[] >> conj_tac
  >- (gvs[expr_post_def, vv_post_def, vv_holds_def, vv_at_def,
          read_result_def, return_def] >> metis_tac[]) >>
  irule bodyMemTbConvertDestMemoryTheory.convert_vv_store_bound_stack_capacity >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem bytestring_convert_stack_outcome[local]:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert ann [e]) es /\
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (eval_expr cx (TypeBuiltin ann Convert ann [e])) (read_result cx)) (es,s0)
    (\res fin ss. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert ann [e]) es sa sb s0
        fin v op ss /\ ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func ss /\ s0.vs_alloca_next <= ss.vs_alloca_next /\
      (?w. eval_operand op ss = SOME w /\
        w2n w + type_memory_bytes cenv ann <= ss.vs_alloca_next))
    (\res fin out. expr_exit res out) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (eval_expr cx (TypeBuiltin ann Convert ann [e])) (es,s0)
    (\res fin ss. ?tv. res = INL tv /\
      vv_post ctx func cenv cx (TypeBuiltin ann Convert ann [e]) es sa sb s0
        fin tv (StackValue t op) ss /\
      vv_store_bound cx ann ann fin tv (StackValue t op) ss /\
      ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func ss /\ s0.vs_alloca_next <= ss.vs_alloca_next)
    (\res fin out. expr_exit res out)
Proof
  `!s tv s'. eval_expr cx (TypeBuiltin ann Convert ann [e]) s = (INL tv,s') ==>
       ?v. tv = Value v` by metis_tac[eval_expr_type_builtin_value] >>
  rw[gasOutcomeTheory.gas_outcome_def] >> qexists_tac `marks`
  >- (disj1_tac >> gvs[gas_summary_at_def, gas_marked_exec_def]
      >- (qexistsl_tac [`INL (Value v)`, `es_end`, `OK ss`] >>
          simp[] >> conj_tac
          >- (gen_tac >> drule exprSimStackTheory.eval_expr_force_value >>
              disch_then (qspec_then `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail` mp_tac) >>
              simp[] >> metis_tac[eval_expr_type_builtin_value]) >>
          metis_tac[bytestring_convert_capacity_posts]) >>
      qexistsl_tac [`case res of INL v => INL (Value v) | INR ex => INR ex`,
                   `es_end`, `out`] >>
      simp[expr_exit_success_map] >> gen_tac >>
      drule exprSimStackTheory.eval_expr_force_value >>
      disch_then (qspec_then `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail` mp_tac) >>
      simp[] >> metis_tac[eval_expr_type_builtin_value]) >>
  disj2_tac >> drule exprSimStackTheory.eval_expr_force_ignore >>
  disch_then (fn th => fs[th]) >> metis_tac[eval_expr_type_builtin_value]
QED

Theorem bytestring_convert_branch_sim_mem[local]:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  is_bytestring_type dst /\
  (!a f args d. e = Call a (IntCall f) args d ==>
     lowered_value_type cenv e = expr_type e) /\
  expr_vv_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_sim_mem ctx func cenv cx ty (TypeBuiltin ann Convert dst [e]) es
Proof
  strip_tac >> drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  rw[expr_sim_mem_def] >>
  drule_at (Pat `lower_value _ _ _ _ _ = _`) bytestring_convert_capacity_outcome >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  irule gas_outcome_post_mono >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >> simp[vyperASTTheory.expr_type_def] >>
  metis_tac[bytestring_convert_capacity_posts]
QED

Theorem bytestring_convert_branch_vv_sim_mem[local]:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  is_bytestring_type dst /\
  (!a f args d. e = Call a (IntCall f) args d ==>
     lowered_value_type cenv e = expr_type e) /\
  expr_vv_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_vv_sim_mem ctx func cenv cx ty (TypeBuiltin ann Convert dst [e]) es
Proof
  strip_tac >> drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  rw[expr_vv_sim_mem_def] >>
  `?t op. vv = StackValue t op` by metis_tac[compile_convert_stack, pairTheory.PAIR_EQ] >> gvs[] >>
  `lower_value compile_expr cenv ty (TypeBuiltin ann Convert ann [e]) sa = (op,sb)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  `gas_admissible (bind (eval_expr cx (TypeBuiltin ann Convert ann [e])) (read_result cx))
      expr_res_ok es` by
    (irule exprSimStackTheory.eval_expr_force_admissible >>
     simp[] >> metis_tac[eval_expr_type_builtin_value]) >>
  simp[vyperASTTheory.expr_type_def, lowered_value_type_def] >>
  irule bytestring_convert_stack_outcome >>
  conj_tac >- metis_tac[] >>
  irule bytestring_convert_capacity_outcome >> simp[] >> metis_tac[]
QED

Theorem bytestring_convert_branch_mem:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  is_bytestring_type dst /\
  (!a f args d. e = Call a (IntCall f) args d ==>
     lowered_value_type cenv e = expr_type e) /\
  expr_vv_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_sim_mem ctx func cenv cx ty (TypeBuiltin ann Convert dst [e]) es /\
  expr_vv_sim_mem ctx func cenv cx ty (TypeBuiltin ann Convert dst [e]) es
Proof
  metis_tac[bytestring_convert_branch_sim_mem, bytestring_convert_branch_vv_sim_mem]
QED
