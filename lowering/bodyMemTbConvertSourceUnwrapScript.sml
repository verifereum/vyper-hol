(* Same-execution source window for plain bytestring conversion. *)
Theory bodyMemTbConvertSourceUnwrap
Ancestors
  bodyMemTbConvertSourceSizing bodyMemAggregateUnwrap bodyMemAggregateMaterialise
  exprSimSource exprSimHyps exprSimHypsDefs memoryLocalRhsProps
  exprSimMemDefs exprSimUnwrap exprSimUnwrapProps loweringPosts
  exprLowering context compileEnv fragGasPathMem gasSummary gasOutcome fragGasMode exprSimMemorySource
  bodyMemTbConvertLoweredSize bodyMemTbConvertSourceDispatch
  vyperTypeInvariants vyperTypeSystem vyperValue vyperInterpreter vyperState valueCopyBytes

Theorem convert_identity_source_window[local]:
  expr_body_pre ce cx env e es /\ is_bytestring_type (expr_type e) /\
  (!a f args d. e = Call a (IntCall f) args d ==>
     lowered_value_type ce e = expr_type e) /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
        type_memory_bytes ce (expr_type e) = type_memory_size tv /\
        type_memory_size tv < 2 ** 64) /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee (Value v) vv s /\
  ((?t. vv = StackValue t op) \/
   (?t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory /\
          p.ptr_operand = op)) ==>
  (!w. eval_operand op s = SOME w ==>
    w2n w + type_memory_bytes ce (lowered_value_type ce e) <= s.vs_alloca_next) /\
  (lowered_value_type ce e <> BaseT (BytesT (Dynamic 0)) /\
   lowered_value_type ce e <> BaseT (StringT 0) ==>
   !w. eval_operand op s = SOME w ==> w2n w + 64 <= s.vs_alloca_next)
Proof
  strip_tac >>
  drule expr_body_pre_var_types_well_formed >> strip_tac >>
  `well_typed_expr env e /\
   sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    gvs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
        env_context_consistent_def] >>
  `lowered_value_type ce e = expr_type e \/
   is_bytestring_type (expr_type e) /\
   is_bytestring_type (lowered_value_type ce e) /\
   arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    (irule convert_plain_lowered_type_compatible >> metis_tac[]) >>
  `type_memory_bytes ce (lowered_value_type ce e) <=
   type_memory_bytes ce (expr_type e)` by
    metis_tac[arg_type_fits_bytestring_memory_bytes, arithmeticTheory.LESS_EQ_REFL] >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv` by
    metis_tac[expr_body_pre_type_evaluates, optionTheory.IS_SOME_EXISTS] >>
  `type_memory_bytes ce (lowered_value_type ce e) < 2 ** 64` by metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS] >>
  `?ltv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv /\
         type_memory_bytes ce (lowered_value_type ce e) = type_memory_size ltv` by
    (irule memory_rhs_lowered_runtime_layout >> simp[] >> metis_tac[]) >>
  `~is_word_type (expr_type e)` by metis_tac[is_bytestring_word_type] >>
  `is_bytestring_type (lowered_value_type ce e)` by metis_tac[] >>
  `0 < type_memory_bytes ce (lowered_value_type ce e)` by
    gvs[exprSimConvertBytesTheory.bytestring_type_cases, type_memory_bytes_def] >>
  `!w. eval_operand op s = SOME w ==>
    w2n w + type_memory_bytes ce (lowered_value_type ce e) <= s.vs_alloca_next` by
    (gvs[vv_store_bound_def, read_result_def, return_def] >> metis_tac[]) >>
  simp[] >> strip_tac >>
  `64 <= type_memory_bytes ce (lowered_value_type ce e)` by
    (irule convert_nonzero_bytestring_memory_size >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> decide_tac
QED

Theorem convert_unwrap_value_path_mem_window:
  !ctx func cenv cx env e es sa sm sb s0 es' v vv op s.
    unwrap_value cenv vv sm = (op, sb) /\
    expr_body_pre cenv cx env e es /\ is_bytestring_type (expr_type e) /\
    (!a f args d. e = Call a (IntCall f) args d ==>
       lowered_value_type cenv e = expr_type e) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) es' (Value v) vv s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path_mem ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        expr_store_bound cx (expr_type e) v op u /\
        (!sw. eval_operand op u = SOME sw ==>
          w2n sw + type_memory_bytes cenv (lowered_value_type cenv e) <= u.vs_alloca_next) /\
        (lowered_value_type cenv e <> BaseT (BytesT (Dynamic 0)) /\
         lowered_value_type cenv e <> BaseT (StringT 0) ==>
         !sw. eval_operand op u = SOME sw ==> w2n sw + 64 <= u.vs_alloca_next) /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  `~is_word_type (expr_type e)` by metis_tac[is_bytestring_word_type] >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_bytestring >> first_assum ACCEPT_TAC) >>
  Cases_on `vv`
  >- suspend "stack" >>
  rename1 `LocatedValue t p` >>
  RULE_ASSUM_TAC (REWRITE_RULE [vv_operand_def]) >>
  Cases_on `p.ptr_location = LocCalldata`
  >- gvs[vv_post_calldata] >>
  Cases_on `p.ptr_location = LocMemory`
  >- suspend "memory" >>
  `t = expr_type e` by
    (Cases_on `p.ptr_location` >> gvs[vv_post_def, vv_holds_def]) >>
  `?u w tv. gas_path_mem ctx func s 0 (OK u) /\
      expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
      evaluate_type (get_tenv cx) t = SOME tv /\
      eval_operand op u = SOME w /\
      w2n w + type_memory_size tv <= u.vs_alloca_next /\
      alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (Cases_on `p.ptr_location = LocCode`
     >- (irule aggregate_code_materialise_post_capacity >> simp[] >> metis_tac[]) >>
     irule aggregate_storage_materialise_post_capacity >> simp[] >>
     qexistsl_tac [`p`, `sm`] >> simp[] >>
     Cases_on `p.ptr_location` >> gvs[]) >>
  qexists_tac `u` >> simp[] >>
  conj_tac
  >- (irule expr_store_bound_capacity >> simp[] >>
      conj_tac >- (rpt strip_tac >> gvs[arithmeticTheory.ADD_COMM]) >> metis_tac[]) >>
  `type_memory_bytes cenv (lowered_value_type cenv e) <=
   type_memory_bytes cenv (expr_type e)` by
    (drule expr_body_pre_var_types_well_formed >> strip_tac >>
     `well_typed_expr env e /\
      sfields_tenv_consistent cenv.ce_struct_fields env.type_defs` by
       gvs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
           env_context_consistent_def] >>
     drule_all convert_plain_lowered_type_compatible >> strip_tac >>
     metis_tac[arg_type_fits_bytestring_memory_bytes, arithmeticTheory.LESS_EQ_REFL]) >>
  conj_tac >- (rpt strip_tac >> gvs[] >> decide_tac) >>
  strip_tac >>
  `64 <= type_memory_bytes cenv (expr_type e)` by
    (irule convert_plain_nonzero_source_size >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Resume convert_unwrap_value_path_mem_window[stack]:
  gvs[unwrap_value_def, comp_return_def] >>
  qexists_tac `s` >> simp[cj 1 gas_path_mem_rules] >>
  conj_tac >- metis_tac[expr_post_of_vv_post_stack] >>
  conj_tac
  >- (qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
      simp[vv_store_bound_def, expr_store_bound_def, read_result_def, return_def]) >>
  drule_at (Pat `vv_store_bound _ _ _ _ _ _ _`) convert_identity_source_window >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  disch_then (qspec_then `o'` mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED

Resume convert_unwrap_value_path_mem_window[memory]:
  `~is_word_type t` by
    (strip_tac >>
     qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `post_value_type cenv e = _`
       (fn th => rewrite_tac[vv_post_def, vv_holds_def, th]) >>
     strip_tac >> gvs[is_bytestring_word_type]) >>
  gvs[unwrap_value_def, comp_return_def] >>
  qexists_tac `s` >> simp[cj 1 gas_path_mem_rules] >>
  conj_tac >- metis_tac[expr_post_of_vv_post_memory] >>
  conj_tac
  >- (qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
      simp[vv_store_bound_def, expr_store_bound_def, read_result_def, return_def]) >>
  drule_at (Pat `vv_store_bound _ _ _ _ _ _ _`) convert_identity_source_window >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  disch_then (qspec_then `p.ptr_operand` mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED

Finalise convert_unwrap_value_path_mem_window

Theorem convert_unwrap_value_marked_read_mem_window:
  !ctx func cenv cx env e es sa sm sb s0 ee tv vv op s.
    unwrap_value cenv vv sm = (op, sb) /\
    expr_body_pre cenv cx env e es /\ is_bytestring_type (expr_type e) /\
    (!a f args d. e = Call a (IntCall f) args d ==>
       lowered_value_type cenv e = expr_type e) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) /\
    vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?v u. gas_marked_exec T (ctx,func) (read_result cx tv) (ee,s)
            [] (INL v) ee (OK u) /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
      expr_store_bound cx (expr_type e) v op u /\
      (!sw. eval_operand op u = SOME sw ==>
        w2n sw + type_memory_bytes cenv (lowered_value_type cenv e) <= u.vs_alloca_next) /\
      (lowered_value_type cenv e <> BaseT (BytesT (Dynamic 0)) /\
       lowered_value_type cenv e <> BaseT (StringT 0) ==>
       !sw. eval_operand op u = SOME sw ==> w2n sw + 64 <= u.vs_alloca_next) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `read_result cx tv ee` >> rename1 `_ = (res, ee')` >>
  `ee' = ee` by metis_tac[read_result_state] >> gvs[] >>
  reverse (Cases_on `res`)
  >- metis_tac[vv_post_failed_read] >>
  rename1 `read_result cx tv ee = (INL v, ee)` >>
  `vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee (Value v) vv s` by
    (qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
     simp[vv_store_bound_def, read_result_def, return_def] >>
     rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  drule vv_post_read_result >> strip_tac >> gvs[] >> pop_assum kall_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`) convert_unwrap_value_path_mem_window >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  qexistsl_tac [`v`, `u`] >> simp[] >>
  simp[gas_marked_exec_def, gas_marked_path_def] >>
  metis_tac[read_result_gas_obs, listTheory.APPEND]
QED
