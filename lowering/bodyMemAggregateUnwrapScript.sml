(* Uniform full-type source capacity after nonword child unwrapping. *)
Theory bodyMemAggregateUnwrap
Ancestors
  bodyMemAggregateMaterialise exprSimMemUnwrap exprSimMemDefs exprSimUnwrap
  loweringPosts exprLowering compileEnv context fragGasPathMem exprSimUnwrapProps
  exprLoweringProps vyperInterpreter vyperState gasSummary gasOutcome
  fragGasMode exprSimMemorySource list

Theorem aggregate_unwrap_value_path_mem_capacity:
  !ctx func cenv cx e es sa sm sb s0 es' v vv op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv vv sm = (op, sb) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    ~is_word_type (expr_type e) /\
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
        (lowered_value_type cenv e = expr_type e ==>
         !sw tvt. eval_operand op u = SOME sw /\
                  evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
                  type_memory_size tvt = 0 \/
                  w2n sw + type_memory_size tvt <= u.vs_alloca_next) /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `vv`
  >- (gvs[unwrap_value_def, comp_return_def] >>
      qexists_tac `s` >> simp[cj 1 gas_path_mem_rules] >>
      conj_tac >- metis_tac[expr_post_of_vv_post_stack] >>
      qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
      simp[vv_store_bound_def, expr_store_bound_def, read_result_def, return_def] >>
      metis_tac[]) >>
  rename1 `LocatedValue t p` >>
  RULE_ASSUM_TAC (REWRITE_RULE [vv_operand_def]) >>
  Cases_on `p.ptr_location = LocCalldata`
  >- gvs[vv_post_calldata] >>
  Cases_on `p.ptr_location = LocMemory`
  >- (`~is_word_type t` by
        gvs[vv_post_def, vv_holds_def, valueCopyBytesTheory.is_bytestring_word_type] >>
      gvs[unwrap_value_def, comp_return_def] >>
      qexists_tac `s` >> simp[cj 1 gas_path_mem_rules] >>
      conj_tac >- metis_tac[expr_post_of_vv_post_memory] >>
      qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
      simp[vv_store_bound_def, expr_store_bound_def, read_result_def, return_def] >>
      metis_tac[]) >>
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
      conj_tac >- (rpt strip_tac >> gvs[arithmeticTheory.ADD_COMM]) >>
      metis_tac[]) >>
  rpt strip_tac >> gvs[arithmeticTheory.ADD_COMM]
QED

Theorem aggregate_unwrap_value_marked_read_mem_capacity:
  !ctx func cenv cx e es sa sm sb s0 ee tv vv op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv vv sm = (op, sb) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    ~is_word_type (expr_type e) /\
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
      (lowered_value_type cenv e = expr_type e ==>
       !sw tvt. eval_operand op u = SOME sw /\
                evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
                type_memory_size tvt = 0 \/
                w2n sw + type_memory_size tvt <= u.vs_alloca_next) /\
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
  drule_at (Pat `unwrap_value _ _ _ = _`) aggregate_unwrap_value_path_mem_capacity >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`v`, `u`] >> simp[] >>
  simp[gas_marked_exec_def, gas_marked_path_def] >>
  conj_tac >- metis_tac[read_result_gas_obs, APPEND] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED
