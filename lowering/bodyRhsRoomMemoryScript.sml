(* The forced memory judgment of a non-word expression, with the room its
   value view's type takes when the value is left in memory: what a staging
   copy at that type reads.  exprSimMemUnwrap's expr_sim_mem_of_vv_sim_mem,
   carrying vv_store_bound's type-size bound through unwrap_value. *)
Theory bodyRhsRoomMemory
Ancestors
  exprSimMemUnwrap
  exprSimMemDefs exprSimUnwrap exprSimDefs loweringPosts gasOutcome
  exprLowering compileEnv vyperInterpreter vyperState
  exprSimUnwrapProps exprSimProps exprSimMemorySource bodyFieldMemoryProps
  gasSummary gasSummaryCompose gasExemptCert fragGasMode fragGasPath
  fragGasPathMem fragGasSeqMem fragExecMem instMemFrontier allocaHistoryFragment
  emitHelperProps emitHelper exprLoweringProps loweringSlice context
  bodyImmutableUnwrapMemory memSafeRun exprSimAccounts
  fragExec exprOperandVar vyperEvalExprPreservesScopesDom
  exprSimAlloc exprSimStorageCopy exprSimCopy storageCopyGasPath
  immutableCopyExecution bodyImmutableCopyMemory bodyStorageCopyMemory
  bodyAllocMemory bodyDeclMemoryCounted valueEncodingProps abiBuiltinAllocation
  freshWrites allocaHistory immutableMemoryFrame venomMemDefs
  venomExecSemantics venomInst venomState list rich_list finite_map

(* unwrap_value_path_mem for a non-word expression, plus the room of a
   value left in memory. *)
Theorem unwrap_value_path_mem_room[local]:
  !ctx func cenv cx e es sa sm sb s0 es' v vv op s.
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
        (vv_location vv = SOME LocMemory ==>
         !sw tvt. eval_operand op u = SOME sw /\
                  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tvt ==>
                  type_memory_size tvt = 0 \/
                  w2n sw + type_memory_size tvt <= u.vs_alloca_next) /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `vv`
  >- (gvs[unwrap_value_def, comp_return_def, vv_location_def] >>
      qexists_tac `s` >> simp[cj 1 gas_path_mem_rules] >>
      conj_tac >- metis_tac[expr_post_of_vv_post_stack] >>
      qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
      simp[vv_store_bound_def, expr_store_bound_def, read_result_def,
           return_def] >>
      metis_tac[]) >>
  rename1 `LocatedValue t p` >>
  `t = expr_type e` by gvs[vv_post_def, vv_holds_def] >>
  reverse (Cases_on `p.ptr_location = LocMemory`)
  >- (drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_path_mem >>
      disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      simp[vv_location_def] >> strip_tac >> qexists_tac `u` >> simp[]) >>
  gvs[unwrap_value_def, comp_return_def, vv_location_def] >>
  qexists_tac `s` >> simp[cj 1 gas_path_mem_rules] >>
  conj_tac >- metis_tac[expr_post_of_vv_post_memory] >>
  qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
  simp[vv_store_bound_def, expr_store_bound_def, read_result_def,
       return_def] >>
  metis_tac[]
QED

(* The counted read suffix, memory-checked, with the room. *)
Theorem unwrap_value_marked_read_mem_room[local]:
  !ctx func cenv cx e es sa sm sb s0 ee tv vv op s.
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
      (vv_location vv = SOME LocMemory ==>
       !sw tvt. eval_operand op u = SOME sw /\
                evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tvt ==>
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
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_path_mem_room >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`v`, `u`] >> simp[] >>
  simp[gas_marked_exec_def, gas_marked_path_def] >>
  conj_tac >- metis_tac[read_result_gas_obs, APPEND] >>
  rpt strip_tac >>
  qpat_x_assum `vv_location _ = _ ==> _` drule >>
  disch_then (qspecl_then [`sw`, `tvt`] mp_tac) >> simp[]
QED

(* The memory judgment of a non-word expression from its value one, with the
   room of a value left in memory, for the expression's own compile and
   unwrap. *)
Theorem expr_sim_mem_room:
  !ctx func cenv cx ty e es.
    expr_vv_sim_mem ctx func cenv cx ty e es /\
    ~is_word_type (expr_type e) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
    !sa sm sb vv op s0.
      compile_expr cenv ty e sa = (vv, sm) /\
      unwrap_value cenv vv sm = (op, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
      stmt_state_rel ctx func cenv cx es s0 /\
      alloca_history func s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome T (cx_tops cx) (ctx, func)
        (bind (eval_expr cx e) (read_result cx)) (es, s0)
        (\res ee t. ?v. res = INL v /\
          expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
          expr_store_bound cx (expr_type e) v op t /\
          (vv_location vv = SOME LocMemory ==>
           !sw tvt. eval_operand op t = SOME sw /\
                    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tvt ==>
                    type_memory_size tvt = 0 \/
                    w2n sw + type_memory_size tvt <= t.vs_alloca_next) /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
        (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (drule (cj 1 exprOperandVarTheory.compiler_compile_var) >> simp[]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_mem_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `s0`] mp_tac) >>
  simp[] >>
  rewrite_tac[gas_outcome_def] >> strip_tac >>
  qexists_tac `marks`
  >- (disj1_tac >> gvs[gas_summary_at_def]
      >- (rename1 `vv_post _ _ _ _ _ _ _ _ _ _ tv vv u` >>
          `~u.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          `MAP FDOM es.scopes = MAP FDOM (es_end with gas_obs := []).scopes` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
               (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
             strip_tac >> first_x_assum (qspec_then `[]` assume_tac) >>
             drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >>
             simp[]) >>
          drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_marked_read_mem_room >>
          disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
          impl_tac >- simp[] >> strip_tac >>
          rename1 `gas_marked_exec T _ (read_result _ _) _ [] _ _ (OK u2)` >>
          qexistsl_tac [`INL v`, `es_end with gas_obs := []`, `OK u2`] >>
          simp[] >>
          reverse conj_tac
          >- (rpt strip_tac >>
              qpat_x_assum `vv_location _ = _ ==> _` drule >>
              disch_then (qspecl_then [`sw`, `tvt`] mp_tac) >> simp[]) >>
          `marks = marks ++ []` by simp[] >>
          pop_assum SUBST1_TAC >> irule gas_marked_exec_bind_normal >>
          goal_assum drule >> simp[]) >>
      Cases_on `res`
      >- (Cases_on `r` >> gvs[expr_exit_def]) >>
      rename1 `expr_exit (INR exc) r` >>
      `expr_res_ok (INR exc : value + exception)` by
        (Cases_on `exc` >> Cases_on `r` >>
         gvs[expr_exit_def, expr_res_ok_def, AllCaseEqs()] >>
         Cases_on `e'` >> gvs[expr_exit_def, expr_res_ok_def]) >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >>
      simp[GSYM expr_exit_exception_transport] >>
      irule gas_marked_exec_bind_exception >> goal_assum drule) >>
  disj2_tac >> metis_tac[force_exempt_cert]
QED
