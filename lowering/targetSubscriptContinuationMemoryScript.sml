(* Counted dispatch for successful subscript bases. *)
Theory targetSubscriptContinuationMemory
Ancestors
  targetSubscriptLocalMemory targetStorageContinuationMemory
  targetSubscriptMemoryResiduals targetSubscriptSplit exprSimPopNested
  stmtSimAugAssignPlace exprSimPopNestedBase bodyAttributeMemory
  exprSimMemDefs targetPlaceSimDefs targetPlaceSim exprSimHypsDefs
  vyperInterpreter vyperState allocaHistory vyperTypeCallGraph

Theorem target_subscript_base_continuation_mem:
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  (nocalls ==> int_calls_target (SubscriptTarget bt e) = []) /\
  ((?s p s1. eval_base_place cx bt s = (INL p,s1)) ==>
    (!env ty es. expr_body_pre cenv cx env e es /\
      (nocalls ==> int_calls_expr e = []) ==>
      expr_sim_mem ctx func cenv cx ty e es) /\
    (!env ty es. expr_body_pre cenv cx env e es /\
      (nocalls ==> int_calls_expr e = []) ==>
      expr_vv_sim_mem ctx func cenv cx ty e es)) /\
  (!nsid. target_root bt = TopLevelNameTarget nsid ==>
    EVERY pure_expr (target_indices (SubscriptTarget bt e))) /\
  body_inv tops ctx cenv cx /\ supported_expr tops e /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  type_place_target env bt = SOME bvt /\
  subscript_vtype bvt (expr_type e) = SOME vt /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb /\
  fn_has_code sm sn func /\ fn_has_code sn sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~block_is_terminated sa /\ ~block_is_terminated sm /\
  gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  alloca_history func s0 /\ alloca_history func t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  gas_marked_exec T (ctx,func) (eval_base_place cx bt)
    (es,s0) left (INL pv) mid (OK t) /\
  target_post ctx func cenv cx es sa sm s0 (mid with gas_obs := []) pv bvt rb t /\
  (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
    slots_in_range (get_storage cx (mid with gas_obs := []) tr) (w2n slot) tv /\
    storage_read_live cx tr (get_storage cx (mid with gas_obs := []) tr) slot tv) /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx))
      (\key. extend_place cx pv (ValueSubscript key)))
    (mid with gas_obs := [],t)
    (\res ee u. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es sa sb s0 ee pv' vt op u /\
      (!tr slot tv. pv' = PlaceR (StoragePlace tr slot tv) ==>
        slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
        storage_read_live cx tr (get_storage cx ee tr) slot tv) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `!gs. eval_base_place cx bt
    (es with gas_obs := gas_explicit left s0.vs_gas_readings ++ gs) =
    (INL pv,mid with gas_obs := gs)` by
    metis_tac[target_subscript_marked_base_source] >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  `expr_sim_mem ctx func cenv cx (expr_type e) e (mid with gas_obs := [])` by
    (drule_all target_subscript_marked_base_inv >> strip_tac >>
     `expr_body_pre cenv cx env e (mid with gas_obs := [])` by
       fs[target_pre_def, target_indices_pre_def] >>
     `nocalls ==> int_calls_expr e = []` by fs[int_calls_expr_def] >>
     metis_tac[exprSimSourceTheory.expr_body_pre_gas_obs]) >>
  mp_tac (Q.SPEC `bt` target_root_cases) >> strip_tac
  >- suspend "local" >>
  suspend "storage"
QED

Resume target_subscript_base_continuation_mem[local]:
  Cases_on `!gs key ee.
    bind (eval_expr cx e) (read_result cx) (mid with gas_obs := gs) =
      (INL key,ee) ==>
    ?path entry v. pv = PlaceR (MemoryPlace id path) /\
      lookup_scopes id ee.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v`
  >- suspend "live" >>
  pop_assum (strip_assume_tac o SIMP_RULE pure_ss [NOT_FORALL_THM, NOT_IMP]) >>
  drule_all target_subscript_local_popped_case_mem >> simp[]
QED

Resume target_subscript_base_continuation_mem[storage]:
  qpat_assum `!gs. eval_base_place _ _ _ = _` (qspec_then `[]` assume_tac) >>
  `EVERY pure_expr (target_indices (SubscriptTarget bt e))` by metis_tac[] >>
  `?rvt. type_place_target env (TopLevelNameTarget (src,id)) = SOME rvt` by
    (Cases_on `type_place_target env (TopLevelNameTarget (src,id))` >>
     simp[] >> metis_tac[target_root_untyped, optionTheory.NOT_NONE_SOME]) >>
  `env_consistent env cx es` by fs[target_pre_def, expr_sim_inv_def] >>
  `!ts. get_module_code cx src = SOME ts ==>
    find_var_decl_by_name id ts <> NONE` by
    fs[target_pre_def, immutable_root_def] >>
  drule_all toplevel_target_decl >> strip_tac >>
  `(?tr slot tv. pv = PlaceR (StoragePlace tr slot tv)) \/
   (?tr slot kt tv. pv = HashMapRef tr slot kt tv)` by
    (irule nested_pop_eval_base_storage_class >>
     goal_assum (drule_at (Pat `target_root _ = _`)) >>
     goal_assum (drule_at (Pat `eval_base_place _ _ _ = _`)) >>
     metis_tac[]) >>
  irule target_subscript_storage_continuation_mem >> simp[] >> metis_tac[]
QED

Resume target_subscript_base_continuation_mem[live]:
  `?path. pv = PlaceR (MemoryPlace id path)` by
    metis_tac[aug_place_name_root_base] >> gvs[] >>
  drule_all target_subscript_local_live_continuation_mem >> strip_tac >>
  drule gas_outcome_link >> strip_tac >>
  irule exprSimMemDefsTheory.gas_outcome_post_mono >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >>
  rpt gen_tac >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `bind _ _ _ = (INL pv',ee)` mp_tac >>
  simp[Once bind_def, AllCaseEqs()] >> strip_tac >>
  drule aug_place_extend_name_memory >> simp[]
QED

Finalise target_subscript_base_continuation_mem
