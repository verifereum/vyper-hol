(* The two authorized residual branches of counted target simulation.
   Contracts are expanded to avoid a dependency on targetPlaceSimMem. *)
Theory targetSubscriptMemoryResiduals
Ancestors
  targetSubscriptSplit exprSimMemDefs allocaHistory targetPlaceSimDefs
  gasOutcome gasContext gasSummary loweringPosts exprLowering compileEnv
  vyperInterpreter vyperState venomState

(* Counted twin of targetSubscriptSplit.target_subscript_local_popped_case:
   the index pops the local place containing the target itself. *)
Theorem target_subscript_local_popped_case_mem:
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  (nocalls ==> int_calls_target (SubscriptTarget bt e) = []) /\
  ((?s p s1. eval_base_place cx bt s = (INL p,s1)) ==>
    (!env ty es. expr_body_pre cenv cx env e es /\
      (nocalls ==> int_calls_expr e = []) ==>
      expr_sim_mem ctx func cenv cx ty e es) /\
    (!env ty es. expr_body_pre cenv cx env e es /\
      (nocalls ==> int_calls_expr e = []) ==>
      expr_vv_sim_mem ctx func cenv cx ty e es)) /\
  target_root bt = NameTarget id /\
  type_place_target env bt = SOME bvt /\
  subscript_vtype bvt (expr_type e) = SOME vt /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb /\
  fn_has_code sm sn func /\ fn_has_code sn sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~block_is_terminated sa /\
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
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  bind (eval_expr cx e) (read_result cx) (mid with gas_obs := gs) =
    (INL key0,fin) /\
  ~(?path entry v. pv = PlaceR (MemoryPlace id path) /\
      lookup_scopes id fin.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v) ==>
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
  cheat
QED

(* Counted twin of targetSubscriptSplit.target_subscript_storage_effectful_case:
   a storage-root index is not pure, so it may invalidate a live header. *)
Theorem target_subscript_storage_effectful_case_mem:
  !nocalls ctx func cenv cx bt e nsid.
    (!env es.
      target_pre cenv cx env bt es /\
      (nocalls ==> int_calls_target bt = []) ==>
      !vt sa sb op s0.
        type_place_target env bt = SOME vt /\
        compile_get_target_ptr compile_expr cenv bt sa = (op,sb) /\
        fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
        local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
        gas_admissible (eval_base_place cx bt) target_res_ok es /\
        stmt_state_rel ctx func cenv cx es s0 /\
        alloca_history func s0 /\ ~s0.vs_halted /\
        s0.vs_current_bb = sa.cs_current_bb /\
        s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
        gas_outcome T (cx_tops cx) (ctx,func) (eval_base_place cx bt) (es,s0)
          (\res ee t. ?pv. res = INL pv /\
            target_post ctx func cenv cx es sa sb s0 ee pv vt op t /\
            (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
              slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
              storage_read_live cx tr (get_storage cx ee tr) slot tv) /\
            t.vs_current_bb = sb.cs_current_bb /\
            t.vs_inst_idx = LENGTH sb.cs_current_insts /\
            alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
          (\res ee r. expr_exit res r)) /\
    ((?s pv s1. eval_base_place cx bt s = (INL pv,s1)) ==>
      (!env ty es. expr_body_pre cenv cx env e es /\
        (nocalls ==> int_calls_expr e = []) ==>
        expr_sim_mem ctx func cenv cx ty e es) /\
      (!env ty es. expr_body_pre cenv cx env e es /\
        (nocalls ==> int_calls_expr e = []) ==>
        expr_vv_sim_mem ctx func cenv cx ty e es)) /\
    target_root bt = TopLevelNameTarget nsid /\
    ~EVERY pure_expr (target_indices (SubscriptTarget bt e)) ==>
    !env es.
      target_pre cenv cx env (SubscriptTarget bt e) es /\
      (nocalls ==> int_calls_target (SubscriptTarget bt e) = []) ==>
      !vt sa sb op s0.
        type_place_target env (SubscriptTarget bt e) = SOME vt /\
        compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa = (op,sb) /\
        fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
        local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
        gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
        stmt_state_rel ctx func cenv cx es s0 /\
        alloca_history func s0 /\ ~s0.vs_halted /\
        s0.vs_current_bb = sa.cs_current_bb /\
        s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
        gas_outcome T (cx_tops cx) (ctx,func)
          (eval_base_place cx (SubscriptTarget bt e)) (es,s0)
          (\res ee t. ?pv. res = INL pv /\
            target_post ctx func cenv cx es sa sb s0 ee pv vt op t /\
            (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
              slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
              storage_read_live cx tr (get_storage cx ee tr) slot tv) /\
            t.vs_current_bb = sb.cs_current_bb /\
            t.vs_inst_idx = LENGTH sb.cs_current_insts /\
            alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
          (\res ee r. expr_exit res r)
Proof
  cheat
QED
