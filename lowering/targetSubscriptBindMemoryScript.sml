(* Counted subscript composition from compiler and continuation boundaries. *)
Theory targetSubscriptBindMemory
Ancestors
  targetSubscriptSplit targetPlaceSim
  exprSimMemDefs exprSimHypsDefs exprSimSource targetPlaceSimDefs
  stmtLoweringMono exprLoweringProps vyperInterpreter vyperState
  allocaHistory vyperTypeCallGraph vyperTypeEnv targetSubscriptContinuation
  gasOutcome gasStorage gasSummary vyperStorageFootprint vyperStorageTrace stmtSimProps

Theorem target_subscript_case_mem_from_boundaries:
  (!nocalls ctx func cenv cx env bt e es tops bvt vt sa rb sm ix sn op sb s0 st0 left pv mid t.
    target_pre cenv cx env (SubscriptTarget bt e) es /\
    (nocalls ==> int_calls_target (SubscriptTarget bt e) = []) /\
    ((?s p s1. eval_base_place cx bt s = (INL p,s1)) ==>
      (!env ty es. expr_body_pre cenv cx env e es /\
        (nocalls ==> int_calls_expr e = []) ==>
        expr_sim_mem ctx func cenv cx ty e es) /\
      (!env ty es. expr_body_pre cenv cx env e es /\
        (nocalls ==> int_calls_expr e = []) ==>
        expr_vv_sim_mem ctx func cenv cx ty e es)) /\
    body_inv tops ctx cenv cx /\
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
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H)) /\
    alloca_history func s0 /\ alloca_history func t /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    gas_marked_exec T (ctx,func) (eval_base_place cx bt)
      (es,s0) left (INL pv) mid (OK t) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      target_post H ctx func cenv cx es sa sm s0 (mid with gas_obs := []) pv bvt rb t /\
      (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
        slots_in_range (get_storage cx (mid with gas_obs := []) tr) (w2n slot) tv /\
        storage_read_live H tr (get_storage cx (mid with gas_obs := []) tr) slot tv)) /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    gas_outcome T (cx_tops cx) (ctx,func) cx st0
      (bind (bind (eval_expr cx e) (read_result cx))
        (\key. extend_place cx pv (ValueSubscript key)))
      (mid with gas_obs := [],t)
      (\H res ee u. ?pv'. res = INL pv' /\
        target_post H ctx func cenv cx es sa sb s0 ee pv' vt op u /\
        (!tr slot tv. pv' = PlaceR (StoragePlace tr slot tv) ==>
          slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
          storage_read_live H tr (get_storage cx ee tr) slot tv) /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next)
      (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)) /\
  (!bt tops ctx cenv cx env es pv ee sa rb sm.
    body_inv tops ctx cenv cx /\
    target_pre cenv cx env bt es /\
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
    eval_base_place cx bt es = (INL pv,ee) /\
    compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
    ~block_is_terminated sa ==> ~block_is_terminated sm) ==>
  !nocalls ctx func cenv cx bt e tops.
    (!env es.
      target_pre cenv cx env bt es /\
      (nocalls ==> int_calls_target bt = []) ==>
      !vt sa sb op s0 st0.
        type_place_target env bt = SOME vt /\
        compile_get_target_ptr compile_expr cenv bt sa = (op,sb) /\
        fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
        local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
        gas_admissible (eval_base_place cx bt) target_res_ok es /\
        (!H. valid_horizon cx st0 H es.storage_trace ==>
          stmt_state_rel H ctx func cenv cx es s0 /\
          storage_well_formed_on cx es (FST H)) /\
        alloca_history func s0 /\ ~s0.vs_halted /\
        s0.vs_current_bb = sa.cs_current_bb /\
        s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
        gas_outcome T (cx_tops cx) (ctx,func) cx st0 (eval_base_place cx bt) (es,s0)
          (\H res ee t. ?pv. res = INL pv /\
            target_post H ctx func cenv cx es sa sb s0 ee pv vt op t /\
            (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
              slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
              storage_read_live H tr (get_storage cx ee tr) slot tv) /\
            t.vs_current_bb = sb.cs_current_bb /\
            t.vs_inst_idx = LENGTH sb.cs_current_insts /\
            alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
          (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)) /\
    ((?s pv s1. eval_base_place cx bt s = (INL pv,s1)) ==>
      (!env ty es. expr_body_pre cenv cx env e es /\
        (nocalls ==> int_calls_expr e = []) ==>
        expr_sim_mem ctx func cenv cx ty e es) /\
      (!env ty es. expr_body_pre cenv cx env e es /\
        (nocalls ==> int_calls_expr e = []) ==>
        expr_vv_sim_mem ctx func cenv cx ty e es)) /\
    body_inv tops ctx cenv cx ==>
    !env es.
      target_pre cenv cx env (SubscriptTarget bt e) es /\
      (nocalls ==> int_calls_target (SubscriptTarget bt e) = []) ==>
      !vt sa sb op s0 st0.
        type_place_target env (SubscriptTarget bt e) = SOME vt /\
        compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa = (op,sb) /\
        fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
        local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
        gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
        (!H. valid_horizon cx st0 H es.storage_trace ==>
          stmt_state_rel H ctx func cenv cx es s0 /\
          storage_well_formed_on cx es (FST H)) /\
        alloca_history func s0 /\ ~s0.vs_halted /\
        s0.vs_current_bb = sa.cs_current_bb /\
        s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
        gas_outcome T (cx_tops cx) (ctx,func) cx st0
          (eval_base_place cx (SubscriptTarget bt e)) (es,s0)
          (\H res ee t. ?pv. res = INL pv /\
            target_post H ctx func cenv cx es sa sb s0 ee pv vt op t /\
            (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
              slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
              storage_read_live H tr (get_storage cx ee tr) slot tv) /\
            t.vs_current_bb = sb.cs_current_bb /\
            t.vs_inst_idx = LENGTH sb.cs_current_insts /\
            alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
          (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  rpt strip_tac >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    metis_tac[target_subscript_base_admissible] >>
  `?bvt. type_place_target env bt = SOME bvt /\
    subscript_vtype bvt (expr_type e) = SOME vt` by
    fs[type_place_target_SubscriptTarget] >>
  drule target_subscript_compile_decompose >> strip_tac >>
  drule_all target_subscript_compile_intervals >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\
    fn_has_code sn sb func` by
    (irule target_subscript_interval_code >> simp[]) >>
  suspend "bind"
QED

Resume target_subscript_case_mem_from_boundaries[bind]:
  irule (Q.INST [`keep_halt` |-> `T`] target_subscript_bind_outcome_halt |> SRULE []) >>
  qexists `\H pv ee t.
    target_post H ctx func cenv cx es sa sm s0 ee pv bvt rb t /\
    (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
      slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
      storage_read_live H tr (get_storage cx ee tr) slot tv) /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` >>
  reverse conj_tac
  >- (first_x_assum (qspecl_then [`env`, `es`] mp_tac) >>
      (impl_tac >- fs[int_calls_expr_def]) >>
      simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[BETA_THM] >>
  reverse (Cases_on `storage_trace_domain cx st0 mid.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists `[]` >> disj1_tac >>
      irule gas_bad_storage_at_initial >> simp[] >>
      irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_extend_place] >>
      irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     es.storage_trace` by
    metis_tac[gas_marked_exec_valid_prefix, evaluate_storage_trace_frame] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    (qpat_x_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       drule >>
     simp[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def]) >>
  `alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
   t.vs_current_bb = sm.cs_current_bb /\
   t.vs_inst_idx = LENGTH sm.cs_current_insts` by
    (qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       drule >> simp[]) >>
  drule target_subscript_marked_base_source >>
  disch_then (qspec_then `[]` assume_tac) >>
  `~block_is_terminated sm` by
    (qpat_x_assum `!bt tops ctx cenv cx env es pv ee sa rb sm. _` irule >>
     goal_assum (drule_at (Pat `eval_base_place _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `compile_get_target_ptr _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `body_inv _ _ _ _`)) >>
     qexists `env` >> simp[targetPlaceLiveTheory.target_indices_def] >>
     gvs[targetPlaceLiveTheory.target_indices_def]) >>
  qpat_x_assum `!nocalls ctx func cenv cx env bt e es tops bvt vt sa rb sm ix sn op sb s0 st0 left pv mid t. _` irule >>
  simp[] >> conj_tac
  >- (qexists `tops` >> gvs[targetPlaceLiveTheory.target_indices_def]) >>
  goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  qexistsl [`bvt`, `env`, `ix`, `nocalls`, `rb`, `sm`, `sn`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >> simp[] >> metis_tac[]
QED

Finalise target_subscript_case_mem_from_boundaries
