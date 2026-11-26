Theory s1PrefixIntCallCalleeLocked
Ancestors
  bodyFullIntCallCallee bodyFullIntCallDefs s1PrefixDefs fragGasOriginPtr
  vyperState vyperInterpreter vyperStorageTrace vyperStorageFootprint vyperContext
  gasOutcomeFull gasStorage venomState finite_map gasExplicitSites gasSummary
  nonreentrantEquiv list

(* The successful lock adds no request and at most one lock observation. *)
Theorem intcall_callee_lock_request_frame[local]:
  lock_if_nr cx nr view es = (INL (),locked) ==>
  locked.requests = es.requests /\
  (?key. locked.storage_trace =
     es.storage_trace ++ (if nr then [StorageLock key] else []))
Proof
  Cases_on `nr` >> simp[lock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >> simp[raise_def] >>
  rename1 `cx.nonreentrant_slot = SOME key` >>
  Cases_on `view` >> Cases_on `cx.txn.is_static` >>
  Cases_on `lookup_storage (n2w key) (es.tStorage cx.txn.target) = 1w` >>
  simp[acquire_nonreentrant_lock_execution, ignore_bind_def, bind_def,
       check_not_static_def, check_def, assert_def, return_def, raise_def] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem intcall_callee_locked_request_prefix:
  lock_if_nr cx nr (is_view_mut mut) es1 = (INL (),locked) /\
  storage_trace_domain (cx with stk updated_by CONS (NONE,name)) st0
    locked.storage_trace /\
  at_body.vs_gas_readings = entered.vs_gas_readings /\
  (!H. gas_origin_ptr_path
     (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,MAP (op_prov G) arg_ops)
     (entered,FEMPTY,tn with t_var := FEMPTY) [] (OK at_body,Gl,tnl)) /\
  gas_prefix_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,MAP (op_prov G) arg_ops)
    (cx with stk updated_by CONS (NONE,name)) st0
    (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss) (locked,at_body,Gl,tnl) ==>
  gas_prefix_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,MAP (op_prov G) arg_ops)
    cx st0 (intcall_callee_src cx name mut nr ss)
    (es1,entered,FEMPTY,tn with t_var := FEMPTY)
Proof
  strip_tac >> drule intcall_callee_lock_request_frame >> strip_tac >>
  drule intcall_callee_body_gas_trace >> strip_tac >>
  qabbrev_tac `pushed = cx with stk updated_by CONS (NONE,name)` >>
  `!H tr. valid_horizon pushed st0 H tr <=> valid_horizon cx st0 H tr` by
    simp[Abbr `pushed`, valid_horizon_def,
         vyperFiniteStoragePreservationTheory.storage_well_formed_on_stk,
         vyperFiniteStoragePreservationTheory.storage_observations_ok_stk] >>
  qpat_x_assum `gas_prefix_full _ _ _ _ _`
    (qx_choose_then `marks` strip_assume_tac o
      ONCE_REWRITE_RULE[gas_prefix_full_def]) >>
  rewrite_tac[gas_prefix_full_def] >> qexists_tac `marks` >> conj_tac
  >- (qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
      conj_tac
      >- (strip_tac >> irule valid_horizon_append >>
          qexists_tac `if nr then [StorageLock key] else []` >> metis_tac[]) >>
      qpat_assum `!H. gas_origin_ptr_path _ _ [] _` (qspec_then `H` assume_tac) >>
      drule_then (irule o SIMP_RULE (srw_ss()) []) (cj 2 gas_origin_ptr_focus_rules) >>
      first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> rename1 `valid_horizon cx st0 J obs_pre` >>
  Cases_on `eval_stmts pushed ss
      (locked with gas_obs := gas_explicit marks entered.vs_gas_readings ++ tail)` >>
  rename1 `eval_stmts _ _ _ = (bres,body_end)` >>
  `body_end = ee` by metis_tac[pairTheory.SND] >>
  `?suffix. ee.storage_trace = locked.storage_trace ++ suffix` by
    (drule_at (Pos last) storage_trace_frame_prefix >>
     simp[evaluate_storage_trace_frame]) >>
  `LENGTH locked.storage_trace <= LENGTH obs_pre` by
    (Cases_on `nr` >> simp[] >> CCONTR_TAC >>
     `LENGTH obs_pre = LENGTH es1.storage_trace` by decide_tac >>
     `EL (LENGTH obs_pre) ee.storage_trace = StorageLock key` by
       (qpat_assum `ee.storage_trace = locked.storage_trace ++ _`
          (pure_rewrite_tac o single) >> simp[EL_APPEND_EQN]) >>
     `EL (LENGTH obs_pre) ee.storage_trace = StorageOutcome rq outcome` by
       (qpat_assum `ee.storage_trace = obs_pre ++ _`
          (pure_rewrite_tac o single) >> simp[EL_APPEND_EQN]) >>
     fs[]) >>
  `request_site
    (DF J,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,MAP (op_prov G) arg_ops)
    pushed J (at_body,Gl,tnl) (e2eRequestCutDefs$recorded_outcomes_count obs_pre) rq outcome` by
    (first_x_assum irule >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC >> NO_TAC)
     >- (qpat_assum `LENGTH es1.requests = _` mp_tac >>
         Cases_on `nr` >>
         simp[e2eRequestCutDefsTheory.recorded_outcomes_count_def,
              FILTER_APPEND_DISTRIB])
     >- (qexistsl_tac [`ee`,`bres`,`sfx`,`tail`] >> conj_tac
         >- first_assum ACCEPT_TAC >>
         qpat_assum `body_end = ee` (pure_rewrite_tac o single o GSYM) >> simp[]) >>
     metis_tac[]) >>
  qpat_x_assum `request_site _ _ _ _ _ _ _` mp_tac >>
  simp[request_site_def, Abbr `pushed`] >> strip_tac >>
  rename1 `gas_origin_ptr_focus (DF J,_,_,_,_,_) (at_body,Gl,tnl) site_marks
    (site_fn,site_pg,site_g,site_tn,site_state)` >>
  rename1 `step_inst site_fuel ctx site_inst site_state = OK site_next` >>
  qexistsl_tac [`site_marks`,`site_fn`,`site_pg`,`site_g`,`site_tn`,
               `site_state`,`site_inst`,`site_fuel`,`site_next`] >>
  simp[] >>
  qpat_assum `!H. gas_origin_ptr_path _ _ [] _` (qspec_then `J` assume_tac) >>
  drule_then (irule o SIMP_RULE (srw_ss()) []) (cj 2 gas_origin_ptr_focus_rules) >>
  first_assum ACCEPT_TAC
QED
