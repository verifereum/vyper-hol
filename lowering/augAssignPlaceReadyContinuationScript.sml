(* Counted target traversal retaining storage readiness at the continuation. *)
Theory augAssignPlaceReadyContinuation
Ancestors
  augAssignPlaceMemoryTarget augAssignPlaceRhsMemory
  augAssignPlaceWordStoreMemory bodyAugAssignOther gasSummary
  targetPlaceSimMem stmtSimAugAssignPlaceMemory exprSimSubscriptMap
  vyperInterpreter gasOutcome targetPlaceSimDefs
  gasContext targetPlaceSimCases vyperState vyperStorageTrace
  vyperStorageFootprint gasStorage bodyPtrPopTargetFragTransport
Libs
  pairLib

(* The continuation sees the place with its storage range and liveness, the
   pointer facts, and the marked run that reached it.  The guarded premise
   carries the horizon-indexed facts; the rest does not depend on it. *)
Theorem aug_place_target_ready_mem_continuation:
  target_sim_mem ctx func cenv cx env bt es /\
  type_place_target env bt = SOME (Type ty) /\
  compile_get_target_ptr compile_expr cenv bt sa = (r,sp) /\
  fn_has_code sa sp func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H)) /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!p mid t marks.
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      target_post H ctx func cenv cx es sa sp s0 mid (PlaceR p) (Type ty) r t /\
      (!tr slot tv. p = StoragePlace tr slot tv ==>
        slots_in_range (get_storage cx mid tr) (w2n slot) tv /\
        storage_read_live H tr (get_storage cx mid tr) slot tv)) /\
    t.vs_current_bb = sp.cs_current_bb /\
    t.vs_inst_idx = LENGTH sp.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    (!tail. eval_target_place cx bt
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL p, mid with gas_obs := tail)) /\
    gas_marked_path T ctx func s0 (LENGTH marks) (OK t) ==>
    gas_outcome T (cx_tops cx) (ctx,func) cx st0
      ((k p) : evaluation_state -> 'a evaluation_result) (mid,t) Q R) /\
  (!p. storage_trace_frame ((k p) : evaluation_state -> 'a evaluation_result)) /\
  (!H res ee rr. expr_exit (res : eval_result + exception) rr ==>
    ?ex. res = INR ex /\ R H (INR ex) ee rr) ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
    (bind (eval_target_place cx bt) k) (es,s0) Q R
Proof
  strip_tac >>
  `gas_admissible (bind (eval_base_place cx bt) get_place) target_place_res_ok es` by
    (qpat_x_assum `gas_admissible (eval_target_place _ _) _ _`
       (mp_tac o PURE_REWRITE_RULE
          [bodyPtrPopTargetFragTransportTheory.eval_target_place_as_bind]) >>
     simp[]) >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    (irule bodyPtrPopTargetFragTransportTheory.get_place_base_admissible >>
     first_assum ACCEPT_TAC) >>
  `!v. storage_trace_frame (bind (get_place v) k)` by
    (gen_tac >> irule storage_trace_frame_bind_all >> simp[] >>
     Cases_on `v` >>
     simp[get_place_def, storage_trace_frame_return, storage_trace_frame_raise]) >>
  qpat_x_assum `target_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [target_sim_mem_def]) >>
  disch_then (qspecl_then [`st0`, `Type ty`, `sa`, `sp`, `r`, `s0`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  rewrite_tac[aug_place_target_bind_base] >>
  irule gas_outcome_bind_result_exec >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _ _ _`)) >>
  rpt conj_tac
  >- (rpt strip_tac >> gvs[])
  >- (rpt gen_tac >> BETA_TAC >> strip_tac >> first_x_assum irule >>
      first_assum ACCEPT_TAC)
  >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
      reverse (Cases_on `storage_trace_domain cx st0 mid.storage_trace`)
      >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
          irule gas_bad_storage_at_initial >> simp[]) >>
      `?H0. valid_horizon cx st0 H0 mid.storage_trace` by
        (qexists_tac `storage_trace_horizon mid.storage_trace` >>
         fs[storage_trace_domain_def]) >>
      qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
      `?p. v = PlaceR p` by
        (qpat_x_assum `gas_admissible (bind _ get_place) _ _`
           (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
         disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
         qpat_assum `!tail. eval_base_place _ _ _ = _` (qspec_then `[]` mp_tac) >>
         simp[bind_def] >> strip_tac >> Cases_on `v` >>
         simp[get_place_def, raise_def, target_place_res_ok_def]) >>
      rpt BasicProvers.VAR_EQ_TAC >>
      `gas_outcome T (cx_tops cx) (ctx,func) cx st0 (k p)
         (mid with gas_obs := [],t) Q R` suffices_by
        simp[get_place_def, bind_return] >>
      `t.vs_current_bb = sp.cs_current_bb /\
       t.vs_inst_idx = LENGTH sp.cs_current_insts /\
       alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` by
        (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
           (qspec_then `H0` mp_tac) >> simp[]) >>
      first_x_assum (qspecl_then [`p`, `mid with gas_obs := []`, `t`, `marks`]
                       mp_tac) >>
      impl_tac
      >- (conj_tac >- simp[] >>
          conj_tac
          >- (rpt strip_tac >>
              qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
                (qspec_then `H` mp_tac) >>
              impl_tac >- gvs[] >> simp[]) >>
          rpt (conj_tac >- first_assum ACCEPT_TAC) >>
          conj_tac
          >- (gen_tac >>
              qpat_assum `!tail. eval_base_place _ _ _ = _`
                (qspec_then `tail` mp_tac) >>
              simp[bodyPtrPopTargetFragTransportTheory.eval_target_place_as_bind,
                   bind_def, get_place_def, return_def]) >>
          first_assum ACCEPT_TAC) >>
      simp[])
  >- (gen_tac >> BETA_TAC >> first_assum ACCEPT_TAC)
QED
