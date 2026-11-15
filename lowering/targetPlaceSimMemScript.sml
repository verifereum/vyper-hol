(* Memory-counted place-target simulation: the gas_outcome T twin of
   targetPlaceSimDefs.target_sim, which also keeps the alloca history and
   the allocation frontier, as the memory expression simulations need at
   their entry. *)
Theory targetPlaceSimMem
Ancestors
  bodyMemoryPreds targetPlaceSimCases targetPlaceSim exprSimMemDefs
  bodyPtrPopTargetFragTransport
  allocaHistory exprSimDefs targetPlaceSimDefs gasContext gasOutcome gasSummary
  gasExemptCert gasStorage vyperStorageFootprint vyperStorageTrace
  stmtSimProps loweringPosts exprLowering compileEnv
  supportedTargets vyperAST vyperInterpreter vyperState vyperTypeSystem
  venomState targetRootAttributeMemory targetAttributeMemory
  targetSubscriptCompositionMemory targetPlaceSimCasesBase
Libs
  pairLib

Definition target_sim_mem_def:
  target_sim_mem ctx func cenv cx env bt es <=>
    !st0 vt sa sb op s0.
      type_place_target env bt = SOME vt /\
      compile_get_target_ptr compile_expr cenv bt sa = (op, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
      gas_admissible (eval_base_place cx bt) target_res_ok es /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H)) /\
      alloca_history func s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome T (cx_tops cx) (ctx, func) cx st0 (eval_base_place cx bt) (es, s0)
        (\H res ee t. ?pv. res = INL pv /\
          target_post H ctx func cenv cx es sa sb s0 ee pv vt op t /\
          (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
             slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
             storage_read_live H tr (get_storage cx ee tr) slot tv) /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
        (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)
End

Theorem body_target_sim_mem:
  !t cx tops ctx func cenv env es.
    body_base_target_mem_ok cx t /\ body_inv tops ctx cenv cx /\
    EVERY (supported_expr tops) (target_indices t) /\
    target_pre cenv cx env t es ==>
    target_sim_mem ctx func cenv cx env t es
Proof
  ho_match_mp_tac base_assignment_target_induct >> rpt conj_tac
  >- (rpt strip_tac >> rewrite_tac[target_sim_mem_def] >>
      rpt strip_tac >> irule target_name_memory >> simp[] >> qexists `env` >> simp[])
  >- (rpt strip_tac >> rewrite_tac[target_sim_mem_def] >>
      rpt strip_tac >> irule target_toplevel_memory >> simp[] >> qexists `env` >> simp[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      rewrite_tac[target_sim_mem_def] >>
      rpt strip_tac >> irule (Q.SPEC `F` target_subscript_case_mem) >> simp[] >>
      conj_tac
      >- (rpt strip_tac >>
          first_x_assum (irule o REWRITE_RULE [target_sim_mem_def]) >>
          gvs[body_base_target_mem_ok_def, targetPlaceLiveTheory.target_indices_def] >>
          conj_tac >- (qexists `tops` >> simp[]) >> qexists `env'` >> simp[]) >>
      conj_tac
      >- (gvs[body_base_target_mem_ok_def, body_expr_mem_ok_def] >> metis_tac[]) >>
      conj_tac >- (qexists `tops` >> simp[]) >> qexists `env` >> simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rewrite_tac[target_sim_mem_def] >> rpt strip_tac >>
  irule target_attribute_memory >> simp[] >>
  qexists `env` >> simp[] >> rpt strip_tac >>
  first_x_assum (irule o REWRITE_RULE [target_sim_mem_def]) >>
  gvs[body_base_target_mem_ok_def, targetPlaceLiveTheory.target_indices_def] >>
  conj_tac >- (qexists `tops` >> simp[]) >>
  qexists `env` >> simp[] >> metis_tac[target_pre_sub]
QED

(* The place-valued evaluation after the base's counted outcome: the base's
   normal post carries over at its PlaceR payload (admissibility rules out
   the other value shapes), and its exits are unchanged. *)
Theorem gas_outcome_get_place_mem:
  gas_admissible (bind (source : evaluation_state -> eval_result evaluation_result)
                       get_place) target_place_res_ok es /\
  gas_outcome memory tops (ctx, func) cx st0 source (es, s0)
    (\H res ee t. ?pv. res = INL pv /\ P H pv ee t)
    (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r) ==>
  gas_outcome memory tops (ctx, func) cx st0 (bind source get_place) (es, s0)
    (\H res ee t. ?p. res = INL p /\ P H (PlaceR p) ee t)
    (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  strip_tac >>
  `!v. storage_trace_frame (get_place v)` by
    (Cases_on `v` >>
     simp[get_place_def, storage_trace_frame_return, storage_trace_frame_raise]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ source _ _ _`
    (mp_tac o BETA_RULE o REWRITE_RULE [gas_outcome_def]) >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN mp_tac))
  >- (strip_tac >> rewrite_tac[gas_outcome_def] >>
      qexists_tac `marks` >> disj1_tac >>
      irule gas_bad_storage_at_bind_left >> simp[]) >>
  disch_then (DISJ_CASES_THEN mp_tac)
  >- (rewrite_tac[gas_summary_at_def] >> BETA_TAC >>
      disch_then (qx_choose_then `res` (qx_choose_then `mid`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
      reverse (Cases_on `storage_trace_domain cx st0 mid.storage_trace`)
      >- (disch_then kall_tac >> rewrite_tac[gas_outcome_def] >>
          qexists_tac `marks` >> disj1_tac >>
          irule gas_bad_storage_at_bind_left >> simp[] >>
          irule gas_bad_storage_at_counted_prefix >>
          metis_tac[]) >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
         mid.storage_trace` by fs[storage_trace_domain_def] >>
      disch_then (DISJ_CASES_THEN strip_assume_tac)
      >- (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
            (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
          impl_tac >- first_assum ACCEPT_TAC >>
          strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
          qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
            (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
          `?p. pv = PlaceR p` by (
            qpat_x_assum `gas_admissible _ _ _`
              (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
            disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings`
                          mp_tac) >>
            qpat_assum `!tail. source _ = _` (qspec_then `[]` mp_tac) >>
            simp[bind_def] >> strip_tac >>
            Cases_on `pv` >>
            simp[get_place_def, raise_def, target_place_res_ok_def]) >>
          rpt BasicProvers.VAR_EQ_TAC >>
          rewrite_tac[gas_outcome_def] >>
          qexists_tac `marks` >> disj2_tac >> disj1_tac >>
          rewrite_tac[gas_summary_at_def] >>
          qexistsl_tac [`INL p`, `mid`, `OK t`] >>
          conj_tac
          >- (rewrite_tac[gas_marked_exec_def] >> conj_tac
              >- (gen_tac >>
                  qpat_assum `!tail. source _ = _` (qspec_then `tail` mp_tac) >>
                  simp[bind_def, get_place_def, return_def]) >>
              first_assum ACCEPT_TAC) >>
          BETA_TAC >> disj1_tac >> qexists_tac `t` >> simp[] >>
          qx_gen_tac `H1` >> strip_tac >>
          qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
            (qspec_then `H1` mp_tac) >>
          simp[]) >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _`
        (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >>
      strip_tac >>
      `?ex. res = INR ex` by (Cases_on `res` >> gvs[expr_exit_def]) >>
      rpt BasicProvers.VAR_EQ_TAC >>
      rewrite_tac[gas_outcome_def] >>
      qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR ex`, `mid`, `r`] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      BETA_TAC >> disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      qx_gen_tac `H1` >> strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
        (qspec_then `H1` mp_tac) >>
      simp[expr_exit_INR_type, halt_exit_def]) >>
  strip_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err, ef) (callee, tf)` >>
  rewrite_tac[gas_outcome_def] >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ef`, `callee`, `tf`] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_result >> simp[]
QED

(* The judgment for eval_target_place: a target typed by a value type
   evaluates to a place, at the pointer. *)
Theorem target_place_sim_mem:
  !ctx func cenv cx env bt es st0 ty sa sb r s0.
    target_sim_mem ctx func cenv cx env bt es /\
    type_place_target env bt = SOME (Type ty) /\
    compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
    gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H)) /\
    alloca_history func s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome T (cx_tops cx) (ctx, func) cx st0 (eval_target_place cx bt) (es, s0)
      (\H res ee t. ?p. res = INL p /\
        target_post H ctx func cenv cx es sa sb s0 ee (PlaceR p) (Type ty) r t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
      (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  rpt strip_tac >>
  qpat_x_assum `gas_admissible _ _ _`
    (assume_tac o PURE_REWRITE_RULE [eval_target_place_as_bind]) >>
  pure_rewrite_tac [eval_target_place_as_bind] >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    (irule get_place_base_admissible >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `target_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [target_sim_mem_def]) >>
  disch_then (qspecl_then [`st0`, `Type ty`, `sa`, `sb`, `r`, `s0`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  mp_tac (BETA_RULE (Q.INST [`P` |->
    `\H pv ee t. target_post H ctx func cenv cx es sa sb s0 ee pv (Type ty) r t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next`]
    gas_outcome_get_place_mem)) >>
  disch_then irule >> conj_tac >- first_assum ACCEPT_TAC >>
  irule gas_outcome_post_mono >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _ _ _`)) >>
  rpt gen_tac >> strip_tac >> gvs[]
QED
