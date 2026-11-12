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
  venomState
Libs
  pairLib

Definition target_sim_mem_def:
  target_sim_mem ctx func cenv cx env bt es <=>
    !st0 vt sa sb op s0.
      type_place_target env bt = SOME vt /\
      compile_get_target_ptr compile_expr cenv bt sa = (op, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
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
        (\H res ee r. expr_exit res r)
End

(* Held: the subscript case waits on S1's proved
   targetSubscriptSplit.target_subscript_main_case, which this base
   predates; the name, toplevel and attribute cases are in reach. *)
Theorem body_target_sim_mem:
  !t cx tops ctx func cenv env es.
    body_base_target_mem_ok cx t /\ body_inv tops ctx cenv cx /\
    EVERY (supported_expr tops) (target_indices t) /\
    target_pre cenv cx env t es ==>
    target_sim_mem ctx func cenv cx env t es
Proof
  cheat
QED

(* The place-valued evaluation after the base's counted outcome: the base's
   normal post carries over at its PlaceR payload (admissibility rules out
   the other value shapes), and its exits are unchanged. *)
Theorem gas_outcome_get_place_mem:
  gas_admissible (bind (source : evaluation_state -> eval_result evaluation_result)
                       get_place) target_place_res_ok es /\
  gas_outcome memory tops (ctx, func) cx st0 source (es, s0)
    (\H res ee t. ?pv. res = INL pv /\ P H pv ee t)
    (\H res ee r. expr_exit res r) ==>
  gas_outcome memory tops (ctx, func) cx st0 (bind source get_place) (es, s0)
    (\H res ee t. ?p. res = INL p /\ P H (PlaceR p) ee t)
    (\H res ee r. expr_exit res r)
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
      simp[expr_exit_INR_type]) >>
  strip_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err, ef) (callee, tf)` >>
  rewrite_tac[gas_outcome_def] >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ef`, `callee`, `tf`] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_result >> simp[]
QED

(* The judgment for eval_target_place: a target typed by a value type
   evaluates to a place, at the pointer, a storage place in range and live. *)
Theorem target_place_sim_mem_ready:
  !ctx func cenv cx env bt es st0 ty sa sb r s0.
    target_sim_mem ctx func cenv cx env bt es /\
    type_place_target env bt = SOME (Type ty) /\
    compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
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
        (!tr slot tv. p = StoragePlace tr slot tv ==>
           slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
           storage_read_live H tr (get_storage cx ee tr) slot tv) /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
      (\H res ee r. expr_exit res r)
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
        (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
           slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
           storage_read_live H tr (get_storage cx ee tr) slot tv) /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next`]
    gas_outcome_get_place_mem)) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  irule gas_outcome_post_mono >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _ _ _`)) >>
  rpt gen_tac >> strip_tac >> gvs[]
QED

Theorem target_place_sim_mem:
  !ctx func cenv cx env bt es st0 ty sa sb r s0.
    target_sim_mem ctx func cenv cx env bt es /\
    type_place_target env bt = SOME (Type ty) /\
    compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
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
      (\H res ee r. expr_exit res r)
Proof
  rpt strip_tac >> irule gas_outcome_post_mono >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _ _ _`)) >>
  irule_at Any target_place_sim_mem_ready >>
  rpt gen_tac >> strip_tac >> gvs[]
QED

(* What a target the lowering does not snapshot the RHS for
   (~expr_can_mutate) keeps: every live local's region whole, dynamic-array
   length words included (locals_kept exempts them), storage, transient
   storage, and the constructor's staged immutables.  Its scratch ALLOCAs can be reused in a loop, so the bytes
   below the frontier are not all kept, only these. *)
Definition target_pure_frame_def:
  target_pure_frame cenv cx (es : evaluation_state) (s0 : venom_state)
    (t : venom_state) <=>
    (!n b sz. local_region cenv es.scopes s0 n b sz ==>
              mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
    contract_storage t = contract_storage s0 /\
    contract_transient t = contract_transient s0 /\
    (!name off itv iv.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module, name) =
         SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
                  NONE => FEMPTY
                | SOME imms => get_source_immutables cenv.ce_module imms)
               name = SOME (itv, iv) ==>
       mem_bytes_at off (type_memory_size itv) t.vs_memory =
         mem_bytes_at off (type_memory_size itv) s0.vs_memory)
End

(* target_sim_mem with the pure-target frame on success. *)
Definition target_sim_mem_pure_def:
  target_sim_mem_pure ctx func cenv cx env bt es <=>
    !st0 vt sa sb op s0.
      type_place_target env bt = SOME vt /\
      compile_get_target_ptr compile_expr cenv bt sa = (op, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
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
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
          target_pure_frame cenv cx es s0 t)
        (\H res ee r. expr_exit res r)
End

(* Held with body_target_sim_mem: the subscript case waits on the same
   S1 target_subscript_main_case.  Stated for every target the lowering
   does not snapshot the RHS for (compile_stmt's Assign tests
   expr_can_mutate); a supported_target_pure target is one of them
   (bodySimLog.supported_pure_expr_no_mutate).  The ce_func_mutability pin
   it needs comes from body_inv (cenv_module_pins).  Proving it needs raw
   storage kept across compile_get_target_ptr, which the index's expr_post
   gives only on live slots (a dead popped storage slot is the gap). *)
Theorem body_target_sim_mem_pure:
  !t cx tops ctx func cenv env es.
    ~expr_can_mutate cenv (target_to_expr t) /\
    body_base_target_mem_ok cx t /\ body_inv tops ctx cenv cx /\
    target_pre cenv cx env t es ==>
    target_sim_mem_pure ctx func cenv cx env t es
Proof
  cheat
QED

Theorem target_place_sim_mem_pure:
  !ctx func cenv cx env bt es st0 ty sa sb r s0.
    target_sim_mem_pure ctx func cenv cx env bt es /\
    type_place_target env bt = SOME (Type ty) /\
    compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
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
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
        target_pure_frame cenv cx es s0 t)
      (\H res ee r. expr_exit res r)
Proof
  rpt strip_tac >>
  qpat_x_assum `gas_admissible _ _ _`
    (assume_tac o PURE_REWRITE_RULE [eval_target_place_as_bind]) >>
  pure_rewrite_tac [eval_target_place_as_bind] >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    (irule get_place_base_admissible >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `target_sim_mem_pure _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [target_sim_mem_pure_def]) >>
  disch_then (qspecl_then [`st0`, `Type ty`, `sa`, `sb`, `r`, `s0`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  mp_tac (BETA_RULE (Q.INST [`P` |->
    `\H pv ee t. target_post H ctx func cenv cx es sa sb s0 ee pv (Type ty) r t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
        target_pure_frame cenv cx es s0 t`]
    gas_outcome_get_place_mem)) >>
  disch_then irule >> conj_tac >- first_assum ACCEPT_TAC >>
  first_assum ACCEPT_TAC
QED
