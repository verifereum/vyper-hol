(* Saved located arguments on the selected positional path. *)
Theory bodyFullExtCallRequestSavedLocated
Ancestors
  bodyFullGhostFrame exprSimVVFrame logValueFramePtr exprPtrUnwrapStorageFacts
  bodyFullExtCallRequestPositional
  exprSimProps exprSimDefs exprSimMemDefs loweringPosts bodyPtrDefs
  loweringStateRelDefs venomState vyperState context compileEnv
  exprLoweringProps freshWrites finite_map words list

Theorem extcall_request_saved_located_endpoint:
  ~is_word_type (lowered_value_type cenv e) /\
  (p.ptr_location = LocMemory \/
   (?si sm0. lowered_value_type cenv e = expr_type e /\
    compile_expr cenv (expr_type e) e si =
      (LocatedValue (lowered_value_type cenv e) p,sm0) /\
    sa.cs_next_var <= si.cs_next_var /\ sa.cs_next_id <= si.cs_next_id /\
    sm0.cs_next_var <= sm.cs_next_var /\ sm0.cs_next_id <= sm.cs_next_id)) /\
  (?raw. read_result cx raw mid = (INL v,mid) /\
    vv_holds cenv cx (lowered_value_type cenv e) raw
      (LocatedValue (lowered_value_type cenv e) p) mid t /\
    vv_at cenv cx (lowered_value_type cenv e) sa sm mid raw
      (LocatedValue (lowered_value_type cenv e) p) t /\
    ptr_vv_ok cx (lowered_value_type cenv e) raw
      (LocatedValue (lowered_value_type cenv e) p) mid G1 tn1 t /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) mid raw
      (LocatedValue (lowered_value_type cenv e) p) t) /\
  vv_storage_live H cx (LocatedValue (lowered_value_type cenv e) p) mid t /\
  (p.ptr_location = LocMemory ==> ptr_buf_ok cenv e p.ptr_operand G1 t) /\
  (cenv.ce_is_ctor /\ p.ptr_location = LocCode ==>
    !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
      eval_operand p.ptr_operand t = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
        val_in_memory rt v (w2n w) mem)) /\
  ci_mono sm sb /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  pure_frame cenv func mid sm t u /\
  ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2 /\
  (!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==> lookup_var x u = SOME w) /\
  (!aid row. FLOOKUP t.vs_allocas aid = SOME row ==> FLOOKUP u.vs_allocas aid = SOME row) /\
  alloca_inv u /\ t.vs_alloca_next <= u.vs_alloca_next /\
  u.vs_labels = t.vs_labels /\
  (!n b sz. local_region cenv mid.scopes t n b sz <=> local_region cenv ee.scopes u n b sz) /\
  (ee with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) =
    (mid with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) /\
  stmt_state_rel H ctx func cenv cx ee u /\
  ghost_inv_at D lo d cenv cx ee G2 tn2 u /\
  dead_lo_ok H D lo cenv cx ==>
  (p.ptr_location = LocMemory \/
   (?si sm0. lowered_value_type cenv e = expr_type e /\
    compile_expr cenv (expr_type e) e si =
      (LocatedValue (lowered_value_type cenv e) p,sm0) /\
    sa.cs_next_var <= si.cs_next_var /\ sa.cs_next_id <= si.cs_next_id /\
    sm0.cs_next_var <= sb.cs_next_var /\ sm0.cs_next_id <= sb.cs_next_id)) /\
  (?raw. read_result cx raw ee = (INL v,ee) /\
    vv_holds cenv cx (lowered_value_type cenv e) raw
      (LocatedValue (lowered_value_type cenv e) p) ee u /\
    vv_at cenv cx (lowered_value_type cenv e) sa sb ee raw
      (LocatedValue (lowered_value_type cenv e) p) u /\
    ptr_vv_ok cx (lowered_value_type cenv e) raw
      (LocatedValue (lowered_value_type cenv e) p) ee G2 tn2 u /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw
      (LocatedValue (lowered_value_type cenv e) p) u) /\
  vv_storage_live H cx (LocatedValue (lowered_value_type cenv e) p) ee u /\
  (p.ptr_location = LocMemory ==> ptr_buf_ok cenv e p.ptr_operand G2 u) /\
  (cenv.ce_is_ctor /\ p.ptr_location = LocCode ==>
    !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
      eval_operand p.ptr_operand u = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
        val_in_memory rt v (w2n w) mem))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?raw. _` strip_assume_tac >> (
  `?w. eval_operand p.ptr_operand t = SOME w` by gvs[vv_holds_def] >>
  `eval_operand p.ptr_operand u = SOME w` by
    (Cases_on `p.ptr_operand` >> gvs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `eval_operand p.ptr_operand u = eval_operand p.ptr_operand t` by simp[] >>
  `ee.scopes = mid.scopes /\ ee.accounts = mid.accounts /\
   ee.tStorage = mid.tStorage /\ ee.immutables = mid.immutables` by
    (qpat_assum `ee with <|gas_obs := []; outcomes := NONE; storage_trace := []|> = _`
      (mp_tac o AP_TERM
        ``\st:evaluation_state. (st.scopes,st.accounts,st.tStorage,st.immutables)``) >>
     simp[]) >>
  conj_tac >- (gvs[ci_mono_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (`expr_val_at cenv cx (lowered_value_type cenv e) sa sm mid v p.ptr_operand t` by
        (drule_all vv_at_memory_val_at >> simp[]) >>
      `!tv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv ==>
        val_wf tv v /\
        mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
          mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory /\
        (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tn2.t_mem ==>
          i IN tn1.t_mem)` by
        (rpt gen_tac >> strip_tac >> conj_tac
         >- (gvs[expr_val_at_def] >> metis_tac[]) >>
         conj_tac >- (drule_all expr_val_at_pure_frame_bytes >> simp[]) >>
         rpt strip_tac >>
         drule_all (INST_TYPE [alpha |-> ``:num # num``, beta |-> ``:num # num``]
           expr_val_at_ghost_kept_at_taint) >> simp[]) >>
      `(!x. p.ptr_operand = Var x ==> FLOOKUP G2 x = FLOOKUP G1 x) /\
       op_taint tn2 p.ptr_operand = op_taint tn1 p.ptr_operand` by
        (gvs[ghost_kept_at_def] >> Cases_on `p.ptr_operand` >>
         gvs[ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
      simp[] >> reverse conj_tac
      >- (irule ptr_buf_ok_frame >> qexistsl_tac [`G1`,`t`] >> simp[]) >>
      qexists_tac `Value v` >>
      simp[vv_holds_def, vv_at_def, ptr_vv_ok_def, read_result_def, return_def] >>
      conj_tac
      >- (gvs[vv_holds_def] >> rpt strip_tac >>
          irule val_in_memory_footprint_agree >> conj_tac >- metis_tac[] >>
          qexists_tac `t.vs_memory` >>
          metis_tac[]) >>
      conj_tac
      >- (gvs[expr_val_at_def, ci_mono_def] >> rpt gen_tac >> strip_tac >>
          simp[] >>
          qpat_x_assum `!tv. _ ==> (?(aid:num) b sz. _) \/ _` drule >>
          simp[] >> strip_tac
          >- (disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >> simp[] >>
              metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS])
          >- (disj2_tac >> disj1_tac >> qexistsl_tac [`n`,`b`,`sz`] >>
              simp[local_place_at_def] >> metis_tac[]) >> simp[]) >>
      conj_tac
      >- (`ptr_val_ok cx (lowered_value_type cenv e) v p.ptr_operand G1 tn1 t` by
            gvs[ptr_vv_ok_def, ptr_val_ok_def] >>
          `ptr_val_ok cx (lowered_value_type cenv e) v p.ptr_operand G2 tn2 u` by
            (irule ptr_val_ok_footprint_frame >>
             qexistsl_tac [`G1`,`t`,`tn1`] >> simp[] >> metis_tac[]) >>
          gvs[ptr_vv_ok_def, ptr_val_ok_def]) >>
      gvs[vv_store_bound_def, read_result_def, return_def] >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  gvs[] >>
  `op_taint tn2 p.ptr_operand = op_taint tn1 p.ptr_operand /\
   op_prov G2 p.ptr_operand = op_prov G1 p.ptr_operand` by
    (gvs[ghost_kept_at_def] >> Cases_on `p.ptr_operand` >>
     gvs[ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def] >> metis_tac[]) >>
  `vv_storage_live H cx (LocatedValue (lowered_value_type cenv e) p) ee u` by
    gvs[vv_storage_live_def, vyperStorageBackendTheory.get_storage_def] >>
  simp[] >>
  reverse conj_tac
  >- (conj_tac
      >- gvs[vyperStorageBackendTheory.get_storage_def] >>
      rpt strip_tac >>
      `val_wf rt v` by
        (gvs[vv_holds_def, immutable_holds_def] >>
         metis_tac[valueEncodingTypingTheory.value_has_type_val_wf]) >>
      `val_footprint rt v <= type_memory_size rt` by
        metis_tac[val_footprint_le] >>
      `w2n w + type_memory_size rt <= lo` by
        (qpat_assum `cenv.ce_is_ctor /\ _ ==> _` mp_tac >> simp[] >> decide_tac) >>
      `mem_bytes_at (w2n w) (val_footprint rt v) u.vs_memory =
       mem_bytes_at (w2n w) (val_footprint rt v) t.vs_memory` by
        (gvs[pure_frame_def, ghost_inv_at_def, ptrDisciplineTheory.allocas_from_def] >>
         first_x_assum irule >> rpt strip_tac >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
         first_x_assum (drule_at Any) >> strip_tac >> decide_tac) >>
      irule robust_val_in_memory_footprint_frame >>
      conj_tac >- simp[] >>
      qexistsl_tac [`t.vs_memory`,`u.vs_memory`,`tn1.t_mem`,`tn2.t_mem`] >>
      simp[] >>
      gvs[ghost_kept_at_def] >> rpt strip_tac >>
      first_x_assum irule >> simp[] >> decide_tac) >>
  qexists_tac `Value v` >>
  simp[read_result_def, return_def, vv_at_def, vv_store_bound_def] >>
  conj_tac >- (gvs[vv_holds_def] >> Cases_on `p.ptr_location` >>
    gvs[storage_holds_def, immutable_holds_def, read_result_def, return_def,
        vyperStorageBackendTheory.get_storage_def]
    >- (conj_tac >-
         (gvs[read_storage_slot_def, get_storage_backend_def, bind_def,
              get_accounts_def, get_transient_storage_def, return_def,
              lift_option_def] >>
          Cases_on `decode_value (lookup_account cx.txn.target mid.accounts).storage (w2n w) tvt` >>
          gvs[return_def, raise_def]) >>
         irule accountsRelPropsTheory.storage_range_agree_of_live >>
         conj_tac >- gvs[accountsRelPropsTheory.storage_range_agree_def] >>
         qexistsl_tac [`H`,`F`] >>
         gvs[stmt_state_rel_def, state_rel_def, storage_rel_def,
             vfmStateTheory.lookup_account_def])
    >- (conj_tac >-
         (gvs[read_storage_slot_def, get_storage_backend_def, bind_def,
              get_accounts_def, get_transient_storage_def, return_def,
              lift_option_def] >>
          Cases_on `decode_value (vfmExecution$lookup_transient_storage cx.txn.target mid.tStorage) (w2n w) tvt` >>
          gvs[return_def, raise_def]) >>
         irule accountsRelPropsTheory.storage_range_agree_of_live >>
         conj_tac >- gvs[accountsRelPropsTheory.storage_range_agree_def] >>
         qexistsl_tac [`H`,`T`] >>
         gvs[stmt_state_rel_def, state_rel_def, transient_rel_def]) >>
    qexistsl_tac [`name`,`off`,`itv`,`iv`,`k`] >> simp[]) >>
  gvs[ptr_vv_ok_def, read_result_def, return_def] >>
  Cases_on `p.ptr_location` >> gvs[]
  >- (rpt strip_tac >>
      `storage_agree (storage_dead H F (get_storage cx ee F))
        (get_storage cx ee F) (contract_storage u)` by
        gvs[stmt_state_rel_def, state_rel_def, storage_rel_def,
            vyperStorageBackendTheory.get_storage_def, vfmStateTheory.lookup_account_def] >>
      drule accountsRelPropsTheory.storage_agree_storage_dead >> strip_tac >>
      `storage_range_agree (get_storage cx ee F) (contract_storage u) w ty` by
        (irule accountsRelPropsTheory.storage_range_agree_of_live >>
         conj_tac >- (gvs[vv_holds_def, storage_holds_def,
                          accountsRelPropsTheory.storage_range_agree_def] >> metis_tac[]) >>
         qexistsl_tac [`H`,`F`] >> simp[]) >>
      drule storage_range_agree_dead_bytes >> strip_tac >>
      gvs[ghost_inv_at_def, stor_taint_ok_at_def, dead_lo_ok_def,
          sourceUnitExecutionTheory.cx_dead_def, pred_setTheory.SUBSET_DEF] >>
      `storage_dead H F (contract_storage u) (w2n k) b` by
        (qpat_x_assum `!x. x IN tn2.t_stor ==> _` (qspec_then `(k,b)` mp_tac) >>
         Cases_on `u.vs_call_ctx.cc_address = cx.txn.target` >>
         gvs[contract_storage_def, vfmStateTheory.lookup_account_def]) >>
      gvs[contract_storage_def, vfmStateTheory.lookup_account_def, storage_read_live_def] >>
      metis_tac[arithmeticTheory.ADD_COMM]) >>
  rpt strip_tac >>
  `storage_agree (storage_dead H T (get_storage cx ee T))
    (get_storage cx ee T) (contract_transient u)` by
    gvs[stmt_state_rel_def, state_rel_def, transient_rel_def,
        vyperStorageBackendTheory.get_storage_def] >>
  drule accountsRelPropsTheory.storage_agree_storage_dead >> strip_tac >>
  `storage_range_agree (get_storage cx ee T) (contract_transient u) w ty` by
    (irule accountsRelPropsTheory.storage_range_agree_of_live >>
     conj_tac >- (gvs[vv_holds_def, storage_holds_def,
                      accountsRelPropsTheory.storage_range_agree_def] >> metis_tac[]) >>
     qexistsl_tac [`H`,`T`] >> simp[]) >>
  drule storage_range_agree_dead_bytes >> strip_tac >>
  gvs[ghost_inv_at_def, stor_taint_ok_at_def, dead_lo_ok_def,
      sourceUnitExecutionTheory.cx_dead_def, pred_setTheory.SUBSET_DEF] >>
  `storage_dead H T (contract_transient u) (w2n k) b` by
    (qpat_x_assum `!x. x IN tn2.t_trans ==> _` (qspec_then `(k,b)` mp_tac) >>
     Cases_on `u.vs_call_ctx.cc_address = cx.txn.target` >>
     gvs[contract_transient_def]) >>
  gvs[contract_transient_def, storage_read_live_def] >>
  metis_tac[arithmeticTheory.ADD_COMM])
QED
