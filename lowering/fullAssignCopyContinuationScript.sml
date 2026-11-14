(* The concrete successful continuation of a top-level aggregate store. *)
Theory fullAssignCopyContinuation
Ancestors
  fullAssignCopyStoreEntry fullAssignCopyWrite fullStoreCopyPost
  fullAssignCopyFacts exprSimSource exprSimHypsDefs bodyExprPreFacts
  vyperTypeSystem vyperTyping bodyPtrDefs loweringPosts loweringStateRelDefs
  vyperStorageTrace vyperStorageFootprint exprLoweringProps stmtLoweringMono fragExec
  vyperStoragePlaceRegion compileEnv emitHelperProps stmtSimDefs bodySim bodyMemoryDefs
  vyperStorageBackend

Theorem topcopy_store_continuation:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  expr_body_pre cenv cx env e es /\
  type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) = SOME env' /\
  ~cx.txn.is_static /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  expr_type e = typ /\ lowered_value_type cenv e = expr_type e /\
  ~is_word_type typ /\ ~is_bytestring_type typ /\ ~has_length_word typ /\
  (!elem n. typ <> ArrayT elem (Dynamic n)) /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  0 < type_slot_size tvt /\ 0 < type_memory_size tvt /\
  type_memory_bytes cenv typ = type_memory_size tvt /\
  slot + type_slot_size tvt <= dimword(:256) /\
  (!gs v es1. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
    (INL v,es1) ==> value_has_type tvt v) /\
  stmt_env cenv lctx ret_ty
    (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) sa = (cenv,sb) /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  MEM func ctx.ctx_functions /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~block_is_terminated sa /\ return_buf_frame d cenv sa s0 /\
  alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  compile_expr cenv (expr_type e) e sa = (vv,sV) /\
  unwrap_value cenv vv sV = (op,sm) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
  compile_assign_value cenv (Lit (n2w slot))
    (if tr then LocTransient else LocStorage) op F (vv_location vv)
    typ typ (type_memory_bytes cenv typ) sm = ((),sb) /\
  ee.gas_obs = [] /\ ~t.vs_halted /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL v,ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func cenv cx e es sa sm s0 ee v op t /\
    expr_store_bound cx (expr_type e) v op t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t /\
    ptr_val_ok cx (post_value_type cenv e) v op G1 tn1 t /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G1 t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1) ==>
  ?ef u G2 tn2.
    (!tail. ignore_bind (record_storage_event (StorageRoot tr slot tvt))
      (write_storage_slot cx tr (n2w slot) tvt v)
      (ee with gas_obs := tail) = (INL (),ef with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H ef.storage_trace ==>
      gas_origin_ptr_path
        (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G1,tn1) [] (OK u,G2,tn2) /\
      (?cenv''.
        stmt_lands lctx sb (INL ()) u /\ ~u.vs_halted /\
        (~block_is_terminated sb /\ cenv'' = cenv) /\
        cenv_top_ext cenv cenv'' (ef with gas_obs := []).scopes /\
        stmt_state_rel H ctx func cenv'' cx (ef with gas_obs := []) u /\
        storage_well_formed_on cx (ef with gas_obs := []) (FST H) /\
        return_buf_frame d cenv'' sb u /\ alloca_history func u /\
        s0.vs_alloca_next <= u.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv'' cx (ef with gas_obs := []) G2 tn2 u /\
        (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
          lookup_var x u = SOME w) /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
          FLOOKUP u.vs_allocas aid = SOME b) /\
        (!x. not_fresh_at sa x ==>
          FLOOKUP G2 x = FLOOKUP G0 x /\
          op_taint tn2 (Var x) = op_taint tn0 (Var x))))
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  `value_has_type tvt v` by
    (qpat_x_assum `!gs v es1. _` irule >>
     qexistsl_tac [`ee with gas_obs := []`, `gas_explicit marks s0.vs_gas_readings ++ []`] >>
     qpat_x_assum `!tail. _` (qspec_then `[]` ACCEPT_TAC)) >>
  `well_formed_type_value tvt` by metis_tac[evaluate_type_well_formed] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[cj 2 compile_expr_grows, cj 1 ci_mono_stmt_helpers,
      ci_mono_def, pairTheory.SND] >>
  `fn_has_code sm sb func` by metis_tac[fn_has_code_split] >>
  `expr_post (storage_trace_horizon ee.storage_trace) ctx func cenv cx
     e es sa sm s0 ee v op t /\
   expr_store_bound cx (expr_type e) v op t /\
   ghost_inv_at (DF (storage_trace_horizon ee.storage_trace)) lo d cenv cx ee G1 tn1 t /\
   ptr_val_ok cx (post_value_type cenv e) v op G1 tn1 t /\
   ptr_buf_ok cenv e op G1 t /\
   t.vs_current_bb = sm.cs_current_bb /\
   t.vs_inst_idx = LENGTH sm.cs_current_insts` by
    (drule post_value_type_lowered >> strip_tac >> metis_tac[]) >>
  qpat_x_assum `expr_type e = typ` (SUBST_ALL_TAC o SYM) >>
  drule_all topcopy_assign_store_endpoint >> strip_tac >>
  drule_all topcopy_write_endpoint >>
  disch_then (qspecl_then [`tr`, `slot`] strip_assume_tac) >>
  `expr_sim_inv cenv cx env ee` by
    (`expr_body_pre cenv cx env e
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by simp[] >>
     qpat_assum `!tail. bind (eval_expr _ _) _ _ = _`
       (qspec_then `[]` assume_tac) >>
     drule_all (REWRITE_RULE [ETA_THM] expr_body_pre_eval) >> simp[]) >>
  qexistsl_tac [`ef`, `u`, `Gf`, `tf`] >> conj_tac
  >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 H ee.storage_trace` by metis_tac[] >>
  conj_tac >- metis_tac[] >>
  qexists_tac `cenv` >> suspend "post"
QED

Resume topcopy_store_continuation[post]:
  `expr_post H ctx func cenv cx e es sa sm s0 ee v op t /\
   ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t /\
   alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` by metis_tac[] >>
  `regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
   MEM (tr,n2w slot,tvt) (FST H)` by
    (fs[valid_horizon_def] >>
     qpat_assum `ef = _` SUBST_ALL_TAC >>
     fs[storage_observations_ok_def, storage_trace_regions_def]) >>
  `stmt_state_rel H ctx func cenv cx
    (set_storage cx ee tr (apply_writes (n2w slot) writes (get_storage cx ee tr)))
    (store_copy_normalize t u)` by
    (qpat_x_assum `!H cx env ee rootk region path delta. _` irule >>
     simp[SF CONJ_ss] >> conj_tac >- metis_tac[] >>
     conj_tac >- (qexistsl_tac [`0`, `[]`, `tvt`, `n2w slot`] >>
       simp[storage_subregion_def]) >> fs[expr_post_def]) >>
  `sa.cs_next_var <= sm.cs_next_var` by metis_tac[cj 2 compile_expr_grows] >>
  `stmt_state_rel H ctx func cenv cx (ef with gas_obs := []) u` by
    (qpat_assum `ef = _` SUBST_ALL_TAC >>
     simp[] >> irule store_copy_normalize_state_post >>
     qexistsl_tac [`t`, `sa`] >> conj_tac
     >- (rpt strip_tac >>
         `not_fresh_at sm x` by
           (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
         metis_tac[]) >> simp[]) >>
  suspend "frames"
QED

Resume topcopy_store_continuation[frames]:
  `sm.cs_next_var <= sb.cs_next_var` by
    metis_tac[cj 1 ci_mono_stmt_helpers, ci_mono_def, pairTheory.SND] >>
  `~block_is_terminated sb` by
    (irule compile_assign_storage_endpoint_open >>
     goal_assum (drule_at Any) >> fs[body_inv_def]) >>
  `return_buf_frame d cenv sm t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >>
     fs[expr_post_def]) >>
  qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_post_def] >> strip_tac >>
  qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_kept_at_def] >> strip_tac >>
  drule_all store_copy_kept_resources_post >> strip_tac >>
  `alloca_history func u` by
    (`alloca_inv t` by fs[stmt_state_rel_def] >>
     metis_tac[store_copy_path_history]) >>
  `storage_well_formed_on cx ef (FST H)` by
    (qpat_assum `ef = _` SUBST_ALL_TAC >>
     `write_storage_slot cx tr (n2w slot) tvt v ee =
       (INL (),set_storage cx ee tr
         (apply_writes (n2w slot) writes (get_storage cx ee tr)))` by
       simp[write_storage_slot_eq] >>
     `storage_well_formed_on cx
       (set_storage cx ee tr
         (apply_writes (n2w slot) writes (get_storage cx ee tr))) (FST H)` by
       (irule typed_write_preserves_storage_well_formed_on >>
        conj_tac >- simp[] >>
        qexistsl_tac [`tr`, `n2w slot`, `ee`, `tvt`, `v`] >> simp[]) >>
     Cases_on `tr` >>
     gvs[set_storage_def, get_storage_def, storage_well_formed_on_def]) >>
  `storage_well_formed_on cx (ef with gas_obs := []) (FST H)` by
    (qpat_x_assum `storage_well_formed_on cx ef _` mp_tac >>
     rewrite_tac[storage_well_formed_on_def] >>
     disch_tac >> map_every qx_gen_tac [`b`, `k`, `tv`] >>
     Cases_on `b` >> simp[NoAsms, get_storage_def] >>
     metis_tac[get_storage_def]) >>
  simp[IgnAsm `ef = _`, stmt_lands_def, cenv_top_ext_def] >>
  suspend "ghost"
QED

Resume topcopy_store_continuation[ghost]:
  irule (INST_TYPE [``:'a`` |-> ``:256``] store_copy_joint_frame_post) >>
  conj_tac
  >- (qexists_tac `H` >> simp[] >> suspend "taint") >>
  qexistsl_tac [`G1`, `ee`, `t`, `sa`, `tn1`] >>
  simp[IgnAsm `ef = _`] >>
  conj_tac
  >- fs[ret_pc_ok_def] >>
  rpt strip_tac >>
  `not_fresh_at sm x` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  metis_tac[]
QED

Resume topcopy_store_continuation[taint]:
  FAIL_TAC "live storage taint"
QED

Finalise topcopy_store_continuation
