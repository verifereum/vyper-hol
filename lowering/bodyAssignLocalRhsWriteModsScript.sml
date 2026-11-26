(* Package the local write callbacks at the actual paired compiler cuts. *)
Theory bodyAssignLocalRhsWriteMods
Ancestors
  bodyAssignPlaceRhsDispatchMods bodyAssignLocalReachedTargetEntryMods
  bodyAssignLocalReachedMemoryOutcomeMods bodyQualifiedPlaceTargetEntryMods
  bodyQualifiedPlaceRhsPostMods bodyAssignQualifiedStageJoinMods
  bodyAssignLocalPlaceRoutesMods bodyPlaceWriteSourceMods bodyFullPostsMods
  stmtLoweringMono exprLoweringProps vyperTypeContract vyperTypeCallGraph list
Libs monadsyntax

val rhs_post =
  ``qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
       es sa shadow_sa sr shadow_sr saved s0 G0 tn0``;

val normal =
  ``\(H : (bool # bytes32 # type_value) list # num list) res ef Gf tf t.
      ?ce. stmt_lands lctx sb res t /\ ~t.vs_halted /\
        (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
        cenv_top_ext cenv ce ef.scopes /\ stmt_state_rel H ctx func ce cx ef t /\
        immutable_frame_mods func ce cx ef t /\ storage_well_formed_on cx ef (FST H) /\
        return_buf_frame d ce sb t /\ alloca_history func t /\ return_buf_sep d ce ef t /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at_mods (DF H) lo d ce cx ef Gf tf t /\
        (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
        (!x. not_fresh_at sa x ==>
          FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
        alloca_frame cenv es sa s0 ce ef t /\
        (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
          (!n b len. local_region cenv es.scopes s0 n b len ==> off + sz <= b \/ b + len <= off) /\
          off <= i /\ i < off + sz /\ i IN tf.t_mem ==> i IN tn0.t_mem)``;

Theorem assign_local_paired_rhs_write_supplier_mods:
  target_root bt = NameTarget id /\
  type_place_target env bt = SOME (Type dty) /\
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
  type_widens_to env.type_defs (expr_type e) dty /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  supported_stmt tops bindings (Assign (BaseTarget bt) e) /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env e es /\ body_expr_full_ok_mods mods exps cx e /\
  stmt_exprs_ok cenv (Assign (BaseTarget bt) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget bt) e)) /\
  EVERY (source_body_call_supported cx) (int_calls_stmt (Assign (BaseTarget bt) e)) /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_stmt (Assign (BaseTarget bt) e)) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env)
    (Assign (BaseTarget bt) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (Assign (BaseTarget bt) e) ==> EXISTS (occurs_abi_decode_target target o SND) mods) /\
  exports_ok cx.layouts cx.txn.target mods exps /\
  IS_SOME (check_contract F cx.layouts cx.txn.target mods) /\
  stmt_env cenv lctx ret_ty (Assign (BaseTarget bt) e) sa = (ce,sb) /\
  stmt_env (gas_shadow_env T cenv) lctx ret_ty
    (gas_shadow_stmt (Assign (BaseTarget bt) e)) shadow_sa =
    (gas_shadow_env T ce,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~block_is_terminated sa /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget bt) e)) (stmt_res_ok lctx) es /\
  return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst t. frag_reachable ctx func s0 fn inst t ==> dalloca_fmp_headroom inst t) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ce = cenv /\
  !saved sr shadow_sr dst st shadow_st.
    assign_place_rhs_code_mods cenv bt e sa = (saved,sr) /\
    assign_place_rhs_code_mods (gas_shadow_env T cenv) (gas_shadow_target bt)
      (gas_shadow_expr e) shadow_sa = (saved,shadow_sr) /\
    gas_shadow_state sr shadow_sr /\ gas_shadow_state st shadow_st /\
    compile_get_target_ptr compile_expr cenv bt sr = (dst,st) /\
    compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
      (gas_shadow_target bt) shadow_sr = (dst,shadow_st) /\
    assign_place_store_code_mods cenv e saved dst st = ((),sb) /\
    assign_place_store_code_mods (gas_shadow_env T cenv) (gas_shadow_expr e)
      saved dst shadow_st = ((),shadow_sb) ==>
    ?RhsQ.
      (gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es ==>
       gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
         (\H res mid Gu tu u. ?v. res = INL v /\ RhsQ H v mid Gu tu u)
         (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
           (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))) /\
      (!marks v mid Gu tu u.
        (!tail. bind (eval_expr cx e) (read_result cx)
          (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
          (INL v,mid with gas_obs := tail)) /\
        storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
        (!H. valid_horizon cx st0 H mid.storage_trace ==> RhsQ H v mid Gu tu u) /\
        body_base_target_full_ok_mods mods exps cx bt /\
        gas_admissible (eval_target_place cx bt) target_place_res_ok mid ==>
        write_place_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx env bt mid /\
        write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
          cenv cx bt mid st0 sr st shadow_sr shadow_st dst u Gu tu) /\
      (!ms v mid Gu tu u marks path ee Gz tz z.
        (!tail. bind (eval_expr cx e) (read_result cx)
          (es with gas_obs := gas_explicit ms s0.vs_gas_readings ++ tail) =
          (INL v,mid with gas_obs := tail)) /\
        storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
        (!H. valid_horizon cx st0 H mid.storage_trace ==> RhsQ H v mid Gu tu u) /\
        (!tail. eval_target_place cx bt
          (mid with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail) =
          (INL (MemoryPlace id path),ee with gas_obs := tail)) /\
        storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
        dst = (FST dst,SOME LocMemory,SOME (ValPT dty)) /\
        (?entry w. lookup_scopes id ee.scopes = SOME entry /\
          evaluate_subscripts entry.type entry.value path = INL w) /\
        (!H. valid_horizon cx st0 H ee.storage_trace ==>
          write_target_post_mods H (DF H) lo d ctx func cenv cx bt mid sr st u
            ee (PlaceR (MemoryPlace id path)) (Type dty) dst Gu tu Gz tz z) /\
        (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) z) /\
        ~block_is_terminated st ==>
        gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          cenv.ce_modules cx st0 (write_place cx (MemoryPlace id path) v) (ee,z,Gz,tz)
          ^normal
          (\H res ee gt r.
            (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
            halt_exit H cx ee res r /\
            (ctx_has_dalloca ctx ==> !s.
              (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))) /\
      (!H v mid Gu tu u. RhsQ H v mid Gu tu u ==>
        u.vs_current_bb = sr.cs_current_bb /\ u.vs_inst_idx = LENGTH sr.cs_current_insts) /\
      fn_has_code sa sr func /\ fn_has_code sr st func /\ cs_extends sr st
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac >- (drule_all_then (ACCEPT_TAC o CONJUNCT1) assign_place_paired_code_mods) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb saved sr st
    shadow_sr shadow_st dst` by simp[qualified_assign_code_mods_def] >>
  qexists `^rhs_post` >> BETA_TAC >>
  conj_tac
  >- (disch_tac >> irule (REWRITE_RULE [GSYM AND_IMP_INTRO] assign_place_rhs_dispatch_mods) >>
      qhdtm_assum `qualified_assign_code_mods` (irule_at Any) >>
      qhdtm_assum `contract_inv` (irule_at Any) >>
      qhdtm_assum `module_body_inv` (irule_at Any) >>
      qpat_assum `gas_shadow_function _ _` (irule_at Any) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "target" >>
  conj_tac >- suspend "write" >>
  conj_tac
  >- (rpt gen_tac >> rewrite_tac[qualified_place_rhs_post_mods_def] >>
      disch_then (map_every assume_tac o CONJUNCTS) >> simp[]) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) qualified_place_code_intervals_mods >>
  simp[] >>
  qspecl_then [`bt`,`cenv`,`sr`] mp_tac ci_mono_compile_get_target_ptr >>
  simp[ci_mono_def]
QED

Resume assign_local_paired_rhs_write_supplier_mods[target]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `qualified_assign_rhs_reached_mods cx st0 e es s0 ^rhs_post marks v mid Gu tu u` by
    simp[qualified_assign_rhs_reached_mods_def] >>
  irule assign_local_reached_target_entry_mods >>
  qhdtm_assum `qualified_assign_rhs_reached_mods` (irule_at Any) >>
  qhdtm_assum `qualified_assign_code_mods` (irule_at Any) >>
  qpat_assum `supported_stmt _ _ (Assign _ _)` (irule_at Any) >>
  qhdtm_assum `module_body_inv` (irule_at Any) >>
  qhdtm_assum `contract_inv` (irule_at Any) >>
  qpat_assum `target_root bt = NameTarget id` (irule_at Any) >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
QED

Resume assign_local_paired_rhs_write_supplier_mods[write]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `qualified_assign_rhs_reached_mods cx st0 e es s0 ^rhs_post ms v mid Gu tu u` by
    simp[qualified_assign_rhs_reached_mods_def] >>
  `qualified_assign_target_reached_mods (DF,lo,d,ctx,func) cenv cx st0 bt dty
    mid sr st dst u Gu tu marks (MemoryPlace id path) ee Gz tz z` by
    simp[qualified_assign_target_reached_mods_def] >>
  `!i se. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env se ==>
          expr_body_pre_mods mods cenv cx env i se` by
    (match_mp_tac (GEN_ALL place_write_index_pre_mods) >>
     qpat_assum `supported_stmt _ _ (Assign _ _)` (irule_at Any) >>
     qhdtm_assum `contract_inv` (irule_at Any) >> simp[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `EVERY (source_body_call_supported cx) (int_calls_target bt)` by
    fs[int_calls_stmt_def,int_calls_atarget_def,EVERY_APPEND] >>
  `EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_target bt)` by
    fs[int_calls_stmt_def,int_calls_atarget_def,EVERY_APPEND] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H)` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qpat_x_assum `?entry w. lookup_scopes _ _ = _ /\ _`
    (qx_choose_then `entry` (qx_choose_then `old` strip_assume_tac)) >>
  irule assign_local_reached_memory_outcome_mods >>
  qhdtm_assum `qualified_assign_rhs_reached_mods` (irule_at Any) >>
  qhdtm_assum `qualified_assign_target_reached_mods` (irule_at Any) >>
  qhdtm_assum `qualified_assign_code_mods` (irule_at Any) >>
  qhdtm_assum `module_body_inv` (irule_at Any) >>
  qhdtm_assum `contract_inv` (irule_at Any) >>
  qpat_assum `fn_has_code shadow_sa shadow_sb shadow_func` (irule_at Any) >>
  qpat_assum `type_stmt env ret_ty _ = SOME env'` (irule_at Any) >>
  qpat_assum `lookup_scopes id ee.scopes = SOME entry` (irule_at Any) >>
  qpat_assum `evaluate_subscripts _ _ path = INL old` (irule_at Any) >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
QED

Finalise assign_local_paired_rhs_write_supplier_mods
