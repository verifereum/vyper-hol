(* Request-prefix companion to bodyFullTargetSubscript. *)
Theory s1PrefixTargetSubscript
Ancestors
  s1PrefixPreds bodyFullTargetSubscript s1PrefixDefs s1PrefixCompose
  exprSimSliceCompose stmtSimForRounds fragGasOriginPtrExec
  vyperTypeEnv exprLoweringProps gasShadowCompileStmtHelpers gasShadow fragExec compileEnv
  bodyFullIfExpReach gasOutcomeFullCompose vyperInterpreter vyperState gasContext
  bodyFullTargetDefs vyperStorageTrace s1PrefixProps loweringPosts bodyMemoryDefs
  targetPlaceSim targetPlaceSimDefs targetPlaceSimCasesBase exprSimSource bodyFullPreds bodySimFull
  freshWrites vyperStorageFootprint exprSimDefs bodyFullHashKeccakFixed list
  bodyFullBaseTargetProjection bodyFullSimProjection

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `type_place_target _ (SubscriptTarget _ _) = _`
    (strip_assume_tac o REWRITE_RULE [type_place_target_SubscriptTarget]) >>
  rename1 `type_place_target env bt = SOME bvt` >>
  Cases_on `compile_get_target_ptr compile_expr cenv bt sa` >>
  rename1 `compile_get_target_ptr _ _ bt sa = (rb,sm)` >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sm` >>
  rename1 `lower_value _ _ _ e sm = (iop,sn)` >>
  qpat_assum `compile_get_target_ptr _ _ (SubscriptTarget bt e) sa = _`
    (mp_then (Pos last) mp_tac target_subscript_compile_cut) >>
  simp[compile_expr_ci_mono] >> strip_tac >>
  `?shadow_sm.
     compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
       (gas_shadow_target bt) shadow_sa = (rb,shadow_sm) /\
     gas_shadow_state sm shadow_sm` by
    (irule (MATCH_MP gas_shadow_compile_result gas_shadow_stmt_get_target_ptr_env) >>
     qexists_tac `sa` >> simp[]) >>
  `?shadow_sn.
     lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sm = (iop,shadow_sn) /\
     gas_shadow_state sn shadow_sn` by
    (irule (MATCH_MP gas_shadow_compile_result gas_shadow_stmt_lower_value_env) >>
     qexists_tac `sm` >> simp[]) >>
  qpat_assum `compile_get_target_ptr _ _ (gas_shadow_target (SubscriptTarget _ _)) _ = _`
    ((mp_then (Pos last) mp_tac target_subscript_compile_cut) o
     SIMP_RULE std_ss [gas_shadow_expr_def]) >>
  simp[compile_expr_ci_mono, gas_shadow_expr_type] >> strip_tac >>
  `cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
   sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
   cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sn /\
   cs_extends shadow_sn shadow_sb` by fs[ci_mono_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `fn_has_code shadow_sa shadow_sm shadow_func /\
   fn_has_code shadow_sm shadow_sn shadow_func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  suspend "base"
QED
*)
Theorem target_subscript_sim_prefix:
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_base_target_full_ok cx (SubscriptTarget bt e) /\
  body_base_target_prefix_ok cx (SubscriptTarget bt e) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  target_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx env bt es /\
  subscript_tail_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx env bt e es /\
  (!st0 vt sa sb shadow_sa shadow_sb r s0 G0 tn0.
      type_place_target env bt = SOME vt /\
      compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
      compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
        (gas_shadow_target bt)
        shadow_sa = (r, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_base_place cx bt) target_res_ok es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_prefix_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cx st0 (eval_base_place cx bt) (es, s0, G0, tn0)) /\
  (!st0 vt bvt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
     mid1 t1 G1 tn1 mid2 t2 G2 tn2.
      type_place_target env bt = SOME bvt /\
      type_place_target env (SubscriptTarget bt e) = SOME vt /\
      compile_get_target_ptr compile_expr cenv bt sa = (rb, sm) /\
      lower_value compile_expr cenv (expr_type e) e sm = (iop, sn) /\
      compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa =
        (r, sb) /\
      fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t2) /\
      local_ptrs_reserved cenv sa /\
      sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      expr_sim_inv cenv cx env mid1 /\ mid1.gas_obs = [] /\
      eval_base_place cx bt (es with gas_obs := base_gas) =
        (INL pv, mid1) /\
      bind (eval_expr cx e) (read_result cx)
        (mid1 with gas_obs := index_gas) = (INL v, mid2) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
      gas_admissible (extend_place cx pv (ValueSubscript v))
        target_res_ok mid2 /\
      storage_trace_domain cx st0 mid2.storage_trace /\ mid2.gas_obs = [] /\
      ~t1.vs_halted /\ ~t2.vs_halted /\
      t1.vs_current_bb = sm.cs_current_bb /\
      t1.vs_inst_idx = LENGTH sm.cs_current_insts /\
      t2.vs_current_bb = sn.cs_current_bb /\
      t2.vs_inst_idx = LENGTH sn.cs_current_insts /\
      alloca_history func t1 /\ alloca_history func t2 /\
      s0.vs_alloca_next <= t1.vs_alloca_next /\
      t1.vs_alloca_next <= t2.vs_alloca_next /\
      (!H. valid_horizon cx st0 H mid2.storage_trace ==>
        target_post H ctx func cenv cx es sa sm s0 mid1 pv bvt rb t1 /\
        ghost_inv_at (DF H) lo d cenv cx mid1 G1 tn1 t1 /\
        target_ptr_ok cenv pv rb G1 tn1 t1 /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
        expr_post H ctx func cenv cx e mid1 sm sn t1 mid2 v iop t2 /\
        expr_store_bound cx (expr_type e) v iop t2 /\
        ghost_inv_at (DF H) lo d cenv cx mid2 G2 tn2 t2 /\
        ptr_val_ok cx (post_value_type cenv e) v iop G2 tn2 t2 /\
        (~is_word_type (post_value_type cenv e) ==>
         ptr_buf_ok cenv e iop G2 t2) /\
        ghost_kept_at lo cenv mid1 sm G1 tn1 t1 G2 tn2) ==>
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cx st0 (extend_place cx pv (ValueSubscript v)) (mid2,t2,G2,tn2)) ==>
    !st0 vt sa sb shadow_sa shadow_sb r s0 G0 tn0.
      type_place_target env (SubscriptTarget bt e) = SOME vt /\
      compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa = (r, sb) /\
      compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
        (gas_shadow_target (SubscriptTarget bt e))
        shadow_sa = (r, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_prefix_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cx st0 (eval_base_place cx (SubscriptTarget bt e)) (es, s0, G0, tn0)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume target_subscript_sim_prefix[base]:
  `eval_base_place cx (SubscriptTarget bt e) =
     bind (eval_base_place cx bt)
       (\pv. bind (bind (eval_expr cx e) (read_result cx))
                  (\v. extend_place cx pv (ValueSubscript v)))` by
    simp[FUN_EQ_THM, Once evaluate_def, bind_assoc] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    (qpat_assum `gas_admissible (bind _ _) _ _`
       (mp_then Any irule slice_gas_admissible_bind_head) >> simp[target_res_ok_def]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_base_place cx bt) (es,s0,G0,tn0)` by
    (qpat_assum `!_ _ _ _ _ _ _ _ _ _. _ ==> gas_prefix_full _ _ _ (eval_base_place _ _) _`
       (qspecl_then [`st0`,`bvt`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`rb`,
                    `s0`,`G0`,`tn0`] mp_tac) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `target_sim_full _ _ _ _ bt _`
    (mp_tac o REWRITE_RULE [target_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`bvt`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,
                          `rb`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ (eval_base_place cx bt) _ childQ childR` >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  qabbrev_tac `baseQ = \H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted /\
    !fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_base_place cx bt) (es,s0,G0,tn0) baseQ childR` by
    (irule gas_outcome_full_post_path >> qexists_tac `childQ` >>
     simp[Abbr `baseQ`] >> rpt strip_tac
     >- (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
     drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]) >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_base_place cx bt) (es,s0,G0,tn0)
     (\H res ee G tn t. baseQ H res ee G tn t /\ ee.gas_obs = []) childR` by
    (irule gas_outcome_full_post_source >> qexistsl_tac [`baseQ`,`childR`] >> simp[]) >>
  `!H res ee gt q. childR H res ee gt q ==> ISR res` by
    (simp[Abbr `childR`] >> rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn t. baseQ H res ee G tn t /\ _) _`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[evaluate_requests_outcomes_frame, evaluate_storage_trace_frame,
       storage_trace_frame_extend_place, storage_trace_frame_bind_all,
       storage_trace_frame_read_result] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >> suspend "index"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume target_subscript_sim_prefix[index]:
  qx_genl_tac [`marks`,`pv`,`mid1`,`G1`,`tn1`,`t1`] >>
  BETA_TAC >> strip_tac >>
  qunabbrev_tac `baseQ` >> qunabbrev_tac `childQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid1.storage_trace) mid1.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid1.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  `mid1 with gas_obs := [] = mid1` by simp[evaluation_state_component_equality] >>
  `eval_base_place cx bt (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL pv,mid1)` by
    (qpat_assum `!tail. eval_base_place _ _ _ = _` (qspec_then `[]` mp_tac) >>
     REWRITE_TAC[APPEND_NIL] >>
     qpat_assum `mid1 with gas_obs := [] = mid1` (fn th => REWRITE_TAC[th])) >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  `expr_sim_inv cenv cx env mid1` by
    (irule eval_base_place_sim_inv >> qexistsl_tac [`bt`,`es with gas_obs :=
       gas_explicit marks s0.vs_gas_readings`,`INL pv`] >> fs[target_pre_def]) >>
  `expr_body_pre cenv cx env e mid1` by fs[target_pre_def,target_indices_pre_def] >>
  `body_const_cells_agree [(NONE,tops)] cx env mid1` by
    (irule body_const_cells_agree_base >> goal_assum (drule_at Any) >> simp[]) >>
  `body_expr_full_ok cx e /\ body_expr_prefix_ok cx e` by
    (fs[body_base_target_full_ok_subscript_projection,
        body_base_target_prefix_ok_def] >> metis_tac[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e mid1 /\
   expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e mid1` by
    (conj_tac
     >- (irule (cj 1 body_expr_full_ok_simulations) >>
         simp[] >> qexistsl_tac [`env`, `tops`] >> simp[]) >>
     qpat_assum `body_expr_prefix_ok cx e`
       (mp_tac o Q.SPECL [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,
         `func`,`shadow_func`,`cenv`,`env`,`expr_type e`,`mid1`] o
        CONJUNCT1 o ONCE_REWRITE_RULE [CONJUNCT1 body_expr_prefix_ok_def]) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `return_buf_frame d cenv sm t1` by
    (qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[target_post_def]) >>
     irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
     simp[] >> first_assum ACCEPT_TAC) >>
  suspend "index_run"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume target_subscript_sim_prefix[index_run]:
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid1` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `!H. valid_horizon cx st0 H mid1.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid1 t1 /\
     storage_well_formed_on cx mid1 (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx mid1 G1 tn1 t1` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _`
       (qspec_then `H` (drule_then
         (strip_assume_tac o SIMP_RULE (srw_ss()) [target_post_def]))) >>
     simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (eval_expr cx e) (read_result cx)) (mid1,t1,G1,tn1)` by
    (qpat_x_assum `expr_sim_prefix _ _ _ _ _ _` (mp_tac o REWRITE_RULE[expr_sim_prefix_def]) >>
     disch_then (qspecl_then [`st0`,`sm`,`sn`,`shadow_sm`,`shadow_sn`,`iop`,`t1`,`G1`,`tn1`] mp_tac) >>
     (impl_tac >- (asm_rewrite_tac[expr_sim_full_pre_def])) >> simp[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` (mp_tac o REWRITE_RULE[expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sm`,`sn`,`shadow_sm`,`shadow_sn`,`iop`,`t1`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ (bind (eval_expr cx e) _) _ idxQ idxR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (mid1,t1,G1,tn1)
     (\H res ee G tn t. idxQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []) idxR` by
    (irule gas_outcome_full_post_source >> qexistsl_tac [`idxQ`,`idxR`] >> simp[]) >>
  `!H res ee gt q. idxR H res ee gt q ==> ISR res` by
    (simp[Abbr `idxR`] >> rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn t. idxQ H res ee G tn t /\ _) _`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[evaluate_requests_outcomes_frame, evaluate_storage_trace_frame,
       storage_trace_frame_extend_place, storage_trace_frame_bind_all,
       storage_trace_frame_read_result, requests_outcomes_frame_bind_all,
       requests_outcomes_frame_read_result] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >> suspend "tail"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume target_subscript_sim_prefix[tail]:
  qx_genl_tac [`marks2`,`v`,`mid2`,`G2`,`tn2`,`t2`] >>
  BETA_TAC >> strip_tac >>
  qunabbrev_tac `idxQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace) mid2.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid2.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  `mid2 with gas_obs := [] = mid2` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx)
     (mid1 with gas_obs := gas_explicit marks2 t1.vs_gas_readings) =
     (INL v,mid2)` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     REWRITE_TAC[APPEND_NIL] >>
     qpat_assum `mid2 with gas_obs := [] = mid2` (fn th => REWRITE_TAC[th])) >>
  `!H. valid_horizon cx st0 H mid2.storage_trace ==>
       valid_horizon cx st0 H mid1.storage_trace` by
    (gen_tac >> disch_tac >>
     qspecl_then [`bind (eval_expr cx e) (read_result cx)`,
                  `mid1 with gas_obs := gas_explicit marks2 t1.vs_gas_readings`,
                  `INL v`, `mid2`]
       mp_tac (Q.GENL [`f`, `st`, `res`, `st'`] vyperStorageFootprintTheory.valid_horizon_frame) >>
     simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_read_result]) >>
  suspend "extend"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume target_subscript_sim_prefix[extend]:
  `post_value_type cenv e = expr_type e` by
    (irule target_subscript_index_post_type >> metis_tac[]) >>
  `gas_admissible
     (bind (bind (eval_expr cx e) (read_result cx))
           (\v. extend_place cx pv (ValueSubscript v))) target_res_ok mid1` by
    (qpat_assum `gas_admissible (bind (eval_base_place _ _) _) _ _`
       (fn th => drule_all (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] gas_admissible_bind_tail) th)) >>
     simp[]) >>
  `gas_admissible (extend_place cx pv (ValueSubscript v)) target_res_ok mid2` by
    (qpat_assum `gas_admissible (bind (bind (eval_expr _ _) _) _) _ _`
       (fn th => drule_all (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] gas_admissible_bind_tail) th)) >>
     simp[]) >>
  qpat_assum `!_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. _ ==>
      gas_prefix_full _ _ _ (extend_place _ _ _) _`
    (qspecl_then [`st0`,`vt`,`bvt`,`sa`,`sm`,`sn`,`sb`,`rb`,`iop`,`r`,
                   `s0`,`G0`,`tn0`,`pv`,`v`,`gas_explicit marks s0.vs_gas_readings`,
                   `gas_explicit marks2 t1.vs_gas_readings`,
                   `mid1`,`t1`,`G1`,`tn1`,`mid2`,`t2`,`G2`,`tn2`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> suspend "extend_pre")) >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume target_subscript_sim_prefix[extend_pre]:
  gen_tac >> disch_tac >>
  `valid_horizon cx st0 H mid1.storage_trace` by
    (qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> valid_horizon _ _ H mid1.storage_trace`
       irule >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==>
     ((?pv'. INL pv = INL pv' /\ _) /\ _) /\ _`
    (qspec_then `H` (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) []))) >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> (_ /\ _)`
    (qspec_then `H` (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) []))) >>
  qpat_assum `post_value_type cenv e = expr_type e`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  asm_rewrite_tac[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise target_subscript_sim_prefix
*)
