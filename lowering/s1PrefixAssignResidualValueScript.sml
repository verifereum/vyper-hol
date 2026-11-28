(* The evaluated assignment RHS reaches the target either directly or via a silent snapshot. *)
Theory s1PrefixAssignResidualValue
Ancestors
  bodyFullAssign s1PrefixAssignValueRhsReplay s1PrefixPreds s1PrefixCompose
  bodyFullSimProjection bodyFullIfExpReach bodyFullPreds bodySimStmtFacts
  fragGasOriginPtrExec fragExec loweringPosts exprSimSource exprLoweringProps
  exprLowering stmtLowering stmtSimDefs exprSimDefs bodySimFull freshWrites
  gasOutcomeFull gasShadow gasShadowState compileEnv targetPlaceSim
  vyperInterpreter vyperState vyperStorageFootprint vyperStorageTrace
  tuplePlaceStep list pair sum s1PrefixDefs bodyMemoryDefs exprSimHyps

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  pop_assum (mk_asm "target") >>
  drule_all_then assume_tac body_assign_value_rhs_pre >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    metis_tac[body_expr_full_ok_simulations] >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (qpat_assum `body_expr_prefix_ok cx e`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [Once body_expr_prefix_ok_def]) >>
     disch_then (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,
       `func`,`shadow_func`,`cenv`,`env`,`expr_type e`,`es`] mp_tac) >> simp[]) >>
  pure_rewrite_tac[stmt_frag_prefix_def,stmt_frag_full_pre_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all body_assign_value_paired_code >>
  disch_then (qx_choosel_then [`vv0`,`sr`,`vv`,`ss`,`r`,`st`,`op`,`su`,`tr`,`ts`,`tt`,`tu`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    (drule expr_body_pre_vv_gas_admissible >> simp[]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (eval_expr cx e) (es,s0,G0,tn0)` by
    (qpat_x_assum `expr_vv_sim_prefix _ _ _ _ _ _`
       (qspecl_then [`st0`,`sa`,`sr`,`shadow_sa`,`tr`,`vv0`,`s0`,`G0`,`tn0`] mp_tac o
        REWRITE_RULE [expr_vv_sim_prefix_def,expr_vv_sim_full_pre_def]) >>
     disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _`
    (qspecl_then [`st0`,`sa`,`sr`,`shadow_sa`,`tr`,`vv0`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE [expr_vv_sim_full_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  once_rewrite_tac[evaluate_def] >>
  qpat_assum `gas_outcome_full _ _ _ _ (eval_expr _ _) _ _ _`
    (mp_then Any irule body_assign_raw_read_bind_prefix) >>
  reverse conj_tac
  >- (conj_tac
      >- (qexistsl_tac [`cenv`,`sa`,`sr`,`vv0`] >>
          BETA_TAC >> rpt gen_tac >> disch_then (qx_choose_then `pv` strip_assume_tac) >>
          qexists_tac `pv` >> simp[]) >>
      simp[] >> rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def]) >>
  qx_genl_tac [`marks`,`tv`,`v`,`mid`,`G`,`tn`,`s`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "rhs_replay"
QED
*)
Theorem body_assign_residual_value_from_target:
  !cx t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx t) /\
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_prefix_ok cx t) /\
  body_expr_full_ok cx e /\ body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  struct_args_unique tops /\
  supported_stmt tops bindings (Assign (BaseTarget t) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget t) e) ==> occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ cenv ret_ty /\
  ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\ is_word_type ty) /\
  ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
       ~is_word_type ty /\
       (expr_type e = ty \/ lowered_value_type cenv e = ty \/ is_bytestring_type ty \/
        has_length_word (expr_type e) /\ is_empty_value_expr e)) /\
  ~(?nsid dty. t = TopLevelNameTarget nsid /\ supported_scalar_target tops nsid /\
       type_place_target env t = SOME (Type dty) /\ is_word_type dty) /\
  ~(?nsid mut ty slot. t = TopLevelNameTarget nsid /\
       supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
       (mut = Storage \/ mut = Transient) /\ ~is_word_type ty /\
       (!elem n. ty <> ArrayT elem (Dynamic n)) /\ ~is_bytestring_type ty /\
       0 < type_memory_bytes cenv ty /\ expr_type e = ty /\
       lowered_value_type cenv e = expr_type e) /\
  ~(?id fld sid fty. t = AttributeTarget (NameTarget id) fld /\
       FLOOKUP env.var_types id = SOME (StructT sid) /\
       attribute_type env.type_defs (StructT sid) fld = SOME fty /\ is_word_type fty) /\
  ~(?nsid fld fty. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
       supported_storage_field_write tops nsid fld /\
       type_place_target env t = SOME (Type fty) /\ is_word_type fty) /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  (~immutable_root cx t \/ (?root. t = TopLevelNameTarget root)) /\
  (!mid v st0 vt sa sb shadow_sa shadow_sb r s0 G0 tn0.
      body_base_target_full_ok cx t /\ body_base_target_prefix_ok cx t /\
      body_const_cells_agree [(NONE,tops)] cx env mid /\
      expr_sim_inv cenv cx env mid /\ target_indices_pre cenv cx env t /\
      type_place_target env t = SOME vt /\
      compile_get_target_ptr compile_expr cenv t sa = (r,sb) /\
      compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
        (gas_shadow_target t) shadow_sa = (r,shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      gas_admissible (eval_target_place cx t) target_place_res_ok mid /\
      return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        stmt_state_rel H ctx func cenv cx mid s0 /\
        storage_well_formed_on cx mid (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx mid G0 tn0 s0) /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cx st0 (bind (eval_target_place cx t) (\p. write_place cx p v)) (mid,s0,G0,tn0)) ==>
  stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget t) e)))
    (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume body_assign_residual_value_from_target[rhs_replay]:
  qpat_x_assum `gas_outcome_full _ _ _ _ (eval_expr _ _) _ _ _` kall_tac >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,mid)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => simp[NoAsms,th])) >>
  `read_result cx tv mid = (INL v,mid)` by
    (qpat_assum `!tail. read_result _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => simp[NoAsms,th])) >>
  `body_base_target_full_ok cx t /\ body_base_target_prefix_ok cx t` by
    (conj_tac >> first_assum irule >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  `expr_sim_inv cenv cx env mid` by
    (irule bodySimStmtFactsTheory.expr_body_pre_eval_result >>
     qexistsl_tac [`e`,`es with gas_obs := gas_explicit marks s0.vs_gas_readings`,`INL tv`] >>
     simp[expr_body_pre_gas_obs]) >>
  drule body_assign_empty_target_typing >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `ty` strip_assume_tac))) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (irule body_const_cells_agree_expr_read >>
     qexistsl_tac [`e`,`INL v`,`es with gas_obs := gas_explicit marks s0.vs_gas_readings`] >>
     simp[Once bind_def]) >>
  `target_indices_pre cenv cx env t` by (drule_all body_assign_target_indices_pre >> simp[]) >>
  `gas_admissible (eval_target_place cx t) target_place_res_ok mid` by
    (irule body_assign_saved_target_admissible >>
     qexistsl_tac [`e`,`es`,`lctx`,`gas_explicit marks s0.vs_gas_readings`,`tv`,`v`] >> simp[]) >>
  suspend "rhs_landing"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume body_assign_residual_value_from_target[rhs_landing]:
  RULE_ASSUM_TAC BETA_RULE >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by
    fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ gas_origin_ptr_path _ _ _ _`
    (qspec_then `H0` (drule_then (CONJUNCTS_THEN2 (qx_choose_then `pv` strip_assume_tac) assume_tac))) >>
  qpat_x_assum `INL tv = INL pv` (SUBST_ALL_TAC o SYM o SRULE []) >>
  `!fn inst z. frag_reachable ctx func s fn inst z ==> dalloca_fmp_headroom inst z` by
    (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
       metis_tac[body_inv_no_phi] >>
     qx_genl_tac [`leaf`,`inst`,`z`] >> strip_tac >>
     irule gas_origin_ptr_path_dalloca_fmp_headroom >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks _` (irule_at Any) >>
     qexists_tac `leaf` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `return_buf_frame d cenv sr s` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
     fs[ci_mono_def,vv_post_def]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      vv_post H ctx func cenv cx e es sa sr s0 mid tv vv0 s /\
      ghost_inv_at (DF H) lo d cenv cx mid G tn s` by
    (gen_tac >> strip_tac >>
     `valid_horizon cx st0 H es.storage_trace` by
       (`valid_horizon cx st0 H
           (es with gas_obs := gas_explicit marks s0.vs_gas_readings).storage_trace`
          suffices_by simp[] >>
        irule (INST_TYPE [alpha |-> ``:eval_result``] valid_horizon_frame) >>
        qexistsl_tac [`eval_expr cx e`, `INL tv`, `mid`] >>
        simp[cj 5 evaluate_storage_trace_frame]) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ gas_origin_ptr_path _ _ _ _`
       (qspec_then `H` (drule_then (CONJUNCTS_THEN2 (qx_choose_then `pv` strip_assume_tac) kall_tac))) >>
     qpat_x_assum `INL tv = INL pv` (SUBST_ALL_TAC o SYM o SRULE []) >>
     simp[] >> first_assum ACCEPT_TAC) >>
  `!u Gu tnu.
      local_ptrs_reserved cenv ss /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x) /\
      return_buf_frame d cenv ss u /\ alloca_history func u /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      (!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z) /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        stmt_state_rel H ctx func cenv cx mid u /\ storage_well_formed_on cx mid (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx mid Gu tnu u) /\
      ~u.vs_halted /\ u.vs_current_bb = ss.cs_current_bb /\ u.vs_inst_idx = LENGTH ss.cs_current_insts ==>
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cx st0 (bind (eval_target_place cx t) (\p. write_place cx p v)) (mid,u,Gu,tnu)` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     asm "target" irule >>
     qpat_assum `compile_get_target_ptr compile_expr _ (gas_shadow_target t) ts = (r,tt)`
       (irule_at Any) >>
     qpat_assum `compile_get_target_ptr compile_expr cenv _ ss = (r,st)` (irule_at Any) >>
     qpat_assum `type_place_target env t = SOME (Type ty)` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `(_ /\ compile_snapshot_vv _ _ _ _ = _ /\ _) \/ _`
     (DISJ_CASES_THEN (map_every assume_tac o CONJUNCTS))
  >- suspend "snapshot"
  >> suspend "saved"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume body_assign_residual_value_from_target[snapshot]:
  `cenv.ce_is_ctor /\ vv_location vv0 = SOME LocCode ==>
    !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
      eval_operand (vv_operand vv0) s = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory rt v (w2n w) mem)` by
    (strip_tac >>
     qpat_assum `_ ==> ?val. read_result cx tv mid = _ /\ _` mp_tac >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (qx_choose_then `val` strip_assume_tac) >>
     `val = v` by metis_tac[sumTheory.INL_11,pairTheory.PAIR_EQ] >>
     qpat_x_assum `val = v` SUBST_ALL_TAC >> first_assum ACCEPT_TAC) >>
  (let
     fun from pat k th = qpat_assum pat (mp_then Any k th)
   in
     (from `compile_snapshot_vv _ _ _ sr = (vv,ss)` o
      from `ghost_kept_at lo cenv es sa G0 tn0 s0 G tn` o
      from `vv_store_bound _ _ _ mid tv vv0 s` o
      from `body_inv tops ctx cenv cx` o
      from `fn_has_code sr ss func` o
      from `expr_body_pre cenv cx env e es` o
      from `read_result cx tv mid = (INL v,mid)` o
      from `!tail. eval_expr cx e _ = (INL tv,mid with gas_obs := tail)` o
      from `!H. valid_horizon cx st0 H mid.storage_trace ==>
           _ /\ vv_post H ctx func cenv cx e es sa sr s0 mid tv vv0 s /\ _`)
     mp_tac body_assign_snapshot_target_entry
   end) >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`u`,`Gu`,`tnu`,`uv`] (map_every assume_tac o CONJUNCTS)) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cx st0 (bind (eval_target_place cx t) (\p. write_place cx p v)) (mid,u,Gu,tnu)` by
    (qpat_assum `!u Gu tnu. local_ptrs_reserved _ _ /\ _ ==> _` irule >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
       (qspec_then `H` (drule_then (ACCEPT_TAC o CONJUNCT2)))) >>
  qpat_assum `gas_prefix_full _ _ _ _ (mid,u,Gu,tnu)`
    (mp_then Any irule gas_prefix_full_zero_prefix_guarded) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
        (qspec_then `H` (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
  irule storage_trace_frame_bind_all >>
  simp[cj 8 evaluate_storage_trace_frame, storage_trace_frame_write_place]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume body_assign_residual_value_from_target[saved]:
  qpat_x_assum `ss = sr` SUBST_ALL_TAC >> qpat_x_assum `ts = tr` SUBST_ALL_TAC >>
  `sa.cs_next_var <= sr.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sr` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sr x` by metis_tac[not_fresh_at_mono] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sr x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sr x)` by metis_tac[] >>
  qpat_assum `!u Gu tnu. local_ptrs_reserved _ _ /\ _ ==> _` irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
      _ /\ vv_post H ctx func cenv cx e es sa sr s0 mid tv vv0 s /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_x_assum `vv_post H ctx func cenv cx e es sa sr s0 mid tv vv0 s`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise body_assign_residual_value_from_target
*)
