(* Pointwise joint runtime boundary; compiler witnesses are supplied by Entry. *)
Theory bodyFullAnnAssignEmptyRuntime
Ancestors
  bodyFullAnnAssignReserve bodyFullAnnAssignCompose bodyFullAnnAssignMemoryPost
  bodyFullAnnAssignEmptyCompose bodyFullAnnAssignEmptyStore
  bodyMemBopRestWordPath fragGasOriginPtr fragGasOrigin fragFuelRuntimeBody
  contextRawReachable ptrDiscipline unitMemInv exprSimMemorySource exprSimHyps
  allocLimitsProps allocLimits exprSimUnwrap words bodyPtrDefs vyperTypeInvariants
  bodyMemoryDefs
  bodyFullPreds bodySimFull bodyInvNoDalloca gasOutcomeFullStmts
  gasOutcomeFullCompose gasOutcomeFullGuarded bodyFullPathHistory
  stmtSimDeclSource annAssignPtrEmptySource
  bodySim exprSimHypsDefs gasShadow vyperStorageTrace vyperStorageFootprint
  stmtSimProps exprLoweringProps emitHelperProps loweringSlice
  compileEnv exprLowering stmtLowering loweringPosts vyperTypeSystem
  vyperContext vyperInterpreter vyperState vyperValue vyperAST list finite_map
Libs monadsyntax

Theorem annassign_empty_runtime_outcome:
  !cx id typ e DF lo d PG tops bindings ctx shadow_ctx func shadow_func
   cenv env env' ret_ty lctx RetQ es st0 sa sf shadow_sa shadow_sf s0 G0 tn0 ce
   r a b vv p shadow_r shadow_a shadow_b.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==> body_expr_full_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AnnAssign id typ e) ==> occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx RetQ cenv ret_ty /\
    ~is_word_type typ /\ 0 < type_memory_bytes cenv typ /\
    (lowered_value_type cenv e = typ \/ is_bytestring_type typ \/
     has_length_word typ /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
    has_length_word typ /\ is_empty_value_expr e /\
    stmt_env cenv lctx ret_ty (AnnAssign id typ e) sa = (ce,sf) /\
    stmt_env cenv lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)) shadow_sa =
      (ce,shadow_sf) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sf shadow_sf /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sf func /\ fn_has_code shadow_sa shadow_sf shadow_func /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    ret_pc_ok cenv sa s0 /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at sa x) /\
    ~block_is_terminated sa /\
    gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_no_wrap inst s) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    declare_local cenv id typ sa = (ce,r) /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv typ)) /\
    emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv typ))] [p] r = ((),a) /\
    compile_expr ce (expr_type e) e a = (vv,b) /\
    emit_void MSTORE [Var p; Lit 0w] b = ((),sf) /\
    local_ptrs_reserved ce r /\ local_ptrs_reserved ce a /\ not_fresh_at a p /\
    cs_extends r a /\ cs_extends a b /\ cs_extends b sf /\
    fn_has_code r a func /\ fn_has_code a b func /\ fn_has_code b sf func /\
    MEM (mk_inst r.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes cenv typ))] [p]) (fn_insts func) /\
    compile_alloc_buffer (type_memory_bytes cenv typ) sa =
      (<|buf_operand := Var p; buf_size := type_memory_bytes cenv typ|>,a) /\
    cs_extends sa a /\ fn_has_code sa a func /\
    body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      ce cx (expr_type e) e es /\
    emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv typ))] [p] shadow_r =
      ((),shadow_a) /\
    compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_a = (vv,shadow_b) /\
    gas_shadow_state a shadow_a /\ gas_shadow_state b shadow_b /\
    emit_void MSTORE [Var p; Lit 0w] shadow_b = ((),shadow_sf) /\
    fn_has_code shadow_a shadow_b shadow_func ==>
    gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_stmt cx (AnnAssign id typ e)) (es,s0,G0,tn0)
      (\H res ee G tn t. ?cenv''.
        stmt_lands lctx sf res t /\ ~t.vs_halted /\
        (res = INL () ==> ~block_is_terminated sf /\ cenv'' = ce) /\
        cenv_top_ext cenv cenv'' ee.scopes /\
        stmt_state_rel H ctx func cenv'' cx ee t /\
        storage_well_formed_on cx ee (FST H) /\
        return_buf_frame d cenv'' sf t /\ alloca_history func t /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv'' cx ee G tn t /\
        (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
          lookup_var x t = SOME w) /\
        (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
          FLOOKUP t.vs_allocas aid = SOME entry) /\
        (!x. not_fresh_at sa x ==>
          FLOOKUP G x = FLOOKUP G0 x /\
          op_taint tn (Var x) = op_taint tn0 (Var x)))
      (\H res ee gt out.
        (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt out) /\
        halt_exit H cx ee res out /\
        (ctx_has_dalloca ctx ==>
          !s. (out = Halt s \/ ?ir. out = IntRet ir s) ==> allocas_below_fmp s))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  irule gas_outcome_full_initial_domain >>
  simp[evaluate_storage_trace_frame] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (drule_all_then strip_assume_tac) >>
  `well_typed_expr env e /\ assignable_type env.type_defs typ /\
   type_widens_to env.type_defs (expr_type e) typ /\ id NOTIN FDOM env.var_types` by
    fs[type_stmt_def, AllCaseEqs()] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (Cases_on `FLOOKUP cenv.ce_vars id` >> simp[] >>
     fs[ce_locals_declared_def] >> metis_tac[]) >>
  `lookup_scopes id es.scopes = NONE` by
    (fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     qpat_x_assum `!id entry. lookup_scopes _ _ = _ ==> _`
       (drule_then mp_tac) >> simp[FLOOKUP_DEF]) >>
  drule annassign_admissible_type >> strip_tac >>
  `type_memory_bytes cenv typ < 2 ** 64` by
    fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==>
     not_fresh_at sa x` by fs[ret_pc_ok_def] >>
  `type_memory_bytes cenv typ < dimword (:256)` by
    fs[wordsTheory.dimword_def] >>
  drule_all (INST_TYPE [beta |-> ``:256``] body_full_declared_alloc_path) >>
  disch_then (qspecl_then [`tn0`,`gas_explicit_sites ctx shadow_ctx`,`PG`,`G0`]
    strip_assume_tac) >>
  `ce.ce_return_buf = cenv.ce_return_buf /\
   ce.ce_return_pc = cenv.ce_return_pc /\
   ce.ce_is_ctor = cenv.ce_is_ctor` by
    (drule_all stmtSimPropsTheory.declare_local_ptr >> strip_tac >>
     qpat_x_assum `ce with <| ce_vars := _; ce_var_type := _;
                             ce_dynarray_capacity := _ |> = cenv` mp_tac >>
     simp[compile_env_component_equality]) >>
  `alloca_inv s0` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ s0`
      (mp_tac o REWRITE_RULE [stmt_state_rel_def]) >> simp[]) >>
  `gas_marked_path T ctx func s0 0 (OK u)` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
      (qspec_then `DF (storage_trace_horizon es.storage_trace)` mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule gas_origin_path_erase >> simp[]) >>
  `alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next` by
    metis_tac[rest_word_marked_allocation_posts] >>
  `sa.cs_next_var <= a.cs_next_var` by
    (qpat_assum `compile_alloc_buffer _ sa = _`
       (mp_tac o MATCH_MP compile_alloc_buffer_var) >> simp[]) >>
  `return_buf_frame d ce a u` by
    (irule return_buf_frame_frame >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `ret_pc_ok ce a u` by
    (fs[ret_pc_ok_def] >> metis_tac[]) >>
  `!H. dead_lo_ok H (DF H) lo ce cx` by fs[dead_lo_ok_def] >>
  `!fn inst s. frag_reachable ctx func u fn inst s ==> dalloca_no_wrap inst s` by
    (rpt strip_tac >>
     drule_all frag_reachable_members >> strip_tac >>
     qpat_assum `~ctx_has_dalloca ctx`
       (mp_tac o REWRITE_RULE [ctx_has_dalloca_def, EXISTS_MEM]) >>
     simp[dalloca_no_wrap_def] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es`
    by metis_tac[annassign_admissible_rhs] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim_full _ ce cx _ e es`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`a`,`b`,`shadow_a`,`shadow_b`,`vv`,`u`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> disch_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ rawQ rawR` >>
  irule gas_outcome_full_zero_prefix_guarded >>
  simp[evaluate_storage_trace_frame] >>
  qexistsl_tac [`G1`,`u`,`tn1`] >>
  conj_tac >- simp[] >>
  irule annassign_empty_full_rhs_bind >>
  simp[] >> conj_tac >- (qexists_tac `env` >> simp[]) >>
  qexistsl_tac [`rawQ`,`rawR`] >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> simp[Abbr `rawR`] >> strip_tac >> Cases_on `res`
      >- (qpat_x_assum `expr_exit (INL _) _` mp_tac >>
          simp[exprSimDefsTheory.expr_exit_INL]) >>
      rename1 `expr_exit (INR exc) rr` >> qexists_tac `exc` >>
      qpat_x_assum `expr_exit (INR exc) rr`
        (assume_tac o ONCE_REWRITE_RULE
          [INST_TYPE [alpha |-> ``:eval_result``, beta |-> ``:unit``]
            stmtSimPropsTheory.expr_exit_INR_type]) >>
      simp[stmt_exit_ptr_def] >> fs[exprSimDefsTheory.halt_exit_def]) >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
        (drule_then mp_tac) >> simp[Abbr `rawQ`]) >>
  suspend "normal"
QED

Resume annassign_empty_runtime_outcome[normal]:
  qx_genl_tac [`marks`,`tv`,`mid`,`Gr`,`tr`,`s`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  qunabbrev_tac `rawQ` >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (drule_then (strip_assume_tac o SRULE [])) >>
  `tv = Value (default_value tyv)` by
    (qpat_assum `!tail. eval_expr cx e _ = _` (qspec_then `[]` assume_tac) >>
     drule_all memoryLocalRhsPropsTheory.memory_rhs_empty_eval_destination >> simp[]) >>
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail) =
    (INL (default_value tyv),mid with gas_obs := tail)` by
      simp[bind_def,read_result_def,return_def] >>
  drule_all annassign_continuation_all_tails >> strip_tac >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func ce cx mid s` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [vv_post_def]) >> simp[]) >>
  `lookup_var p s = SOME (n2w b') /\
   FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b',type_memory_bytes cenv typ)` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [vv_post_def]) >> simp[] >> metis_tac[]) >>
  `ptr_covers Gr tr p s (type_memory_bytes cenv typ)` by
    (qpat_assum `ghost_kept_at lo ce es a G1 tn1 u Gr tr`
      (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     qpat_assum `ptr_covers G1 tn1 p u _`
      (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
     qpat_x_assum `lookup_var p u = SOME w` mp_tac >> simp[] >>
     disch_then SUBST_ALL_TAC >> simp[ptr_covers_def]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `b' + type_memory_bytes cenv typ <= s.vs_alloca_next` by
    (qpat_assum `stmt_state_rel _ ctx func ce cx mid s`
      (strip_assume_tac o REWRITE_RULE [stmt_state_rel_def]) >>
     fs[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
  `type_memory_bytes cenv typ = type_memory_size tyv` by
    (irule typedMemoryCopyTheory.typed_copy_memory_size >>
     fs[expr_sim_inv_def] >> metis_tac[]) >>
  `w2n (n2w b' : 256 word) = b'` by simp[] >>
  qpat_assum `emit_void MSTORE [Var p; Lit 0w] b = _`
    (mp_then Any mp_tac annassign_empty_full_store_path) >>
  disch_then (fn th => qpat_assum `lookup_var p s = SOME (n2w b')`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `ptr_covers Gr tr p s _`
    (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`tyv`,`typ`,`lo`,`lctx`,`id`,`func`,
    `gas_explicit_sites ctx shadow_ctx`,`es`,`e`,`cx`,`ctx`,`PG`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf`
    (qx_choose_then `tf` strip_assume_tac))) >>
  `a.cs_next_var <= b.cs_next_var` by
    (qspec_then `a` mp_tac
      (Q.SPECL [`ce`,`expr_type e`,`e`] (cj 1 compile_expr_ci_mono)) >>
     simp[ci_mono_def]) >>
  `local_ptrs_reserved ce b` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `a` >> simp[]) >>
  `not_fresh_at b p` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `a` >> simp[]) >>
  `not_local_ptr ce mid.scopes p` by
    (irule local_ptrs_reserved_not_live >>
     conj_tac >- (qexistsl_tac [`id`,`type_memory_bytes cenv typ`] >> simp[]) >>
     qexists_tac `b` >> simp[]) >>
  `!q. q = p \/ ~not_local_ptr ce mid.scopes q ==> not_fresh_at b q` by
    (rpt gen_tac >> strip_tac >- gvs[] >>
     qpat_x_assum `~not_local_ptr ce mid.scopes q` mp_tac >>
     qpat_assum `local_ptrs_reserved ce b` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[loweringStateRelDefsTheory.not_local_ptr_def,
          loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
  `!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  `!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`Gf`,
    `mid with scopes := (sc |+ (id,<|assignable := T; type := tyv; value := default_value tyv; popped := []|>)) :: rest`,
    `INL ()`,`t`,`tf`] >> simp[] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (drule_then (strip_assume_tac o SRULE [])) >>
  `stmt_state_rel H ctx func ce cx mid s` by
    (qpat_assum `vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [vv_post_def]) >> simp[]) >>
  qpat_assum `!D. gas_origin_ptr_path _ (s,Gr,tr) [] (OK t,Gf,tf)`
    (qspec_then `DF H` (mp_then Any mp_tac
      (INST_TYPE [alpha |-> ``:256``] body_full_annassign_memory_post))) >>
  disch_then (fn th => qpat_assum `typed_copy_state_frame b _ _ s t`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `stmt_state_rel H ctx func ce cx mid s`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `ghost_inv_at (DF H) lo d ce cx mid Gr tr s`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) _)`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `mid.scopes = sc :: rest`
    (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`default_value tyv`,`sf`,
    `mk_inst r.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv typ))] [p]`,`T`] mp_tac) >>
  (impl_tac >- (simp[venomInstTheory.mk_inst_def] >>
    qpat_assum `!q. q = p \/ ~not_local_ptr ce mid.scopes q ==> _` mp_tac >>
    simp[memoryValueFrameTheory.default_value_val_wf,
         vyperTypingTheory.default_value_well_typed])) >>
  strip_tac >>
  conj_tac >- simp[stmt_lands_def] >>
  conj_tac >- (qpat_assum `emit_void MSTORE _ b = ((),sf)`
    (mp_tac o MATCH_MP exprOpenPrimitivesTheory.emit_void_terminated) >>
    simp[venomInstTheory.is_terminator_def]) >>
  conj_tac >- (irule stmtSimDeclComposeTheory.cenv_top_ext_declare_local >>
    simp[] >> qexistsl_tac [`id`,`sa`,`r`,`typ`] >> simp[] >>
    qpat_assum `lookup_scopes id mid.scopes = NONE` mp_tac >>
    qpat_assum `mid.scopes = sc :: rest` (fn th => rewrite_tac[th]) >>
    Cases_on `FLOOKUP sc id` >> simp[lookup_scopes_def]) >>
  simp[] >>
  conj_tac >- (qpat_assum `vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [vv_post_def]) >> strip_tac >>
    irule (iffRL storage_well_formed_on_backends) >>
    simp[] >> qexists_tac `mid` >> simp[]) >>
  `t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas` by
    (qpat_assum `typed_copy_state_frame b _ _ s t`
      (strip_assume_tac o REWRITE_RULE [typedMemoryCopyTheory.typed_copy_state_frame_def]) >>
     qpat_x_assum `(t with <|vs_vars := _; vs_memory := _; vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|>) = s`
       mp_tac >> simp[venomStateTheory.venom_state_component_equality]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at a x /\ not_fresh_at b x` by
       (conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
        qexists_tac `sa` >> simp[]) >>
     qpat_assum `!x. not_fresh_at b x ==> _` (qspec_then `x` mp_tac) >> simp[] >>
     qpat_assum `vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [vv_post_def]) >> strip_tac >>
     first_x_assum irule >> simp[] >>
     qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by simp[] >>
  `sf.cs_next_var = b.cs_next_var` by
    (qpat_assum `emit_void MSTORE _ b = ((),sf)`
      (mp_tac o MATCH_MP emitted_insts_emit_void) >> simp[]) >>
  `sa.cs_next_var <= sf.cs_next_var` by (simp[] >> decide_tac) >>
  conj_tac >- (irule return_buf_frame_frame >>
    qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  conj_tac >- (qpat_assum `!D. gas_origin_ptr_path _ (s,Gr,tr) [] (OK t,Gf,tf)`
    (qspec_then `DF H` (mp_then Any mp_tac body_full_path_alloca_history)) >>
    simp[] >> qpat_assum `stmt_state_rel H ctx func ce cx mid s`
      (mp_tac o REWRITE_RULE [stmt_state_rel_def]) >> simp[]) >>
  simp[] >>
  conj_tac >- (qpat_x_assum `ghost_inv_at (DF H) lo d ce cx (mid with scopes := _) Gf tf t` mp_tac >>
    simp[ghost_inv_at_def] >> strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (rpt strip_tac >> simp[] >>
    qpat_assum `vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [vv_post_def]) >> strip_tac >>
    first_x_assum irule >> simp[] >> first_x_assum irule >> simp[]) >>
  rpt strip_tac >>
  `not_fresh_at a x /\ not_fresh_at b x` by
    (conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `sa` >> simp[]) >>
  qpat_assum `!x. not_fresh_at b x ==> _` (qspec_then `x` mp_tac) >> simp[] >>
  qpat_assum `ghost_kept_at lo ce es a G1 tn1 u Gr tr`
    (mp_tac o REWRITE_RULE [ghost_kept_at_def]) >> strip_tac >>
  qpat_assum `!x. not_fresh_at a x ==> _` (qspec_then `x` mp_tac) >> simp[] >>
  qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >> simp[]
QED

Finalise annassign_empty_runtime_outcome
