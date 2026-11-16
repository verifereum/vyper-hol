(* Pointwise declaration runtime, supplied with concrete compiler-entry witnesses. *)
Theory bodyFullAnnAssignOrdinaryRuntime
Ancestors
  bodyFullAnnAssignCompose bodyFullAnnAssignReserve bodyFullMemoryValue
  bodyFullAnnAssignMemoryPost bodyFullPathHistory bodyInvNoDalloca
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  memoryLocalRhsProps exprSimSource stmtSimDeclSource
  compileEnv exprLowering stmtLowering loweringPosts vyperTypeSystem
  vyperContext vyperInterpreter vyperState vyperValue vyperAST
  gasOutcomeFullGuarded gasOutcomeFullCompose bodyFullUnwrap bodyMemoryDefs
  gasStorage vyperStorageTrace vyperStorageFootprint bodyPtrDefs
  stmtSimDefs bodyMemBopRestWordPath fragGasOriginPtr fragGasOrigin fragGasPath
  exprLoweringProps stmtSimProps fragFuelRuntimeBody gasShadowState exprSimUnwrap
  fragExec venomState venomInst list finite_map
Libs monadsyntax

Theorem annassign_copy_runtime_outcome:
  !cx id typ e DF lo d PG tops bindings ctx shadow_ctx func shadow_func
   cenv env env' ret_ty lctx RetQ es st0 sa shadow_sa sf shadow_sf
   s0 G0 tn0 ce tyv ltv r a b c vv op p shadow_r shadow_a shadow_b shadow_c.
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
    ~(has_length_word typ /\ is_empty_value_expr e) /\
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
    well_typed_expr env e /\ assignable_type env.type_defs typ /\
    type_widens_to env.type_defs (expr_type e) typ /\
    id NOTIN FDOM env.var_types /\ env.type_defs = get_tenv cx /\
    supported_expr tops e /\ body_stmt_safe tops (AnnAssign id typ e) /\
    FLOOKUP cenv.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE /\
    body_expr_full_ok cx e /\ expr_body_pre cenv cx env e es /\
    (expr_type e = typ \/ is_bytestring_type typ) /\
    0 < type_memory_bytes cenv (lowered_value_type cenv e) /\
    type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_bytes cenv typ /\
    type_memory_bytes cenv typ < 2 ** 64 /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
    type_memory_bytes cenv typ = type_memory_size tyv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv /\
    declare_local cenv id typ sa = (ce,r) /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv typ)) /\
    emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv typ))] [p] r = ((),a) /\
    compile_expr ce (expr_type e) e a = (vv,b) /\
    unwrap_value ce vv b = (op,c) /\
    lower_value compile_expr ce (expr_type e) e a = (op,c) /\
    compile_assign_value ce (Var p) LocMemory op F (vv_location vv) typ
      (lowered_value_type cenv e) (type_memory_bytes ce typ) c = ((),sf) /\
    local_ptrs_reserved ce r /\ local_ptrs_reserved ce a /\ not_fresh_at a p /\
    cs_extends r a /\ cs_extends a c /\ cs_extends c sf /\
    fn_has_code r a func /\ fn_has_code a c func /\ fn_has_code c sf func /\
    cs_extends a b /\ cs_extends b c /\
    fn_has_code a b func /\ fn_has_code b c func /\
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
    unwrap_value ce vv shadow_b = (op,shadow_c) /\
    gas_shadow_state a shadow_a /\ gas_shadow_state b shadow_b /\
    gas_shadow_state c shadow_c /\
    compile_assign_value ce (Var p) LocMemory op F (vv_location vv) typ
      (lowered_value_type ce e) (type_memory_bytes ce typ) shadow_c = ((),shadow_sf) /\
    fn_has_code shadow_a shadow_b shadow_func /\
    fn_has_code shadow_b shadow_c shadow_func /\
    fn_has_code shadow_c shadow_sf shadow_func ==>
    gas_outcome_full
      (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
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
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        (!x. not_fresh_at sa x ==>
             FLOOKUP G x = FLOOKUP G0 x /\
             op_taint tn (Var x) = op_taint tn0 (Var x)))
      (\H res ee gt r.
        (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
        halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==>
         !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  irule gas_outcome_full_initial_domain >>
  simp[evaluate_storage_trace_frame] >> disch_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==>
     not_fresh_at sa x` by fs[ret_pc_ok_def] >>
  `type_memory_bytes cenv typ < dimword (:256)` by
    fs[wordsTheory.dimword_def] >>
  drule_all (INST_TYPE [beta |-> ``:256``] body_full_declared_alloc_path) >>
  disch_then (qspecl_then [`tn0`,`gas_explicit_sites ctx shadow_ctx`,`PG`,`G0`]
    strip_assume_tac) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      ce cx (expr_type e) e es` by
    (qpat_assum `body_expr_full_ok cx e`
      (mp_tac o CONJUNCT1 o REWRITE_RULE [Once body_expr_full_ok_def]) >>
     disch_then drule_all >> simp[]) >>
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
     disch_then (strip_assume_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
     drule fragGasOriginTheory.gas_origin_path_erase >> simp[]) >>
  `alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next` by
    metis_tac[bodyMemBopRestWordPathTheory.rest_word_marked_allocation_posts] >>
  `sa.cs_next_var <= a.cs_next_var` by
    (qpat_assum `compile_alloc_buffer _ sa = _`
       (mp_tac o MATCH_MP fragFuelRuntimeBodyTheory.compile_alloc_buffer_var) >> simp[]) >>
  `return_buf_frame d ce a u` by
    (irule return_buf_frame_frame >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `ret_pc_ok ce a u` by
    (fs[ret_pc_ok_def] >> metis_tac[]) >>
  `!H. dead_lo_ok H (DF H) lo ce cx` by fs[dead_lo_ok_def] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es`
    by metis_tac[annassign_admissible_rhs] >>
  `lower_value compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_a =
    (op,shadow_c)` by simp[lower_value_def,comp_bind_def] >>
  `cs_extends shadow_a shadow_b /\ cs_extends shadow_b shadow_c` by
    metis_tac[compile_expr_extends,unwrap_value_extends] >>
  `fn_has_code shadow_a shadow_c shadow_func` by
    (qpat_assum `cs_extends shadow_a shadow_b`
       (strip_assume_tac o REWRITE_RULE [cs_extends_def]) >>
     qpat_assum `cs_extends shadow_b shadow_c`
       (strip_assume_tac o REWRITE_RULE [cs_extends_def]) >>
     `emitted_blocks shadow_a shadow_c =
       emitted_blocks shadow_b shadow_c ++ emitted_blocks shadow_a shadow_b` by
       (rename1 `shadow_b.cs_blocks = n12 ++ shadow_a.cs_blocks` >>
        rename1 `shadow_c.cs_blocks = n23 ++ shadow_b.cs_blocks` >>
        `shadow_c.cs_blocks = (n23 ++ n12) ++ shadow_a.cs_blocks`
          by simp[] >>
        metis_tac[emitted_blocks_append]) >>
     qpat_assum `fn_has_code shadow_a shadow_b shadow_func`
       (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
     qpat_assum `fn_has_code shadow_b shadow_c shadow_func`
       (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
     simp[fn_has_code_def] >> metis_tac[MEM_APPEND]) >>
  `!fn inst s. frag_reachable ctx func u fn inst s ==> dalloca_no_wrap inst s` by
    (rpt strip_tac >>
     drule_all contextRawReachableTheory.frag_reachable_members >> strip_tac >>
     qpat_assum `~ctx_has_dalloca ctx`
       (mp_tac o REWRITE_RULE [ptrDisciplineTheory.ctx_has_dalloca_def, EXISTS_MEM]) >>
     simp[unitMemInvTheory.dalloca_no_wrap_def] >> metis_tac[]) >>
  qpat_x_assum `expr_sim_full _ ce cx _ e es`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`a`,`c`,`shadow_a`,`shadow_c`,`op`,`u`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >-
    (simp[] >> (metis_tac[]))) >>
  disch_tac >>
  irule gas_outcome_full_zero_prefix_guarded >>
  simp[evaluate_storage_trace_frame] >>
  qexistsl_tac [`G1`,`u`,`tn1`] >>
  conj_tac >- metis_tac[] >>
  irule annassign_full_outcome >>
  conj_tac >- metis_tac[] >>
  goal_assum (drule_at Any) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `res`
      >- fs[exprSimDefsTheory.expr_exit_INL] >>
      rename1 `expr_exit (INR exc) rr` >> qexists_tac `exc` >>
      qpat_x_assum `expr_exit (INR exc) rr`
        (assume_tac o ONCE_REWRITE_RULE
          [INST_TYPE [alpha |-> ``:value``, beta |-> ``:unit``]
            stmtSimPropsTheory.expr_exit_INR_type]) >>
      simp[stmt_exit_ptr_def] >> fs[exprSimDefsTheory.halt_exit_def]) >>
  reverse conj_tac >- (rpt strip_tac >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  FAIL_TAC "memory_resources"
QED
