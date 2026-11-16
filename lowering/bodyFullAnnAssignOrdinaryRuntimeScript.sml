(* Pointwise declaration runtime, supplied with concrete compiler-entry witnesses. *)
Theory bodyFullAnnAssignOrdinaryRuntime
Ancestors valueTypingMemoryProps[qualified,ignore_grammar]
  immutableDeployAssignRanges[qualified,ignore_grammar]
  typedCopyCompatibility[qualified,ignore_grammar]
  abiDecodePtrBytesRuntimeFrame[qualified,ignore_grammar]
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
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[exprSimMemorySourceTheory.forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim_full _ ce cx _ e es`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`a`,`b`,`shadow_a`,`shadow_b`,`vv`,`u`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> disch_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ rawQ rawR` >>
  `type_memory_bytes ce = type_memory_bytes cenv /\
   (!e. lowered_value_type ce e = lowered_value_type cenv e)` by
    (drule_all stmtSimPropsTheory.declare_local_ptr >> strip_tac >>
     `ce.ce_struct_fields = cenv.ce_struct_fields /\
      ce.ce_func_return_type = cenv.ce_func_return_type` by
       (qpat_x_assum `ce with <| ce_vars := _; ce_var_type := _;
                               ce_dynarray_capacity := _ |> = cenv` mp_tac >>
        simp[compile_env_component_equality]) >>
     metis_tac[type_memory_bytes_frame,allocLimitsPropsTheory.lowered_value_type_frame]) >>
  `post_value_type ce e = expr_type e` by
    metis_tac[post_value_type_lowered,post_value_type_bytestring] >>
  `?rty. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty` by
    (drule exprSimHypsTheory.expr_body_pre_type_evaluates >>
     simp[optionTheory.IS_SOME_EXISTS]) >>
  `!rt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        ~is_word_type (post_value_type ce e) ==>
        type_memory_bytes ce (post_value_type ce e) = type_memory_size rt /\
        type_memory_size rt < 2**64` by
    metis_tac[aggregateEvaluatedLayoutTheory.body_post_type_allocation_bound] >>
  qpat_assum `compile_expr ce (expr_type e) e a = _`
    (strip_assume_tac o MATCH_MP exprSimUnwrapTheory.compile_expr_extends) >>
  `local_ptrs_reserved ce b` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `a` >> simp[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at b x` by
    metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var] >>
  qabbrev_tac `rhsQ = \H (res:value + exception) ee G tn t. ?v.
    res = INL v /\ expr_post H ctx func ce cx e es a c u ee v op t /\
    expr_store_bound cx (post_value_type ce e) v op t /\
    t.vs_current_bb = c.cs_current_bb /\ t.vs_inst_idx = LENGTH c.cs_current_insts /\
    alloca_history func t /\ u.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d ce cx ee G tn t /\
    ptr_val_ok cx (post_value_type ce e) v op G tn t /\
    (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G t) /\
    ghost_kept_at lo ce es a G1 tn1 u G tn /\
    (~is_word_type (post_value_type ce e) ==>
      !rt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
             eval_operand op t = SOME w ==>
             type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= t.vs_alloca_next) /\
    ?raw tv rawG rawtn rawt.
      rawQ H (INL tv) raw rawG rawtn rawt /\ raw.gas_obs = [] /\
      read_result cx tv raw = (INL v,raw) /\ ee = raw /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (rawt,rawG,rawtn) [] (OK t,G,tn) /\
      (~is_word_type (post_value_type ce e) ==>
       vv_at ce cx (post_value_type ce e) a c raw tv
         (LocatedValue (post_value_type ce e) (mk_ptr op LocMemory)) t) /\
      (!x. not_fresh_at b x ==> lookup_var x t = lookup_var x rawt /\
        FLOOKUP G x = FLOOKUP rawG x /\ op_taint tn (Var x) = op_taint rawtn (Var x)) /\
      wb_frame ce raw raw b rawt t /\ ghost_kept_at lo ce raw b rawG rawtn rawt G tn` >>
  qabbrev_tac `rhsR = \(H:(bool # 256 word # type_value) list # num list)
    (res:value + exception) ee (gt:(string |-> num # num) # taint) r.
    expr_exit res r /\ halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx))
    (es,u,G1,tn1) rhsQ rhsR` by
    (irule gas_outcome_full_bind_all >> rpt conj_tac
     >~ [`storage_trace_frame (eval_expr _ _)`]
     >- simp[evaluate_storage_trace_frame]
     >~ [`!v. storage_trace_frame (read_result cx v)`]
     >- simp[storage_trace_frame_read_result]
     >~ [`gas_marked_exec _ _ _ _ _ _ _`]
     >- (rpt strip_tac >> drule gasExemptCertTheory.gas_exempt_cert_bind_result >>
         simp[] >> disch_then irule >> simp[])
     >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
     >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_result >>
         first_assum ACCEPT_TAC) >>
     qexists_tac `\H res ee G tn t. rawQ H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted` >>
     reverse conj_tac
     >- (irule gas_outcome_full_post_source >>
         first_assum (irule_at Any) >> conj_tac
         >- simp[] >>
         simp[Abbr `rawR`,Abbr `rhsR`] >> rpt gen_tac >> strip_tac >>
         Cases_on `res`
         >- (qpat_x_assum `expr_exit (INL _) _` mp_tac >>
             simp[exprSimDefsTheory.expr_exit_INL]) >>
         rename1 `expr_exit (INR exc) rr` >> qexists_tac `exc` >> simp[] >>
         conj_tac
         >- (qpat_x_assum `expr_exit (INR exc) rr`
               (mp_tac o ONCE_REWRITE_RULE
                 [INST_TYPE [alpha |-> ``:eval_result``, beta |-> ``:value``]
                   stmtSimPropsTheory.expr_exit_INR_type]) >> simp[]) >>
         qpat_x_assum `halt_exit H cx ee (INR exc) rr` mp_tac >>
         simp[exprSimDefsTheory.halt_exit_def]) >>
     suspend "read") >>
  qpat_x_assum `gas_outcome_full _ _ _ _ (eval_expr cx e) _ _ _` kall_tac >>
  qunabbrev_tac `rhsQ` >> qunabbrev_tac `rhsR` >>
  irule gas_outcome_full_zero_prefix_guarded >>
  simp[evaluate_storage_trace_frame] >>
  qexistsl_tac [`G1`,`u`,`tn1`] >>
  conj_tac >- simp[] >>
  irule annassign_full_outcome >>
  conj_tac >- (qexists_tac `lctx` >> first_assum ACCEPT_TAC) >>
  goal_assum (drule_at Any) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `res`
      >- (qpat_x_assum `expr_exit (INL _) _` mp_tac >>
          simp[exprSimDefsTheory.expr_exit_INL]) >>
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
  `value_runtime_typed env (lowered_value_type ce e) v /\
   value_runtime_typed env typ v` by
    (qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
       (qspec_then `[]` assume_tac) >>
     `ce.ce_func_return_type = build_func_return_type tops /\
      supported_program tops /\ get_module_code cx NONE = SOME tops` by
       fs[body_inv_def] >>
     conj_tac
     >- (irule memory_rhs_read_lowered_typed >>
         qexistsl_tac [`cx`,`es with gas_obs := gas_explicit marks u.vs_gas_readings ++ []`,
           `mid with gas_obs := []`,`tops`] >>
         fs[expr_body_pre_gas_obs,SF ETA_ss]) >>
     irule memory_rhs_read_destination_typed >>
     qexistsl_tac [`ce`,`cx`,`e`,
       `es with gas_obs := gas_explicit marks u.vs_gas_readings ++ []`,
       `mid with gas_obs := []`] >>
     fs[expr_body_pre_gas_obs,SF ETA_ss]) >>
  `value_has_type ltv v` by
    (drule_all (Q.INST [`ty` |-> `lowered_value_type ce e`]
       (SPEC_ALL memory_rhs_runtime_layout)) >>
     strip_tac >>
     qpat_x_assum `evaluate_type _ (lowered_value_type ce e) = _` mp_tac >>
     asm_rewrite_tac[] >> simp[] >> strip_tac >> asm_rewrite_tac[]) >>
  `value_has_type tyv v` by
    (drule_all (Q.INST [`ty` |-> `typ`]
       (SPEC_ALL memory_rhs_runtime_layout)) >>
     strip_tac >>
     qpat_x_assum `evaluate_type _ typ = _` mp_tac >>
     asm_rewrite_tac[] >> simp[] >> strip_tac >> asm_rewrite_tac[]) >>
  suspend "memory_resources"
QED

Resume annassign_copy_runtime_outcome[read]:
  qx_genl_tac [`marks`,`res`,`ee`,`rawG`,`rawtn`,`rawt`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qunabbrev_tac `rawQ` >> disch_then (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [listTheory.APPEND_NIL])) >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v` by
    (rpt strip_tac >>
     `bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := gas_explicit marks u.vs_gas_readings) = (INL v,ee)` by
       simp[bind_def] >>
     `value_runtime_typed env (post_value_type ce e) v` by
       (irule exprSimHypsTheory.memory_rhs_read_post_typed >>
        qexistsl_tac [`cx`,`es with gas_obs := gas_explicit marks u.vs_gas_readings`,`ee`] >>
        simp[expr_body_pre_gas_obs,SF ETA_ss]) >>
     drule_all (Q.INST [`ty` |-> `post_value_type ce e`]
       (SPEC_ALL memory_rhs_runtime_layout)) >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post H ctx func ce cx e es a b u ee tv vv rawt /\
      ghost_inv_at (DF H) lo d ce cx ee rawG rawtn rawt` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  mp_tac (Q.INST [`cenv` |-> `ce`, `ty` |-> `expr_type e`,
    `sa` |-> `a`, `sm` |-> `b`, `sb` |-> `b`, `sc` |-> `c`,
    `s0` |-> `u`, `s` |-> `rawt`, `G` |-> `rawG`, `tn` |-> `rawtn`,
    `Gi` |-> `G1`, `ti` |-> `tn1`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (SPEC_ALL unwrap_value_origin_ptr)) >>
  (impl_tac >- simp[]) >>
  strip_tac >> simp[] >>
  irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`G'`,`ee`,`INL v`,`z`,`tn'`] >>
  conj_tac
  >- (drule exprSimMemorySourceTheory.read_result_gas_obs >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _ /\ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `post_value_type ce e = expr_type e` SUBST_ALL_TAC >>
  `0 < type_memory_size ltv` by metis_tac[] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
    _ /\ ee.gas_obs = [] /\ ~rawt.vs_halted`
    (drule_then (strip_assume_tac o BETA_RULE)) >>
  qpat_x_assum `INL tv = INL _` (SUBST_ALL_TAC o SYM o REWRITE_RULE [sumTheory.INL_11]) >>
  simp[Abbr `rhsQ`] >>
  conj_tac
  >- (qpat_x_assum `~is_word_type (expr_type e) ==> !rt w. _` mp_tac >> simp[]) >>
  qexistsl_tac [`tv`,`rawG`,`rawtn`,`rawt`] >>
  simp[] >> conj_tac
  >- (qpat_x_assum `!e. lowered_value_type ce e = _`
        (fn th => pure_rewrite_tac [GSYM th]) >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==> _` mp_tac >>
  qpat_x_assum `ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==> _` kall_tac >>
  simp[]
QED

Resume annassign_copy_runtime_outcome[memory_resources]:
  `~is_word_type (expr_type e)` by
    (Cases_on `expr_type e = typ` >- fs[] >>
     `is_bytestring_type typ` by metis_tac[] >>
     `has_length_word typ` by
       (qpat_x_assum `is_bytestring_type typ` mp_tac >>
        Cases_on `typ` >> simp[is_bytestring_type_def,has_length_word_def]) >>
     drule_all type_widens_to_has_length_word_source >>
     Cases_on `expr_type e` >>
     simp[NoAsms,has_length_word_def,is_bytestring_type_def,is_word_type_def] >>
     rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
     simp[NoAsms,is_bytestring_type_def,is_word_type_def] >>
     rename1 `is_bytestring_type (BaseT (BytesT bd))` >> Cases_on `bd` >>
     simp[NoAsms,is_bytestring_type_def,is_word_type_def]) >>
  `expr_val_rel cx (expr_type e) v op t /\
   expr_val_at ce cx (expr_type e) a c mid v op t` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [expr_post_def]) >> simp[]) >>
  `?sw. eval_operand op t = SOME sw` by fs[expr_val_rel_def] >>
  `ptr_buf_ok ce e op G1' t` by metis_tac[] >>
  `?xs. op = Var xs` by
    (qpat_assum `ptr_buf_ok ce e op G1' t`
      (mp_tac o REWRITE_RULE [ptr_buf_ok_def]) >>
     disch_then (qspec_then `sw` mp_tac) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `op = Var xs` SUBST_ALL_TAC >>
  `lookup_var xs t = SOME sw` by fs[eval_operand_def] >>
  qpat_x_assum `rawQ _ (INL tv) mid rawG rawtn rawt` mp_tac >>
  qunabbrev_tac `rawQ` >> disch_then (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `post_value_type ce e = expr_type e` SUBST_ALL_TAC >>
  `!mem. mem_agree_outside tn1'.t_mem t.vs_memory mem ==>
     val_in_memory rty v (w2n sw) mem` by
    (qpat_assum `ptr_val_ok cx (expr_type e) v _ G1' tn1' t`
      (mp_tac o REWRITE_RULE [ptr_val_ok_def,ptr_mem_ok_def]) >>
     simp[] >> strip_tac >>
     qpat_x_assum `!tv. evaluate_type _ _ = SOME tv ==> _`
       (qspec_then `rty` mp_tac) >> simp[]) >>
  `!mem. mem_agree_outside tn1'.t_mem t.vs_memory mem ==>
     val_in_memory ltv v (w2n sw) mem` by
    (rpt strip_tac >> Cases_on `lowered_value_type cenv e = expr_type e`
     >- (`rty = ltv` by
           (qpat_x_assum `evaluate_type _ (lowered_value_type cenv e) = SOME ltv` mp_tac >>
            simp[]) >>
         qpat_x_assum `rty = ltv` SUBST_ALL_TAC >>
         qpat_x_assum `!mem. mem_agree_outside tn1'.t_mem t.vs_memory mem ==> val_in_memory ltv v (w2n sw) mem` irule >>
         first_assum ACCEPT_TAC) >>
     irule valueCopyBytesTheory.bytestring_val_in_memory_transfer >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`expr_type e`,`lowered_value_type cenv e`,`get_tenv cx`,`rty`] >>
     simp[] >>
     (metis_tac[])) >>
  `ptr_covers G1' tn1' xs t (type_memory_size ltv)` by
    (simp[ptr_covers_def] >>
     qpat_assum `ptr_val_ok cx (expr_type e) v _ G1' tn1' t`
       (strip_assume_tac o REWRITE_RULE [ptr_val_ok_def]) >>
     qpat_assum `ptr_buf_ok ce e (Var xs) G1' t`
       (mp_tac o REWRITE_RULE [ptr_buf_ok_def]) >>
     disch_then (qspec_then `sw` mp_tac) >> simp[]) >>
  `w2n sw + type_memory_size ltv <= t.vs_alloca_next` by
    (qpat_x_assum `~is_word_type (expr_type e) ==> !w. _` mp_tac >>
     simp[] >> disch_then (qspec_then `sw` mp_tac) >> simp[]) >>
  Cases_on `vv_location vv = SOME LocMemory`
  >- suspend "staged_resources" >>
  suspend "direct_resources"
QED

Resume annassign_copy_runtime_outcome[staged_resources]:
  qpat_x_assum `vv_location vv = SOME LocMemory` SUBST_ALL_TAC >>
  qpat_assum `compile_assign_value _ _ LocMemory _ F _ _ _ _ c = ((),sf)`
    (mp_then Any mp_tac annassignRelayoutCodeTheory.assign_memory_relayout_code) >>
  disch_then (qspec_then `func` mp_tac) >> simp[] >> strip_tac >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func ce cx mid t` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_post_def]) >> simp[]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ mid _ _ t`
       (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >> simp[]) >>
  `t.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ mid t`
       (strip_assume_tac o REWRITE_RULE [stmt_state_rel_def]) >>
     drule exprLoweringPropsTheory.alloca_room_next_lt >> simp[]) >>
  `w2n sw + type_memory_size ltv < dimword (:256)` by decide_tac >>
  suspend "staged_source_at"
QED

Resume annassign_copy_runtime_outcome[staged_source_at]:
  `post_value_type ce e = expr_type e` by
    (Cases_on `lowered_value_type cenv e = expr_type e`
     >- (irule post_value_type_lowered >> simp[]) >>
     `is_bytestring_type (expr_type e)` by fs[] >> simp[]) >>
  `expr_val_at ce cx (lowered_value_type ce e) a c mid v (Var xs) t` by
    (irule abiEncodeArgsSimTheory.abi_args_at_lowered_transport >>
     conj_tac
     >- (strip_tac >> qexists_tac `ltv` >> simp[] >>
         (simp[valueTypingMemoryPropsTheory.value_has_type_memory_wf])) >>
     conj_tac
     >- (qexistsl_tac [`env`,`es`] >> simp[]) >>
     simp[]) >>
  `~is_word_type (lowered_value_type ce e)` by
    (Cases_on `lowered_value_type cenv e = expr_type e` >- simp[] >>
     `is_bytestring_type (lowered_value_type cenv e)` by fs[] >>
     simp[] >>
     qpat_x_assum `is_bytestring_type (lowered_value_type cenv e)` mp_tac >>
     Cases_on `lowered_value_type cenv e` >>
     simp[NoAsms,is_bytestring_type_def,is_word_type_def] >>
     rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
     simp[NoAsms,is_bytestring_type_def,is_word_type_def] >>
     rename1 `is_bytestring_type (BaseT (BytesT bd))` >> Cases_on `bd` >>
     simp[NoAsms,is_bytestring_type_def,is_word_type_def]) >>
  `val_wf ltv v` by simp[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `local_ptrs_reserved ce c` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `a` >>
     qspec_then `a` mp_tac
       (Q.SPECL [`ce`,`expr_type e`,`e`] ci_mono_lower_value_compile_expr) >>
     simp[ci_mono_def]) >>
  `not_fresh_at c xs` by
    (qpat_assum `lower_value compile_expr ce (expr_type e) e a = _`
      (mp_then Any mp_tac exprOperandVarTheory.compile_lower_value_var) >> simp[]) >>
  `!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at c x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `a` >>
     qspec_then `a` mp_tac
       (Q.SPECL [`ce`,`expr_type e`,`e`] ci_mono_lower_value_compile_expr) >>
     simp[ci_mono_def] >> strip_tac >>
     qpat_x_assum `return_buf_frame d ce a u` mp_tac >>
     Cases_on `d`
     >- simp[return_buf_frame_def] >>
     rename1 `return_buf_frame (SOME db) ce a u` >>
     PairCases_on `db` >> simp[return_buf_frame_def] >>
     strip_tac >> fs[]) >>
  `!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at c x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `a` >>
     qspec_then `a` mp_tac
       (Q.SPECL [`ce`,`expr_type e`,`e`] ci_mono_lower_value_compile_expr) >>
     simp[ci_mono_def] >> strip_tac >>
     qpat_x_assum `ret_pc_ok ce a u` mp_tac >>
     simp[NoAsms,ret_pc_ok_def] >> disch_then (qspecl_then [`x`,`cap`] mp_tac) >>
     simp[]) >>
  `type_memory_size ltv < dimword (:256)` by decide_tac >>
  `~t.vs_halted` by
    (qpat_assum `gas_origin_ptr_path _ (rawt,rawG,rawtn) [] (OK t,G1',tn1')`
       (mp_then Any mp_tac fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec) >>
     simp[exit_result_def]) >>
  qpat_assum `compile_alloc_buffer (type_memory_size ltv) c = _`
    (mp_then Any (fn th =>
      qpat_assum `expr_val_at ce cx (lowered_value_type ce e) a c mid v (Var xs) t`
        (mp_then Any (fn th =>
          qpat_assum `stmt_state_rel _ ctx func ce cx mid t`
            (mp_then Any (fn th =>
              qpat_assum `ptr_covers G1' tn1' xs t (type_memory_size ltv)`
                (mp_then Any (fn th =>
                  qpat_assum `compile_copy_memory _ (Var xs) (type_memory_size ltv) sm = ((),sc)`
                    (mp_then Any (fn th =>
                      qpat_assum `lookup_var xs t = SOME sw`
                        (mp_then Any (qspecl_then
                          [`ltv`,`lo`,`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac) th)) th)) th)) th)) th))
      (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
        bodyFullMemoryStageTheory.body_full_memory_stage_path)) >>
  (impl_tac >- simp[]) >>
  strip_tac >> suspend "staged_assembly"
QED

Resume annassign_copy_runtime_outcome[direct_resources]:
  `compile_store_memory ce (Var xs) (Var p) typ
     (lowered_value_type cenv e) c = ((),sf)` by
    (qpat_x_assum `compile_assign_value _ _ LocMemory _ F _ _ _ _ c = _` mp_tac >>
     simp[compile_assign_value_def]) >>
  `not_fresh_at c xs` by
    (qpat_assum `lower_value compile_expr ce (expr_type e) e a = _`
      (mp_then Any mp_tac exprOperandVarTheory.compile_lower_value_var) >> simp[]) >>
  `not_fresh_at c p` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `a` >>
     qspec_then `a` mp_tac
       (Q.SPECL [`ce`,`expr_type e`,`e`] ci_mono_lower_value_compile_expr) >>
     simp[ci_mono_def]) >>
  `lookup_var p t = SOME (n2w b')` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [expr_post_def]) >> simp[] >> metis_tac[]) >>
  `ptr_covers G1' tn1' p t (type_memory_bytes cenv typ)` by
    (qpat_assum `ghost_kept_at lo ce es a G1 tn1 u G1' tn1'`
       (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     qpat_assum `ptr_covers G1 tn1 p u _`
       (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
     qpat_x_assum `lookup_var p u = SOME w` mp_tac >> simp[] >>
     disch_then SUBST_ALL_TAC >> simp[ptr_covers_def]) >>
  `b' + type_memory_bytes cenv typ <= t.vs_alloca_next` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     `FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b',type_memory_bytes cenv typ)` by
       (qpat_x_assum `!aid b. FLOOKUP u.vs_allocas aid = SOME b ==> _` irule >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `stmt_state_rel _ ctx func ce cx mid t`
       (strip_assume_tac o REWRITE_RULE [stmt_state_rel_def]) >>
     qpat_x_assum `alloca_inv t`
       (strip_assume_tac o REWRITE_RULE
         [venomMemDefsTheory.alloca_inv_def,venomMemDefsTheory.alloca_next_valid_def]) >>
     first_x_assum drule >> simp[]) >>
  Cases_on `is_bytestring_type typ` >- suspend "direct_bytes" >>
  `lowered_value_type cenv e = typ` by metis_tac[] >>
  `ltv = tyv` by
    ((qpat_assum `lowered_value_type cenv e = typ` (fn eq =>
       qpat_assum `evaluate_type _ (lowered_value_type cenv e) = SOME ltv`
         (mp_tac o PURE_REWRITE_RULE [eq])) >> asm_rewrite_tac[] >> (simp[]))) >>
  `type_memory_bytes ce typ = type_memory_size ltv` by
    (qpat_x_assum `type_memory_bytes cenv (lowered_value_type cenv e) = _` mp_tac >>
     simp[]) >>
  `compile_copy_memory (Var p) (Var xs) (type_memory_size ltv) c = ((),sf)` by
    (qpat_assum `lowered_value_type cenv e = typ` (fn eq =>
       qpat_assum `compile_store_memory _ _ _ _ _ c = _`
         (mp_tac o PURE_REWRITE_RULE [eq,contextTheory.compile_store_memory_def])) >>
     asm_rewrite_tac[]) >>
  `val_wf ltv v` by simp[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ mid _ _ t`
       (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >> simp[]) >>
  `~t.vs_halted` by
    (qpat_assum `gas_origin_ptr_path _ (rawt,rawG,rawtn) [] (OK t,G1',tn1')`
       (mp_then Any mp_tac fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec) >>
     simp[exit_result_def]) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func ce cx mid t` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_post_def]) >> simp[]) >>
  `t.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ mid t`
       (strip_assume_tac o REWRITE_RULE [stmt_state_rel_def]) >>
     drule exprLoweringPropsTheory.alloca_room_next_lt >> simp[]) >>
  `w2n sw + type_memory_size ltv < dimword (:256)` by decide_tac >>
  `w2n (n2w b' : 256 word) = b'` by simp[] >>
  `ptr_covers G1' tn1' p t (type_memory_size ltv)` by
    (qpat_assum `type_memory_bytes cenv typ = type_memory_size tyv` (fn eq =>
       qpat_assum `ptr_covers G1' tn1' p t (type_memory_bytes cenv typ)`
         (mp_tac o PURE_REWRITE_RULE [eq])) >> simp[]) >>
  `b' + type_memory_size ltv <= t.vs_alloca_next` by
    (qpat_assum `b' + type_memory_bytes cenv typ <= t.vs_alloca_next` mp_tac >> simp[]) >>
  qpat_assum `compile_copy_memory _ _ _ c = _`
    (mp_then Any (fn th =>
      qpat_assum `!mem. mem_agree_outside tn1'.t_mem t.vs_memory mem ==> val_in_memory ltv v (w2n sw) mem`
        (mp_then Any mp_tac th)) bodyFullMemoryCopyTheory.body_full_memory_copy_path) >>
  disch_then (fn th => qpat_assum `lookup_var p t = SOME (n2w b')`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `allocas_from lo t`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `fn_has_code c sf func`
    (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`ctx`,`PG`,`G1'`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> suspend "flat_assembly"
QED

Resume annassign_copy_runtime_outcome[direct_bytes]:
  `compile_store_bytestring (Var xs) (Var p) c = ((),sf)` by
    (qpat_x_assum `compile_store_memory _ _ _ _ _ c = _` mp_tac >>
     asm_rewrite_tac[contextTheory.compile_store_memory_def]) >>
  `is_bytestring_type (expr_type e)` by
    (Cases_on `expr_type e = typ` >- simp[] >>
     irule compileEnvTheory.arg_type_fits_bytestring_source >>
     qexists_tac `typ` >> simp[] >>
     qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     simp[vyperTypeSystemTheory.type_widens_to_def]) >>
  `is_bytestring_type (lowered_value_type cenv e)` by
    (Cases_on `lowered_value_type cenv e = expr_type e` >- simp[] >>
     qpat_x_assum `lowered_value_type cenv e = expr_type e \/ _` mp_tac >>
     simp[]) >>
  `val_in_memory tyv v (w2n sw) t.vs_memory` by
    (irule valueCopyBytesTheory.bytestring_val_in_memory_transfer >>
     conj_tac >- simp[] >>
     qexistsl_tac [`lowered_value_type cenv e`,`typ`,`get_tenv cx`,`ltv`] >>
     simp[] >>
     qpat_assum `!mem. mem_agree_outside tn1'.t_mem t.vs_memory mem ==> val_in_memory ltv v (w2n sw) mem` irule >>
     simp[mem_agree_outside_def]) >>
  `?len. mload (w2n sw) t = n2w len /\
     val_store_size tyv v = 32 + 32 * word_size len` by
    (irule exprSimBufferStoreTheory.buffer_typed_bytestring_header >>
     simp[] >> qexistsl_tac [`get_tenv cx`,`typ`] >> simp[]) >>
  `val_wf ltv v /\ val_wf tyv v` by
    simp[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `val_store_size ltv v = val_store_size tyv v` by
    (irule valueCopyBytesTheory.bytestring_val_store_size_eq >> simp[] >>
     qexistsl_tac [`lowered_value_type cenv e`,`typ`,`get_tenv cx`] >> simp[]) >>
  `val_store_size ltv v <= type_memory_size ltv /\
   val_store_size tyv v <= type_memory_size tyv` by
    simp[exprSimPropsTheory.val_store_size_le] >>
  qmatch_asmsub_abbrev_tac `val_store_size tyv v = n` >>
  `n = 32 + 32 * ((len+31) DIV 32)` by
    simp[Abbr `n`,vfmConstantsTheory.word_size_def] >>
  `n <= type_memory_size ltv /\ n <= type_memory_size tyv /\
   n < dimword (:256)` by
    (fs[Abbr `n`] >> simp[wordsTheory.dimword_def] >> decide_tac) >>
  `len + 31 < dimword (:256)` by
    (irule exprSimBufferStoreTheory.buffer_round_no_wrap >> fs[Abbr `n`]) >>
  `ptr_covers G1' tn1' xs t n` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     qexists_tac `type_memory_size ltv` >> simp[]) >>
  `ptr_covers G1' tn1' p t n` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     qexists_tac `type_memory_bytes cenv typ` >> simp[]) >>
  `!i. w2n sw <= i /\ i < w2n sw+32 ==> i NOTIN tn1'.t_mem` by
    (qpat_assum `!mem. mem_agree_outside tn1'.t_mem t.vs_memory mem ==> val_in_memory ltv v (w2n sw) mem`
       (mp_then Any mp_tac assignTuplePtrBytesResourcesTheory.robust_bytestring_header_clean_ptr) >>
     disch_then (qspecl_then [`lowered_value_type cenv e`,`get_tenv cx`] mp_tac) >>
     simp[]) >>
  `w2n (n2w b' : 256 word) = b'` by simp[] >>
  `run_inst_seq_mem_ok (emitted_insts c sf) t` by
    (irule bodyCopyMemoryBaseTheory.compile_store_bytestring_body_mem_ok >>
     qexistsl_tac [`n2w b'`,`Var p`,`len`,`Var xs`,`sw`] >>
     qunabbrev_tac `n` >> simp[eval_operand_def] >> rpt strip_tac >>
     pop_assum (fn th => rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ mid _ _ t`
       (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >> simp[]) >>
  `~t.vs_halted` by
    (qpat_assum `gas_origin_ptr_path _ (rawt,rawG,rawtn) [] (OK t,G1',tn1')`
       (mp_then Any mp_tac fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec) >>
     simp[exit_result_def]) >>
  `sf.cs_current_bb = c.cs_current_bb /\
   sf.cs_current_insts = c.cs_current_insts ++ emitted_insts c sf` by
    (qpat_assum `compile_store_bytestring _ _ c = _`
       (mp_then Any mp_tac bytesCopyCodeTheory.compile_store_bytestring_code) >>
     simp[same_blocks_def]) >>
  `?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts c sf) (DROP t.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `fn_has_code c sf func`
       (mp_then Any mp_tac stmtReasonLitFragMemoryTheory.fn_has_code_code) >>
     simp[] >> strip_tac >> qexists_tac `bb` >> simp[]) >>
  qpat_assum `compile_store_bytestring _ _ c = _`
    (mp_then Any mp_tac bodyFullAllocGenericTheory.compile_store_bytestring_origin_ptr_path) >>
  disch_then (fn th => qpat_assum `lookup_var xs t = SOME sw`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `lookup_var p t = SOME (n2w b')`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `ptr_covers G1' tn1' xs t n`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `allocas_from lo t`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `lookup_block t.vs_current_bb func.fn_blocks = SOME bb`
    (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`ctx`,`PG`,`len`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> suspend "bytes_assembly"
QED

Resume annassign_copy_runtime_outcome[flat_assembly]:
  qpat_x_assum `ltv = tyv` SUBST_ALL_TAC >>
  `c.cs_next_var <= sf.cs_next_var` by
    (qspecl_then [`Var p`,`Var xs`,`type_memory_size tyv`,`c`] mp_tac
      ci_mono_compile_copy_memory >> simp[ci_mono_def]) >>
  suspend "copy_assembly"
QED

Resume annassign_copy_runtime_outcome[copy_assembly]:
  drule_all annassign_continuation_all_tails >> strip_tac >>
  `local_ptrs_reserved ce c` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `a` >>
     qspec_then `a` mp_tac
       (Q.SPECL [`ce`,`expr_type e`,`e`] ci_mono_lower_value_compile_expr) >>
     simp[ci_mono_def]) >>
  `not_local_ptr ce mid.scopes p` by
    (irule local_ptrs_reserved_not_live >>
     conj_tac >- (qexistsl_tac [`id`,`type_memory_bytes cenv typ`] >> simp[]) >>
     qexists_tac `c` >> simp[]) >>
  `FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b',type_memory_bytes cenv typ)` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     qpat_x_assum `!aid b. FLOOKUP u.vs_allocas aid = SOME b ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  `!q. q = p \/ ~not_local_ptr ce mid.scopes q ==> not_fresh_at c q` by
    (rpt gen_tac >> strip_tac
     >- (qpat_x_assum `q = p` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     qpat_x_assum `~not_local_ptr ce mid.scopes q` mp_tac >>
     qpat_assum `local_ptrs_reserved ce c` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[loweringStateRelDefsTheory.not_local_ptr_def,
          loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
  `a.cs_next_var <= c.cs_next_var` by
    (qspec_then `a` mp_tac
       (Q.SPECL [`ce`,`expr_type e`,`e`] ci_mono_lower_value_compile_expr) >>
     simp[ci_mono_def]) >>
  `!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at c x` by
    (rpt strip_tac >>
     `not_fresh_at sa x` by
       (qpat_assum `!x sz. cenv.ce_return_buf = _ ==> _`
          (qspecl_then [`x`,`cap`] mp_tac) >>
        qpat_x_assum `ce.ce_return_buf = SOME _` mp_tac >> simp[]) >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at c x` by
    (rpt strip_tac >>
     `not_fresh_at sa x` by
       (qpat_assum `!x cap. cenv.ce_return_pc = _ ==> _`
          (qspecl_then [`x`,`cap`] mp_tac) >>
        qpat_x_assum `ce.ce_return_pc = SOME _` mp_tac >> simp[]) >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  qexistsl_tac [`mid with scopes := (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>)) :: rest`,
    `t'`,`Gf`,`tf`] >> simp[] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `stmt_state_rel H ctx func ce cx mid t` by
    (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [expr_post_def]) >> simp[]) >>
  qpat_assum `!D. gas_origin_ptr_path _ (t,G1',tn1') [] (OK t',Gf,tf)`
    (qspec_then `DF H` (mp_then Any mp_tac
      (INST_TYPE [alpha |-> ``:256``] body_full_annassign_memory_post))) >>
  disch_then (fn th => qpat_assum `typed_copy_state_frame c _ _ t t'`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `stmt_state_rel H ctx func ce cx mid t`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `ghost_inv_at (DF H) lo d ce cx mid G1' tn1' t`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) _)`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `mid.scopes = sc :: rest`
    (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`v`,`sf`,
    `mk_inst r.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv typ))] [p]`,`T`] mp_tac) >>
  (impl_tac >- (simp[mk_inst_def] >>
    qpat_assum `!q. q = p \/ ~not_local_ptr ce mid.scopes q ==> _` mp_tac >> simp[])) >>
  strip_tac >>
  conj_tac >- simp[stmt_lands_def] >>
  conj_tac >- (irule stmtSimDeclMemTheory.compile_assign_value_memory_widen_open >>
    goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (irule stmtSimDeclComposeTheory.cenv_top_ext_declare_local >>
    simp[] >> qexistsl_tac [`id`,`sa`,`r`,`typ`] >> simp[] >>
    qpat_assum `lookup_scopes id mid.scopes = NONE` mp_tac >>
    qpat_assum `mid.scopes = sc :: rest` (fn th => rewrite_tac[th]) >>
    Cases_on `FLOOKUP sc id` >>
    simp[vyperStateTheory.lookup_scopes_def]) >>
  simp[] >>
  conj_tac >- (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_post_def]) >>
    strip_tac >>
    irule (iffRL vyperStorageFootprintTheory.storage_well_formed_on_backends) >>
    simp[] >> qexists_tac `mid` >> simp[]) >>
  `t'.vs_alloca_next = t.vs_alloca_next /\ t'.vs_allocas = t.vs_allocas` by
    (qpat_assum `typed_copy_state_frame c _ _ t t'`
      (strip_assume_tac o REWRITE_RULE [typedMemoryCopyTheory.typed_copy_state_frame_def]) >>
     qpat_x_assum `(t' with <|vs_vars := _; vs_memory := _; vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|>) = t`
       mp_tac >>
     simp[venomStateTheory.venom_state_component_equality]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t' = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at a x /\ not_fresh_at c x` by
       (conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
        qexists_tac `sa` >> simp[]) >>
     qpat_assum `!x. not_fresh_at c x ==> _` (qspec_then `x` mp_tac) >> simp[] >>
     qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_post_def]) >> strip_tac >>
     first_x_assum irule >> simp[] >>
     qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  `s0.vs_alloca_next <= t'.vs_alloca_next` by simp[] >>
  conj_tac >- (irule return_buf_frame_frame >>
    qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  conj_tac >- (qpat_assum `!D. gas_origin_ptr_path _ (t,G1',tn1') [] (OK t',Gf,tf)`
    (qspec_then `DF H` (mp_then Any mp_tac body_full_path_alloca_history)) >>
    simp[] >>
    qpat_assum `stmt_state_rel H ctx func ce cx mid t`
      (mp_tac o REWRITE_RULE [stmt_state_rel_def]) >> simp[]) >>
  simp[] >>
  conj_tac >- (qpat_x_assum `ghost_inv_at (DF H) lo d ce cx (mid with scopes := _) Gf tf t'` mp_tac >>
    pure_rewrite_tac[ghost_inv_at_def] >> strip_tac >> simp[] >>
    qpat_assum `!name entry p sz. lookup_scopes name _ = SOME entry /\ _ ==> _`
      (ACCEPT_TAC o SRULE [])) >>
  conj_tac >- (rpt strip_tac >> simp[] >>
    qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [expr_post_def]) >> strip_tac >>
    first_x_assum irule >> simp[] >> first_x_assum irule >> simp[]) >>
  rpt strip_tac >>
  `not_fresh_at a x /\ not_fresh_at c x` by
    (conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `sa` >> simp[]) >>
  qpat_assum `!x. not_fresh_at c x ==> _` (qspec_then `x` mp_tac) >> simp[] >>
  qpat_assum `ghost_kept_at lo ce es a G1 tn1 u G1' tn1'`
    (mp_tac o REWRITE_RULE [ghost_kept_at_def]) >> strip_tac >>
  qpat_assum `!x. not_fresh_at a x ==> _` (qspec_then `x` mp_tac) >> simp[] >>
  qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >> simp[]
QED

Resume annassign_copy_runtime_outcome[bytes_assembly]:
  `(sf' with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>) = t /\
   LENGTH t.vs_memory <= LENGTH sf'.vs_memory` by
    (irule abiDecodePtrBytesRuntimeFrameTheory.abi_decode_memory_run_frame >>
     qexists_tac `emitted_insts c sf` >> simp[] >>
     qpat_assum `compile_store_bytestring _ _ c = _`
       (mp_then Any mp_tac bytesCopyCodeTheory.compile_store_bytestring_code) >>
     strip_tac >> simp[bytesCopyCodeTheory.bytes_copy_insts_def,
       venomInstTheory.mk_inst_def,freshWritesTheory.fresh_write_op_def]) >>
  qmatch_asmsub_abbrev_tac `(OK (sf' with vs_inst_idx := lastidx),Gf,tnf)` >>
  qabbrev_tac `t' = sf' with vs_inst_idx := lastidx` >>
  `typed_copy_state_frame c b' (type_memory_size tyv) t t'` by
    (simp[NoAsms,typedMemoryCopyTheory.typed_copy_state_frame_def,Abbr `t'`] >>
     conj_tac >- (qpat_assum `(sf' with <|vs_vars := _; vs_memory := _|>) = t` mp_tac >>
       simp[venomStateTheory.venom_state_component_equality]) >>
     conj_tac >- (rpt strip_tac >>
       qpat_assum `!p. not_fresh_at c p ==> lookup_var p sf' = _ /\ _` (qspec_then `x` mp_tac) >>
       disch_then drule >> strip_tac >>
       qpat_assum `lookup_var x sf' = lookup_var x t` mp_tac >>
       simp[NoAsms,venomStateTheory.lookup_var_def]) >>
     pure_rewrite_tac[typedMemoryCopyTheory.typed_copy_frame_def] >>
     reverse conj_tac >- (qpat_assum `LENGTH t.vs_memory <= LENGTH sf'.vs_memory` ACCEPT_TAC) >>
     rpt strip_tac >> simp[] >>
     irule valueCopyTheory.mem_bytes_at_mcopy_disjoint >> simp[]) >>
  `!mem. mem_agree_outside tn1'.t_mem t.vs_memory mem ==> val_in_memory tyv v (w2n sw) mem` by
    (rpt strip_tac >> irule valueCopyBytesTheory.bytestring_val_in_memory_transfer >>
     conj_tac >- simp[] >>
     qexistsl_tac [`lowered_value_type cenv e`,`typ`,`get_tenv cx`,`ltv`] >>
     simp[]) >>
  `!mem. mem_agree_outside tnf.t_mem t'.vs_memory mem ==> val_in_memory tyv v b' mem` by
    (simp[NoAsms,Abbr `t'`] >>
     qpat_assum `sf'.vs_memory = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `w2n (n2w b' : 256 word) = b'` (fn th => pure_rewrite_tac[th]) >>
     match_mp_tac (Q.INST [`tn` |-> `tn1'.t_mem`] forPtrBulkTheory.for_bulk_copy_robust) >>
     simp[] >>
     irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `val_store_size tyv v` >>
     simp[exprSimPropsTheory.val_footprint_le_store_size]) >>
  rename1 `!mem. mem_agree_outside tf.t_mem t'.vs_memory mem ==> val_in_memory tyv v b' mem` >>
  `~t'.vs_halted /\ t'.vs_current_bb = sf.cs_current_bb /\
   t'.vs_inst_idx = LENGTH sf.cs_current_insts` by
    (qpat_assum `(sf' with <|vs_vars := _; vs_memory := _|>) = t` mp_tac >>
     simp[Abbr `t'`,Abbr `lastidx`,venomStateTheory.venom_state_component_equality]) >>
  `val_in_memory tyv v b' t'.vs_memory` by
    (qpat_assum `!mem. mem_agree_outside tf.t_mem t'.vs_memory mem ==> _` irule >>
     simp[mem_agree_outside_def]) >>
  `!x. not_fresh_at c x ==> lookup_var x t' = lookup_var x t /\
    FLOOKUP Gf x = FLOOKUP G1' x /\ op_taint tf (Var x) = op_taint tn1' (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!p. not_fresh_at c p ==> lookup_var p sf' = _ /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     fs[Abbr `t'`,venomStateTheory.lookup_var_def]) >>
  `!i. ~(b' <= i /\ i < b' + type_memory_size tyv) ==>
    (i IN tf.t_mem <=> i IN tn1'.t_mem)` by
    (qpat_x_assum `tf.t_mem = _` (fn th => rewrite_tac[th]) >>
     simp[] >> rpt strip_tac >> eq_tac >> simp[] >> rpt strip_tac >> decide_tac) >>
  `c.cs_next_var <= sf.cs_next_var` by
    (qspecl_then [`Var xs`,`Var p`,`c`] mp_tac
      ci_mono_compile_store_bytestring >> simp[ci_mono_def]) >>
  suspend "copy_assembly"
QED

Resume annassign_copy_runtime_outcome[staged_assembly]:
  `not_fresh_at c p` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `a` >>
     qspec_then `a` mp_tac
       (Q.SPECL [`ce`,`expr_type e`,`e`] ci_mono_lower_value_compile_expr) >>
     simp[ci_mono_def]) >>
  `lookup_var p t = SOME (n2w b')` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_post_def]) >> simp[] >> metis_tac[]) >>
  `ptr_covers G1' tn1' p t (type_memory_bytes cenv typ)` by
    (
     qpat_assum `ghost_kept_at lo ce es a G1 tn1 u G1' tn1'`
       (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     qpat_assum `ptr_covers G1 tn1 p u _`
       (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
     qpat_x_assum `lookup_var p u = SOME w` mp_tac >> simp[] >>
     disch_then SUBST_ALL_TAC >> simp[ptr_covers_def]) >>
  `FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b',type_memory_bytes cenv typ)` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     qpat_x_assum `!aid b. FLOOKUP u.vs_allocas aid = SOME b ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  `FLOOKUP t'.vs_allocas sa.cs_next_id = SOME (b',type_memory_bytes cenv typ)` by
    (qpat_assum `!aid ent. FLOOKUP t.vs_allocas aid = SOME ent ==> _`
       irule >> first_assum ACCEPT_TAC) >>
  `not_fresh_at sc p /\ lookup_var p t' = SOME (n2w b') /\
   FLOOKUP Gf p = FLOOKUP G1' p /\ op_taint tf (Var p) = op_taint tn1' (Var p)` by
    (qpat_assum `!x. not_fresh_at c x ==> not_fresh_at sc x /\ _`
       (qspec_then `p` (drule_then strip_assume_tac)) >> simp[]) >>
  `ptr_covers Gf tf p t' (type_memory_bytes cenv typ)` by
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl_tac [`G1'`,`t`,`tn1'`] >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func ce cx mid t'` by
    (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  `alloca_inv t' /\ t'.vs_alloca_next < dimword (:256)` by
    (conj_tac
     >- (qpat_assum `stmt_state_rel _ _ _ _ _ mid t'`
          (mp_tac o REWRITE_RULE [stmt_state_rel_def]) >> simp[]) >>
     qpat_assum `stmt_state_rel _ _ _ _ _ mid t'`
       (strip_assume_tac o REWRITE_RULE [stmt_state_rel_def]) >>
     drule exprLoweringPropsTheory.alloca_room_next_lt >> simp[]) >>
  `b' + type_memory_bytes cenv typ <= t'.vs_alloca_next` by
    (qpat_assum `alloca_inv t'`
       (strip_assume_tac o REWRITE_RULE
         [venomMemDefsTheory.alloca_inv_def,venomMemDefsTheory.alloca_next_valid_def]) >>
     first_x_assum drule >> simp[]) >>
  `sa.cs_next_id < c.cs_next_id` by
    (qpat_assum `emit_inst ALLOCA _ _ r = _`
       (mp_then Any mp_tac emitHelperPropsTheory.emit_inst_extends) >>
     qspec_then `a` mp_tac
       (Q.SPECL [`ce`,`expr_type e`,`e`] ci_mono_lower_value_compile_expr) >>
     simp[ci_mono_def]) >>
  `b'' + type_memory_size ltv <= b' \/
   b' + type_memory_size tyv <= b''` by
    (qpat_assum `alloca_inv t'`
       (strip_assume_tac o REWRITE_RULE
         [venomMemDefsTheory.alloca_inv_def,
          venomMemDefsTheory.allocas_non_overlapping_def]) >>
     qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _`
       (qspecl_then [`c.cs_next_id`,`sa.cs_next_id`,`b''`,
         `type_memory_size ltv`,`b'`,`type_memory_bytes cenv typ`] mp_tac) >> simp[]) >>
  `w2n (n2w b' : 256 word) = b' /\ w2n (n2w b'' : 256 word) = b''` by simp[] >>
  `compile_store_memory ce (Var root) (Var p) typ (lowered_value_type cenv e) sc = ((),sf)` by
    (qpat_assum `buf.buf_operand = Var root` (fn eq =>
      qpat_assum `compile_store_memory ce buf.buf_operand _ _ _ sc = _`
        (ACCEPT_TAC o PURE_REWRITE_RULE [eq]))) >>
  qpat_assum `compile_store_memory ce (Var root) _ _ _ sc = _`
    (mp_then Any mp_tac bodyFullMemoryStoreTheory.body_full_memory_store_path) >>
  disch_then (fn th => qpat_assum `lookup_var root t' = SOME (n2w b'')`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `lookup_var p t' = SOME (n2w b')`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `ptr_covers Gf tf root t' _`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `fn_has_code sc sf func`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `evaluate_type (get_tenv cx) typ = SOME tyv`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `value_has_type tyv v`
    (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`lo`,`gas_explicit_sites ctx shadow_ctx`,`ctx`,`PG`] mp_tac) >>
  (impl_tac >-
    (`expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
     drule_all immutableDeployAssignRangesTheory.immutable_assign_copy_metadata >>
     strip_tac >>
     `val_wf tyv v` by simp[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
     `ptr_covers Gf tf p t' (type_memory_size tyv)` by
       (qpat_assum `type_memory_bytes cenv typ = type_memory_size tyv` (fn eq =>
          qpat_assum `ptr_covers Gf tf p t' (type_memory_bytes cenv typ)`
            (ACCEPT_TAC o PURE_REWRITE_RULE [eq]))) >>
     simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
     Cases_on `lowered_value_type cenv e = expr_type e` >- fs[] >>
     `arg_type_fits (lowered_value_type cenv e) (expr_type e)` by fs[] >>
     `well_formed_type (get_tenv cx) typ` by
       (irule assignable_type_well_formed >> fs[]) >>
     Cases_on `expr_type e = typ` >- fs[type_widens_to_def] >>
     `arg_type_fits (expr_type e) typ` by
       (qpat_assum `type_widens_to env.type_defs (expr_type e) typ`
          (mp_tac o REWRITE_RULE [type_widens_to_def]) >> simp[]) >>
     simp[type_widens_to_def] >> disj2_tac >>
     irule (cj 1 typedCopyCompatibilityTheory.arg_type_fits_trans) >>
     qexists_tac `expr_type e` >> simp[])) >>
  disch_then (qx_choose_then `t''`
    (qx_choose_then `Gf'` (qx_choose_then `tf'` strip_assume_tac))) >>
  drule_all annassign_continuation_all_tails >> strip_tac >>
  `c.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sc.cs_next_var` by
    (qspec_then `c` mp_tac (Q.SPEC `type_memory_size ltv` ci_mono_compile_alloc_buffer) >>
     qspec_then `sm` mp_tac (Q.SPECL [`buf.buf_operand`,`Var xs`,`type_memory_size ltv`]
       ci_mono_compile_copy_memory) >> simp[ci_mono_def]) >>
  `local_ptrs_reserved ce sc` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `c` >> simp[]) >>
  `not_local_ptr ce mid.scopes p` by
    (irule local_ptrs_reserved_not_live >>
     conj_tac >- (qexistsl_tac [`id`,`type_memory_bytes cenv typ`] >> simp[]) >>
     qexists_tac `sc` >> simp[]) >>
  `!q. q = p \/ ~not_local_ptr ce mid.scopes q ==> not_fresh_at sc q` by
    (rpt gen_tac >> strip_tac
     >- (qpat_x_assum `q = p` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     qpat_x_assum `~not_local_ptr ce mid.scopes q` mp_tac >>
     qpat_assum `local_ptrs_reserved ce sc` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[loweringStateRelDefsTheory.not_local_ptr_def,
          loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
  `!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sc x` by
    (rpt strip_tac >>
     qpat_assum `!x cap. ce.ce_return_buf = _ ==> not_fresh_at c x`
       (qspecl_then [`x`,`cap`] (drule_then assume_tac)) >>
     qpat_assum `!x. not_fresh_at c x ==> not_fresh_at sc x /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >> simp[]) >>
  `!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sc x` by
    (rpt strip_tac >>
     qpat_assum `!x cap. ce.ce_return_pc = _ ==> not_fresh_at c x`
       (qspecl_then [`x`,`cap`] (drule_then assume_tac)) >>
     qpat_assum `!x. not_fresh_at c x ==> not_fresh_at sc x /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >> simp[]) >>
  qexistsl_tac [`mid with scopes := (sc' |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>)) :: rest`,
    `t''`,`Gf'`,`tf'`] >> simp[] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `stmt_state_rel H ctx func ce cx mid t` by
    (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [expr_post_def]) >> simp[]) >>
  `stmt_state_rel H ctx func ce cx mid t'` by
    (qpat_assum `!H. stmt_state_rel H _ _ _ _ mid t ==> _`
       (drule_then assume_tac) >> simp[]) >>
  `ghost_inv_at (DF H) lo d ce cx mid Gf tf t'` by
    (qpat_assum `!D d. ghost_inv_at D _ _ _ _ mid G1' tn1' t ==> _`
       (drule_then assume_tac) >> simp[]) >>
  qpat_assum `!D. gas_origin_ptr_path _ (t',Gf,tf) [] (OK t'',Gf',tf')`
    (qspec_then `DF H` (mp_then Any mp_tac
      (INST_TYPE [alpha |-> ``:256``] body_full_annassign_memory_post))) >>
  disch_then (fn th => qpat_assum `typed_copy_state_frame sc _ _ t' t''`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `stmt_state_rel H ctx func ce cx mid t'`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `ghost_inv_at (DF H) lo d ce cx mid Gf tf t'`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) _)`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `mid.scopes = sc' :: rest`
    (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`v`,`sf`,
    `mk_inst r.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv typ))] [p]`,`T`] mp_tac) >>
  (impl_tac >- (simp[mk_inst_def] >>
    qpat_assum `!q. q = p \/ ~not_local_ptr ce mid.scopes q ==> _` mp_tac >> simp[])) >>
  strip_tac >> FAIL_TAC "staged_post_installed"
QED

Finalise annassign_copy_runtime_outcome
