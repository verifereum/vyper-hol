(* Static and compiler boundaries for copying memory declarations. *)
Theory bodyFullAnnAssignCopyEntry
Ancestors
  annAssignPtrMemoryLayout annAssignPtrFacts bodyFullPreds bodySimFull
  exprSimDeclEnv bodySim exprSimHypsDefs supportedStmts supportedStmtTraverse
  supportedExprTraverse bodyExprPreFacts memoryLocalRhsProps vyperTypeCallGraph
  gasShadowCompileStmtHelpers gasShadowCompileStmtBase gasShadowCompile
  stmtSimDecl stmtSimProps exprLoweringProps emitHelperProps loweringSlice
  compileEnv exprLowering stmtLowering loweringPosts vyperTypeSystem
  vyperContext vyperInterpreter vyperState vyperValue vyperAST list finite_map

Theorem annassign_copy_full_static_preparation:
  (!tenv s'' tyv t. tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
      (INL tyv,t) ==> body_expr_full_ok cx e) /\
  body_inv tops ctx cenv cx /\ supported_stmt tops bindings (AnnAssign id typ e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (AnnAssign id typ e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
  stmt_exprs_ok cenv (AnnAssign id typ e) /\
  call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
  0 < type_memory_bytes cenv typ /\
  ~(has_length_word typ /\ is_empty_value_expr e) /\
  (lowered_value_type cenv e = typ \/ is_bytestring_type typ \/
    has_length_word typ /\ is_empty_value_expr e) /\
  (lowered_value_type cenv e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type cenv e) /\
    arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
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
  ?tyv ltv. evaluate_type (get_tenv cx) typ = SOME tyv /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
    type_memory_bytes cenv typ = type_memory_size tyv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `well_typed_expr env e /\ assignable_type env.type_defs typ /\
   type_widens_to env.type_defs (expr_type e) typ /\
   id NOTIN FDOM env.var_types` by gvs[type_stmt_def, AllCaseEqs()] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    metis_tac[assignable_type_well_formed, well_formed_type_def,
              optionTheory.IS_SOME_EXISTS] >>
  `body_expr_full_ok cx e` by
    (first_x_assum irule >> qexistsl_tac [`es`,`es`,`get_tenv cx`,`tyv`] >>
     simp[lift_option_type_def, return_def]) >>
  `supported_expr tops e` by fs[supported_stmt_def] >>
  drule supported_expr_body_calls >> strip_tac >>
  `body_stmt_safe tops (AnnAssign id typ e)` by
    simp[body_stmt_safe_def, supported_stmt_expr_exists_def,
         int_calls_stmt_def, GSYM expr_has_evm_run_def, EVERY_CONJ] >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (Cases_on `FLOOKUP cenv.ce_vars id` >> simp[] >>
     fs[ce_locals_declared_def] >> metis_tac[]) >>
  `lookup_scopes id es.scopes = NONE` by
    (fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
         vyperTypeInvariantsTheory.env_scopes_consistent_def] >>
     Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     qpat_x_assum `!id entry. lookup_scopes _ _ = _ ==> _`
       (drule_then mp_tac) >> simp[FLOOKUP_DEF]) >>
  `expr_body_pre cenv cx env e es` by
    (drule_all annassign_rhs_pre_ptr >> simp[]) >>
  `expr_type e = typ \/ is_bytestring_type typ` by metis_tac[] >>
  `0 < type_memory_bytes cenv (lowered_value_type cenv e) /\
   type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_bytes cenv typ` by
    metis_tac[memory_rhs_destination_bound] >>
  `type_memory_bytes cenv typ < 2 ** 64` by
    gvs[stmt_exprs_ok_flat, allocLimitsTheory.alloc_limits_stmt_def] >>
  `type_memory_bytes cenv (lowered_value_type cenv e) < 2 ** 64` by decide_tac >>
  drule_all memory_rhs_lowered_runtime_layout >> strip_tac >>
  `type_memory_bytes cenv typ = type_memory_size tyv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  simp[] >> metis_tac[]
QED

Theorem annassign_copy_full_code_entry:
  body_stmt_safe tops (AnnAssign id typ e) /\
  body_inv tops ctx old cx /\ supported_expr tops e /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (AnnAssign id typ e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv old cx env es /\ well_typed_expr env e /\
  id NOTIN FDOM env.var_types /\ FLOOKUP old.ce_vars id = NONE /\
  stmt_exprs_ok old (AnnAssign id typ e) /\
  call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
  body_expr_full_ok cx e /\ ~is_word_type typ /\
  ~(has_length_word typ /\ is_empty_value_expr e) /\
  (lowered_value_type old e = typ \/ is_bytestring_type typ) /\
  stmt_env old lctx ret_ty (AnnAssign id typ e) sa = (ce,sf) /\
  fn_has_code sa sf func /\ local_ptrs_reserved old sa ==>
  ?r a b c vv op p.
    declare_local old id typ sa = (ce,r) /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes old typ)) /\
    emit_inst ALLOCA [Lit (n2w (type_memory_bytes old typ))] [p] r = ((),a) /\
    compile_expr ce (expr_type e) e a = (vv,b) /\
    unwrap_value ce vv b = (op,c) /\
    lower_value compile_expr ce (expr_type e) e a = (op,c) /\
    compile_assign_value ce (Var p) LocMemory op F (vv_location vv) typ
      (lowered_value_type old e) (type_memory_bytes ce typ) c = ((),sf) /\
    local_ptrs_reserved ce r /\ local_ptrs_reserved ce a /\ not_fresh_at a p /\
    cs_extends r a /\ cs_extends a c /\ cs_extends c sf /\
    fn_has_code r a func /\ fn_has_code a c func /\ fn_has_code c sf func /\
    cs_extends a b /\ cs_extends b c /\
    fn_has_code a b func /\ fn_has_code b c func /\
    MEM (mk_inst r.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes old typ))] [p]) (fn_insts func) /\
    compile_alloc_buffer (type_memory_bytes old typ) sa =
      (<|buf_operand := Var p; buf_size := type_memory_bytes old typ|>,a) /\
    cs_extends sa a /\ fn_has_code sa a func /\
    body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      ce cx (expr_type e) e es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `old.ce_alloca_locals` by fs[body_inv_def] >>
  `!st0 c st1. declare_local old id typ st0 = (c,st1) ==>
    !a b op. lower_value compile_expr c (expr_type e) e a = (op,b) ==> cs_extends a b` by
    (rpt strip_tac >> metis_tac[compile_expr_grows]) >>
  drule_all annassign_memory_code_parts_ptr >> strip_tac >>
  drule_all annassign_declared_rhs_pre_ptr >> strip_tac >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      ce cx (expr_type e) e es` by metis_tac[body_expr_full_ok_def] >>
  `cs_extends sA sV` by metis_tac[compile_expr_grows] >>
  `cs_extends sV sB` by metis_tac[exprSimUnwrapTheory.unwrap_value_extends] >>
  `fn_has_code sA sV func /\ fn_has_code sV sB func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all declare_local_ptr >> strip_tac >>
  `compile_alloc_buffer (type_memory_bytes old typ) sa =
    (<|buf_operand := Var (STRING #"%" (toString sa.cs_next_var));
       buf_size := type_memory_bytes old typ|>,sA)` by
    (qpat_x_assum `emit_inst ALLOCA _ _ _ = _` mp_tac >>
     qpat_x_assum `st = _` SUBST1_TAC >>
     simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
       emitHelperTheory.emit_inst_def, fresh_id_def, fresh_var_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       pairTheory.pair_case_thm] >> strip_tac >> gvs[]) >>
  `cs_extends sa sA` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `fn_has_code sa sA func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  goal_assum (drule_at (Pat `declare_local _ _ _ _ = _`)) >> gvs[]
QED

Theorem annassign_copy_full_shadow_entry:
  ~is_word_type typ /\ ~(has_length_word typ /\ is_empty_value_expr e) /\
  (lowered_value_type ce e = typ \/ is_bytestring_type typ) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) cap) /\
  gas_shadow_state r shadow_r /\
  compile_stmt ce lctx ret_ty (AnnAssign id typ (gas_shadow_expr e)) shadow_r =
    ((),shadow_sf) /\
  emit_inst ALLOCA [Lit (n2w cap)] [p] r = ((),a) /\
  compile_expr ce (expr_type e) e a = (vv,b) /\
  unwrap_value ce vv b = (op,c) /\
  fn_has_code shadow_r shadow_sf shadow_func ==>
  ?shadow_a shadow_b shadow_c.
    emit_inst ALLOCA [Lit (n2w cap)] [p] shadow_r = ((),shadow_a) /\
    compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_a = (vv,shadow_b) /\
    unwrap_value ce vv shadow_b = (op,shadow_c) /\
    gas_shadow_state a shadow_a /\ gas_shadow_state b shadow_b /\
    gas_shadow_state c shadow_c /\
    compile_assign_value ce (Var p) LocMemory op F (vv_location vv) typ
      (lowered_value_type ce e) (type_memory_bytes ce typ) shadow_c = ((),shadow_sf) /\
    fn_has_code shadow_a shadow_b shadow_func /\
    fn_has_code shadow_b shadow_c shadow_func /\
    fn_has_code shadow_c shadow_sf shadow_func
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `emit_inst ALLOCA [Lit (n2w cap)] [p] shadow_r` >>
  rename1 `emit_inst ALLOCA _ _ shadow_r = (u,shadow_a)` >>
  `u = () /\ gas_shadow_state a shadow_a` by
    (mp_tac (Q.INST [`opc` |-> `ALLOCA`, `ops` |-> `[Lit (n2w cap)]`,
       `outs` |-> `[p]`] gasShadowStateTheory.gas_shadow_compiles_emit_inst) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`r`,`shadow_r`] mp_tac) >> gvs[]) >> gvs[] >>
  Cases_on `compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_a` >>
  rename1 `compile_expr _ _ (gas_shadow_expr e) _ = (shadow_vv,shadow_b)` >>
  `shadow_vv = vv /\ gas_shadow_state b shadow_b` by
    (mp_tac (Q.SPECL [`ce`,`expr_type e`,`e`,`T`] (cj 1 gas_shadow_compile_expr)) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`a`,`shadow_a`] mp_tac) >> simp[]) >> gvs[] >>
  rename1 `compile_expr ce (expr_type e) e a = (vv,b)` >>
  Cases_on `unwrap_value ce vv shadow_b` >>
  rename1 `unwrap_value ce vv shadow_b = (shadow_op,shadow_c)` >>
  `shadow_op = op /\ gas_shadow_state c shadow_c` by
    (mp_tac (Q.INST [`cenv` |-> `ce`,`vv` |-> `vv`]
       gasShadowCompileConvertTheory.gas_shadow_compiles_unwrap_value) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`b`,`shadow_b`] mp_tac) >> simp[]) >> gvs[] >>
  drule annassign_memory_lowering_parts_ptr >>
  simp[gasShadowCompileStmtBaseTheory.gas_shadow_is_empty_value_expr] >> strip_tac >>
  gvs[gasShadowTheory.gas_shadow_expr_type,
      gasShadowCompileStmtBaseTheory.gas_shadow_is_empty_value_expr,
      gasShadowCompilePureTheory.gas_shadow_lowered_value_type] >>
  `cs_extends shadow_r shadow_a` by
    metis_tac[fragExecTheory.cs_appends_emit_helpers, fragExecTheory.cs_appends_def] >>
  `cs_extends shadow_a shadow_b /\ cs_extends shadow_b shadow_c` by
    metis_tac[compile_expr_grows, exprSimUnwrapTheory.unwrap_value_extends] >>
  `cs_extends shadow_c shadow_sf` by
    metis_tac[stmtSimDeclMemTheory.compile_assign_memory_widen_appends,
      fragExecTheory.cs_appends_def] >>
  metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans]
QED
