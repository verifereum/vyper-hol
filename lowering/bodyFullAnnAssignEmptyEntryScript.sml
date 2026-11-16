(* Compiler and raw expression entry for empty memory declarations. *)
Theory bodyFullAnnAssignEmptyEntry
Ancestors
  annAssignPtrEmptyLayout annAssignPtrFacts bodyFullPreds bodySimFull
  exprSimDeclEnv bodySim exprSimHypsDefs
  gasShadowCompileStmtHelpers gasShadowCompileStmtBase gasShadowCompile
  stmtSimDecl stmtSimProps exprLoweringProps emitHelperProps loweringSlice
  compileEnv exprLowering stmtLowering loweringPosts vyperTypeSystem
  vyperContext vyperInterpreter vyperState vyperValue vyperAST list finite_map

Theorem annassign_empty_full_code_entry:
  body_stmt_safe tops (AnnAssign id typ e) /\
  body_inv tops ctx old cx /\ supported_expr tops e /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (AnnAssign id typ e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv old cx env es /\ well_typed_expr env e /\
  id NOTIN FDOM env.var_types /\ FLOOKUP old.ce_vars id = NONE /\
  stmt_exprs_ok old (AnnAssign id typ e) /\
  call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
  body_expr_full_ok cx e /\ has_length_word typ /\ is_empty_value_expr e /\
  stmt_env old lctx ret_ty (AnnAssign id typ e) sa = (ce,sf) /\
  fn_has_code sa sf func /\ local_ptrs_reserved old sa ==>
  ?r a b vv p.
    declare_local old id typ sa = (ce,r) /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes old typ)) /\
    emit_inst ALLOCA [Lit (n2w (type_memory_bytes old typ))] [p] r = ((),a) /\
    compile_expr ce (expr_type e) e a = (vv,b) /\
    emit_void MSTORE [Var p; Lit 0w] b = ((),sf) /\
    local_ptrs_reserved ce r /\ local_ptrs_reserved ce a /\ not_fresh_at a p /\
    cs_extends r a /\ cs_extends a b /\ cs_extends b sf /\
    fn_has_code r a func /\ fn_has_code a b func /\ fn_has_code b sf func /\
    MEM (mk_inst r.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes old typ))] [p]) (fn_insts func) /\
    compile_alloc_buffer (type_memory_bytes old typ) sa =
      (<|buf_operand := Var p; buf_size := type_memory_bytes old typ|>,a) /\
    cs_extends sa a /\ fn_has_code sa a func /\
    body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      ce cx (expr_type e) e es
Proof
  strip_tac >>
  `old.ce_alloca_locals` by fs[body_inv_def] >>
  `!st0 c st1. declare_local old id typ st0 = (c,st1) ==>
    !a b vv. compile_expr c (expr_type e) e a = (vv,b) ==> cs_extends a b` by
    (rpt strip_tac >> metis_tac[compile_expr_grows]) >>
  drule_all annassign_empty_code_parts_ptr >> strip_tac >>
  drule_all annassign_declared_rhs_pre_ptr >> strip_tac >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      ce cx (expr_type e) e es` by metis_tac[body_expr_full_ok_def] >>
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

Theorem annassign_empty_full_shadow_entry:
  has_length_word typ /\ is_empty_value_expr e /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) cap) /\
  gas_shadow_state r shadow_r /\
  compile_stmt ce lctx ret_ty (AnnAssign id typ (gas_shadow_expr e)) shadow_r =
    ((),shadow_sf) /\
  emit_inst ALLOCA [Lit (n2w cap)] [p] r = ((),a) /\
  compile_expr ce (expr_type e) e a = (vv,b) /\
  fn_has_code shadow_r shadow_sf shadow_func ==>
  ?shadow_a shadow_b.
    emit_inst ALLOCA [Lit (n2w cap)] [p] shadow_r = ((),shadow_a) /\
    compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_a = (vv,shadow_b) /\
    gas_shadow_state a shadow_a /\ gas_shadow_state b shadow_b /\
    emit_void MSTORE [Var p; Lit 0w] shadow_b = ((),shadow_sf) /\
    fn_has_code shadow_a shadow_b shadow_func
Proof
  strip_tac >>
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
  `cs_extends shadow_a shadow_b` by metis_tac[compile_expr_grows] >>
  `is_empty_value_expr (gas_shadow_expr e)` by
    fs[stmtLoweringTheory.is_empty_value_expr_def, gasShadowTheory.gas_shadow_expr_def] >>
  drule_all compile_annassign_empty_parts_ptr >> strip_tac >>
  gvs[gasShadowTheory.gas_shadow_expr_type] >>
  rename1 `compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_a = (shadow_vv,shadow_b)` >>
  `cs_extends shadow_r shadow_a` by
    metis_tac[fragExecTheory.cs_appends_emit_helpers, fragExecTheory.cs_appends_def] >>
  `cs_extends shadow_b shadow_sf` by
    metis_tac[fragExecTheory.cs_appends_emit_helpers, fragExecTheory.cs_appends_def] >>
  `cs_extends shadow_a shadow_sf` by metis_tac[cs_extends_trans] >>
  metis_tac[fragExecTheory.fn_has_code_split]
QED
