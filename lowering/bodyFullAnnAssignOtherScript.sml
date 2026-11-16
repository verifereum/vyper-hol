(* Direct other-layout declaration: compiler and value preparation. *)
Theory bodyFullAnnAssignOther
Ancestors
  annAssignPtrMemoryLayout annAssignPtrFacts bodyFullPreds bodySimFull
  bodyExprPreFacts exprSimHypsDefs exprSimHyps exprSimSource exprLoweringProps
  gasShadow gasShadowCompileStmtHelpers gasShadowCompileStmtBase gasShadowCompile
  assignRelayoutCaller typedMemoryCopy abiEncodeMaterialize annassignRelayoutSource
  stmtSimDeclMem stmtSimProps loweringSlice stmtLoweringMono
  compileEnv exprLowering stmtLowering loweringPosts
  vyperTypeSystem vyperTypeInvariants vyperInterpreter vyperState vyperAST
  list finite_map

Theorem annassign_other_full_code_parts:
  compile_stmt ce lctx ret_ty (AnnAssign id typ e) r = ((),sf) /\
  compile_stmt ce lctx ret_ty (AnnAssign id typ (gas_shadow_expr e)) shadow_r =
    ((),shadow_sf) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  ~is_word_type typ /\ ~(has_length_word typ /\ is_empty_value_expr e) /\
  gas_shadow_state r shadow_r ==>
  ?a m b vv op shadow_a shadow_m shadow_b.
    emit_inst ALLOCA [Lit (n2w sz)] [p] r = ((),a) /\
    compile_expr ce (expr_type e) e a = (vv,m) /\
    unwrap_value ce vv m = (op,b) /\
    lower_value compile_expr ce (expr_type e) e a = (op,b) /\
    compile_assign_value ce (Var p) LocMemory op F (vv_location vv)
      typ (lowered_value_type ce e) (type_memory_bytes ce typ) b = ((),sf) /\
    emit_inst ALLOCA [Lit (n2w sz)] [p] shadow_r = ((),shadow_a) /\
    compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_a = (vv,shadow_m) /\
    unwrap_value ce vv shadow_m = (op,shadow_b) /\
    lower_value compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_a =
      (op,shadow_b) /\
    compile_assign_value ce (Var p) LocMemory op F (vv_location vv)
      typ (lowered_value_type ce e) (type_memory_bytes ce typ) shadow_b =
      ((),shadow_sf) /\
    gas_shadow_state a shadow_a /\ gas_shadow_state m shadow_m /\
    gas_shadow_state b shadow_b
Proof
  strip_tac >>
  drule_all annassign_memory_lowering_parts_ptr >>
  disch_then (qx_choosel_then [`a`,`m`,`b`,`vv`,`op`] strip_assume_tac) >>
  `~(has_length_word typ /\ is_empty_value_expr (gas_shadow_expr e))` by gvs[] >>
  drule_all (Q.INST [`e` |-> `gas_shadow_expr e`]
    (SPEC_ALL annassign_memory_lowering_parts_ptr)) >>
  simp[gas_shadow_expr_type, gasShadowCompilePureTheory.gas_shadow_lowered_value_type] >>
  disch_then (qx_choosel_then
    [`shadow_a`,`shadow_m`,`shadow_b`,`shadow_vv`,`shadow_op`] strip_assume_tac) >>
  `gas_shadow_state a shadow_a` by
    (mp_tac (Q.INST [`opc` |-> `ALLOCA`, `ops` |-> `[Lit (n2w sz)]`,
       `outs` |-> `[p]`] gasShadowStateTheory.gas_shadow_compiles_emit_inst) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`r`,`shadow_r`] mp_tac) >> simp[]) >>
  `shadow_vv = vv /\ gas_shadow_state m shadow_m` by
    (mp_tac (Q.INST [`cenv` |-> `ce`, `ty` |-> `expr_type e`, `e` |-> `e`]
       gas_shadow_stmt_compile_expr) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`a`,`shadow_a`] mp_tac) >> simp[]) >>
  qpat_x_assum `shadow_vv = vv` SUBST_ALL_TAC >>
  `shadow_op = op /\ gas_shadow_state b shadow_b` by
    (mp_tac (Q.INST [`cenv` |-> `ce`, `vv` |-> `vv`]
       gasShadowCompileConvertTheory.gas_shadow_compiles_unwrap_value) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`m`,`shadow_m`] mp_tac) >> simp[]) >> gvs[] >>
  metis_tac[]
QED

Theorem annassign_other_full_layout:
  expr_body_pre ce cx env e es /\
  type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
  ~is_word_type typ /\ ~is_bytestring_type typ ==>
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  ~is_word_type (lowered_value_type ce e) /\
  ~is_bytestring_type (lowered_value_type ce e) /\
  post_value_type ce e = lowered_value_type ce e /\
  type_widens_to (get_tenv cx) (expr_type e) typ /\
  type_widens_to (get_tenv cx) (lowered_value_type ce e) typ /\
  ?stv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `type_widens_to (get_tenv cx) (expr_type e) typ` by
    gvs[type_stmt_def, AllCaseEqs()] >>
  drule expr_body_pre_physical_type >> strip_tac >>
  `type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e)` by
    (simp[type_widens_to_def] >>
     drule expr_body_pre_type_evaluates >> simp[well_formed_type_def]) >>
  `type_widens_to (get_tenv cx) (lowered_value_type ce e) typ` by
    metis_tac[assignRelayoutCallerTheory.type_widens_to_trans] >>
  `~is_word_type (expr_type e) /\ ~is_word_type (lowered_value_type ce e)` by
    metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq] >>
  `~is_bytestring_type (expr_type e) /\
   ~is_bytestring_type (lowered_value_type ce e)` by
    metis_tac[typedMemoryCopyTheory.type_widens_from_bytestring] >>
  `post_value_type ce e = lowered_value_type ce e` by
    metis_tac[abiEncodeMaterializeTheory.materialize_post_lowered_classify] >>
  simp[] >> metis_tac[]
QED

Theorem annassign_other_full_value_ready:
  expr_body_pre ce cx env e es /\ supported_expr tops e /\
  ce.ce_func_return_type = build_func_return_type tops /\
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
  ~is_word_type typ /\ ~is_bytestring_type typ /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  type_memory_bytes ce typ < 2 ** 64 ==>
  ?stv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    post_value_type ce e = lowered_value_type ce e /\
    ~is_word_type (expr_type e) /\ ~is_word_type (lowered_value_type ce e) /\
    ~is_bytestring_type (lowered_value_type ce e) /\
    type_widens_to (get_tenv cx) (expr_type e) typ /\
    type_widens_to (get_tenv cx) (lowered_value_type ce e) typ /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
    type_memory_bytes ce typ = type_memory_size tyv /\
    type_memory_bytes ce (lowered_value_type ce e) <= type_memory_bytes ce typ /\
    type_memory_size stv < dimword (:256) /\
    (!gs v es'. bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := gs) = (INL v,es') ==>
      value_has_type stv v /\ value_has_type tyv v /\
      val_wf stv v /\ val_wf tyv v /\
      val_footprint stv v = type_memory_size stv)
Proof
  strip_tac >> drule_all annassign_other_full_layout >> strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  drule_all annassignRelayoutSourceTheory.widening_memory_layout_bound >>
  strip_tac >> qexists_tac `stv` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule annassignRelayoutSourceTheory.annassign_relayout_read_layout >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem annassign_other_full_code_frame[local]:
  declare_local cenv id typ sa = (ce,r) /\ cenv.ce_alloca_locals /\
  local_ptrs_reserved cenv sa /\
  compile_stmt ce lctx ret_ty (AnnAssign id typ e) r = ((),sf) /\
  emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv typ))]
    [STRING #"%" (toString sa.cs_next_var)] r = ((),a) /\
  compile_expr ce (expr_type e) e a = (vv,m) /\ unwrap_value ce vv m = (op,b) /\
  compile_assign_value ce (Var p) LocMemory op F (vv_location vv)
    typ (lowered_value_type ce e) (type_memory_bytes ce typ) b = ((),sf) /\
  fn_has_code r sf func ==>
  ci_mono a m /\ ci_mono m b /\ ci_mono b sf /\
  local_ptrs_reserved ce r /\ local_ptrs_reserved ce a /\
  local_ptrs_reserved ce m /\ local_ptrs_reserved ce b /\
  not_fresh_at a (STRING #"%" (toString sa.cs_next_var)) /\
  cs_extends r a /\ fn_has_code r a func /\
  fn_has_code a m func /\ fn_has_code m b func /\ fn_has_code b sf func /\
  MEM (mk_inst r.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv typ))]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  strip_tac >>
  `ci_mono a m` by (drule (cj 1 compile_expr_grows) >> simp[ci_mono_def]) >>
  `ci_mono m b` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  `ci_mono b sf` by metis_tac[cj 1 ci_mono_stmt_helpers, pairTheory.SND] >>
  `cs_extends a sf /\ cs_extends a m /\ cs_extends m b /\ cs_extends b sf` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  drule_all stmtSimDeclMemTheory.annassign_alloca_code >> strip_tac >>
  `cs_extends m sf` by metis_tac[cs_extends_trans] >>
  `fn_has_code a m func /\ fn_has_code m sf func` by
    (irule fragExecTheory.fn_has_code_split >> simp[]) >>
  `fn_has_code m b func /\ fn_has_code b sf func` by
    (irule fragExecTheory.fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved ce m /\ local_ptrs_reserved ce b` by
    (fs[ci_mono_def] >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
               arithmeticTheory.LESS_EQ_TRANS]) >> simp[]
QED

Theorem annassign_other_full_declared_layout:
  declare_local old id typ sa = (ce,r) /\
  declare_local old id typ shadow_sa = (ce,shadow_r) /\
  old.ce_alloca_locals /\ local_ptrs_reserved old sa /\
  gas_shadow_state sa shadow_sa /\
  compile_stmt ce lctx ret_ty (AnnAssign id typ e) r = ((),sf) /\
  compile_stmt ce lctx ret_ty (AnnAssign id typ (gas_shadow_expr e)) shadow_r = ((),shadow_sf) /\
  fn_has_code sa sf func /\ fn_has_code shadow_sa shadow_sf shadow_func /\
  ~is_word_type typ /\ ~(has_length_word typ /\ is_empty_value_expr e) ==>
  ?p a m b vv op shadow_a shadow_m shadow_b.
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes old typ)) /\
    (!n. n <> id ==> FLOOKUP ce.ce_vars n = FLOOKUP old.ce_vars n) /\
    ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
      ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
    emit_inst ALLOCA [Lit (n2w (type_memory_bytes old typ))] [p] r = ((),a) /\
    compile_expr ce (expr_type e) e a = (vv,m) /\ unwrap_value ce vv m = (op,b) /\
    lower_value compile_expr ce (expr_type e) e a = (op,b) /\
    compile_assign_value ce (Var p) LocMemory op F (vv_location vv)
      typ (lowered_value_type ce e) (type_memory_bytes ce typ) b = ((),sf) /\
    lower_value compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_a = (op,shadow_b) /\
    gas_shadow_state a shadow_a /\ gas_shadow_state b shadow_b /\
    ci_mono a m /\ ci_mono m b /\ ci_mono b sf /\
    local_ptrs_reserved ce a /\ local_ptrs_reserved ce b /\ not_fresh_at a p /\
    fn_has_code a b func /\ fn_has_code b sf func /\
    fn_has_code shadow_a shadow_b shadow_func /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes old typ))] [p]) (fn_insts func) /\
    compile_alloc_buffer (type_memory_bytes old typ) sa =
      (<|buf_operand := Var p; buf_size := type_memory_bytes old typ|>,a) /\
    cs_extends sa a /\ fn_has_code sa a func /\ sa.cs_next_var <= a.cs_next_var
Proof
  strip_tac >>
  qpat_assum `declare_local old id typ sa = _` (mp_then Any mp_tac declare_local_ptr) >>
  simp[] >> strip_tac >>
  `fn_has_code r sf func /\ fn_has_code shadow_r shadow_sf shadow_func` by
    (drule_all (Q.INST [`st` |-> `shadow_sa`] (SPEC_ALL declare_local_ptr)) >> strip_tac >>
     fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def]) >>
  `gas_shadow_state r shadow_r` by
    (mp_tac (Q.INST [`cenv` |-> `old`, `ty` |-> `typ`] gas_shadow_compiles_declare_local) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  drule_all annassign_other_full_code_parts >> strip_tac >>
  drule_all annassign_other_full_code_frame >> strip_tac >>
  `ci_mono shadow_a shadow_m /\ ci_mono shadow_m shadow_b /\ ci_mono shadow_b shadow_sf` by
    metis_tac[cj 1 compile_expr_grows, ci_mono_unwrap_value,
      cj 1 ci_mono_stmt_helpers, pairTheory.SND, ci_mono_def] >>
  `cs_extends a b /\ cs_extends shadow_a shadow_b /\ cs_extends shadow_b shadow_sf /\
   cs_extends shadow_r shadow_a` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, fragExecTheory.cs_extends_emit_inst]) >>
  `fn_has_code a b func` by
    (irule (cj 2 fragExecTheory.fn_has_code_split) >>
     metis_tac[cs_extends_trans, ci_mono_def, fragExecTheory.fn_has_code_split]) >>
  `fn_has_code shadow_a shadow_sf shadow_func` by
    (irule (cj 2 fragExecTheory.fn_has_code_split) >>
     conj_tac >- metis_tac[cs_extends_trans] >> qexists_tac `shadow_r` >> simp[]) >>
  `fn_has_code shadow_a shadow_b shadow_func` by
    (irule (cj 1 fragExecTheory.fn_has_code_split) >> simp[] >> qexists_tac `shadow_sf` >> simp[]) >>
  `compile_alloc_buffer (type_memory_bytes old typ) sa =
      (<|buf_operand := Var (STRING #"%" (toString sa.cs_next_var));
         buf_size := type_memory_bytes old typ|>,a)` by
    (qpat_x_assum `emit_inst ALLOCA _ _ r = _` mp_tac >>
     qpat_x_assum `r = _` SUBST1_TAC >>
     simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
          emitHelperTheory.emit_inst_def, fresh_id_def, fresh_var_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          pairTheory.pair_case_thm] >> strip_tac >> gvs[]) >>
  `cs_extends sa a /\ sa.cs_next_var <= a.cs_next_var` by
    (drule loweringHaltTheory.compile_alloc_buffer_extends >> strip_tac >>
     drule loweringHaltTheory.compile_alloc_buffer_parts >> simp[]) >>
  `fn_has_code sa a func` by
    (irule (cj 1 fragExecTheory.fn_has_code_split) >> simp[] >>
     qexists_tac `sf` >> simp[] >> fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  qexistsl_tac [`a`,`m`,`b`,`vv`,`op`,`shadow_a`,`shadow_b`] >> gvs[]
QED
