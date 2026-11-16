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
  list finite_map exprSimAbiEncodePrefixWindow annassignRelayoutPost stmtSimDeclSource bodyFullMemoryValue bodyFullAnnAssignMemoryPost bodyFullMemoryFrames gasOutcomeFull fragGasOriginPtr freshWrites bodySim exprOperandVar exprSimTypedAlloc stmtSimDeclSourceSeparation bodyPtrDefs venomState bodyFullAnnAssignReserve contextRawReachable ptrDiscipline unitMemInv decoderGhostFramePtr bodyMemBopRestWordPath fragGasOrigin bodyMemoryDefs stmtSimDecl

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

Theorem annassign_other_full_rhs_layout:
  expr_body_pre ce cx env e es /\
  type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
  ~is_word_type typ /\ ~is_bytestring_type typ /\
  expr_post (H:(bool # bytes32 # type_value) list # num list)
    ctx func ce cx e es sa sb s0 ee v op s /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv ==>
  expr_val_at ce cx (lowered_value_type ce e) sa sb ee v op s /\
  (!w. eval_operand op s = SOME w ==>
    type_memory_size stv = 0 \/
    w2n w + type_memory_size stv <= s.vs_alloca_next)
Proof
  strip_tac >> drule_all annassign_other_full_layout >> strip_tac >>
  conj_tac >- gvs[expr_post_def] >>
  rpt strip_tac >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[annassignRelayoutSourceTheory.nonbytes_evaluated_val_footprint] >>
  metis_tac[exprSimAbiEncodePrefixWindowTheory.abi_encode_nonword_expr_bound]
QED

Theorem annassign_other_full_source_positive:
  expr_body_pre ce cx env e es /\
  type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
  ~is_word_type typ /\ ~is_bytestring_type typ /\ expr_type e <> typ /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv ==>
  0 < type_memory_size stv
Proof
  strip_tac >> drule_all annassign_other_full_layout >> strip_tac >>
  drule expr_body_pre_physical_type >> strip_tac >>
  Cases_on `type_memory_size stv = 0` >> simp[] >>
  `lowered_value_type ce e = expr_type e` by
    metis_tac[cj 1 annassignRelayoutPostTheory.arg_type_fits_zero_size_rigid] >>
  metis_tac[annassignRelayoutPostTheory.strict_widening_source_positive,
            arithmeticTheory.NOT_ZERO_LT_ZERO]
QED

Theorem annassign_other_full_store_ready:
  expr_body_pre ce cx env e es /\
  type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
  ~is_word_type typ /\ ~is_bytestring_type typ /\
  expr_post H ctx func ce cx e es a b s0 ee v op s /\
  lower_value compile_expr ce (expr_type e) e a = (op,b) /\
  local_ptrs_reserved ce a /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
  0 < type_memory_size stv /\
  ptr_val_ok cx (post_value_type ce e) v op G tn s /\
  ptr_buf_ok ce e op G s /\
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [p] /\ not_local_ptr ce ee.scopes p /\
  inst.inst_id < a.cs_next_id /\ a.cs_next_id <= b.cs_next_id /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,cap) /\
  type_memory_size dtv <= cap ==>
  inst.inst_id <> b.cs_next_id /\
  ?xs sw. op = Var xs /\ not_fresh_at b xs /\ lookup_var xs s = SOME sw /\
    ptr_covers G tn xs s (type_memory_size stv) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory stv v (w2n sw) mem) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw)
Proof
  strip_tac >> drule_all annassign_other_full_layout >> strip_tac >>
  `expr_val_at ce cx (lowered_value_type ce e) a b ee v op s /\
   stmt_state_rel H ctx func ce cx ee s` by fs[expr_post_def] >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[annassignRelayoutSourceTheory.nonbytes_evaluated_val_footprint] >>
  `?sw. eval_operand op s = SOME sw` by
    (fs[loweringPostsTheory.expr_val_at_def] >> metis_tac[]) >>
  `?xs base sz. op = Var xs /\ FLOOKUP G xs = SOME (base,sz) /\
    base <= w2n sw /\ w2n sw + type_memory_size stv <= base + sz` by
    (`type_memory_bytes ce (lowered_value_type ce e) <> 0` by decide_tac >>
     fs[bodyPtrDefsTheory.ptr_buf_ok_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  gvs[venomStateTheory.eval_operand_def] >>
  `not_fresh_at b xs` by metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `ptr_covers G tn xs s (type_memory_size stv)` by
    (fs[bodyPtrDefsTheory.ptr_covers_def,bodyPtrDefsTheory.ptr_val_ok_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem` by
    (fs[bodyPtrDefsTheory.ptr_val_ok_def,bodyPtrDefsTheory.ptr_mem_ok_def,
        venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    metis_tac[exprSimTypedAllocTheory.expr_val_at_bound,venomStateTheory.eval_operand_def] >>
  `w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + cap <= w2n sw` by
    (`eval_operand (Var xs) s = SOME sw /\ 0 < val_footprint stv v` by
       simp[venomStateTheory.eval_operand_def] >>
     metis_tac[stmtSimDeclSourceSeparationTheory.expr_val_at_alloca_outside_interval_separate]) >>
  simp[] >> decide_tac
QED

Theorem annassign_other_full_operational_packet:
  expr_body_pre ce cx env e es /\ supported_expr tops e /\
  body_inv tops ctx ce cx /\
  type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
  ~is_word_type typ /\ ~is_bytestring_type typ /\ expr_type e <> typ /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  type_memory_bytes ce typ < 2 ** 64 /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  lower_value compile_expr ce (expr_type e) e a = (op,b) /\
  compile_assign_value ce (Var p) LocMemory op F loc
    typ (lowered_value_type ce e) (type_memory_bytes ce typ) b = ((),sf) /\
  (loc = NONE \/ loc = SOME LocMemory) /\
  expr_post H0 ctx func ce cx e es a b s0 ee v op s /\
  valid_horizon cx st0 H0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  ptr_val_ok cx (post_value_type ce e) v op G tn s /\ ptr_buf_ok ce e op G s /\
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  inst.inst_id < a.cs_next_id /\ a.cs_next_id <= b.cs_next_id /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) cap) /\
  not_local_ptr ce ee.scopes p /\ lookup_var p s = SOME dw /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,cap) /\
  (!q. q = p \/ ~not_local_ptr ce ee.scopes q ==> not_fresh_at b q) /\
  local_ptrs_reserved ce a /\ local_ptrs_reserved ce b /\ ptr_covers G tn p s cap /\
  type_memory_size tyv <= cap /\ lo <= w2n dw /\
  w2n dw + type_memory_size tyv < dimword (:256) /\
  w2n dw + type_memory_size tyv <= s.vs_alloca_next /\
  (!src. eval_operand op s = SOME src ==> type_memory_size stv = 0 \/
    w2n src + type_memory_size stv <= s.vs_alloca_next) /\
  ~ctx_has_dalloca ctx /\ fn_has_code b sf func /\ alloca_history func s /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  ~s.vs_halted /\ s.vs_current_bb = b.cs_current_bb /\
  s.vs_inst_idx = LENGTH b.cs_current_insts ==>
  value_has_type tyv v /\ val_wf tyv v /\ ?t Gf tf u Gu tu k.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    (!H : (bool # 256 word # type_value) list # num list.
      stmt_state_rel H ctx func ce cx ee s ==> stmt_state_rel H ctx func ce cx ee u) /\
    (!D d. ghost_inv_at D lo d ce cx ee G tn s ==> ghost_inv_at D lo d ce cx ee Gu tu u) /\
    typed_copy_state_frame k (w2n dw) (type_memory_size tyv) u t /\
    val_in_memory tyv v (w2n dw) t.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==> val_in_memory tyv v (w2n dw) mem) /\
    tf.t_stor = tu.t_stor /\ tf.t_trans = tu.t_trans /\ tf.t_imm = tu.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size tyv) ==> (i IN tf.t_mem <=> i IN tu.t_mem)) /\
    (!x. not_fresh_at k x ==> lookup_var x t = lookup_var x u /\ FLOOKUP Gf x = FLOOKUP Gu x /\ op_taint tf (Var x) = op_taint tu (Var x)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK t,Gf,tf)) /\
    fn_has_code k sf func /\ ci_mono b k /\ local_ptrs_reserved ce k /\ lookup_var p u = SOME dw /\
    ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
    (!x. not_fresh_at b x ==> lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qmatch_goalsub_abbrev_tac `value_has_type tyv v /\ val_wf tyv v /\ packet` >>
  `ce.ce_func_return_type = build_func_return_type tops /\
   supported_program tops /\ get_module_code cx NONE = SOME tops /\
   acyclic_struct_metadata ce.ce_struct_fields` by fs[body_inv_def] >>
  drule_all annassign_other_full_value_ready >> strip_tac >>
  drule_all annassign_other_full_source_positive >> strip_tac >> gnvs[] >>
  `ptr_val_ok cx (post_value_type ce e) v op G tn s` by simp[] >>
  drule_all annassign_other_full_store_ready >> strip_tac >> gnvs[] >>
  `stmt_state_rel H0 ctx func ce cx ee s /\
   ghost_inv_at (DF H0) lo d ce cx ee G tn s` by metis_tac[] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `ptr_covers G tn p s (type_memory_size tyv)` by
    (gvs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
       arithmeticTheory.LESS_EQ_LESS_EQ_MONO]) >>
  `expr_val_at ce cx (lowered_value_type ce e) a b ee v (Var xs) s` by
    (drule_all annassign_other_full_rhs_layout >> simp[]) >>
  `value_has_type stv v /\ value_has_type tyv v /\ val_wf stv v /\ val_wf tyv v` by
    metis_tac[] >>
  `not_fresh_at b p` by metis_tac[] >>
  `type_memory_size stv < dimword (:256) /\
   w2n sw + type_memory_size stv < dimword (:256) /\
   w2n sw + type_memory_size stv <= s.vs_alloca_next` by
    (fs[venomStateTheory.eval_operand_def] >> decide_tac) >>
  `type_memory_size tyv + w2n dw < dimword (:256)` by decide_tac >>
  simp[Abbr `packet`] >>
  irule (SRULE [arithmeticTheory.ADD_COMM]
    (INST_TYPE [``:'a`` |-> ``:256``] body_full_memory_value_path)) >>
  asm_rewrite_tac[] >>
  (conj_tac >- (disj2_tac >> qexistsl_tac [`inst.inst_id`,`cap`] >>
    simp[] >> decide_tac)) >>
  (conj_tac >- (qexists_tac `H0` >> first_assum ACCEPT_TAC)) >>
  qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem annassign_other_full_install:
  gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK t,Gf,tf) /\
  typed_copy_state_frame k (w2n dw) (type_memory_size tyv) u t /\
  ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
  t.vs_inst_idx = LENGTH sf.cs_current_insts /\
  stmt_state_rel H ctx func ce cx ee u /\ ghost_inv_at D lo d ce cx ee Gu tu u /\
  fn_inst_ids_distinct func /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) cap) /\
  not_local_ptr ce ee.scopes p /\ lookup_var p s = SOME dw /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,cap) /\
  (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
  (!q. q = p \/ ~not_local_ptr ce ee.scopes q ==> not_fresh_at b q) /\
  ci_mono b k /\ local_ptrs_reserved ce k /\ ptr_covers G tn p s cap /\
  type_memory_size tyv <= cap /\ lo <= w2n dw /\
  val_wf tyv v /\ value_has_type tyv v /\
  val_in_memory tyv v (w2n dw) t.vs_memory /\
  (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
    val_in_memory tyv v (w2n dw) mem) /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at k x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at k x) /\
  (!x. not_fresh_at b x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!x. not_fresh_at k x ==> lookup_var x t = lookup_var x u /\
    FLOOKUP Gf x = FLOOKUP Gu x /\ op_taint tf (Var x) = op_taint tu (Var x)) /\
  tf.t_stor = tu.t_stor /\ tf.t_trans = tu.t_trans /\ tf.t_imm = tu.t_imm /\
  (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size tyv) ==>
    (i IN tf.t_mem <=> i IN tu.t_mem)) ==>
  ?ff. new_variable id tyv v ee = (INL (),ff) /\
    stmt_state_rel H ctx func ce cx ff t /\ ghost_inv_at D lo d ce cx ff Gf tf t
Proof
  strip_tac >> drule_all stmtSimDeclSourceTheory.annassign_continuation_success >> strip_tac >>
  `!q. not_fresh_at b q ==> not_fresh_at k q` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     goal_assum (drule_at Any) >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `not_fresh_at b p /\ not_fresh_at k p` by metis_tac[] >>
  `lookup_var p u = SOME dw /\ FLOOKUP Gu p = FLOOKUP G p /\
   op_taint tu (Var p) = op_taint tn (Var p)` by metis_tac[] >>
  `ptr_covers Gu tu p u cap` by gvs[bodyPtrDefsTheory.ptr_covers_def] >>
  `u.vs_allocas = t.vs_allocas` by
    fs[typedMemoryCopyTheory.typed_copy_state_frame_def,
       venomStateTheory.venom_state_component_equality] >>
  `FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n dw,cap)` by metis_tac[] >>
  `!q. q = p \/ ~not_local_ptr ce ee.scopes q ==> not_fresh_at k q` by metis_tac[] >>
  qexists_tac `ee with scopes :=
    (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>)) :: rest` >>
  simp[] >> irule bodyFullAnnAssignMemoryPostTheory.body_full_annassign_memory_post >>
  simp[] >> rpt (first_assum (irule_at Any)) >> simp[] >>
  qexists_tac `sf` >> gvs[bodyPtrDefsTheory.mem_agree_outside_def] >>
  first_assum ACCEPT_TAC
QED

Theorem annassign_other_full_continuation:
  expr_body_pre ce cx env e es /\ supported_expr tops e /\
  body_inv tops ctx ce cx /\
  type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
  ~is_word_type typ /\ ~is_bytestring_type typ /\ expr_type e <> typ /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  type_memory_bytes ce typ < 2 ** 64 /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  lower_value compile_expr ce (expr_type e) e a = (op,b) /\
  compile_assign_value ce (Var p) LocMemory op F loc
    typ (lowered_value_type ce e) (type_memory_bytes ce typ) b = ((),sf) /\
  (loc = NONE \/ loc = SOME LocMemory) /\
  expr_post H0 ctx func ce cx e es a b s0 ee v op s /\
  valid_horizon cx st0 H0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  ptr_val_ok cx (post_value_type ce e) v op G tn s /\ ptr_buf_ok ce e op G s /\
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  inst.inst_id < a.cs_next_id /\ a.cs_next_id <= b.cs_next_id /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) cap) /\
  not_local_ptr ce ee.scopes p /\ lookup_var p s = SOME dw /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,cap) /\
  (!q. q = p \/ ~not_local_ptr ce ee.scopes q ==> not_fresh_at b q) /\
  local_ptrs_reserved ce a /\ local_ptrs_reserved ce b /\ ptr_covers G tn p s cap /\
  type_memory_size tyv <= cap /\ lo <= w2n dw /\
  w2n dw + type_memory_size tyv < dimword (:256) /\
  w2n dw + type_memory_size tyv <= s.vs_alloca_next /\
  (!src. eval_operand op s = SOME src ==> type_memory_size stv = 0 \/
    w2n src + type_memory_size stv <= s.vs_alloca_next) /\
  ~ctx_has_dalloca ctx /\ fn_has_code b sf func /\ alloca_history func s /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  ~s.vs_halted /\ s.vs_current_bb = b.cs_current_bb /\
  s.vs_inst_idx = LENGTH b.cs_current_insts ==>
  ?t Gf tf ff.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    new_variable id tyv v ee = (INL (),ff) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ff t /\
      ghost_inv_at (DF H) lo d ce cx ff Gf tf t) /\
    ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
    (!x. not_fresh_at b x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all annassign_other_full_operational_packet >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  drule_all stmtSimDeclSourceTheory.annassign_continuation_success >> strip_tac >>
  qexistsl_tac [`t`,`Gf`,`tf`,
    `ee with scopes := (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>)) :: rest`] >>
  asm_rewrite_tac[] >>
  qx_gen_tac `H` >> strip_tac >>
  `stmt_state_rel H ctx func ce cx ee u /\ ghost_inv_at (DF H) lo d ce cx ee Gu tu u` by metis_tac[] >>
  `!x. not_fresh_at b x ==> not_fresh_at k x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     goal_assum (drule_at Any) >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `(!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at k x) /\
   (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at k x)` by metis_tac[] >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK t,Gf,tf)` by simp[] >>
  drule_all annassign_other_full_install >> strip_tac >> gvs[]
QED

Theorem annassign_other_full_rhs:
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es /\
  lower_value compile_expr ce (expr_type e) e a = (op,b) /\
  lower_value compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_a = (op,shadow_b) /\
  gas_shadow_state a shadow_a /\ gas_shadow_state b shadow_b /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code a b func /\ fn_has_code shadow_a shadow_b shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce a /\ ~ctx_has_dalloca ctx /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d ce a t /\ alloca_history func t /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es t /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es G tn t) /\
  ~t.vs_halted /\ t.vs_current_bb = a.cs_current_bb /\
  t.vs_inst_idx = LENGTH a.cs_current_insts /\
  expr_body_pre ce cx env e es /\
  type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
  ~is_word_type typ /\ ~is_bytestring_type typ /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
  lookup_var p t = SOME w /\ ptr_covers G tn p t n /\ not_fresh_at a p /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,n) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,t,G,tn)
    (\H res ee Gf tnf u. ?v. res = INL v /\
      expr_post H ctx func ce cx e es a b t ee v op u /\
      expr_val_at ce cx (lowered_value_type ce e) a b ee v op u /\
      (!src. eval_operand op u = SOME src ==> type_memory_size stv = 0 \/
        w2n src + type_memory_size stv <= u.vs_alloca_next) /\
      u.vs_current_bb = b.cs_current_bb /\
      u.vs_inst_idx = LENGTH b.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d ce cx ee Gf tnf u /\
      ptr_val_ok cx (post_value_type ce e) v op Gf tnf u /\
      ptr_buf_ok ce e op Gf u /\
      ghost_kept_at lo ce es a G tn t Gf tnf /\
      lookup_var p u = SOME w /\ ptr_covers Gf tnf p u n /\
      FLOOKUP u.vs_allocas aid = SOME (w2n w,n))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  `!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_no_wrap inst s` by
    (rpt strip_tac >> drule_all frag_reachable_members >> strip_tac >>
     qpat_assum `~ctx_has_dalloca ctx`
       (mp_tac o REWRITE_RULE [ctx_has_dalloca_def, listTheory.EXISTS_MEM]) >>
     simp[dalloca_no_wrap_def] >> metis_tac[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `a`, `b`, `shadow_a`, `shadow_b`,
    `op`, `t`, `G`, `tn`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  irule gas_outcome_full_post_mono >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  rename1 `expr_post _ _ _ _ _ _ _ _ _ _ ee v op u` >>
  rename1 `ghost_kept_at lo ce es a G tn t Gf tnf` >>
  drule_all annassign_other_full_rhs_layout >> strip_tac >>
  drule_all annassign_other_full_layout >> strip_tac >>
  `lookup_var p u = SOME w /\
   FLOOKUP u.vs_allocas aid = SOME (w2n w,n)` by
    (fs[loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
  `ptr_covers Gf tnf p u n` by
    (irule ptr_covers_frame >> goal_assum (drule_at Any) >>
     fs[bodyPtrDefsTheory.ghost_kept_at_def]) >>
  qexists_tac `v` >> simp[] >>
  qpat_x_assum `!src. eval_operand op u = SOME src ==> _` mp_tac >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem annassign_other_full_alloc_rhs:
  declare_local old id typ sa = (ce,r) /\ old.ce_alloca_locals /\
  FLOOKUP old.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE /\
  compile_alloc_buffer n sa = (<|buf_operand := Var p; buf_size := n|>,a) /\
  fn_has_code sa a func /\ local_ptrs_reserved old sa /\ n < dimword (:256) /\
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es /\
  lower_value compile_expr ce (expr_type e) e a = (op,b) /\
  lower_value compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_a = (op,shadow_b) /\
  gas_shadow_state a shadow_a /\ gas_shadow_state b shadow_b /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code a b func /\ fn_has_code shadow_a shadow_b shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce a /\ ~ctx_has_dalloca ctx /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  ce.ce_return_buf = old.ce_return_buf /\ ce.ce_return_pc = old.ce_return_pc /\
  (!x sz. old.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. old.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  sa.cs_next_var <= a.cs_next_var /\
  gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
  return_buf_frame d old sa s0 /\ alloca_history func s0 /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func old cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d old cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  expr_body_pre ce cx env e es /\
  type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
  ~is_word_type typ /\ ~is_bytestring_type typ /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv ==>
  ?w t G tn.
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s0,G0,tn0) [] (OK t,G,tn)) /\
    lookup_var p t = SOME w /\ ptr_covers G tn p t n /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
    w2n w + n < dimword (:256) /\ w2n w + n <= t.vs_alloca_next /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    (!aid z. FLOOKUP s0.vs_allocas aid = SOME z ==> FLOOKUP t.vs_allocas aid = SOME z) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0 /\
      FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,t,G,tn)
      (\H res ee Gf tnf u. ?v. res = INL v /\
        expr_post H ctx func ce cx e es a b t ee v op u /\
        expr_val_at ce cx (lowered_value_type ce e) a b ee v op u /\
        (!src. eval_operand op u = SOME src ==> type_memory_size stv = 0 \/
          w2n src + type_memory_size stv <= u.vs_alloca_next) /\
        u.vs_current_bb = b.cs_current_bb /\
        u.vs_inst_idx = LENGTH b.cs_current_insts /\
        alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\
        ghost_inv_at (DF H) lo d ce cx ee Gf tnf u /\
        ptr_val_ok cx (post_value_type ce e) v op Gf tnf u /\
        ptr_buf_ok ce e op Gf u /\ ghost_kept_at lo ce es a G tn t Gf tnf /\
        lookup_var p u = SOME w /\ ptr_covers Gf tnf p u n /\
        FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,n))
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace`
    by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  drule_all (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``] bodyFullMemoryFramesTheory.body_full_alloc_buffer_path) >>
  disch_then (qspecl_then [`tn0`,`gas_explicit_sites ctx shadow_ctx`,`PG`,`G0`]
    (qx_choosel_then [`entry`,`root`,`dest_start`,`G1`,`tn1`] strip_assume_tac)) >>
  gvs[] >>
  rename1 `lookup_var p t = SOME (n2w dest_start)` >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es t /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es G1 tn1 t` by
    (qx_gen_tac `H` >> disch_tac >>
     `stmt_state_rel H ctx func old cx es t /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d old cx es G1 tn1 t` by metis_tac[] >>
     conj_tac >- (irule stmtSimDeclTheory.stmt_state_rel_declare_local_entry >>
       goal_assum (drule_at Any) >>
       qexistsl_tac [`id`,`sa`,`r`,`typ`] >> simp[]) >>
     conj_tac >- simp[] >>
     irule ghost_inv_at_declare_local_entry >> metis_tac[]) >>
  `alloca_inv s0` by metis_tac[exprLoweringPropsTheory.stmt_state_rel_def] >>
  `gas_marked_path T ctx func s0 0 (OK t)` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
      (qspec_then `DF (storage_trace_horizon es.storage_trace)` mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
     drule fragGasOriginTheory.gas_origin_path_erase >> simp[]) >>
  `alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` by
    metis_tac[bodyMemBopRestWordPathTheory.rest_word_marked_allocation_posts] >>
  `dest_start < dimword (:256)` by decide_tac >>
  `w2n (n2w dest_start : bytes32) = dest_start` by simp[wordsTheory.w2n_n2w] >>
  `dest_start + n <= t.vs_alloca_next` by
    (`stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func ce cx es t`
       by metis_tac[] >>
     fs[exprLoweringPropsTheory.stmt_state_rel_def,
        venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
     metis_tac[]) >>
  `return_buf_frame d ce a t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`n2w dest_start`,`t`,`G1`,`tn1`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x)` by
    (conj_tac >> rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[stmtSimDeclSourceTheory.annassign_admissible_rhs] >>
  `FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n (n2w dest_start : bytes32),n)` by simp[] >>
  drule_all annassign_other_full_rhs >> simp[]
QED
