(* A linked aggregate returns its word members in source order. *)
Theory bodySelectedStackReturnMods
Ancestors
  bodySelectedForcedReturnMods internalReturnStackAggregate internalReturnMemoryMem
  bodySelectedUnlockTaintMods
  bodyCopyReadPhysicalTypeMods
  stmtSimReturnWiden internalReturnMemoryInputs internalReturnMemoryFrame
  gasShadowCompileStmtHelpers typedStructMetadata typedStructMemory
  memoryValueAbiTuple valueEncodingProofs valueTypingMemoryProps
  gasOutcomeFullCompose gasOutcomeFullBindMods bodyFullShared stateRelProj vyperTypeEvalCaseProofs
  logArgumentTypeEval freshWrites compileEnv loweringPosts stmtLowering
  vyperAST vyperState vyperTypeSystem vyperTypeInvariants vyperTypeABI
  vyperTypeExprSoundness exprLowering exprLoweringProps stmtSimReturn
  fragExec loweringStateRelDefs valueEncoding valueEncodingDefs
  list rich_list finite_map pair option vyperTyping exprSimProps
  bodySim vyperTypeEvalSoundness typedCopyPtr exprBodyPreProps
  gasShadowCompileBase gasShadow gasShadowState bodyFullPostsMods exprSimHypsDefs vyperTypeCallGraph
  bodyInvSplit bodyPtrDefs venomState exprOperandVar bodyFullShadowBodyInv
  vyperStorageFootprint ptrDiscipline gasOutcome exprSimDefs

Theorem selected_stack_type_args[local]:
  ~is_word_type ty /\
  n = returns_stack_count
    (\k. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields k)) ty /\ 0 < n /\
  tys = (case ty of TupleT ts => ts
    | StructT k => MAP (FST o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string k))
    | _ => []) ==>
  LENGTH tys = n /\ EVERY is_word_type tys /\ tys <> []
Proof
  Cases_on `ty` >> simp[returns_stack_count_def, tuple_like_stack_count_def] >>
  rpt strip_tac >> gvs[COND_RAND, COND_RATOR, COND_EXPAND]
QED

Theorem selected_stack_compile[local]:
  ce.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  ce.ce_return_buf = NONE /\ 0 < ce.ce_returns_count /\
  tys = (case ty of TupleT ts => ts
    | StructT k => MAP (FST o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string k))
    | _ => []) /\ tys <> [] /\ EVERY is_word_type tys /\
  stmt_env ce lctx ty (Return (SOME e)) sa = (ce',sb) /\ fn_has_code sa sb f ==>
  ?op sm su sl elems.
    lower_value compile_expr ce ty e sa = (op,sm) /\
    compile_return_unlock ce sm = ((),su) /\
    compile_tuple_load_all ce op tys 0 su = (elems,sl) /\
    emit_inst RET (elems ++ [Var rpc]) [] sl = ((),sb) /\
    fn_has_code sa sm f /\ fn_has_code sm su f /\
    fn_has_code su sl f /\ fn_has_code sl sb f
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, Once compile_stmt_def] >>
  Cases_on `lower_value compile_expr ce ty e sa` >> simp[] >>
  rename1 `lower_value compile_expr _ _ _ _ = (op,sm)` >>
  simp[compile_internal_return_from_env_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_return_unlock ce sm` >> rename1 `_ = (u,su)` >>
  Cases_on `u` >> simp[] >>
  qpat_assum `tys = _` (rewrite_tac o single o SYM) >>
  simp[compile_internal_return_def, comp_bind_def, GSYM compile_tuple_load_all_words] >>
  Cases_on `compile_tuple_load_all ce op tys 0 su` >>
  rename1 `_ = (elems,sl)` >> simp[] >> strip_tac >> gvs[] >>
  `emit_inst RET (elems ++ [Var rpc]) [] sl = ((),sb)` by
    (Cases_on `emit_inst RET (elems ++ [Var rpc]) [] sl` >> gvs[]) >>
  simp[] >> drule compile_return_unlock_shape >> strip_tac >>
  `cs_extends sa sm` by metis_tac[compile_expr_grows] >>
  `cs_extends su sl` by metis_tac[compile_tuple_load_all_grows] >>
  `cs_extends sl sb` by metis_tac[cs_extends_emit_inst] >>
  metis_tac[fn_has_code_split, cs_extends_trans]
QED

Theorem selected_stack_layout[local]:
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ ~is_word_type ty /\
  tys <> [] /\
  tys = (case ty of TupleT ts => ts
    | StructT k => MAP (FST o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string k))
    | _ => []) ==>
  ?tvs vs.
    LIST_REL (\t rt. evaluate_type tenv t = SOME rt) tys tvs /\
    values_have_types tvs vs /\ type_memory_size_list tvs = type_memory_size tv /\
    val_store_size tv v = type_memory_size tv /\
    (!a mem. val_in_memory tv v a mem <=> tuple_in_memory vs tvs a mem) /\
    intret_vals_match tv v (MAP (\(rt,x). typed_val_to_w256 rt x) (ZIP (tvs,vs)))
Proof
  strip_tac >> Cases_on `ty` >> gvs[]
  >- (drule_all tuple_type_value >> strip_tac >>
      qexistsl [`tvs`,`vs`] >>
      gvs[val_in_memory_def, type_memory_size_def, val_store_size_def, intret_vals_match_def]) >>
  rename1 `evaluate_type tenv (StructT nsid) = SOME tv` >>
  drule evaluate_type_struct_fields >> strip_tac >>
  drule (cj 2 evaluate_type_mono) >> strip_tac >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  `MAP (FST o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) =
     MAP SND args` by
    (qpat_assum `sfields_tenv_consistent _ _`
       (mp_tac o cj 1 o REWRITE_RULE [sfields_tenv_consistent_def]) >>
     disch_then drule >> strip_tac >> simp[get_struct_fields_def]) >>
  `LENGTH (MAP FST args) = LENGTH tvs` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  qpat_x_assum `tv = StructTV _` SUBST_ALL_TAC >>
  drule typed_struct_value_cases >> strip_tac >>
  drule struct_has_type_values_have_types >> strip_tac >>
  qexistsl [`tvs`,`MAP SND fields`] >>
  gvs[val_in_memory_def, fields_in_memory_tuple, MAP_ZIP,
      type_memory_size_def, type_memory_size_fields_list, val_store_size_def,
      intret_vals_match_def]
QED

Theorem selected_stack_operand_type[local]:
  expr_sim_inv_mods mods ce cx env es /\
  IS_SOME (type_stmt env ty (Return (SOME e))) /\
  0 < returns_stack_count sft ty ==>
  well_typed_expr env e /\ expr_type e = ty /\ lowered_value_type ce e = ty /\
  post_value_type ce e = ty
Proof
  simp[type_stmt_return_some_iff] >> strip_tac >>
  `expr_type e = ty` by metis_tac[stack_return_widens_eq] >>
  `well_formed_type env.type_defs (expr_type e)` by
    metis_tac[expr_sim_inv_mods_env, checked_expr_type_well_formed] >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    (drule_all copy_lowered_fits_mods >> simp[]) >>
  `type_widens_to env.type_defs (lowered_value_type ce e) ty` by metis_tac[type_widens_to_def] >>
  `lowered_value_type ce e = ty` by metis_tac[stack_return_widens_eq] >>
  simp[] >> metis_tac[post_value_type_lowered]
QED

Theorem selected_stack_value_typed[local]:
  expr_sim_inv_mods mods ce cx env es /\ well_typed_expr env e /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
  value_has_type tv v
Proof
  strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_mods_def, env_consistent_def, env_context_consistent_def] >>
  `value_runtime_typed env (expr_type e) v` suffices_by simp[value_runtime_typed_def] >>
  `env_consistent env cx (es with gas_obs := gs) /\
   state_well_typed (es with gas_obs := gs) /\
   accounts_well_typed (es with gas_obs := gs).accounts /\
   context_well_typed cx /\ functions_well_typed cx /\
   call_evaluation_safe cx (int_calls_expr e)` by
    (fs[expr_sim_inv_mods_def, state_well_typed_def, env_consistent_def,
        env_scopes_consistent_def, env_immutables_consistent_def, int_calls_stmt_def,
        int_calls_expr_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) eval_expr_read_type_sound) >> simp[]
QED

Theorem selected_stack_compile_cut[local]:
  ce.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  ce.ce_return_buf = NONE /\ 0 < ce.ce_returns_count /\
  tys = (case ty of TupleT ts => ts
    | StructT k => MAP (FST o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string k))
    | _ => []) /\ tys <> [] /\ EVERY is_word_type tys /\
  stmt_env ce lctx ty (Return (SOME e)) sa = (ce',sb) /\
  stmt_env (gas_shadow_env T ce) lctx ty (Return (SOME (gas_shadow_expr e))) sha =
    (gas_shadow_env T ce',shb) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb f /\ fn_has_code sha shb sf ==>
  ?op sm shm su sl elems.
    lower_value compile_expr ce ty e sa = (op,sm) /\
    lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha = (op,shm) /\
    gas_shadow_state sm shm /\ fn_has_code sa sm f /\ fn_has_code sha shm sf /\
    compile_return_unlock ce sm = ((),su) /\
    compile_tuple_load_all ce op tys 0 su = (elems,sl) /\
    emit_inst RET (elems ++ [Var rpc]) [] sl = ((),sb) /\
    fn_has_code sm su f /\ fn_has_code su sl f /\ fn_has_code sl sb f
Proof
  strip_tac >> drule_all selected_stack_compile >> strip_tac >>
  qpat_assum `stmt_env (gas_shadow_env T ce) _ _ _ _ = _`
    (mp_then Any (qspecl_then [`tys`,`rsz`,`rpc`,`sf`] mp_tac) selected_stack_compile) >>
  (impl_tac >- (pure_rewrite_tac [gas_shadow_env_fields] >> simp[])) >> strip_tac >>
  drule (REWRITE_RULE [gas_shadow_compiles_def] gas_shadow_stmt_lower_value_env) >>
  disch_then (qspecl_then [`ty`,`T`,`e`,`ce`] mp_tac) >> simp[] >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem selected_stack_loaded_physical[local]:
  same_frame frame ce /\ immutable_frame_mods func ce cx ee s /\
  fin.vs_memory = s.vs_memory /\ fin.vs_data_section = s.vs_data_section /\
  fin.vs_allocas = s.vs_allocas /\ fin.vs_alloca_next = s.vs_alloca_next ==>
  immutable_frame_mods func frame cx (ee with <|scopes := []; gas_obs := tail|>) fin
Proof
  strip_tac >>
  `frame.ce_modules = ce.ce_modules /\ frame.ce_is_ctor = ce.ce_is_ctor /\
   frame.ce_module_vars = ce.ce_module_vars /\
   frame.ce_module_var_type = ce.ce_module_var_type` by
    fs[same_frame_def, compile_env_component_equality] >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def] >>
  conj_tac
  >- (fs[immutables_rel_def] >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_x_assum `!src tops. _ ==> immutable_alloca_sep _ _ _ _ _` (drule_then mp_tac) >>
  simp[immutable_alloca_sep_def, immutable_decl_sep_def, local_region_def, lookup_scopes_def] >>
  metis_tac[]
QED

Theorem selected_stack_unlock_physical[local]:
  (return_unlock_state ce s).vs_data_section = s.vs_data_section /\
  (return_unlock_state ce s).vs_alloca_next = s.vs_alloca_next
Proof
  Cases_on `ce.ce_nonreentrant` >>
  rename1 `ce.ce_nonreentrant = (nr,info)` >> PairCases_on `info` >>
  Cases_on `nr` >> Cases_on `info1` >> Cases_on `info2` >>
  simp[return_unlock_state_def, tstore_def, sstore_def]
QED

Theorem selected_stack_intret[local]:
  same_frame frame ce /\ stmt_state_rel H ctx func ce cx mid t /\
  (!p. ce.ce_imm_alloca = SOME (Var p) ==> lookup_var p fin = lookup_var p t) /\
  LENGTH (return_unlock_insts ce id) <= fin.vs_inst_idx /\
  LENGTH vals = frame.ce_returns_count /\ intret_vals_match tv v vals /\
  fin = (return_unlock_state ce t) with
    <|vs_vars := fin.vs_vars; vs_inst_idx := fin.vs_inst_idx|> ==>
  intret_q H func frame cx tv v (mid with <|scopes := []; gas_obs := tail|>)
    (IntRet <|iret_values := vals; iret_adopt_fmp := NONE|> fin)
Proof
  strip_tac >>
  `frame.ce_nonreentrant = ce.ce_nonreentrant /\ frame.ce_imm_alloca = ce.ce_imm_alloca` by
    fs[same_frame_def, compile_env_component_equality] >>
  qabbrev_tac `n = fin.vs_inst_idx - LENGTH (return_unlock_insts ce id)` >>
  qabbrev_tac `pre = (t with vs_vars := fin.vs_vars) with vs_inst_idx := n` >>
  `fin = return_unlock_state frame pre` by
    (`return_unlock_state frame pre = return_unlock_state ce pre` by
       simp[return_unlock_state_def] >>
     simp[] >> qpat_assum `fin = _` (once_rewrite_tac o single) >>
     simp[Abbr `pre`, Abbr `n`] >> irule return_unlock_load_frame >> simp[]) >>
  irule intret_q_intro >>
  qexistsl [`<|iret_values := vals; iret_adopt_fmp := NONE|>`,`pre`] >>
  simp[result_rel_def] >>
  `stmt_state_rel H ctx func frame cx (mid with scopes := []) t` by
    metis_tac[internal_return_exit_stmt_state_rel] >>
  `stmt_state_rel H ctx func frame cx (mid with scopes := []) (t with vs_vars := fin.vs_vars)` by
    (irule stmt_state_rel_vars_frame >> simp[lookup_scopes_def, Abbr `pre`] >>
     fs[lookup_var_def]) >>
  `stmt_state_rel H ctx func frame cx (mid with scopes := []) pre` by
    simp[Abbr `pre`, stmt_state_rel_inst_idx] >>
  `mid with <|scopes := []; gas_obs := tail|> =
   (mid with scopes := []) with gas_obs := tail` by simp[] >>
  asm_rewrite_tac[state_rel_gas_obs] >> metis_tac[stmt_state_rel_state_rel]
QED

Theorem selected_stack_run_inputs[local]:
  expr_sim_inv_mods mods ce cx env es /\
  expr_type e = ty /\ lowered_value_type ce e = ty /\ post_value_type ce e = ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  0 < type_memory_size tv /\ val_store_size tv v = type_memory_size tv /\
  lower_value compile_expr ce ty e sa = (op,sm) /\
  expr_post_mods H ctx func ce cx e es sa sm s0 mid v op t /\
  ptr_val_ok cx (post_value_type ce e) v op G tn t /\ ptr_buf_ok ce e op G t /\
  expr_store_bound cx (post_value_type ce e) v op t /\
  ghost_inv_at_mods D lo NONE ce cx mid G tn t /\
  ce.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  ret_pc_ok ce sa s0 /\ local_ptrs_reserved ce sa /\
  ((FST ce.ce_nonreentrant /\ ~SND (SND (SND ce.ce_nonreentrant))) ==>
    ~cx.txn.is_static) ==>
  ?src w pc.
    op = Var src /\ not_fresh_at sm src /\ lookup_var src t = SOME w /\
    ptr_covers G tn src t (type_memory_size tv) /\
    w2n w + type_memory_size tv < dimword (:256) /\
    w2n w + type_memory_size tv <= t.vs_alloca_next /\
    (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory tv v (w2n w) m) /\
    not_fresh_at sm rpc /\ lookup_var rpc t = SOME pc /\ op_taint tn (Var rpc) = {} /\
    local_ptrs_reserved ce sm /\ allocas_from lo t /\
    ((FST ce.ce_nonreentrant /\ ~SND (SND (SND ce.ce_nonreentrant))) ==>
      ~t.vs_call_ctx.cc_static)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_memory_bytes ce ty = type_memory_size tv` by
    (metis_tac[expr_sim_inv_mods_memory_layout]) >>
  qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  `?src w. op = Var src /\ lookup_var src t = SOME w /\
    ptr_covers G tn src t (type_memory_size tv) /\
    (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory tv v (w2n w) m) /\
    w2n w + val_store_size tv v <= t.vs_alloca_next` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then Any (qspecl_then [`G`,`tn`,`ty`,`tv`] mp_tac)
         internal_return_memory_value_inputs) >> simp[]) >>
  `not_fresh_at sa rpc /\ ?pc. lookup_var rpc t = SOME pc` by
    (fs[ret_pc_ok_def, expr_post_def] >> metis_tac[]) >>
  `allocas_from lo t /\ op_taint tn (Var rpc) = {}` by fs[ghost_inv_at_mods_def] >>
  `stmt_state_rel H ctx func ce cx mid t` by fs[expr_post_def] >>
  `t.vs_alloca_next < dimword (:256)` by
    (drule stmt_state_rel_alloca_room >> metis_tac[alloca_room_next_lt]) >>
  `t.vs_call_ctx.cc_static = cx.txn.is_static` by
    (drule_then assume_tac stmt_state_rel_state_rel >> drule state_rel_call_ctx_rel >>
     simp[call_ctx_rel_def]) >>
  `sa.cs_next_var <= sm.cs_next_var` by metis_tac[compile_expr_grows] >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `not_fresh_at sm src /\ not_fresh_at sm rpc` by
    (conj_tac >- metis_tac[compile_lower_value_var] >> metis_tac[not_fresh_at_mono]) >>
  qexistsl [`src`,`w`,`pc`] >> fs[] >> decide_tac
QED

Theorem selected_stack_loaded_post[local]:
  same_frame frame ce /\ local_ptrs_reserved ce sm /\
  stmt_state_rel H ctx func ce cx mid t /\ immutable_frame_mods func ce cx mid t /\
  dead_lo_ok_mods H D lo ce cx /\ ghost_inv_at_mods D lo NONE ce cx mid G tn t /\
  ((FST ce.ce_nonreentrant /\ ~SND (SND (SND ce.ce_nonreentrant))) ==>
     FST (SND (SND ce.ce_nonreentrant))) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans SUBSET tn.t_trans /\ tf.t_imm = tn.t_imm /\
  tf.t_mem = tn.t_mem /\
  (!x. not_fresh_at sm x ==> lookup_var x fin = lookup_var x t) /\
  LENGTH (return_unlock_insts ce sm.cs_next_id) <= fin.vs_inst_idx /\
  LENGTH vals = frame.ce_returns_count /\ intret_vals_match tv v vals /\
  fin = (return_unlock_state ce t) with
    <|vs_vars := fin.vs_vars; vs_inst_idx := fin.vs_inst_idx|> ==>
  intret_q H func frame cx tv v (mid with <|scopes := []; gas_obs := tail|>)
    (IntRet <|iret_values := vals; iret_adopt_fmp := NONE|> fin) /\
  immutable_frame_mods func frame cx (mid with <|scopes := []; gas_obs := tail|>) fin /\
  stor_taint_ok_at D tf fin /\
  (!i. i < lo /\ i IN tf.t_mem ==>
     imm_section_dead_mods frame (mem_bytes_at 0 lo fin.vs_memory) i)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (irule selected_stack_intret >> simp[] >> qexistsl [`ce`,`ctx`,`sm.cs_next_id`,`t`] >>
      simp[] >> rpt strip_tac >> first_x_assum irule >> fs[local_ptrs_reserved_def]) >>
  conj_tac
  >- (irule selected_stack_loaded_physical >> goal_assum (drule_at Any) >>
      qpat_assum `fin = _` (once_rewrite_tac o single) >>
      simp[selected_stack_unlock_physical, return_unlock_state_frames]) >>
  `!sec i. imm_section_dead_mods frame sec i = imm_section_dead_mods ce sec i` by
    fs[same_frame_def, compile_env_component_equality, imm_section_dead_mods_def] >>
  drule_all selected_unlock_exit_taint_mods >>
  qpat_assum `fin = _` (once_rewrite_tac o single) >>
  simp[stor_taint_ok_at_def]
QED

Theorem selected_stack_return_frag_mods:
  same_frame frame ce /\ frame.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  frame.ce_return_buf = NONE /\ 0 < frame.ce_returns_count /\
  frame.ce_returns_count = returns_stack_count
    (\k. MAP (FST o SND) (get_struct_fields frame.ce_struct_fields k)) ty /\
  ((FST frame.ce_nonreentrant /\ ~SND (SND (SND frame.ce_nonreentrant))) ==>
     ~cx.txn.is_static /\ FST (SND (SND frame.ce_nonreentrant))) /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  expr_sim_inv_mods mods ce cx env es /\
  IS_SOME (type_stmt env ty (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  expr_sim_full_mods (DF,lo,NONE,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es ==>
  stmt_frag_full_mods (DF,lo,NONE,ctx,shadow_ctx,PG,func,shadow_func) cx lctx
    (\H v ee gt r. intret_q H func frame cx tv v ee r /\
      !ir u. r = IntRet ir u ==> immutable_frame_mods func frame cx (ee with scopes := []) u /\
        stor_taint_ok_at (DF H) (SND gt) u /\
        !i. i < lo /\ i IN (SND gt).t_mem ==>
          imm_section_dead_mods frame (mem_bytes_at 0 lo u.vs_memory) i)
    ce (stmt_env ce lctx ty (Return (SOME e)))
    (stmt_env (gas_shadow_env T ce) lctx ty (Return (SOME (gas_shadow_expr e))))
    (eval_stmt cx (Return (SOME e))) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ce.ce_return_pc = frame.ce_return_pc /\ ce.ce_return_buf = frame.ce_return_buf /\
   ce.ce_returns_count = frame.ce_returns_count /\ ce.ce_struct_fields = frame.ce_struct_fields /\
   ce.ce_nonreentrant = frame.ce_nonreentrant` by
    fs[same_frame_def, compile_env_component_equality] >>
  qabbrev_tac `tys = case ty of TupleT ts => ts
    | StructT k => MAP (FST o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string k))
    | _ => []` >>
  `tys = (case ty of TupleT ts => ts
    | StructT k => MAP (FST o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string k))
    | _ => [])` by simp[Abbr `tys`] >>
  `frame.ce_returns_count =
   returns_stack_count (\k. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields k)) ty` by
    (qpat_assum `ce.ce_struct_fields = _` (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  `LENGTH tys = frame.ce_returns_count /\ EVERY is_word_type tys /\ tys <> []` by
    (irule selected_stack_type_args >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`ce`,`ty`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `0 < returns_stack_count (\k. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields k)) ty` by
    metis_tac[] >>
  drule_all selected_stack_operand_type >> strip_tac >>
  irule (SIMP_RULE bool_ss [LET_THM] selected_forced_return_frag_mods) >> simp[] >>
  qexists `\sa sb sha shb op sm shm.
    ?su sl elems. compile_return_unlock ce sm = ((),su) /\
    compile_tuple_load_all ce op tys 0 su = (elems,sl) /\
    emit_inst RET (elems ++ [Var rpc]) [] sl = ((),sb) /\
    fn_has_code sm su func /\ fn_has_code su sl func /\ fn_has_code sl sb func` >>
  conj_tac
  >- (rpt gen_tac >> BETA_TAC >> rewrite_tac[gas_shadow_stmt_def, optionTheory.OPTION_MAP_DEF] >> strip_tac >>
      `ce.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\ ce.ce_return_buf = NONE /\
       0 < ce.ce_returns_count` by metis_tac[] >>
      drule_all selected_stack_compile_cut >> strip_tac >>
      qexistsl [`op`,`sm`,`shm`] >> ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
      qexistsl [`su`,`sl`,`elems`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "reached"
QED

Resume selected_stack_return_frag_mods[reached]:
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    (`mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[APPEND_NIL] >>
     qpat_assum `mid with gas_obs := [] = mid` (pure_rewrite_tac o single) >> simp[]) >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME tv` by metis_tac[] >>
  drule_all selected_stack_value_typed >> strip_tac >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by fs[expr_sim_inv_mods_def] >>
  drule_all selected_stack_layout >> strip_tac >>
  `type_memory_size tv = 32 * LENGTH tys` by metis_tac[word_tuple_size] >>
  `0 < type_memory_size tv` by decide_tac >>
  `LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) tys tvs` by
    (irule LIST_REL_mono >>
     qexists `\t rt. evaluate_type (get_tenv cx) t = SOME rt` >>
     BETA_TAC >> reverse conj_tac >- first_assum ACCEPT_TAC >>
     rpt strip_tac >> metis_tac[expr_sim_inv_mods_memory_layout]) >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by fs[Abbr `H0`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `ce.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\ ce.ce_return_buf = NONE /\
   ((FST ce.ce_nonreentrant /\ ~SND (SND (SND ce.ce_nonreentrant))) ==>
     ~cx.txn.is_static /\ FST (SND (SND ce.ce_nonreentrant)))` by metis_tac[] >>
  `ptr_val_ok cx (post_value_type ce e) v op G tn t /\
   expr_store_bound cx (post_value_type ce e) v op t` by metis_tac[] >>
  `((FST ce.ce_nonreentrant /\ ~SND (SND (SND ce.ce_nonreentrant))) ==>
      ~cx.txn.is_static)` by metis_tac[] >>
  drule_all selected_stack_run_inputs >> strip_tac >>
  qpat_x_assum `op = Var _` SUBST_ALL_TAC >>
  `!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
    tuple_in_memory vs tvs (w2n w) mem` by
    (rpt strip_tac >>
     qpat_assum `!a mem. val_in_memory _ _ a mem <=> _` (rewrite_tac o single o GSYM) >>
     first_assum irule >> first_assum ACCEPT_TAC) >>
  `type_memory_size_list tvs <= type_memory_size tv` by simp[] >>
  `((FST ce.ce_nonreentrant /\ ~SND (SND (SND ce.ce_nonreentrant))) ==>
     FST (SND (SND ce.ce_nonreentrant)))` by metis_tac[] >>
  drule_all (Q.INST [`capacity` |-> `type_memory_size tv`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`] return_stack_aggregate_suffix) >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`] strip_assume_tac) >>
  rename1 `tf.t_mem = tn.t_mem` >>
  rename1 `fin = (return_unlock_state ce t) with <|vs_vars := fin.vs_vars; vs_inst_idx := fin.vs_inst_idx|>` >>
  qabbrev_tac `vals = MAP (\(rt,x). typed_val_to_w256 rt x) (ZIP (tvs,vs))` >>
  `LENGTH vals = frame.ce_returns_count` by
    (`LENGTH tvs = LENGTH tys /\ LENGTH vs = LENGTH tvs` by
       metis_tac[LIST_REL_LENGTH, values_have_types_length] >>
     simp[Abbr `vals`, LENGTH_ZIP]) >>
  irule gas_outcome_full_mods_exit >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gf`, `mid`, `IntRet <|iret_values := vals; iret_adopt_fmp := NONE|> fin`,
            `INR (ReturnException v)`, `tf`] >>
  simp[raise_def, exit_result_def, halt_exit_def, stmt_exit_ptr_def, expr_exit_def] >>
  gen_tac >> disch_tac >>
  reverse conj_tac
  >- (disch_tac >> qpat_assum `fin = _` (once_rewrite_tac o single) >>
      `allocas_below_fmp (return_unlock_state ce t with
        <|vs_vars := fin.vs_vars; vs_inst_idx := fin.vs_inst_idx|>) =
       allocas_below_fmp (return_unlock_state ce t)` by
        (pure_rewrite_tac [allocas_below_fmp_def] >> simp[NoAsms]) >>
      qpat_assum `allocas_below_fmp _ = allocas_below_fmp _` (pure_rewrite_tac o single) >>
      simp[]) >>
  gen_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `stmt_state_rel H ctx func ce cx mid t /\ immutable_frame_mods func ce cx mid t` by
    fs[expr_post_mods_def, expr_post_def] >>
  qpat_assum `!H. dead_lo_ok_mods H (DF H) lo ce cx` (qspec_then `H` assume_tac) >>
  `tf.t_stor = tn.t_stor /\ tf.t_trans SUBSET tn.t_trans /\ tf.t_imm = tn.t_imm` by metis_tac[] >>
  drule_all selected_stack_loaded_post >> simp[]
QED

Finalise selected_stack_return_frag_mods
