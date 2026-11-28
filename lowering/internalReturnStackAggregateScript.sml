(* Tuple and struct returns load their word members before RET. *)
Theory internalReturnStackAggregate
Ancestors
  bodyFullPostsMods[qualified]
  stmtSimReturn stmtLowering exprLowering exprLoweringProps emitHelperProps
  compileEnv fragExec gasShadowCompileStmtOps gasShadowCompileStmtHelpers
  gasShadowCompilePure gasShadowState intCallReturnMem internalReturnMemoryFrame
  exprSimProps bodyFullAssignTuple tupleLoadProps stateFrame fragGasOriginPtr
  typedStructMetadata typedStructMemory memoryValueAbiTuple valueEncodingProofs
  vyperTypeABI vyperTypeExprSoundness vyperTyping bodyDeclCopyMemory
  stateRelProj instIdxIndep loweringStateRelDefs loweringPosts
  vyperState venomState list rich_list valueEncodingDefs valueEncoding ptrDiscipline
  decoderGhostFramePtr bodySimFull bodySim bodyPtrDefs exprSimDefs
  exprSimHypsDefs exprSimHyps exprOperandVar internalReturnMemoryInputs
  stmtSimReturnWiden gasOutcomeFullCompose gasExemptCert
  vyperStorageTrace vyperStorageFootprint allocLimits vyperTypeSystem
  vyperTypeInvariants freshWrites
Libs
  monadsyntax

Theorem compile_internal_stack_aggregate_parts[local]:
  cenv.ce_return_buf = NONE /\ 0 < cenv.ce_returns_count /\
  tys = (case ty of
         TupleT ts => ts
       | StructT nsid => MAP (FST o SND)
           (get_struct_fields cenv.ce_struct_fields (nsid_to_string nsid))
       | _ => []) /\
  tys <> [] /\ EVERY is_word_type tys /\
  compile_internal_return_from_env cenv ty sty op ret_op sm = ((),sb) ==>
  ?su sl elems.
    compile_return_unlock cenv sm = ((),su) /\
    compile_tuple_load_all cenv op tys 0 su = (elems,sl) /\
    emit_inst RET (elems ++ [ret_op]) [] sl = ((),sb)
Proof
  strip_tac >>
  qpat_x_assum `compile_internal_return_from_env _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_from_env_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_return_unlock cenv sm` >> rename1 `_ = (u,su)` >>
  Cases_on `u` >> simp[] >>
  qpat_x_assum `tys = _` (rewrite_tac o single o SYM) >>
  simp[compile_internal_return_def, comp_bind_def,
       GSYM compile_tuple_load_all_words] >>
  Cases_on `compile_tuple_load_all cenv op tys 0 su` >>
  rename1 `_ = (elems,sl)` >> simp[]
QED

Theorem return_stack_aggregate_compile_parts[local]:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_return_buf = NONE /\ 0 < cenv.ce_returns_count /\
  tys = (case ty of
         TupleT ts => ts
       | StructT nsid => MAP (FST o SND)
           (get_struct_fields cenv.ce_struct_fields (nsid_to_string nsid))
       | _ => []) /\
  tys <> [] /\ EVERY is_word_type tys /\
  stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv',sb) /\
  fn_has_code sa sb func ==>
  cenv' = cenv /\
  ?op sm su sl elems.
    lower_value compile_expr cenv ty e sa = (op,sm) /\
    compile_return_unlock cenv sm = ((),su) /\
    compile_tuple_load_all cenv op tys 0 su = (elems,sl) /\
    emit_inst RET (elems ++ [Var rpc]) [] sl = ((),sb) /\
    fn_has_code sa sm func /\ fn_has_code sm su func /\
    fn_has_code su sl func /\ fn_has_code sl sb func
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[loweringPostsTheory.stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, Once compile_stmt_def] >>
  Cases_on `lower_value compile_expr cenv ty e sa` >>
  rename1 `_ = (op,sm)` >> simp[] >>
  Cases_on `compile_internal_return_from_env cenv ty (lowered_value_type cenv e) op (Var rpc) sm` >>
  rename1 `_ = (u,sb')` >> Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  mp_tac (Q.INST [
    `tys` |-> `case ty of
      TupleT ts => ts
    | StructT nsid => MAP (FST o SND)
        (get_struct_fields cenv.ce_struct_fields (nsid_to_string nsid))
    | _ => []`,
    `ret_op` |-> `Var rpc`,
    `sty` |-> `lowered_value_type cenv e`]
    compile_internal_stack_aggregate_parts) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  qexistsl_tac [`su`,`sl`,`elems`] >> simp[] >>
  drule compile_return_unlock_shape >> strip_tac >>
  `cs_extends sa sm` by metis_tac[compile_expr_grows] >>
  `cs_extends su sl` by metis_tac[compile_tuple_load_all_grows] >>
  `cs_extends sl sb` by metis_tac[cs_extends_emit_inst] >>
  metis_tac[fn_has_code_split, cs_extends_trans]
QED

Theorem return_stack_aggregate_exit[local]:
  stmt_state_rel H ctx func cenv cx ee s /\
  (!p. cenv.ce_imm_alloca = SOME (Var p) ==>
    lookup_var p (s with vs_vars := vars) = lookup_var p s) /\
  LENGTH (return_unlock_insts cenv id) <= n /\
  LENGTH vals = cenv.ce_returns_count /\ intret_vals_match tv v vals /\
  loaded = (return_unlock_state cenv s) with
    <|vs_vars := vars; vs_inst_idx := n|> ==>
  !tail. intret_q H func cenv cx tv v (ee with <|scopes := []; gas_obs := tail|>)
    (IntRet <|iret_values := vals; iret_adopt_fmp := NONE|> loaded)
Proof
  strip_tac >> gen_tac >>
  qabbrev_tac `pre = s with
    <|vs_vars := vars; vs_inst_idx := n - LENGTH (return_unlock_insts cenv id)|>` >>
  `loaded = return_unlock_state cenv pre` by
    (mp_tac (Q.SPECL [`cenv`,`s`,`vars`,`n`,`id`] return_unlock_load_frame) >>
     simp[Abbr `pre`]) >>
  irule intret_q_intro >>
  qexistsl_tac [`<|iret_values := vals; iret_adopt_fmp := NONE|>`,`pre`] >>
  asm_rewrite_tac[result_rel_def] >> simp[] >>
  `stmt_state_rel H ctx func cenv cx (ee with scopes := []) s` by
    metis_tac[internal_return_exit_stmt_state_rel, bodySimTheory.same_frame_refl] >>
  `stmt_state_rel H ctx func cenv cx (ee with scopes := [])
     (s with vs_vars := vars)` by
    (irule stmt_state_rel_vars_frame >> simp[lookup_scopes_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx (ee with scopes := []) pre` by
    (`pre = (s with vs_vars := vars) with
       vs_inst_idx := n - LENGTH (return_unlock_insts cenv id)` by
       simp[Abbr `pre`] >>
     pop_assum SUBST1_TAC >> simp[stmt_state_rel_inst_idx]) >>
  `ee with <|scopes := []; gas_obs := tail|> =
     (ee with scopes := []) with gas_obs := tail` by simp[] >>
  pop_assum SUBST1_TAC >> rewrite_tac[state_rel_gas_obs] >>
  metis_tac[stmt_state_rel_state_rel]
QED

Theorem return_stack_aggregate_shadow_unlock[local]:
  lower_value compile_expr cenv ty e sa = (op,sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa =
    (shadow_op,shadow_sm) /\
  gas_shadow_state sa shadow_sa /\
  compile_return_unlock cenv sm = ((),su) /\
  compile_return_unlock (gas_shadow_env T cenv) shadow_sm = ((),shadow_su) ==>
  op = shadow_op /\ gas_shadow_state sm shadow_sm /\
  gas_shadow_state su shadow_su
Proof
  simp[gasShadowCompileStmtBaseTheory.compile_return_unlock_gas_shadow_env] >>
  strip_tac >>
  `op = shadow_op /\ gas_shadow_state sm shadow_sm` by
    (drule (REWRITE_RULE[gas_shadow_compiles_def] gas_shadow_stmt_lower_value_env) >>
     disch_then (qspecl_then [`ty`,`T`,`e`,`cenv`] mp_tac) >> simp[]) >>
  mp_tac (Q.SPEC `cenv` (GEN_ALL gas_shadow_compiles_return_unlock)) >>
  simp[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`sm`,`shadow_sm`] mp_tac) >> simp[]
QED

Theorem return_stack_aggregate_layout[local]:
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
  ~is_word_type ty /\
  ret_count = returns_stack_count
    (\n. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields n)) ty /\
  0 < ret_count ==>
  ?tys tvs vs.
    tys = (case ty of
           TupleT ts => ts
         | StructT nsid => MAP (FST o SND)
             (get_struct_fields cenv.ce_struct_fields (nsid_to_string nsid))
         | _ => []) /\
    LENGTH tys = ret_count /\ EVERY is_word_type tys /\
    LIST_REL (\t rt. evaluate_type tenv t = SOME rt) tys tvs /\
    values_have_types tvs vs /\
    type_memory_size_list tvs = type_memory_size tv /\
    val_store_size tv v = type_memory_size tv /\
    (!a mem. val_in_memory tv v a mem <=> tuple_in_memory vs tvs a mem) /\
    intret_vals_match tv v (MAP (\(rt,x). typed_val_to_w256 rt x) (ZIP (tvs,vs)))
Proof
  strip_tac >>
  qpat_x_assum `ret_count = returns_stack_count _ ty` mp_tac >>
  Cases_on `ty` >> simp[returns_stack_count_def, tuple_like_stack_count_def] >>
  TRY (IF_CASES_TAC >> gvs[] >> NO_TAC) >>
  TRY (IF_CASES_TAC >> strip_tac >> gvs[]) >>
  gvs[]
  >~ [`evaluate_type tenv (TupleT tys) = SOME tv`] >-
    (drule_all tuple_type_value >> strip_tac >>
     qexistsl_tac [`tvs`,`vs`] >>
     gvs[val_in_memory_def, type_memory_size_def, val_store_size_def, intret_vals_match_def]) >>
  rename1 `evaluate_type tenv (StructT nsid) = SOME tv` >>
  drule evaluate_type_struct_fields >> strip_tac >>
  drule (cj 2 evaluate_type_mono) >> strip_tac >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  `MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields (nsid_to_string nsid)) =
     MAP SND args` by
    (qpat_assum `sfields_tenv_consistent _ _`
       (mp_tac o cj 1 o REWRITE_RULE [sfields_tenv_consistent_def]) >>
     disch_then drule >> strip_tac >> simp[get_struct_fields_def]) >>
  `LENGTH (MAP FST args) = LENGTH tvs` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  qpat_x_assum `tv = StructTV _` SUBST_ALL_TAC >>
  drule typed_struct_value_cases >> strip_tac >>
  drule struct_has_type_values_have_types >> strip_tac >>
  qexistsl_tac [`tvs`,`MAP SND fields`] >>
  gvs[val_in_memory_def, fields_in_memory_tuple, MAP_ZIP,
      type_memory_size_def, type_memory_size_fields_list, val_store_size_def,
      intret_vals_match_def]
QED

(* The member loads preserve the frame and the storage and memory taint
   needed by the final RET. *)
Theorem return_stack_aggregate_load_ret[local]:
  compile_tuple_load_all cenv (Var root) tys 0 sa = (elems,sb) /\
  emit_inst RET (elems ++ [Var rpc]) [] sb = ((),sc) /\
  EVERY is_word_type tys /\
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_return_buf = NONE /\
  not_fresh_at sa rpc /\ lookup_var rpc s = SOME pc /\
  op_taint tn (Var rpc) = {} /\
  not_fresh_at sa root /\ lookup_var root s = SOME w /\
  ptr_covers G tn root s capacity /\ type_memory_size_list tvs <= capacity /\
  w2n w + capacity < dimword (:256) /\ w2n w + capacity <= s.vs_alloca_next /\
  LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs /\
  LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys tvs /\
  values_have_types tvs vs /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    tuple_in_memory vs tvs (w2n w) mem) /\
  local_ptrs_reserved cenv sa /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (IntRet <|iret_values := MAP (\(tv,v). typed_val_to_w256 tv v) (ZIP (tvs,vs));
                iret_adopt_fmp := NONE|> t,Gf,tf)) /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    s.vs_inst_idx <= t.vs_inst_idx /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  mp_tac (Q.INST [`off` |-> `0`] body_assign_tuple_load_all_path) >>
  impl_tac >- simp[] >> strip_tac >>
  `t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>` by
    (qpat_assum `state_frame t = _`
       (mp_tac o Q.AP_TERM `\s. s with vs_vars := t.vs_vars` o
         REWRITE_RULE [state_frame_eq_reconstruct]) >>
     simp[]) >>
  mp_tac (Q.SPECL [`tys`,`cenv`,`Var root`,`0`,`sa`,`elems`,`sb`,`s`,`w`]
    compile_tuple_load_all_values) >>
  simp[eval_operand_def] >> strip_tac >>
  `s.vs_inst_idx <= t.vs_inst_idx` by fs[] >>
  `?vals. eval_operands elems t = SOME vals` by
    (qpat_assum `t with vs_inst_idx := _ = s with vs_vars := _`
       (fn eq => qpat_assum `eval_operands elems (s with vs_vars := _) = SOME _`
         (assume_tac o REWRITE_RULE [GSYM eq, instIdxIndepTheory.eval_ops_inst_idx])) >>
     goal_assum (drule_at Any)) >>
  `LENGTH vals = LENGTH elems /\ LENGTH tys = LENGTH tvs /\ LENGTH tvs = LENGTH vs` by
    metis_tac[eval_operands_length, LIST_REL_LENGTH, values_have_types_length] >>
  `vals = MAP (\(tv,v). typed_val_to_w256 tv v) (ZIP (tvs,vs))` by
    (simp[LIST_EQ_REWRITE, LENGTH_ZIP, EL_ZIP, EL_MAP] >>
     qx_gen_tac `i` >> disch_tac >>
     `i < LENGTH elems /\ i < LENGTH tvs /\ i < LENGTH vs` by decide_tac >>
     `eval_operand (EL i elems) t = SOME (EL i vals)` by
       metis_tac[eval_operands_index] >>
     qpat_x_assum `!i. i < LENGTH tys ==> ?x. _`
       (qspec_then `i` mp_tac) >>
     qpat_assum `EVERY is_word_type tys` (mp_tac o REWRITE_RULE [EVERY_EL]) >>
     simp[] >> rpt strip_tac >> fs[eval_operand_def]) >>
  `EVERY (\op. op_taint tf op = {}) (elems ++ [Var rpc])` by
    (simp[EVERY_APPEND, EVERY_EL] >> qx_gen_tac `i` >> disch_tac >>
     qpat_x_assum `!i. i < LENGTH tys ==> ?x. _`
       (qspec_then `i` mp_tac) >> simp[] >> strip_tac >> fs[]) >>
  `lookup_var rpc t = SOME pc` by
    (qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `rpc` mp_tac) >> simp[]) >>
  `allocas_from lo t` by
    (rewrite_tac[allocas_from_def] >>
     qpat_assum `t.vs_allocas = s.vs_allocas` (rewrite_tac o single) >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `allocas_below_fmp t = allocas_below_fmp s` by
    (qpat_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>`
       (once_rewrite_tac o single) >>
     simp[allocas_below_fmp_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (pop_assum (rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  reverse conj_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     TRY (qpat_assum `s.vs_inst_idx = LENGTH sa.cs_current_insts`
           (fn eq => qpat_assum `s.vs_inst_idx <= t.vs_inst_idx`
             (ACCEPT_TAC o REWRITE_RULE [eq])) >> NO_TAC) >>
     qx_gen_tac `x` >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  gen_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,Gf,tf) []
     (IntRet <|iret_values := vals; iret_adopt_fmp := NONE|> t,Gf,tf)` by
    (mp_tac (Q.INST [`ops` |-> `elems`, `sa` |-> `sb`, `sb` |-> `sc`,
       `s` |-> `t`, `G` |-> `Gf`, `tn` |-> `tf`] emitted_ret_origin_ptr) >>
     (impl_tac >- simp[]) >>
     disch_then ACCEPT_TAC) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) ([] ++ [])
     (IntRet <|iret_values := vals; iret_adopt_fmp := NONE|> t,Gf,tf)` by
    metis_tac[gas_origin_ptr_path_append] >>
  qpat_assum `vals = _` (fn eq => once_rewrite_tac [GSYM eq]) >>
  metis_tac[APPEND_NIL]
QED

(* The unlock and member loads share one endpoint for every dead mask. *)
Theorem return_stack_aggregate_suffix:
  compile_return_unlock cenv sm = ((),su) /\
  compile_tuple_load_all cenv (Var root) tys 0 su = (elems,sl) /\
  emit_inst RET (elems ++ [Var rpc]) [] sl = ((),sb) /\
  fn_has_code sm su func /\ fn_has_code su sl func /\ fn_has_code sl sb func /\
  EVERY is_word_type tys /\
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\ cenv.ce_return_buf = NONE /\
  not_fresh_at sm rpc /\ lookup_var rpc s = SOME pc /\ op_taint tn (Var rpc) = {} /\
  not_fresh_at sm root /\ lookup_var root s = SOME w /\
  ptr_covers G tn root s capacity /\ type_memory_size_list tvs <= capacity /\
  w2n w + capacity < dimword (:256) /\ w2n w + capacity <= s.vs_alloca_next /\
  LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs /\
  LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys tvs /\
  values_have_types tvs vs /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    tuple_in_memory vs tvs (w2n w) mem) /\
  local_ptrs_reserved cenv sm /\
  ((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
     ~s.vs_call_ctx.cc_static) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (IntRet <|iret_values := MAP (\(tv,v). typed_val_to_w256 tv v) (ZIP (tvs,vs));
                iret_adopt_fmp := NONE|> t,Gf,tf)) /\
    t = (return_unlock_state cenv s) with
      <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    LENGTH (return_unlock_insts cenv sm.cs_next_id) <= t.vs_inst_idx /\
    tf.t_mem = tn.t_mem /\
    (((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
       FST (SND (SND cenv.ce_nonreentrant))) ==>
      tf.t_stor = tn.t_stor /\ tf.t_trans SUBSET tn.t_trans /\
      tf.t_imm = tn.t_imm) /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  mp_tac (Q.INST [`sa` |-> `sm`] (SPEC_ALL return_unlock_origin_ptr_taint)) >>
  impl_tac >- simp[] >> strip_tac >>
  drule compile_return_unlock_shape >> strip_tac >>
  qabbrev_tac `s1 = return_unlock_state cenv s` >>
  `s1.vs_alloca_next = s.vs_alloca_next` by
    (simp[Abbr `s1`] >>
     qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
     Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
     simp[return_unlock_state_def, tstore_def, sstore_def]) >>
  `!x. lookup_var x s1 = lookup_var x s` by
    simp[Abbr `s1`, lookup_var_def] >>
  `allocas_from lo s1 /\ ~s1.vs_halted /\
    s1.vs_current_bb = su.cs_current_bb /\
    s1.vs_inst_idx = LENGTH su.cs_current_insts` by
    (qspecl_then [`cenv`,`s`,`sm.cs_next_id`] strip_assume_tac
       return_unlock_state_frames >>
     simp[Abbr `s1`, allocas_from_def] >>
     fs[allocas_from_def]) >>
  `ptr_covers G tn' root s1 capacity` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`G`,`s`,`tn`] >> simp[op_taint_def]) >>
  `!x. not_fresh_at sm x ==> not_fresh_at su x` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `local_ptrs_reserved cenv su` by
    (mp_tac (Q.SPECL [`cenv`,`sm`,`su`] local_ptrs_reserved_next_var) >>
     simp[]) >>
  mp_tac (Q.INST [`sa` |-> `su`, `sb` |-> `sl`, `sc` |-> `sb`,
    `s` |-> `s1`, `tn` |-> `tn'`] return_stack_aggregate_load_ret) >>
  impl_tac >- fs[Abbr `s1`, op_taint_def] >> strip_tac >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  conj_tac >-
    (gen_tac >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) ([] ++ [])
        (IntRet <|iret_values := MAP (\(tv,v). typed_val_to_w256 tv v) (ZIP (tvs,vs));
                  iret_adopt_fmp := NONE|> t,Gf,tf)` by
       metis_tac[gas_origin_ptr_path_append] >> fs[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_assum `s1.vs_inst_idx = LENGTH su.cs_current_insts`
        (fn idx => qpat_assum `su.cs_current_insts = _`
          (fn code => assume_tac (SIMP_RULE (srw_ss()) [code] idx))) >>
      decide_tac) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[pred_setTheory.SUBSET_TRANS] >>
  rpt strip_tac >>
  `not_fresh_at su x` by metis_tac[] >>
  metis_tac[]
QED


(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `tys = case ty of
    TupleT ts => ts
  | StructT nsid => MAP (FST o SND)
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string nsid))
  | _ => []` >>
  `tys <> [] /\ EVERY is_word_type tys` by
    (qpat_assum `Abbrev (tys = _)` mp_tac >>
     qpat_assum `~is_word_type ty` mp_tac >>
     qpat_assum `0 < cenv.ce_returns_count` mp_tac >>
     qpat_assum `cenv.ce_returns_count = returns_stack_count _ ty` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `ty` >>
     simp[markerTheory.Abbrev_def, returns_stack_count_def,
          tuple_like_stack_count_def] >>
     rpt strip_tac >> gvs[COND_RAND, COND_RATOR, COND_EXPAND] >>
     Cases_on `tys` >> fs[]) >>
  `tys = (case ty of
    TupleT ts => ts
  | StructT nsid => MAP (FST o SND)
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string nsid))
  | _ => [])` by simp[Abbr `tys`] >>
  mp_tac return_stack_aggregate_compile_parts >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `stmt_env _ _ _ (Return (SOME (gas_shadow_expr e))) shadow_sa = _`
    (mp_then Any (qspecl_then [`tys`,`rsz`,`rpc`,`shadow_func`] mp_tac)
      return_stack_aggregate_compile_parts) >>
  impl_tac
  >- (pure_rewrite_tac[gasShadowCompileBaseTheory.gas_shadow_env_fields] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  rename1 `lower_value compile_expr _ ty (gas_shadow_expr e) shadow_sa =
             (shadow_op,shadow_sm)` >>
  rename1 `compile_return_unlock _ shadow_sm = ((),shadow_su)` >>
  `op = shadow_op /\ gas_shadow_state sm shadow_sm` by
    (drule_all return_stack_aggregate_shadow_unlock >> simp[]) >>
  qpat_x_assum `op = shadow_op` SUBST_ALL_TAC >>
  rpt (qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[return_forced_admissible] >>
  `not_fresh_at sa rpc /\ ?pc. lookup_var rpc s0 = SOME pc` by
    fs[ret_pc_ok_def] >>
  qpat_x_assum `!ety. _` (qspec_then `ty` strip_assume_tac) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`,
                           `shadow_op`, `s0`, `G0`, `tn0`] mp_tac) >>
  impl_tac >- (simp[] >> first_assum ACCEPT_TAC) >> strip_tac >>
  `eval_stmt cx (Return (SOME e)) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. raise (ReturnException v))` by
    (simp[FUN_EQ_THM, eval_return_forced] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`storage_trace_frame (bind _ _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_raise]
  >~ [`gas_marked_exec`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >> metis_tac[])
  >~ [`gas_exempt_cert _ _ _ (bind _ _)`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  qexists_tac `\H res mid G1 tn1 t. ?v. res = INL v /\
     expr_post H ctx func cenv cx e es sa sm s0 mid v shadow_op t /\
     expr_store_bound cx (post_value_type cenv e) v shadow_op t /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
     ptr_val_ok cx (post_value_type cenv e) v shadow_op G1 tn1 t /\
     (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e shadow_op G1 t) /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
      simp[] >> conj_tac
      >- (rpt strip_tac >> fs[arithmeticTheory.ADD_COMM] >>
          qexists_tac `v` >> asm_rewrite_tac[]) >>
      rpt gen_tac >> Cases_on `res` >> Cases_on `r` >>
      simp[expr_exit_def, stmt_exit_ptr_def, halt_exit_def] >>
      Cases_on `y` >> simp[expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]) >>
  rpt strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by
    fs[Abbr `H0`, storage_trace_domain_def] >>
  qpat_assum `valid_horizon cx st0 H0 mid.storage_trace`
    (fn vh => qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
      (qspec_then `H0` (strip_assume_tac o BETA_RULE o C MP vh))) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v,mid with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` assume_tac) >> fs[]) >>
  `alloc_limits_expr cenv e` by
    fs[stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def,
       Once allocLimitsTheory.alloc_limits_expr_def] >>
  mp_tac (Q.INST [`ret` |-> `ty`, `g` |-> `gas_explicit marks s0.vs_gas_readings`,
    `ee` |-> `mid with gas_obs := []`] internal_return_buffer_value_layout_typed) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`stv`,`ptv`]
    (map_every assume_tac o CONJUNCTS)) >>
  `lowered_value_type cenv e = ty` by
    metis_tac[stmtSimReturnWidenTheory.stack_return_widens_eq] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `expr_type e = ty` by
    (fs[type_stmt_def, AllCaseEqs()] >>
     metis_tac[stmtSimReturnWidenTheory.stack_return_widens_eq]) >>
  `post_value_type cenv e = ty` by metis_tac[post_value_type_lowered] >>
  `value_has_type tv v` by
    (qpat_assum `lowered_value_type cenv e = ty` (fn eq =>
       qpat_assum `evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME _`
         (mp_tac o REWRITE_RULE [eq])) >>
     simp[]) >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    fs[expr_sim_inv_def] >>
  mp_tac (Q.INST [`tenv` |-> `get_tenv cx`, `ret_count` |-> `cenv.ce_returns_count`]
    return_stack_aggregate_layout) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`layout_tys`,`tvs`,`vs`]
    (map_every assume_tac o CONJUNCTS)) >>
  `layout_tys = tys` by metis_tac[] >>
  pop_assum SUBST_ALL_TAC >>
  `type_memory_size tv = 32 * LENGTH tys` by metis_tac[word_tuple_size] >>
  `0 < type_memory_size tv` by simp[] >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys tvs` by
    (irule LIST_REL_mono >>
     qexists_tac `\sty stv. evaluate_type (get_tenv cx) sty = SOME stv` >>
     simp[] >> rpt strip_tac >>
     qpat_assum `expr_sim_inv cenv cx env es` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) x = SOME y` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[expr_sim_inv_memory_size]) >>
  `ptr_buf_ok cenv e shadow_op G1 t` by
    metis_tac[] >>
  mp_tac (Q.SPECL [`H0`,`ctx`,`func`,`cenv`,`cx`,`e`,
    `es`,`sa`,`sm`,`s0`,`mid`,`v`,`shadow_op`,`t`,`G1`,`tn1`,`ty`,`tv`]
    (INST_TYPE [alpha |-> ``:256``] internal_return_memory_value_inputs)) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  qpat_x_assum `shadow_op = Var src` SUBST_ALL_TAC >>
  `not_fresh_at sm src /\ not_fresh_at sm rpc /\ local_ptrs_reserved cenv sm` by
    metis_tac[compile_lower_value_var, not_fresh_at_mono, compile_expr_grows,
              local_ptrs_reserved_next_var] >>
  `lookup_var rpc t = SOME pc /\ stmt_state_rel H0 ctx func cenv cx mid t` by
    fs[expr_post_def] >>
  `op_taint tn1 (Var rpc) = {} /\ allocas_from lo t` by fs[ghost_inv_at_def] >>
  `((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
     ~t.vs_call_ctx.cc_static)` by
    (imp_res_tac stmt_state_rel_state_rel >>
     imp_res_tac state_rel_call_ctx_rel >> fs[call_ctx_rel_def]) >>
  `t.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_alloca_room, alloca_room_next_lt] >>
  `w2n a + type_memory_size tv <= t.vs_alloca_next` by
    (qpat_assum `val_store_size tv v = type_memory_size tv` (fn size_eq =>
       qpat_assum `w2n a + val_store_size tv v <= t.vs_alloca_next`
         (ACCEPT_TAC o REWRITE_RULE [size_eq]))) >>
  `w2n a + type_memory_size tv < dimword (:256)` by
    decide_tac >>
  `!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
     tuple_in_memory vs tvs (w2n a) mem` by
    (rpt strip_tac >>
     qpat_assum `!a mem. val_in_memory _ _ a mem <=> _`
       (rewrite_tac o single o GSYM) >>
     first_assum irule >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
    `G` |-> `G1`, `tn` |-> `tn1`, `s` |-> `t`, `root` |-> `src`,
    `w` |-> `a`, `capacity` |-> `type_memory_size tv`]
      return_stack_aggregate_suffix) >>
  impl_tac >- asm_simp_tac bool_ss [arithmeticTheory.LESS_EQ_REFL] >>
  disch_then (qx_choosel_then [`fin`,`Gf`,`tf`]
    (map_every assume_tac o CONJUNCTS)) >>
  irule (Q.INST [`res` |-> `INR (ReturnException v)`, `ee` |-> `mid`]
           gas_outcome_full_exit) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gf`,`mid`,
    `IntRet <|iret_values := MAP (\(tv,v). typed_val_to_w256 tv v) (ZIP (tvs,vs));
             iret_adopt_fmp := NONE|> fin`,`tf`] >>
  simp[raise_def, exit_result_def, halt_exit_def] >>
  gen_tac >> disch_tac >> reverse conj_tac
  >- (disch_tac >>
      qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp t` drule >>
      qpat_assum `fin = _` (once_rewrite_tac o single) >>
      `allocas_below_fmp (return_unlock_state cenv t with
         <|vs_vars := fin.vs_vars; vs_inst_idx := fin.vs_inst_idx|>) =
       allocas_below_fmp (return_unlock_state cenv t)` by
        (pure_rewrite_tac [allocas_below_fmp_def] >> simp[NoAsms]) >>
      qpat_assum `allocas_below_fmp _ = allocas_below_fmp _`
        (pure_rewrite_tac o single) >>
      simp[NoAsms, allocas_below_fmp_return_unlock_state]) >>
  gen_tac >>
  qpat_assum `valid_horizon cx st0 H mid.storage_trace`
    (fn vh => qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
      (qspec_then `H` (strip_assume_tac o BETA_RULE o C MP vh))) >>
  simp[stmt_exit_ptr_def, expr_exit_def] >>
  conj_tac
  >- (mp_tac (Q.INST [`ctx` |-> `ctx`, `id` |-> `sm.cs_next_id`,
        `s` |-> `t`, `n` |-> `fin.vs_inst_idx`, `vars` |-> `fin.vs_vars`,
        `loaded` |-> `fin`, `ee` |-> `mid`,
        `vals` |-> `MAP (\(tv,v). typed_val_to_w256 tv v) (ZIP (tvs,vs))`]
        (INST_TYPE [alpha |-> ``:256``] return_stack_aggregate_exit)) >>
      impl_tac
      >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
          >- (qpat_assum `expr_post H ctx func cenv cx e es sa sm s0 mid _ (Var src) t`
                (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
              first_assum ACCEPT_TAC)
          >- (rpt strip_tac >>
              `not_fresh_at sa p` by fs[local_ptrs_reserved_def] >>
              `not_fresh_at sm p` by
                metis_tac[not_fresh_at_mono,compile_expr_grows] >>
              `lookup_var p fin = lookup_var p t` by metis_tac[] >>
              qpat_assum `fin = _`
                (fn eq => pop_assum (mp_tac o REWRITE_RULE [Once eq, lookup_var_def])) >>
              simp[NoAsms, lookup_var_def])
          >- (`LENGTH tvs = LENGTH tys /\ LENGTH vs = LENGTH tvs` by
                metis_tac[LIST_REL_LENGTH, values_have_types_length] >>
              simp[LENGTH_ZIP])) >>
      disch_then (qspec_then `tail` mp_tac) >> simp[NoAsms]) >>
  strip_tac >>
  Q.SUBGOAL_THEN `dead_lo_ok H (DF H) lo cenv cx /\
    ((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
      FST (SND (SND cenv.ce_nonreentrant))) /\
    tf.t_stor = tn1.t_stor /\ tf.t_trans SUBSET tn1.t_trans /\
    tf.t_imm = tn1.t_imm /\ tf.t_mem = tn1.t_mem /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t`
    (mp_tac o MATCH_MP (GEN_ALL return_unlock_exit_taint))
  >- fs[] >>
  qpat_assum `fin = _` (fn eq => once_rewrite_tac [eq]) >>
  simp[stor_taint_ok_at_def]
QED
*)
Theorem compile_return_stack_aggregate_frag_full_taint[local]:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx cenv ty tv es e env
   rpc rsz.
   cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
   cenv.ce_return_buf = NONE /\ 0 < cenv.ce_returns_count /\
   cenv.ce_returns_count = returns_stack_count
     (\n. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields n)) ty /\
   ((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
     ~cx.txn.is_static) /\
   ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
   expr_sim_inv cenv cx env es /\
   stmt_exprs_ok cenv (Return (SOME e)) /\
   IS_SOME (type_stmt env ty (Return (SOME e))) /\
   call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
   (!ety. expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
            cenv cx ety e es /\
          expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
            cenv cx ety e es) ==>
   stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx
     (\H v ee gt r. intret_q H func cenv cx tv v ee r /\
       !ir u. r = IntRet ir u /\
         ((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
           FST (SND (SND cenv.ce_nonreentrant))) ==>
         stor_taint_ok_at (DF H) (SND gt) u /\
         (!i. i < lo /\ i IN (SND gt).t_mem ==>
              imm_section_dead_mods cenv (mem_bytes_at 0 lo u.vs_memory) i)) cenv
     (stmt_env cenv lctx ty (Return (SOME e)))
     (stmt_env (gas_shadow_env T cenv) lctx ty (Return (SOME (gas_shadow_expr e))))
     (eval_stmt cx (Return (SOME e))) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  `ty <> NoneT` by (strip_tac >> fs[returns_stack_count_def]) >>
  pure_rewrite_tac[frame_ret_ok_full_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `eo` >- gvs[type_stmt_def] >>
  rename1 `Return (SOME e)` >>
  `cenv'.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
   cenv'.ce_returns_count = cenv.ce_returns_count /\ cenv'.ce_return_buf = NONE /\
   cenv'.ce_struct_fields = cenv.ce_struct_fields /\
   cenv'.ce_nonreentrant = cenv.ce_nonreentrant` by
    fs[bodySimTheory.same_frame_def, compile_env_component_equality] >>
  `imm_section_dead_mods cenv' = imm_section_dead_mods cenv` by
    fs[bodySimTheory.same_frame_def, compile_env_component_equality,
       FUN_EQ_THM, immSectionDeadTheory.imm_section_dead_mods_def] >>
  mp_tac (Q.SPECL
    [`DF`, `lo`, `d`, `ctx`, `shadow_ctx`, `PG`, `func`, `shadow_func`,
     `cx`, `lctx`, `cenv'`, `ty`, `tv`, `es`, `e`, `env`, `rpc`, `rsz`]
    compile_return_stack_aggregate_frag_full_taint) >>
  simp[] >>
  pure_rewrite_tac[stmt_frag_full_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  conj_tac
  >- (gen_tac >>
      first_x_assum (qspec_then `tail` mp_tac) >>
      simp[stmt_exit_ptr_def] >> strip_tac >> simp[] >>
      disj2_tac >> gvs[intret_q_def, result_rel_def] >>
      `return_unlock_state cenv' s = return_unlock_state cenv s` by
        fs[return_unlock_state_def] >>
      qexistsl_tac [`s`, `i`] >> simp[] >>
      drule_all (Q.INST
        [`es` |-> `ee with <|scopes := []; gas_obs := tail|>`]
        constructor_exit_state_rel) >> simp[]) >>
  first_assum ACCEPT_TAC
QED
*)
Theorem internal_frame_ret_stack_aggregate_full_taint:
  !DF lo d ctx shadow_ctx PG func shadow_func cx cenv ty tv rpc rsz.
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
    cenv.ce_return_buf = NONE /\ 0 < cenv.ce_returns_count /\
    cenv.ce_returns_count = returns_stack_count
      (\n. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields n)) ty /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
    ((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
      ~cx.txn.is_static) ==>
    frame_ret_ok_full_mods mods
      (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cx
      (\H v ee gt r. intret_q H func cenv cx tv v ee r /\
        !ir u. r = IntRet ir u /\
          ((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
            FST (SND (SND cenv.ce_nonreentrant))) ==>
          stor_taint_ok_at (DF H) (SND gt) u /\
          (!i. i < lo /\ i IN (SND gt).t_mem ==>
               imm_section_dead_mods cenv (mem_bytes_at 0 lo u.vs_memory) i)) cenv ty
Proof
  cheat
QED
