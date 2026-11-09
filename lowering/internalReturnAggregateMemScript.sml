(* Typed memory layouts consumed by aggregate internal stack returns. *)
Theory internalReturnAggregateMem
Ancestors
  internalReturnCompileMem internalReturnComposeMem stmtSimReturn
  valueEncodingProofs exprSimProps vyperTypeABI list compileEnv
  typedNormalizeStructMetadata exprSimHyps valueEncodingTyping vyperTypeArgFits
  valueEncoding vyperValue stmtLowering exprLoweringProps emitHelperProps
  stmtLoweringMono ctorReturnFrame bodySim exprSimTypedAlloc loweringPosts
  exprSimHypsDefs returnValueTyped entryDecodeStaticProps
  exprSimAggregateChildren bodyMemAssignTopCopyFacts exprSimMemDefs fragExec
  internalReturnTerminalMem venomExecSemantics venomState arithmetic freshWrites
  exprOperandVar

Theorem aggregate_return_layout[local]:
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  ~is_word_type ty /\
  0 < returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields name)) ty /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
  val_in_memory tv v addr mem /\ addr + type_memory_size tv <= dimword (:256) ==>
  ?tys tvs vs.
    tys = (case ty of TupleT ts => ts | StructT sid =>
      MAP (FST o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string sid))
      | _ => []) /\
    tys <> [] /\ EVERY is_word_type tys /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) tys tvs /\
    values_have_types tvs vs /\ tuple_in_memory vs tvs addr mem /\
    type_memory_size tv = 32 * LENGTH tys /\
    (!w. w2n w = addr ==> intret_vals_match tv v (tuple_words ce w tys 0 mem))
Proof
  strip_tac >> Cases_on `ty` >>
  gvs[returns_stack_count_def, is_word_type_def]
  >~ [`TupleT ts`]
  >- (drule_all tuple_type_value >> strip_tac >> gvs[] >>
      fs[tuple_like_stack_count_def] >>
      qpat_x_assum `0 < _` mp_tac >> IF_CASES_TAC >> simp[] >> strip_tac >>
      `type_memory_size_list tvs = 32 * LENGTH ts` by
        metis_tac[word_tuple_size] >>
      qexistsl_tac [`tvs`,`vs`] >>
      fs[val_in_memory_def, type_memory_size_def] >>
      `ts <> []` by (Cases_on `ts` >> fs[]) >> simp[] >>
      rpt strip_tac >>
      `tuple_words ce w ts 0 mem =
        MAP (\(tv,v). typed_val_to_w256 tv v) (ZIP (tvs,vs))` by
        (irule tuple_words_typed >> simp[] >> metis_tac[]) >>
      simp[intret_vals_match_def]) >>
  `val_wf tv v` by metis_tac[value_has_type_val_wf] >>
  `type_widens_to tenv (StructT p) (StructT p)` by simp[] >>
  drule_all normalize_struct_metadata >> strip_tac >>
  gvs[get_struct_fields_def] >>
  fs[tuple_like_stack_count_def] >>
  qpat_x_assum `0 < _` mp_tac >> IF_CASES_TAC >> simp[] >> strip_tac >>
  `LIST_REL (\t tv. evaluate_type tenv t = SOME tv)
    (MAP (FST o SND) fields) tvs` by
    (irule OPT_MMAP_LIST_REL >> simp[]) >>
  `type_memory_size_list tvs = 32 * LENGTH fields` by
    metis_tac[word_tuple_size, LENGTH_MAP] >>
  qexistsl_tac [`tvs`,`vs`] >>
  fs[val_in_memory_def, fields_in_memory_tuple, MAP_ZIP,
     type_memory_size_def, type_memory_size_fields_zip] >>
  `fields <> []` by (Cases_on `fields` >> fs[]) >> simp[] >>
  rpt strip_tac >>
  `tuple_words ce w (MAP (FST o SND) fields) 0 mem =
    MAP (\(tv,v). typed_val_to_w256 tv v) (ZIP (tvs,vs))` by
    (irule tuple_words_typed >> simp[] >> metis_tac[]) >>
  simp[intret_vals_match_def, MAP_ZIP]
QED

Theorem internal_return_aggregate_code[local]:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_return_buf = NONE /\
  stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv'',sb) /\
  lower_value compile_expr cenv ty e sa = (op,s1) ==>
  compile_internal_return cenv (SOME op) (Var rpc) cenv.ce_returns_count
    ty (lowered_value_type cenv e)
    (case ty of TupleT ts => ts | StructT sid =>
      MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      | _ => []) NONE s1 = ((),sb)
Proof
  strip_tac >> qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, compile_internal_return_from_env_def] >>
  pairarg_tac >> simp[oneTheory.one]
QED

Theorem internal_return_aggregate_suffix[local]:
  same_frame ce cenv /\ expr_sim_inv cenv cx env es /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_returns_count = returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields name)) ty /\
  0 < cenv.ce_returns_count /\ ~is_word_type ty /\
  expr_type e = ty /\ lowered_value_type cenv e = ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  compile_internal_return cenv (SOME op) (Var rpc) cenv.ce_returns_count
    ty ty (case ty of TupleT ts => ts | StructT sid =>
      MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      | _ => []) NONE s1 = ((),sb) /\
  fn_has_code s1 sb func /\ ret_pc_ok cenv sa s0 /\
  (!x. op = Var x ==> not_fresh_at s1 x) /\ sa.cs_next_var <= s1.cs_next_var /\
  expr_post ctx func cenv cx e es sa s1 s0 ee v op t /\
  expr_store_bound cx ty v op t /\
  ~t.vs_halted /\ t.vs_current_bb = s1.cs_current_bb /\
  t.vs_inst_idx = LENGTH s1.cs_current_insts ==>
  ?n r. gas_path_mem ctx func t n r /\ exit_result r /\
    !tail. intret_q func ce cx tv v ((ee with gas_obs := tail) with scopes := []) r
Proof
  strip_tac >>
  `post_value_type cenv e = ty` by metis_tac[post_value_type_lowered] >>
  `~is_bytestring_type ty` by
    (Cases_on `ty` >> fs[returns_stack_count_def, is_word_type_def,
      is_bytestring_type_def] >> rename1 `BaseT bt` >> Cases_on `bt` >>
      fs[returns_stack_count_def, is_word_type_def, is_bytestring_type_def]) >>
  `expr_val_rel cx ty v op t /\
   expr_val_at cenv cx ty sa s1 ee v op t /\ stmt_state_rel ctx func cenv cx ee t` by
    fs[expr_post_def] >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
  simp[expr_val_rel_def] >> strip_tac >>
  `val_footprint tv v = type_memory_size tv` by
    metis_tac[evaluated_nonbytes_footprint] >>
  `w2n w + type_memory_size tv <= dimword (:256)` by
    (drule_all expr_val_at_bound >> simp[]) >>
  `?tys tvs vs. tys = (case ty of TupleT ts => ts | StructT sid =>
      MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      | _ => []) /\ tys <> [] /\ EVERY is_word_type tys /\
    LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs /\
    values_have_types tvs vs /\ tuple_in_memory vs tvs (w2n w) t.vs_memory /\
    type_memory_size tv = 32 * LENGTH tys /\
    (!w'. w2n w' = w2n w ==> intret_vals_match tv v (tuple_words cenv w' tys 0 t.vs_memory))` by
    (irule aggregate_return_layout >> fs[expr_sim_inv_def] >> metis_tac[]) >>
  qpat_x_assum `tys = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
  `EVERY (\ty. type_memory_bytes cenv ty = 32) tys` by
    (fs[EVERY_MEM] >> metis_tac[word_type_dec_sizes]) >>
  `w2n w + 32 * LENGTH tys <= t.vs_alloca_next` by
    (fs[expr_store_bound_def] >>
     `val_store_size tv v = type_memory_size tv` by
       metis_tac[topcopy_val_store_size] >>
     `0 < LENGTH tys` by (Cases_on `tys` >> fs[]) >>
     qpat_x_assum `!tv'. evaluate_type _ _ = _ /\ _ ==> _`
       (qspec_then `tv` mp_tac) >> simp[]) >>
  `?pc. lookup_var rpc t = SOME pc` by
    (fs[ret_pc_ok_def, expr_post_def] >> metis_tac[]) >>
  `not_fresh_at s1 rpc` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> fs[ret_pc_ok_def]) >>
  `w2n w + 32 * LENGTH tys <= dimword (:256)` by fs[] >>
  drule_all compile_internal_return_tuple_register_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `0` >> goal_assum (drule_at Any) >> simp[exit_result_def] >>
  `state_rel func ce cx (ee with scopes := []) t` by
    (irule constructor_exit_state_rel >> fs[stmt_state_rel_def] >> metis_tac[]) >>
  `intret_vals_match tv v (tuple_words cenv w tys 0 t.vs_memory)` by simp[] >>
  drule_all internal_return_register_terminal >> simp[]
QED

Theorem internal_return_aggregate_mem:
  same_frame ce cenv /\ expr_sim_inv cenv cx env es /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_returns_count = returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields name)) ty /\
  0 < cenv.ce_returns_count /\ ~is_word_type ty /\
  expr_type e = ty /\ lowered_value_type cenv e = ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  IS_SOME (type_stmt env ty (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  expr_sim_mem ctx func cenv cx ty e es ==>
  stmt_frag_mem NONE ctx func cx lctx (intret_q func ce cx tv) cenv
    (stmt_env cenv lctx ty (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >> Cases_on `cenv.ce_return_buf = NONE`
  >- (irule internal_return_value_counted_mem >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all internal_return_aggregate_code >>
      metis_tac[cj 1 ci_mono_return_helpers, ci_mono_def, pairTheory.SND]) >>
  rpt strip_tac >>
  `value_has_type tv v` by (drule_all return_value_typed >> fs[]) >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var` by
    metis_tac[ci_mono_compile_expr_sa, ci_mono_def, pairTheory.SND] >>
  drule_all internal_return_aggregate_code >> strip_tac >>
  `cs_extends s1 sb` by
    metis_tac[cj 1 ci_mono_return_helpers, ci_mono_def, pairTheory.SND] >>
  `fn_has_code s1 sb func` by metis_tac[fn_has_code_split] >>
  `!x. op = Var x ==> not_fresh_at s1 x` by
    metis_tac[compile_lower_value_var] >>
  irule internal_return_aggregate_suffix >> simp[] >> metis_tac[]) >>
  simp[stmtSimDefsTheory.stmt_frag_mem_def, return_buf_frame_def]
QED
