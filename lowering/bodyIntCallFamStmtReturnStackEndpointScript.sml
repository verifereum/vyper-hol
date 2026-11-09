(* Stack return layout and terminal boundary. *)
Theory bodyIntCallFamStmtReturnStackEndpoint
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtReturnStackRun
  bodyIntCallFamStmtReturnStackExit bodyIntCallFamStmtReturnLayout
  exprSimTypedAlloc exprSimFieldLayout placeMemoryTypedBase
  stmtSimReturn stmtLowering compileEnv exprLoweringProps loweringPosts
  vyperTyping vyperTypeABI vyperValue valueEncoding valueEncodingProofs
  valueEncodingTyping fragExec list rich_list

Theorem stack_return_operand_layout:
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  0 < returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields name)) ty /\
  expr_val_rel cx ty v op s /\ expr_val_at ce cx ty sa sb es v op s /\
  stmt_state_rel ctx func ce cx es s /\ eval_operand op s = SOME w ==>
  let tys = case ty of TupleT ts => ts | StructT sid =>
      MAP (FST o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string sid))
      | _ => [] in
  let ws = if tys = [] then [w] else tuple_words ce w tys 0 s.vs_memory in
  intret_vals_match tv v ws /\
  LENGTH ws = returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields name)) ty
Proof
  strip_tac >> Cases_on `ty` >>
  gvs[returns_stack_count_def, is_word_type_def]
  >~ [`expr_val_rel cx (BaseT b) v op s`]
  >- (Cases_on `is_word_type (BaseT b)` >> gvs[expr_val_rel_def] >>
      metis_tac[intret_vals_match_word])
  >~ [`expr_val_rel cx (FlagT sid) v op s`]
  >- (gvs[expr_val_rel_def, is_word_type_def] >>
      metis_tac[intret_vals_match_word, is_word_type_def])
  >~ [`expr_val_rel cx (TupleT tys) v op s`]
  >- (drule_all tuple_type_value >> strip_tac >> gvs[] >>
      `EVERY is_word_type tys /\ tys <> [] /\
       tuple_like_stack_count tys = LENGTH tys` by
        (qpat_x_assum `0 < tuple_like_stack_count _` mp_tac >>
         simp[tuple_like_stack_count_def] >> IF_CASES_TAC >> simp[] >>
         strip_tac >> gvs[] >> Cases_on `tys` >> gvs[]) >>
      `~is_word_type (TupleT tys)` by simp[is_word_type_def] >>
      drule_all expr_val_at_bound >>
      gvs[expr_val_rel_def, is_word_type_def] >>
      drule_all word_tuple_size >>
      simp[val_footprint_def, type_memory_size_def] >> strip_tac >>
      gvs[val_in_memory_def] >> strip_tac >>
      irule tuple_return_words >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  rename1 `evaluate_type _ (StructT sid) = SOME tv` >>
  drule_all typed_memory_struct_evaluation >> strip_tac >> gvs[] >>
  gvs[get_struct_fields_def] >>
  qpat_x_assum `0 < tuple_like_stack_count _` mp_tac >>
  simp[tuple_like_stack_count_def] >> IF_CASES_TAC >> simp[] >> strip_tac >>
  `fields <> []` by (Cases_on `fields` >> gvs[]) >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  `~is_word_type (StructT sid)` by simp[is_word_type_def] >>
  drule_all expr_val_at_bound >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  gvs[expr_val_rel_def, is_word_type_def, val_in_memory_def,
      val_footprint_def, type_memory_size_def] >>
  `LENGTH args = LENGTH tvs` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  drule_all word_tuple_size >> strip_tac >>
  gvs[type_memory_size_fields_zip] >>
  `MAP SND (ZIP (MAP FST args,tvs)) = tvs` by
    simp[MAP_ZIP] >>
  `w2n w + 32 * LENGTH (MAP SND args) <= dimword (:256)` by simp[] >>
  `LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv)
     (MAP SND args) (MAP SND (ZIP (MAP FST args,tvs)))` by simp[] >>
  drule_all struct_return_words >> simp[]
QED

Theorem intcall_stack_return_endpoint:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  0 < fp.jc_root_ce.ce_returns_count /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv fp.jc_cx) /\
  value_has_type fp.jc_ret_tv v /\
  expr_val_rel fp.jc_cx fp.jc_ret_ty v op s /\
  expr_val_at ce fp.jc_cx fp.jc_ret_ty spre sa es v op s /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  compile_internal_return_from_env ce fp.jc_ret_ty sty op fp.jc_rpc sa = ((),sb) /\
  fn_has_code sa sb fp.jc_func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?k r. gas_path fp.jc_ctx fp.jc_func s k r /\ exit_result r /\
    intcall_stmt_exit fp (INR (ReturnException v)) es r
Proof
  strip_tac >>
  `ce.ce_returns_count = fp.jc_root_ce.ce_returns_count /\
   ce.ce_return_pc = SOME (PtrVar fp.jc_rpc 0) /\
   ce.ce_struct_fields = fp.jc_root_ce.ce_struct_fields` by
    fs[intcall_joint_res_def, intcall_frame_ok_def,
       bodySimTheory.same_frame_def, compile_env_component_equality] >>
  `fp.jc_rb = NONE` by
    (fs[intcall_frame_ok_def] >> Cases_on `fp.jc_rb` >> gvs[]) >>
  `ce.ce_return_buf = NONE` by fs[intcall_joint_res_def, return_buf_frame_def] >>
  `(!x. fp.jc_rpc = Var x ==> not_fresh_at sa x) /\
   eval_operand fp.jc_rpc s = SOME fp.jc_pc` by
    (fs[intcall_joint_res_def, intcall_frame_ok_def] >> metis_tac[]) >>
  `?w. eval_operand op s = SOME w` by fs[expr_val_rel_def] >>
  qpat_x_assum `compile_internal_return_from_env _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_from_env_def, comp_bind_def, comp_return_def] >>
  strip_tac >> drule_all compile_internal_return_stack_path >>
  disch_then (qspec_then `fp.jc_ctx` strip_assume_tac) >>
  `evaluate_type (get_tenv fp.jc_cx) fp.jc_ret_ty = SOME fp.jc_ret_tv /\
   0 < returns_stack_count
     (\name. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields name))
     fp.jc_ret_ty /\ stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s` by
    fs[intcall_frame_ok_def, intcall_joint_res_def] >>
  drule_all stack_return_operand_layout >>
  simp[] >> strip_tac >>
  qexists_tac `k` >> goal_assum (drule_at Any) >>
  simp[exit_result_def] >>
  irule intcall_stack_exit_frame >> goal_assum (drule_at Any) >>
  simp[] >> fs[intcall_frame_ok_def] >>
  qexistsl_tac [`ce`, `env`, `s`, `sa`] >> simp[]
QED
