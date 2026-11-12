(* Source layout boundary for tuple-like internal stack returns. *)
Theory internalReturnTupleBoundaryMem
Ancestors
  internalReturnTupleMem internalReturnBufferBoundaryMem stmtSimReturnWiden
  compileEnv list arithmetic stmtSimReturn placeMemoryTypedBase memoryValueAbiTuple
  vyperTypeABI vyperTypeValues vyperTyping vyperValue loweringStateRelDefs
  loweringPosts valueEncoding valueEncodingDefs valueEncodingProofs exprSimTypedAlloc
  externalReturnBounds exprSimProps internalReturnWordBoundaryMem
  externalReturnPrefix exprSimHypsDefs vyperTypeSystem stmtLoweringMono
  stmtSimDefs exprLoweringProps venomState vyperTypeInvariants fragExec
  exprOperandVar loweringShapeDefs internalReturnBoundaryCommonMem

Theorem internal_return_tuple_count[local]:
  !sft ty. ~is_word_type ty /\ 0 < returns_stack_count sft ty ==>
  ?tys. (case ty of TupleT ts => ts | StructT nm => sft (nsid_to_string nm)
         | _ => []) = tys /\
    tys <> [] /\ EVERY is_word_type tys /\
    returns_stack_count sft ty = LENGTH tys
Proof
  rpt gen_tac >> Cases_on `ty` >>
  simp[returns_stack_count_def, tuple_like_stack_count_def,
       SF boolSimps.COND_elim_ss] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem internal_return_struct_components[local]:
  sfields_tenv_consistent sf tenv /\
  evaluate_type tenv (StructT name) = SOME tv /\ value_has_type tv v ==>
  ?tvs vs.
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv)
      (MAP (FST o SND) (get_struct_fields sf (nsid_to_string name))) tvs /\
    values_have_types tvs vs /\
    ?fts fields. tv = StructTV fts /\ v = StructV fields /\
                 MAP SND fts = tvs /\ MAP SND fields = vs
Proof
  strip_tac >> drule_all typed_memory_struct_evaluation >> strip_tac >>
  gvs[] >> Cases_on `v` >> gvs[value_has_type_def] >>
  drule struct_has_type_tuple >> strip_tac >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  `LENGTH args = LENGTH tvs` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  gvs[MAP_ZIP] >> simp[get_struct_fields_def]
QED

Theorem internal_return_tuple_components[local]:
  sfields_tenv_consistent sf tenv /\ ~is_word_type ty /\
  0 < returns_stack_count (\nm. MAP (FST o SND) (get_struct_fields sf nm)) ty /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
  ?tys tvs vs.
    (case ty of TupleT ts => ts | StructT nm =>
      MAP (FST o SND) (get_struct_fields sf (nsid_to_string nm)) | _ => []) = tys /\
    tys <> [] /\ EVERY is_word_type tys /\
    returns_stack_count (\nm. MAP (FST o SND) (get_struct_fields sf nm)) ty = LENGTH tys /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) tys tvs /\
    values_have_types tvs vs /\
    (tv = TupleTV tvs /\ v = ArrayV (TupleV vs) \/
     ?fts fields. tv = StructTV fts /\ v = StructV fields /\
                  MAP SND fts = tvs /\ MAP SND fields = vs)
Proof
  strip_tac >> drule_all internal_return_tuple_count >> strip_tac >>
  Cases_on `ty` >> gvs[] >>
  metis_tac[tuple_type_value, internal_return_struct_components]
QED

Theorem internal_return_tuple_memory[local]:
  expr_val_rel cx ty v op s /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  ~is_word_type ty /\
  (tv = TupleTV tvs /\ v = ArrayV (TupleV vs) \/
   ?fts fields. tv = StructTV fts /\ v = StructV fields /\
                MAP SND fts = tvs /\ MAP SND fields = vs) ==>
  ?w. eval_operand op s = SOME w /\ tuple_in_memory vs tvs (w2n w) s.vs_memory
Proof
  rw[expr_val_rel_def] >> gvs[val_in_memory_def, fields_in_memory_tuple] >>
  metis_tac[]
QED

Theorem internal_return_tuple_bounds[local]:
  stmt_state_rel ctx func ce cx es s /\
  expr_val_at ce cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w /\
  LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv) tys tvs /\
  EVERY is_word_type tys /\ tys <> [] /\
  (tv = TupleTV tvs /\ v = ArrayV (TupleV vs) \/
   ?fts fields. tv = StructTV fts /\ v = StructV fields /\
                MAP SND fts = tvs /\ MAP SND fields = vs) ==>
  w2n w + 32 * LENGTH tys <= s.vs_alloca_next /\
  w2n w + 32 * LENGTH tys < dimword (:256)
Proof
  strip_tac >>
  `type_memory_size_list tvs = 32 * LENGTH tys` by metis_tac[word_tuple_size] >>
  `val_footprint tv v = 32 * LENGTH tys` by
    (gvs[val_footprint_def, type_memory_size_def] >>
     metis_tac[type_memory_size_fields_list]) >>
  drule_all expr_val_at_bound >> strip_tac >>
  drule_all expr_val_at_frontier >> strip_tac >> gvs[] >>
  Cases_on `tys` >> gvs[]
QED


Theorem internal_return_tuple_boundary_mem:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_imm_alloca = NONE /\
  cenv.ce_returns_count = returns_stack_count
    (\nm. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields nm)) ty /\
  ~is_word_type ty /\ 0 < cenv.ce_returns_count /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  same_frame cenv ce /\ expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ty (Return (SOME e))) /\
  lowered_value_type ce e = expr_type e /\
  stmt_env ce lctx ty (Return (SOME e)) sa = (cenv'',sb) /\
  lower_value compile_expr ce ty e sa = (op,s1) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa /\ ret_pc_ok ce sa s0 /\
  return_buf_frame NONE ce sa s0 /\
  expr_post ctx func ce cx e es sa s1 s0 ee v op t /\
  ~t.vs_halted /\ t.vs_current_bb = s1.cs_current_bb /\
  t.vs_inst_idx = LENGTH s1.cs_current_insts ==>
  ?n r. gas_path_mem ctx func t n r /\
    intret_q func cenv cx tv v (ee with scopes := []) r
Proof
  strip_tac >>
  `expr_type e = ty` by
    (irule stack_return_widens_eq >>
     conj_tac >- metis_tac[] >> qexists_tac `get_tenv cx` >>
     gvs[type_stmt_def, expr_sim_inv_def, env_consistent_def,
         env_context_consistent_def, AllCaseEqs()]) >>
  `post_value_type ce e = ty` by metis_tac[post_value_type_lowered] >>
  `ce.ce_return_pc = cenv.ce_return_pc /\ ce.ce_imm_alloca = NONE /\
   ce.ce_returns_count = cenv.ce_returns_count /\
   ce.ce_struct_fields = cenv.ce_struct_fields` by
    fs[bodySimTheory.same_frame_def, compile_env_component_equality] >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `0 < returns_stack_count (\nm. MAP (FST o SND)
      (get_struct_fields ce.ce_struct_fields nm)) ty` by metis_tac[] >>
  drule_all internal_return_tuple_components >> strip_tac >>
  drule_at (Pat `lower_value _ _ _ _ _ = _`) internal_return_value_preparation >>
  simp[] >> disch_then drule_all >> strip_tac >>
  `?w. eval_operand op t = SOME w /\ tuple_in_memory vs tvs (w2n w) t.vs_memory` by
    (irule internal_return_tuple_memory >> qexistsl_tac [`cx`,`tv`,`ty`,`v`] >>
     fs[expr_post_def]) >>
  `w2n w + 32 * LENGTH tys <= t.vs_alloca_next /\
   w2n w + 32 * LENGTH tys < dimword (:256)` by
    (irule internal_return_tuple_bounds >> simp[] >>
     qexistsl_tac [`ce`,`ctx`,`cx`,`ee`,`func`,`op`,`sa`,`s1`,`tv`,`tvs`,`ty`,`v`,`vs`] >>
     fs[expr_post_def]) >>

  `ce.ce_return_buf = NONE` by fs[return_buf_frame_def] >>
  `ce.ce_returns_count = LENGTH tys` by metis_tac[] >>
  `!x. Var rpc = Var x ==> not_fresh_at s1 x` by simp[] >>
  `?n r. gas_path_mem ctx func t n r /\
     intret_q func ce cx tv v (ee with scopes := []) r` by
    (irule compile_internal_tuple_return_intret_mem >> metis_tac[]) >>
  goal_assum (drule_at Any) >>
  irule internal_return_post_frame >> metis_tac[]
QED
