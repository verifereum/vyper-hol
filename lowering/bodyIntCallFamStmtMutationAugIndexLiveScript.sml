(* Live local-memory selection after an effectful subscript index. *)
Theory bodyIntCallFamStmtMutationAugIndexLive
Ancestors
  bodyIntCallJointContract targetLocalLive targetSubscriptMemory
  loweringPosts loweringStateRelDefs compileEnv venomState venomExecSemantics
  vyperTyping valueEncodingDefs valueEncodingProps

Theorem intcall_target_index_memory_live:
  target_pre ce fp.jc_cx env (SubscriptTarget bt e) es /\
  type_place_target env bt = SOME bvt /\ target_root bt = NameTarget id /\
  eval_base_place fp.jc_cx bt es = (INL pv,mid) /\
  bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
    (mid with gas_obs := gs) = (INL key,fin) /\
  target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sm s0 mid pv
    (Type ty) rb s /\
  local_ptrs_reserved ce sm /\ u.vs_labels = s.vs_labels /\
  intcall_expr_cont fp ce env mid sm s fin sb u /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv ==>
  ?path entry v w.
    pv = PlaceR (MemoryPlace id path) /\
    lookup_scopes id fin.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL v /\
    eval_operand (FST rb) u = SOME w /\
    place_ptr_rel ce fp.jc_cx u pv w (FST (SND rb)) (Type ty) /\
    val_in_memory tv v (w2n w) u.vs_memory /\
    value_has_type tv v /\ well_formed_type_value tv /\
    subscripts_type entry.type path = SOME tv
Proof
  strip_tac >> drule_all local_subscript_index_live >> strip_tac >> gvs[] >>
  fs[target_post_def, intcall_expr_cont_def, intcall_expr_res_def] >>
  `place_ptr_rel ce fp.jc_cx u (PlaceR (MemoryPlace id path)) w
     (FST (SND rb)) (Type ty)` by
    (fs[place_ptr_rel_def] >>
     metis_tac[local_ptrs_reserved_def]) >>
  `eval_operand (FST rb) u = SOME w` by
    (Cases_on `FST rb` >> gvs[eval_operand_def]) >>
  drule_all place_ptr_rel_memory_current >> strip_tac >>
  metis_tac[]
QED

Theorem intcall_target_index_dynamic_length:
  target_pre ce fp.jc_cx env (SubscriptTarget bt e) es /\
  type_place_target env bt = SOME bvt /\ target_root bt = NameTarget id /\
  eval_base_place fp.jc_cx bt es = (INL pv,mid) /\
  bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
    (mid with gas_obs := gs) = (INL key,fin) /\
  target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sm s0 mid pv
    (Type ty) rb s /\
  local_ptrs_reserved ce sm /\ u.vs_labels = s.vs_labels /\
  intcall_expr_cont fp ce env mid sm s fin sb u /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME (ArrayTV etv (Dynamic cap)) ==>
  ?path entry vs w.
    pv = PlaceR (MemoryPlace id path) /\
    lookup_scopes id fin.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
    eval_operand (FST rb) u = SOME w /\
    val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs))
      (w2n w) u.vs_memory /\
    LENGTH vs <= cap /\ all_have_type etv vs /\
    mload (w2n w) u = n2w (LENGTH vs) /\
    array_len_ok T cnt (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocMemory)
      (FST rb) u (n2w (LENGTH vs))
Proof
  strip_tac >> drule_all intcall_target_index_memory_live >> strip_tac >>
  `?vs. v = ArrayV (DynArrayV vs)` by
    (Cases_on `v` >> gvs[value_has_type_def] >>
     rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def]) >>
  gvs[] >>
  `expr_sim_inv ce fp.jc_cx env fin /\
   stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx fin u` by
    fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  drule_all array_len_ok_memory_current >> strip_tac >>
  fs[value_has_type_def, val_in_memory_def, mem_word_at_eq_mload] >>
  metis_tac[]
QED
