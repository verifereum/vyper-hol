(* Adapt the retained default operand to the declared return type. *)
Theory extcallReturnDefaultMemory
Ancestors
  exprSimExtCallCase exprSimMemDefs valueCopyBytes loweringPosts compileEnv

Theorem extcall_return_default_operand:
  extcall_default_ready cx rt T op dt (SOME v) s /\
  expr_store_bound cx dt v op s ==>
  expr_val_rel cx rt v op s /\ expr_store_bound cx rt v op s /\
  !ce dst. compile_store_memory ce op dst rt dt =
    compile_store_memory ce op dst rt rt
Proof
  strip_tac >> Cases_on `dt = rt`
  >- gvs[extcall_default_ready_def] >>
  `is_bytestring_type dt /\ is_bytestring_type rt` by
    fs[extcall_default_ready_def] >>
  `~is_word_type dt /\ ~is_word_type rt` by
    metis_tac[is_bytestring_word_type] >>
  `?tv rtv w. evaluate_type (get_tenv cx) dt = SOME tv /\
    evaluate_type (get_tenv cx) rt = SOME rtv /\
    value_has_type tv v /\ value_has_type rtv v /\
    eval_operand op s = SOME w /\ val_in_memory tv v (w2n w) s.vs_memory` by
    (fs[extcall_default_ready_def, expr_val_rel_def] >> metis_tac[]) >>
  `val_in_memory rtv v (w2n w) s.vs_memory` by
    metis_tac[bytestring_val_in_memory_transfer] >>
  `val_store_size tv v = val_store_size rtv v` by
    metis_tac[bytestring_val_store_size_eq] >>
  conj_tac >- (simp[expr_val_rel_def] >> metis_tac[]) >>
  conj_tac
  >- (fs[expr_store_bound_def] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  simp[compile_store_memory_bytestring_src]
QED
