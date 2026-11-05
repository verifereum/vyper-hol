(* Saved operand transport across keyword evaluation. *)
Theory rawCallKeywordPrefixPtr
Ancestors
  rawCallOperandPrefixPtr stmtSimLogArgs bodyPtrDefs loweringPosts

Theorem saved_value_footprint_taint_kept:
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  log_arg_clear cenv cx ty v /\ eval_operand op s = SOME w /\
  ghost_kept cenv es sb (G0 : string |-> num # num) tn0 s G tn /\
  w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tn.t_mem ==>
  i IN tn0.t_mem
Proof
  simp[expr_val_at_def] >> strip_tac >>
  first_x_assum (qspec_then `tv` mp_tac) >> simp[] >> strip_tac >> gvs[]
  >- (fs[ghost_kept_def] >>
      qpat_x_assum `!aid off sz i. FLOOKUP _ _ = _ /\ _ ==> _` irule >>
      simp[] >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >> metis_tac[])
  >> fs[ghost_kept_def, log_arg_clear_def] >>
  qpat_x_assum `!n b sz i. local_region _ _ _ _ _ _ /\ _ ==> _` irule >>
  simp[] >> qexistsl_tac [`b`, `n`, `sz`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!tv n j k. _` drule_all >> strip_tac >> decide_tac
QED

Theorem saved_value_footprint_clean:
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  log_arg_clear cenv cx ty v /\ eval_operand op s = SOME w /\
  ghost_kept cenv es sb (G0 : string |-> num # num) tn0 s G tn /\
  (!i. w2n w <= i /\ i < w2n w + val_footprint tv v ==> i NOTIN tn0.t_mem) ==>
  !i. w2n w <= i /\ i < w2n w + val_footprint tv v ==> i NOTIN tn.t_mem
Proof
  metis_tac[saved_value_footprint_taint_kept]
QED

Theorem saved_dynamic_bytes_across_word_args:
  typed_args_post ctx func cenv cx es sb s es' args xs vs t /\
  ghost_kept cenv es sb (G0 : string |-> num # num) tn0 s G tn /\
  expr_sim_inv cenv cx env es /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic n))) sa sb es
    (BytesV bs) (Var x) s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) =
    SOME (BaseTV (BytesT (Dynamic n))) /\
  not_fresh_at sb x /\ eval_operand (Var x) s = SOME (n2w b) /\
  (b:num) < dimword (:256) /\ FLOOKUP G0 x = SOME (region_base,sz) /\
  (region_base:num) <= b /\ b+32+LENGTH bs <= region_base+(sz:num) /\ op_taint tn0 (Var x) = {} /\
  (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn0.t_mem) ==>
  eval_operand (Var x) t = SOME (n2w b) /\
  FLOOKUP G x = SOME (region_base,sz) /\ op_taint tn (Var x) = {} /\
  mem_bytes_at b (32+LENGTH bs) t.vs_memory =
    mem_bytes_at b (32+LENGTH bs) s.vs_memory /\
  (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `wb_frame cenv es sb s t` by
    fs[exprSimPrecompilesTheory.typed_args_post_def] >>
  `log_arg_clear cenv cx (BaseT (BytesT (Dynamic n))) (BytesV bs)` by
    metis_tac[log_arg_clear_base] >>
  conj_tac >- (irule log_frame_operand >> simp[] >> metis_tac[]) >>
  `FLOOKUP G x = FLOOKUP G0 x /\
   op_taint tn (Var x) = op_taint tn0 (Var x)` by fs[ghost_kept_def] >>
  simp[] >> conj_tac
  >- (`~is_word_type (BaseT (BytesT (Dynamic n)))` by
        simp[compileEnvTheory.is_word_type_def] >>
      drule_all log_argument_footprint_kept >>
      simp[compileEnvTheory.is_word_type_def, loweringPostsTheory.val_footprint_def,
        wordsTheory.w2n_n2w]) >>
  rpt strip_tac >> spose_not_then assume_tac >>
  `i IN tn0.t_mem` suffices_by (gvs[] >> metis_tac[]) >>
  irule saved_value_footprint_taint_kept >>
  first_assum (irule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`n2w b`, `BaseTV (BytesT (Dynamic n))`, `tn`, `G0`, `G`] >>
  simp[compileEnvTheory.is_word_type_def, loweringPostsTheory.val_footprint_def,
    wordsTheory.w2n_n2w]
QED
