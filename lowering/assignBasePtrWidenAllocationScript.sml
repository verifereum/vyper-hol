(* Retain the runtime allocation witness discarded by the expression post.
   This is a producer-local ordinary fragment boundary, not a pointer path. *)
Theory assignBasePtrWidenAllocation
Ancestors assignBasePtrWidenLayout exprSimAlloc exprSimBufferStore
  exprSimOperands exprLoweringProps exprLowering context compileEnv fragExec
  loweringPosts exprOperandVar venomExecSemantics venomState words list

Theorem assign_base_widen_allocation:
  !ctx func cenv cx es sm sb s e v tv x op p d k.
    compile_bytestring_widen_copy d x k sm = (op,sb) /\
    0 < k /\ k <= d /\ d < dimword (:256) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
    (!z. x = Var z ==> not_fresh_at sm z) /\
    eval_operand x s = SOME p /\ ~is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    val_wf tv v /\ val_in_memory tv v (w2n p) s.vs_memory /\
    val_footprint tv v <= k ==>
    frag_exec ctx sm sb (\t. t = s)
      (\t. ?w. eval_operand op t = SOME w /\
        FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,d) /\
        w2n w + d < dimword (:256)) (\r. F)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_widen_code >> strip_tac >>
  drule_all alloc_buffer_source_frag >>
  disch_then (qspec_then `(\r. F)` strip_assume_tac) >>
  gvs[] >>
  `not_local_ptr cenv es.scopes p'` by
    (irule exprSimOperandsTheory.fresh_not_local_ptr >> goal_assum (drule_at Any) >> simp[]) >>
  `k < dimword (:256)` by decide_tac >>
  `lookup_var p' u = SOME w` by gvs[eval_operand_def] >>
  `val_in_memory tv v (w2n p) u.vs_memory` by simp[] >>
  `FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n w,d)` by simp[] >>
  drule_all mcopy_alloca_framed_frag >> strip_tac >>
  irule frag_exec_seq >> qexistsl_tac [`(\t. t = u)`, `mid`] >>
  conj_tac >- gvs[ci_mono_def] >>
  conj_tac >- gvs[ci_mono_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule frag_exec_conseq >> goal_assum (drule_at Any) >>
  simp[] >> qx_gen_tac `tt` >> strip_tac >>
  gvs[eval_operand_def]
QED
