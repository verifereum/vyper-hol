(* Representation boundaries for environment-family pointer builtins. *)
Theory bodyPtrEnvBuiltinsBoundary
Ancestors
  bodyPtrDefs representationCleanPtr exprSimLen exprSimProps
  vyperValue vyperTyping valueEncoding loweringPosts venomState
  exprLowering compileEnv

Theorem ptr_mem_ok_header_clean:
  ptr_mem_ok cx ty v op G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand op s = SOME w /\
  (!mem. val_in_memory tv v (w2n w) mem ==>
         mem_word_at (w2n w) mem = n) ==>
  !i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         mem_word_at (w2n w) mem = n` by
    (rpt strip_tac >> first_x_assum irule >>
     gvs[ptr_mem_ok_def] >> metis_tac[]) >>
  drule robust_mem_word_at_clean >> simp[]
QED

(* Coverage of the actual allocation, rather than of the payload alone,
   is the boundary needed by all memory-result builtin consumers. *)
Theorem ptr_covers_buf_ok:
  ptr_covers G tn p s capacity /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= capacity ==>
  ptr_buf_ok cenv e (Var p) G s
Proof
  strip_tac >>
  gvs[ptr_covers_def, ptr_buf_ok_def, eval_operand_def] >>
  rpt strip_tac >> qexistsl [`b`, `sz'`] >> simp[]
QED

Theorem method_id_dynamic_result_capacity:
  type_memory_bytes cenv
    (lowered_value_type cenv
      (Builtin (BaseT (BytesT (Dynamic 4))) MethodId args)) = 64
Proof
  simp[lowered_value_type_def, type_memory_bytes_def, vyperASTTheory.expr_type_def]
QED
