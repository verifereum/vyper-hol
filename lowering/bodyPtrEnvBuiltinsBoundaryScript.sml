(* Representation boundaries for environment-family pointer builtins. *)
Theory bodyPtrEnvBuiltinsBoundary
Ancestors
  bodyPtrDefs representationCleanPtr exprSimLen exprSimProps
  vyperValue vyperTyping valueEncoding loweringPosts venomState
  exprLowering compileEnv bodyPtrPreds bodySim exprOpenFirstOperand exprPtrUnwrap

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

Theorem body_expr_ptr_sim:
  body_expr_ptr_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es ==>
  expr_sim_ptr d ctx PG func cenv cx ty e es
Proof
  simp[body_expr_ptr_ok_def] >> metis_tac[]
QED

Theorem body_expr_ptr_vv_sim:
  body_expr_ptr_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty e es
Proof
  simp[body_expr_ptr_ok_def] >> metis_tac[]
QED

Theorem body_exprs_ptr_head:
  body_exprs_ptr_ok cx (e::es) ==> body_expr_ptr_ok cx e
Proof
  simp[body_exprs_ptr_ok_def]
QED

Theorem body_builtin_head_ptr_sim:
  body_exprs_ptr_ok cx (e::args) /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann bi (e::args)) es /\
  ((!n. bi <> Slice n) \/ ~is_extcode e) ==>
  expr_sim_ptr d ctx PG func cenv cx ty e es
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e es` by
    metis_tac[expr_body_pre_builtin_head] >>
  irule body_expr_ptr_sim >> metis_tac[body_exprs_ptr_head]
QED

Theorem body_builtin_head_ptr_vv_sim:
  body_exprs_ptr_ok cx (e::args) /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann bi (e::args)) es /\
  ((!n. bi <> Slice n) \/ ~is_extcode e) ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty e es
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e es` by
    metis_tac[expr_body_pre_builtin_head] >>
  irule body_expr_ptr_vv_sim >> metis_tac[body_exprs_ptr_head]
QED

Theorem body_expr_ptr_stack:
  (!d PG tops ctx func cenv env ty es.
     body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es ==>
     expr_sim_ptr d ctx PG func cenv cx ty e es) /\
  (!cenv ty sa. ?t op sb.
     compile_expr cenv ty e sa = (StackValue t op, sb)) /\
  (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
  body_expr_ptr_ok cx e
Proof
  strip_tac >> simp[body_expr_ptr_ok_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_ptr d ctx PG func cenv cx ty e es` by metis_tac[] >>
  conj_tac >- simp[] >> irule expr_vv_sim_ptr_stack >> metis_tac[]
QED

Theorem body_expr_ptr_of_vv:
  (!d PG tops ctx func cenv env ty es.
     body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es ==>
     expr_vv_sim_ptr d ctx PG func cenv cx ty e es) ==>
  body_expr_ptr_ok cx e
Proof
  strip_tac >> simp[body_expr_ptr_ok_def] >> rpt gen_tac >> strip_tac >>
  `expr_vv_sim_ptr d ctx PG func cenv cx ty e es` by metis_tac[] >>
  conj_tac >- (irule expr_sim_ptr_of_vv >> metis_tac[]) >> simp[]
QED
