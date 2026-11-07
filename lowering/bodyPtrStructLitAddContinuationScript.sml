Theory bodyPtrStructLitAddContinuation
Ancestors bodyPtrStructLitCountedAdd bodyPtrStructLitSourceFrame
  bodyPtrStructLitFreshGhost bodyPtrStructLitPostAdd exprOperandVar
  exprLoweringProps emitHelperProps freshWrites context compileEnv
  bodyPtrDefs venomState

Theorem raw_child_add_source_frame:
  compile_expr ce (expr_type e) e sb = (vv,sc) /\
  local_ptrs_reserved ce sb /\
  emit_op ADD [Var p; Lit off] sc = (Var dst,sm) /\
  vv_post ctx fn ce cx e es sb sc t ee tv vv s ==>
  vv_post ctx fn ce cx e es sb sm t ee tv vv
    (update_var dst w s with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> irule vv_post_update_var_pc >> simp[] >>
  qexists `sc` >> simp[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule (cj 1 compile_expr_grows) >> strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sc x` by
    metis_tac[compiler_compile_var] >>
  gvs[not_fresh_at_def]
QED

Theorem ptr_buf_ok_operand_frame:
  ptr_buf_ok ce e op G s /\
  eval_operand op s' = eval_operand op s /\
  (!x. op = Var x ==> FLOOKUP G' x = FLOOKUP G x) ==>
  ptr_buf_ok ce e op G' s'
Proof
  simp[ptr_buf_ok_def] >> metis_tac[]
QED

Theorem ptr_buf_ok_fresh_add:
  ptr_buf_ok ce e op G s /\ (!x. op = Var x ==> x <> dst) ==>
  ptr_buf_ok ce e op
    (step_prov PG G (mk_inst id ADD [left;right] [dst]) (update_var dst w s))
    (update_var dst w s)
Proof
  strip_tac >> irule ptr_buf_ok_operand_frame >>
  qexistsl [`G`, `s`] >> simp[] >>
  metis_tac[fresh_add_operand_frame]
QED
