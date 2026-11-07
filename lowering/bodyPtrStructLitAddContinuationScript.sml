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
