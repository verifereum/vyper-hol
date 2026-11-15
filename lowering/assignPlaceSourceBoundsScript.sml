Theory assignPlaceSourceBounds
Ancestors
  exprSimTypedAlloc annassignRelayoutSource loweringPosts stmtSimDefs
  words compileEnv

Theorem nonbytes_expr_val_at_bound:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx sty sa sb es v op s /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  ~is_word_type sty /\ ~is_bytestring_type sty /\
  eval_operand op s = SOME sw ==>
  w2n sw + type_memory_size stv < dimword (:256)
Proof
  strip_tac >> drule_all expr_val_at_bound >>
  drule_all nonbytes_evaluated_val_footprint >> simp[]
QED
