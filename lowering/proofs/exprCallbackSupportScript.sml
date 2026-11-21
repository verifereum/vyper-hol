Theory exprCallbackSupport
Ancestors
  exprCallbackContracts exprLowering vyperAST supportedExprTraverse list

Theorem call_callback_child_supported:
  MEM child (call_callback_children args d) /\
  ~supported_expr_exists R (Call ann target args d) ==>
  ~supported_expr_exists R child
Proof
  strip_tac >> fs[supported_expr_exists_def] >>
  Cases_on `MEM child args`
  >- metis_tac[supported_exprs_exists_every, EXISTS_MEM] >>
  Cases_on `MEM child (case d of NONE => [] | SOME x => [x])`
  >- (Cases_on `d` >> gvs[supported_expr_exists_def]) >>
  `?topic_expr. MEM topic_expr args /\ MEM child (raw_log_topic_exprs topic_expr)` by
    (fs[call_callback_children_def, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `~supported_expr_exists R topic_expr` by
    metis_tac[supported_exprs_exists_every, EXISTS_MEM] >>
  Cases_on `topic_expr` >> gvs[raw_log_topic_exprs_def] >>
  qmatch_asmsub_rename_tac `raw_log_topic_exprs (Builtin topic_ann bi es)` >>
  Cases_on `bi` >>
  gvs[raw_log_topic_exprs_def, supported_expr_exists_def] >>
  metis_tac[supported_exprs_exists_every, EXISTS_MEM]
QED
