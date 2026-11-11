Theory popNestedLocalPoppedOverlap
Ancestors
  targetPlaceSim exprSimHypsDefs vyperSubscriptOverlap allocLimits stmtLowering
  targetOverlapAccess

Theorem local_target_overlap_excludes_write:
  target_root bt = NameTarget id /\
  target_through_dynarray cenv bt /\
  ~target_subscript_overlap cenv bt idx ==>
  ~MEM (WriteAcc (LocalRef id)) (expr_accesses cenv.ce_modules idx) /\
  ~MEM RiskyAcc (expr_accesses cenv.ce_modules idx)
Proof
  strip_tac >> irule target_subscript_overlap_unwritten >>
  simp[target_root_local_nonconstant_read]
QED

Theorem pop_body_alloc_limits_target:
  expr_body_pre cenv cx env (Pop ann bt) es ==>
  alloc_limits_target cenv bt
Proof
  simp[expr_body_pre_def, alloc_limits_expr_def]
QED
