Theory bodyPtrStructLitOwnershipRestrictions
Ancestors supportedExprTraverse exprLowering exprCallBounds list

Theorem ownership_exclusion_member:
  ~supported_exprs_exists p es /\ MEM e es ==>
  ~supported_expr_exists p e
Proof
  simp[supported_exprs_exists_every, EXISTS_MEM] >> metis_tac[]
QED

Theorem ownership_exclusion_array_member:
  ~supported_exprs_exists p args /\ 1 < LENGTH args /\
  HD (TL args) = Builtin av (MakeArray a b) elems /\ MEM e elems ==>
  ~supported_expr_exists p e
Proof
  Cases_on `args` >> simp[] >> Cases_on `t` >> simp[] >>
  rpt strip_tac >> gvs[supported_expr_exists_def] >>
  metis_tac[ownership_exclusion_member]
QED

Theorem ownership_exclusion_extcode_addr:
  ~supported_expr_exists p e /\ is_extcode e ==>
  ~supported_expr_exists p (extcode_addr_expr e)
Proof
  qid_spec_tac `e` >> recInduct is_extcode_ind >>
  simp[is_extcode_def, extcode_addr_expr_def, supported_expr_exists_def]
QED
