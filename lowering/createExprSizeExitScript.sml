(* Relate an oversized CREATE reached within one expression invocation
   to the source initcode-size check. *)
Theory createExprSizeExit
Ancestors
  vyperAST vyperCreate list createExprSizeExitDefs createSizeExitProxy createSizeExitCopy
  createSizeExitRaw createSizeExitBlueprint

Theorem create_expr_size_exit:
  !cx ty kind has_salt rof ks args d.
    EVERY (create_operand_completed_ok cx) (create_operand_order kind has_salt args) ==>
    create_expr_size_exit cx (Call ty (CreateTarget kind has_salt rof ks) args d)
Proof
  rpt gen_tac >> Cases_on `kind` >>
  simp[create_size_exit_proxy, create_size_exit_copy,
       create_size_exit_raw, create_size_exit_blueprint]
QED
