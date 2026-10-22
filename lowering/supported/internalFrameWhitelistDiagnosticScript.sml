(* Checked evidence for the #545 whitelist contract decision.
   No production admission predicate or boundary theorem is changed. *)
Theory internalFrameWhitelistDiagnostic
Ancestors
  supportedProgram supportedStmts supportedStmtTraverse supportedExprTraverse
  supportedNames supportedTypes vyperAST list

(* A Bool declaration meets all internal body conditions except the shape
   guard. Thus deleting that guard also requires explicit authorization to
   remove the shape conclusion from supported_internal_body_contract.
   The independent internal-call restriction is not implicated. *)
Theorem internal_local_shape_contract_obstruction:
  let b = [AnnAssign "y" (BaseT BoolT)
             (Literal (BaseT BoolT) (BoolL T))]
  in supported_function_bindings [] []
       (MAP FST (supported_stmts_bindings T b))
       (MAP FST (supported_stmts_bindings F b)) /\
     supported_stmts []
       (supported_stmts_bindings T b ++ supported_stmts_bindings F b) b /\
     ~supported_stmts_expr_exists expr_nonmain_type_root b /\
     ~supported_stmts_expr_exists expr_internal_call_root b /\
     ~supported_internal_stmts_shape b
Proof
  EVAL_TAC
QED
