(* Return-layout boundary facts for the internal-call body simulation. *)
Theory bodyIntCallReturn
Ancestors
  supportedProgram supportedTypes vyperAST stmtLowering

(* The void Return itself is independent of the function compile type.
   The full NoneT body bridge also needs typed exclusion of Return SOME. *)
Theorem compile_return_none_type_independent:
  compile_stmt cenv lctx ty (Return NONE) =
  compile_stmt cenv lctx ty' (Return NONE)
Proof
  simp[compile_stmt_def]
QED
