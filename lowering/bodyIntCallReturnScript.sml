(* Return-layout boundary facts for the internal-call body simulation. *)
Theory bodyIntCallReturn
Ancestors
  supportedProgram supportedTypes vyperAST stmtLowering

Theorem supported_copy_array_layout:
  supported_copy_types (ArrayT elem bound) src <=> src = ArrayT elem bound
Proof
  Cases_on `src` >>
  simp[supported_copy_types_def, supported_word_type_def, EQ_SYM_EQ]
QED

Theorem supported_copy_tuple_layout:
  supported_copy_types (TupleT tys) src <=> src = TupleT tys
Proof
  Cases_on `src` >>
  simp[supported_copy_types_def, supported_word_type_def, EQ_SYM_EQ]
QED

Theorem supported_program_function_return_layouts:
  supported_program tops /\
  MEM (FunctionDecl vis mut nr rr name args defaults ret ss) tops /\
  vis <> Deploy ==>
  supported_return_layouts ret ss
Proof
  strip_tac >> drule_all supported_program_declaration >>
  simp[supported_declaration_body_def]
QED

(* The void Return itself is independent of the function compile type.
   The full NoneT body bridge also needs typed exclusion of Return SOME. *)
Theorem compile_return_none_type_independent:
  compile_stmt cenv lctx ty (Return NONE) =
  compile_stmt cenv lctx ty' (Return NONE)
Proof
  simp[compile_stmt_def]
QED
