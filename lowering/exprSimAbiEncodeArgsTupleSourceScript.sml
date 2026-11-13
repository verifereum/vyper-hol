Theory exprSimAbiEncodeArgsTupleSource
Ancestors
  exprSimAbiEncodeArgsTupleContracts exprSimAbiEncodeArgsTupleProbe
  supportedProgram supportedDecls
  vyperInterpreter vyperTypeSystem intCallReturn

Definition tuple_return_expr_def:
  tuple_return_expr = Builtin tuple_narrow (MakeArray NONE (Fixed 2))
    [Literal (BaseT (BytesT (Dynamic 32))) (BytesL [170w]);
     Literal (BaseT (BytesT (Dynamic 32))) (BytesL [187w])]
End

Definition tuple_function_def:
  tuple_function = FunctionDecl Internal Nonpayable F F "f" [] [] tuple_narrow
    [Return (SOME tuple_return_expr)]
End

Definition tuple_tops_def:
  tuple_tops = [tuple_function]
End

Theorem tuple_program_supported:
  supported_program tuple_tops
Proof
  EVAL_TAC
QED

Theorem tuple_function_lookup:
  lookup_callable_function deploy "f" tuple_tops =
    SOME (Nonpayable,F,[],[],tuple_narrow,[Return (SOME tuple_return_expr)]) /\
  IS_SOME (supported_function_decl tuple_tops (NONE,"f") Internal)
Proof
  EVAL_TAC
QED

Theorem tuple_return_value_typed:
  evaluate_type tenv tuple_narrow =
    SOME (TupleTV [BaseTV (BytesT (Dynamic 32)); BaseTV (BytesT (Dynamic 32))]) /\
  value_has_type (TupleTV [BaseTV (BytesT (Dynamic 32)); BaseTV (BytesT (Dynamic 32))])
    (ArrayV (TupleV [BytesV [170w]; BytesV [187w]]))
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, vyperValueTheory.type_slot_size_def,
                  vfmConstantsTheory.word_size_def]
QED

Theorem tuple_body_evaluation:
  eval_stmts cx [Return (SOME tuple_return_expr)] es =
    (INR (ReturnException (ArrayV (TupleV [BytesV [170w]; BytesV [187w]]))),es)
Proof
  EVAL_TAC
QED

Theorem tuple_call_evaluation:
  get_module_code cx NONE = SOME tuple_tops /\ ~MEM (NONE,"f") cx.stk ==>
  eval_expr cx tuple_call es =
    (INL (Value (ArrayV (TupleV [BytesV [170w]; BytesV [187w]]))),es)
Proof
  strip_tac >>
  `eval_expr cx (Call tuple_wide (IntCall (NONE,"f")) [] NONE) es =
    (INL (Value (ArrayV (TupleV [BytesV [170w]; BytesV [187w]]))),
     (es with scopes := [FEMPTY]) with scopes := es.scopes)` suffices_by
    simp[tuple_call_def] >>
  irule eval_expr_intcall_return >>
  simp[tuple_function_lookup, tuple_return_value_typed, tuple_body_evaluation] >>
  qexistsl [`FEMPTY`, `[]`] >> EVAL_TAC
QED
