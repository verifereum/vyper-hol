(* Source evaluation for the same Boolean-local branching operand. *)
Theory bodyPtrWordBuiltinsIntervalSource
Ancestors vyperInterpreter vyperState vyperValueOperation

Theorem word_interval_operand_source:
  lookup_scopes "b" es.scopes = SOME entry /\
  read_place cx (MemoryPlace "b" []) es = (INL (BoolV b), es) ==>
  eval_expr cx
    (IfExp (BaseT (IntT 256)) (Name (BaseT BoolT) "b")
      (Literal (BaseT (IntT 256)) (IntL 1))
      (Literal (BaseT (IntT 256)) (IntL 2))) es =
    (INL (Value (IntV (if b then 1 else 2))), es)
Proof
  strip_tac >>
  simp[Once evaluate_def] >>
  simp[Once evaluate_def, bind_def, get_scopes_def, type_check_def,
       return_def, assert_def, switch_BoolV_def, read_result_def] >>
  Cases_on `b` >>
  simp[Once evaluate_def, bind_def, return_def,
       evaluate_literal_def, conditional_result_def, ignore_bind_def,
       assert_def, read_result_def] >>
  simp[Once evaluate_def, return_def, conditional_result_def, bind_def,
       evaluate_literal_def]
QED
