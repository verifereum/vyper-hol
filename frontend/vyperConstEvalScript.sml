Theory vyperConstEval
Ancestors
  vyperEvalPureExpr vyperContext vyperState vyperValue vyperAST
  vyperValueOperation

(* Integer constant expressions have no dependency on runtime state or nominal
   type resolution. Their arithmetic is the existing runtime arithmetic. *)
Definition closed_integer_def:
  closed_integer (Literal (BaseT (UintT bits)) (IntL i)) = T /\
  closed_integer (Literal (BaseT (IntT bits)) (IntL i)) = T /\
  closed_integer (Builtin (BaseT (UintT bits)) (Bop bop) [e1; e2]) =
    (closed_integer e1 /\ closed_integer e2) /\
  closed_integer (Builtin (BaseT (IntT bits)) (Bop bop) [e1; e2]) =
    (closed_integer e1 /\ closed_integer e2) /\
  closed_integer _ = F
End

Theorem closed_integer_value:
  !e. closed_integer e ==>
    !cx st. eval_pure_expr cx st e = NONE \/
      ?v. eval_pure_expr cx st e = SOME (Value v)
Proof
  ho_match_mp_tac closed_integer_ind >>
  rw[closed_integer_def] >>
  ONCE_REWRITE_TAC [eval_pure_expr_def] >>
  simp[evaluate_literal_def, builtin_args_length_ok_def] >>
  rpt CASE_TAC >> simp[]
QED

Theorem closed_integer_context_independent:
  !e. closed_integer e ==>
    !cx st cx' st'. eval_pure_expr cx st e = eval_pure_expr cx' st' e
Proof
  ho_match_mp_tac closed_integer_ind >>
  rw[closed_integer_def] >>
  simp[eval_pure_expr_def, builtin_args_length_ok_def] >>
  fs[] >>
  qpat_x_assum `!a b c d. _` (qspecl_then [`cx'`, `st'`, `cx`, `st`] assume_tac) >>
  qpat_x_assum `!a b c d. _` (qspecl_then [`cx'`, `st'`, `cx`, `st`] assume_tac) >>
  qpat_x_assum `closed_integer _` (mp_tac o MATCH_MP closed_integer_value) >>
  qpat_x_assum `closed_integer _` (mp_tac o MATCH_MP closed_integer_value) >>
  disch_then (qspecl_then [`cx`, `st`] mp_tac) >>
  disch_then strip_assume_tac >>
  disch_then (qspecl_then [`cx`, `st`] mp_tac) >>
  simp[] >> rpt strip_tac >>
  simp[read_result_def, return_def, evaluate_builtin_def, evaluate_type_def]
QED

(* Failure includes unsupported syntax and runtime arithmetic errors. *)
Definition eval_integer_constant_def:
  eval_integer_constant e =
    if closed_integer e then
      case eval_pure_expr empty_evaluation_context empty_state e of
      | SOME (Value (IntV i)) => SOME i
      | _ => NONE
    else NONE
End

Theorem eval_integer_constant_sound:
  eval_integer_constant e = SOME i ==>
  eval_expr cx e st = (INL (Value (IntV i)), st)
Proof
  rw[eval_integer_constant_def, AllCaseEqs()] >>
  irule eval_pure_expr_to_eval_expr_some >>
  drule closed_integer_context_independent >>
  metis_tac[]
QED
