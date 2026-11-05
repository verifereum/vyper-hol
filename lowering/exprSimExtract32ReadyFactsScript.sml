(* Pure result-type projections used at the counted tail boundary. *)
Theory exprSimExtract32ReadyFacts
Ancestors
  exprSimExtract32Source exprSimSource exprLoweringProps exprSimHyps
  vyperValue vyperTypeSystem vyperAST builtinBytes compileEnv
  entryDecodeStructure exprBopSimProps fragExec

Theorem extract32_ready_result_evaluates:
  expr_body_pre cenv cx env
    (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) args) es ==>
  evaluate_type (get_tenv cx) (BaseT bt) = SOME (BaseTV bt)
Proof
  strip_tac >> drule expr_body_pre_type_evaluates >>
  Cases_on `bt` >> simp[expr_type_def, evaluate_type_def, AllCaseEqs()] >>
  Cases_on `b` >> simp[evaluate_type_def, AllCaseEqs()]
QED

Theorem extract32_ready_result_word:
  extract32_result_base_ok bt /\
  evaluate_type tenv (BaseT bt) = SOME (BaseTV bt) ==>
  is_word_type (BaseT bt)
Proof
  Cases_on `bt` >> simp[extract32_result_base_ok_def, is_word_type_def, evaluate_type_def, AllCaseEqs()] >>
  Cases_on `b` >> simp[extract32_result_base_ok_def, is_word_type_def, evaluate_type_def, AllCaseEqs()]
QED

Theorem extract32_ready_result_width:
  evaluate_type tenv (BaseT bt) = SOME (BaseTV bt) ==>
  (case bt of UintT k => k <= 256 | IntT k => 0 < k /\ k <= 256 |
              BytesT (Fixed k) => k <= 32 | _ => T)
Proof
  Cases_on `bt` >> simp[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `b` >> simp[evaluate_type_def, AllCaseEqs()]
QED

Theorem extract32_ready_prepared_id:
  lower_value compile_expr cenv ty src sa = (src_op,sx) /\
  emit_op opc [src_op] sx = (len,sy) /\
  emit_op ADD [src_op; Lit 32w] sy = (dp,sm) ==>
  sa.cs_next_id <= sm.cs_next_id
Proof
  strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  imp_res_tac emit_op_next_id >> decide_tac
QED
