(* Source typing for the value returned by a linked keyword operand. *)
Theory bodyExtKeywordScalarTypingMods
Ancestors
  bodySimStmtFacts exprBodyPreTypingProps vyperTypeExtCallCore
  vyperTypeExprSoundness exprSimHypsDefs compileEnv
Libs monadsyntax

Theorem expr_body_pre_mods_word_value:
  expr_body_pre_mods mods cenv cx env e es /\
  is_word_type (expr_type e) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
  ?tyv. evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
        value_has_type tyv v
Proof
  strip_tac >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac runtime_consistent_get_tenv >>
  drule_all_then mp_tac (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods) >>
  simp[value_runtime_typed_def]
QED
