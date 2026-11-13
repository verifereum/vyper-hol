(* Source admissibility at the extract32 operand binding boundary. *)
Theory bodyMemTbExtract32Bind
Ancestors
  bodyMemTbExtract32Action gasContext gasOutcome exprSimDefs vyperState

Theorem extract32_source_admissible:
  gas_admissible (bind (eval_expr cx (TypeBuiltin ann Extract32 ret [src;off]))
    (read_result cx)) expr_res_ok es ==>
  gas_admissible (bind (eval_expr cx src) (read_result cx)) expr_res_ok es
Proof
  rewrite_tac[extract32_eval_action] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_admissible source _ _` >>
  gvs[gas_admissible_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >> simp[bind_def]
QED
