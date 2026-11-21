Theory stmtSimLogArgsRun
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimProps exprLowering
  stmtSimLogArgs stmtSimLogArgsGrowth stmtSimLogTopics exprReasonOperand exprOperandVar vyperTypeSystem
  exprSimWordArgs supportedTypes  exprSimOps
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  gasStorage vyperStorageTrace vyperStorageFootprint
  fragGasMode fragGasPath list
  loweringSlice exprLoweringProps freshWrites fragExec emitHelperProps varsExt compileEnv
  vyperInterpreter vyperState vyperTyping vyperExprNoControl
  vyperEvalExprPreservesScopesDom
Libs
  monadsyntax


Theorem log_scalar_post_value_type:
  supported_scalar_type (expr_type e) ==> post_value_type cenv e = expr_type e
Proof
  strip_tac >> drule supported_scalar_word_or_bytestring >> strip_tac >> simp[]
QED

(* ===== Source sequencing ===== *)

Theorem eval_exprs_cons_bind:
  eval_exprs cx (e::args) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (eval_exprs cx args) (\vs. return (v::vs)))
Proof
  simp[FUN_EQ_THM, Once evaluate_def] >> gen_tac >>
  simp[bind_def] >> Cases_on `eval_expr cx e x` >> rename1 `_ = (raw, st1)` >>
  Cases_on `raw` >> simp[] >>
  Cases_on `read_result cx x' st1` >> rename1 `_ = (r2, st2)` >>
  Cases_on `r2` >> simp[]
QED

Theorem ignore_bind_bind_return:
  ignore_bind (bind a k) (return ()) =
    bind a (\v. ignore_bind (k v) (return ()))
Proof
  simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
  Cases_on `a x` >> rename1 `a x = (r1, st1)` >> Cases_on `r1` >> simp[]
QED

Theorem stmt_state_rel_any_gas_obs[local]:
  stmt_state_rel H ctx func cenv cx es s ==>
  stmt_state_rel H ctx func cenv cx (es with gas_obs := gs) s
Proof
  strip_tac >>
  `s with <|vs_gas_readings := s.vs_gas_readings;
            vs_inst_idx := s.vs_inst_idx|> = s` by
    simp[venomStateTheory.venom_state_component_equality] >>
  metis_tac[msg_gas_state_frame]
QED

(* The error results the arguments of a log may end in. *)
Definition log_args_res_ok_def:
  log_args_res_ok (r : value list + exception) <=>
    !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception)
End

Theorem log_head_admissible:
  gas_admissible (eval_exprs cx (e::args)) log_args_res_ok es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  rw[gas_admissible_def] >> Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `eval_exprs cx (e::args) (es with gas_obs := gs) = (INR ex, ee)` by
    simp[eval_exprs_cons_bind, Once bind_def] >>
  first_x_assum drule >> simp[log_args_res_ok_def]
QED

Theorem log_tail_admissible:
  gas_admissible (eval_exprs cx (e::args)) log_args_res_ok es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
            (es with gas_obs := xs ++ tail) = (INL v, mid with gas_obs := tail)) ==>
  gas_admissible (eval_exprs cx args) log_args_res_ok (mid with gas_obs := [])
Proof
  rw[gas_admissible_def] >>
  rename1 `eval_exprs cx args _ = (res2, ee2)` >>
  simp[log_args_res_ok_def] >> rpt strip_tac >> gvs[] >>
  `eval_exprs cx (e::args) (es with gas_obs := xs ++ gs) = (INR exc, ee2)` by
    (simp[eval_exprs_cons_bind, Once bind_def] >> simp[bind_def, return_def]) >>
  first_x_assum drule >> simp[log_args_res_ok_def]
QED
