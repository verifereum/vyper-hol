(* TOP-LEVEL: the actual Log argument compiler splits into source-order
   evaluation, saving and the suffix. The source type retained in its result
   is the produced layout type, independently of the event field type. *)
Theory logArgumentCompile
Ancestors
  stmtLowering exprLowering context compileEnv vyperAST list pair

Theorem compile_log_eval_all_cons:
  !cenv e suffix cs args cs'.
    compile_log_eval_all cenv (e::suffix) cs = (args,cs') <=>
    ?arg_op load_cut saved save_cut rest.
      lower_value compile_expr cenv (expr_type e) e cs = (arg_op,load_cut) /\
      compile_log_save_arg cenv (lowered_value_type cenv e) arg_op suffix load_cut = (saved,save_cut) /\
      compile_log_eval_all cenv suffix save_cut = (rest,cs') /\
      args = (saved,lowered_value_type cenv e)::rest
Proof
  rpt gen_tac >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e cs` >>
  rename1 `lower_value compile_expr cenv (expr_type e) e cs = (arg_op,load_cut)` >>
  Cases_on `compile_log_save_arg cenv (lowered_value_type cenv e) arg_op suffix load_cut` >>
  rename1 `compile_log_save_arg cenv (lowered_value_type cenv e) arg_op suffix load_cut = (saved,save_cut)` >>
  simp[Once compile_log_eval_all_def, comp_bind_def, comp_return_def, LET_THM] >>
  Cases_on `compile_log_eval_all cenv suffix save_cut` >> simp[] >> EQ_TAC >> strip_tac >> gvs[]
QED

Theorem compile_log_eval_all_name_cons:
  !cenv ann id suffix cs args cs'.
    compile_log_eval_all cenv (Name ann id::suffix) cs = (args,cs') <=>
    ?arg_op load_cut saved save_cut rest.
      lower_value compile_expr cenv ann (Name ann id) cs = (arg_op,load_cut) /\
      compile_log_save_arg cenv ann arg_op suffix load_cut = (saved,save_cut) /\
      compile_log_eval_all cenv suffix save_cut = (rest,cs') /\ args = (saved,ann)::rest
Proof
  simp[compile_log_eval_all_cons, expr_type_def, lowered_value_type_def]
QED
