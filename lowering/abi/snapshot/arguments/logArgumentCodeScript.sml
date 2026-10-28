(* TOP-LEVEL: the actual Log argument compiler contains each evaluation,
   save and suffix cut. Evaluation uses its per-expression append fact;
   saving and list composition are proved here without argument restrictions. *)
Theory logArgumentCode
Ancestors
  logArgumentCompile compileAppendProps typedCopyAppend copyAppend
  exprLowering stmtLowering context compileEnv emitHelper fragExec list

Theorem cs_appends_compile_materialize_stack:
  !cenv ty src. cs_appends (compile_materialize_vv cenv ty (StackValue ty src))
Proof
  rpt gen_tac >> simp_tac bool_ss [compile_materialize_vv_def, unwrap_value_def] >>
  rpt (FIRST [CHANGED_TAC (asm_simp_tac (srw_ss())
    [cs_appends_compile_alloc_buffer, cs_appends_compile_store_memory, cs_appends_return]),
    irule cs_appends_bind >> conj_tac >> rpt gen_tac,
    irule cs_appends_ignore_bind >> conj_tac])
QED

Theorem cs_appends_compile_log_save_arg:
  !cenv ty src suffix. cs_appends (compile_log_save_arg cenv ty src suffix)
Proof
  rpt gen_tac >> rw[compile_log_save_arg_def, cs_appends_return, cs_appends_compile_materialize_stack]
QED

Theorem cs_appends_compile_log_eval_all:
  !args cenv.
    EVERY (\e. cs_appends (lower_value compile_expr cenv (expr_type e) e)) args ==>
    cs_appends (compile_log_eval_all cenv args)
Proof
  Induct_on `args` >- simp[Once compile_log_eval_all_def, cs_appends_return] >>
  rpt gen_tac >> simp_tac bool_ss [EVERY_DEF, Once compile_log_eval_all_def, LET_THM] >> strip_tac >>
  rpt (FIRST [CHANGED_TAC (asm_simp_tac (srw_ss())
    [cs_appends_compile_log_save_arg, cs_appends_return]),
    gen_tac, irule cs_appends_bind >> conj_tac])
QED

Theorem compile_log_eval_all_cons_contains:
  !cenv e suffix cs args cs' func.
    EVERY (\arg. cs_appends (lower_value compile_expr cenv (expr_type arg) arg)) (e::suffix) /\
    compile_log_eval_all cenv (e::suffix) cs = (args,cs') /\ fn_has_code cs cs' func ==>
    ?arg_op load_cut saved save_cut rest.
      lower_value compile_expr cenv (expr_type e) e cs = (arg_op,load_cut) /\
      compile_log_save_arg cenv (lowered_value_type cenv e) arg_op suffix load_cut = (saved,save_cut) /\
      compile_log_eval_all cenv suffix save_cut = (rest,cs') /\
      args = (saved,lowered_value_type cenv e)::rest /\
      cs_extends cs load_cut /\ cs_extends load_cut save_cut /\ cs_extends save_cut cs' /\
      fn_has_code cs load_cut func /\ fn_has_code load_cut save_cut func /\ fn_has_code save_cut cs' func
Proof
  rpt gen_tac >> simp_tac bool_ss [EVERY_DEF, compile_log_eval_all_cons] >> strip_tac >>
  `cs_extends cs load_cut` by (drule_all cs_appends_result_extends >> simp[]) >>
  `cs_extends load_cut save_cut` by
    (qspecl_then [`compile_log_save_arg cenv (lowered_value_type cenv e) arg_op suffix`,
       `load_cut`, `saved`, `save_cut`] mp_tac cs_appends_result_extends >>
     simp[cs_appends_compile_log_save_arg]) >>
  `cs_extends save_cut cs'` by
    (qspecl_then [`compile_log_eval_all cenv suffix`, `save_cut`, `rest`, `cs'`]
       mp_tac cs_appends_result_extends >>
     simp[cs_appends_compile_log_eval_all]) >>
  `cs_extends load_cut cs'` by (irule cs_extends_trans >> qexists_tac `save_cut` >> simp[]) >>
  qspecl_then [`cs`, `load_cut`, `cs'`, `func`] mp_tac fn_has_code_split >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`load_cut`, `save_cut`, `cs'`, `func`] mp_tac fn_has_code_split >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qexistsl_tac [`arg_op`, `load_cut`, `saved`, `save_cut`, `rest`] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed general Log argument code containment: " ^ name)
  end) (DB.thms "logArgumentCode")
