(* TOP-LEVEL: Log saves retain compiler instruction-ID history. The
   argument-list compiler composes the corresponding expression facts;
   the memory-copy recursion is proved independently for every type. *)
Theory logArgumentIdFlow
Ancestors
  compileIdFlow typedCopyIdFlow copyIdFlow
  exprLowering stmtLowering context compileEnv list

Theorem compiler_id_flow_materialize_stack:
  !cenv ty src. compiler_id_flow (compile_materialize_vv cenv ty (StackValue ty src))
Proof
  rpt gen_tac >> simp_tac bool_ss [compile_materialize_vv_def, unwrap_value_def] >>
  rpt (FIRST [CHANGED_TAC (asm_simp_tac (srw_ss())
    [compiler_id_flow_alloc_buffer, compiler_id_flow_store_memory, compiler_id_flow_return]),
    irule compiler_id_flow_bind >> conj_tac >> rpt gen_tac,
    irule compiler_id_flow_ignore_bind >> conj_tac])
QED

Theorem compiler_id_flow_log_save_arg:
  !cenv ty src suffix. compiler_id_flow (compile_log_save_arg cenv ty src suffix)
Proof
  rpt gen_tac >> rw[compile_log_save_arg_def, compiler_id_flow_return, compiler_id_flow_materialize_stack]
QED

Theorem compiler_id_flow_log_eval_all:
  !args cenv.
    EVERY (\e. compiler_id_flow (lower_value compile_expr cenv (expr_type e) e)) args ==>
    compiler_id_flow (compile_log_eval_all cenv args)
Proof
  Induct_on `args` >- simp[Once compile_log_eval_all_def, compiler_id_flow_return] >>
  rpt gen_tac >> simp_tac bool_ss [EVERY_DEF, Once compile_log_eval_all_def, LET_THM] >> strip_tac >>
  rpt (FIRST [CHANGED_TAC (asm_simp_tac (srw_ss())
    [compiler_id_flow_log_save_arg, compiler_id_flow_return]),
    gen_tac, irule compiler_id_flow_bind >> conj_tac])
QED

Theorem compile_log_save_arg_id_history:
  !cenv ty src suffix cs saved cut.
    compile_log_save_arg cenv ty src suffix cs = (saved,cut) /\ compiler_id_history cs ==>
    compiler_id_history cut /\ cs.cs_next_id <= cut.cs_next_id
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`compile_log_save_arg cenv ty src suffix`, `cs`, `saved`, `cut`]
    mp_tac compiler_id_flow_result >> simp[compiler_id_flow_log_save_arg]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed Log argument instruction-ID flow: " ^ name)
  end) (DB.thms "logArgumentIdFlow")
